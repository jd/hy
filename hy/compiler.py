# -*- encoding: utf-8 -*-
#
# Copyright (c) 2013 Paul Tagliamonte <paultag@debian.org>
# Copyright (c) 2013 Julien Danjou <julien@danjou.info>
#
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.

from hy.errors import HyError

from hy.models.lambdalist import HyLambdaListKeyword
from hy.models.expression import HyExpression
from hy.models.keyword import HyKeyword
from hy.models.integer import HyInteger
from hy.models.complex import HyComplex
from hy.models.string import HyString
from hy.models.symbol import HySymbol
from hy.models.float import HyFloat
from hy.models.list import HyList
from hy.models.dict import HyDict

from hy.util import str_type

import codecs
import copy
import traceback
import ast
import sys


class HyCompileError(HyError):
    def __init__(self, exception, traceback=None):
        self.exception = exception
        self.traceback = traceback

    def __str__(self):
        if isinstance(self.exception, HyTypeError):
            return str(self.exception)
        if self.traceback:
            tb = "".join(traceback.format_tb(self.traceback)).strip()
        else:
            tb = "No traceback available. 😟"
        return("Internal Compiler Bug 😱\n⤷ %s: %s\nCompilation traceback:\n%s"
               % (self.exception.__class__.__name__,
                  self.exception, tb))


class HyTypeError(TypeError):
    def __init__(self, expression, message):
        super(HyTypeError, self).__init__(message)
        self.expression = expression

    def __str__(self):
        return (super(HyTypeError, self).__str__() + " (line %s, column %d)"
                % (self.expression.start_line,
                   self.expression.start_column))


_compile_table = {}


def ast_str(foobar):
    if sys.version_info[0] >= 3:
        return str(foobar)

    try:
        return str(foobar)
    except UnicodeEncodeError:
        pass

    enc = codecs.getencoder('punycode')
    foobar, _ = enc(foobar)
    return "hy_%s" % (str(foobar).replace("-", "_"))


def builds(_type):
    def _dec(fn):
        _compile_table[_type] = fn
        return fn
    return _dec


class Result(object):
    """
    Smart representation of the result of a hy->AST compilation

    This object tries to reconcile the hy world, where everything can be used
    as an expression, with the Python world, where statements and expressions
    need to coexist.

    To do so, we represent a compiler result as a list of statements `stmts`,
    terminated by an expression context `expr`. The expression context is used
    when the compiler needs to use the result as an expression.

    Results are chained by addition: adding two results together returns a
    Result representing the succession of the two Results' statements, with
    the second Result's expression context.

    We make sure that a non-empty expression context does not get clobbered by
    adding more results, by checking accesses to the expression context. We
    assume that the context has been used, or deliberately ignored, if it has
    been accessed.

    The Result object is interoperable with python AST objects: when an AST
    object gets added to a Result object, it gets converted on-the-fly.
    """
    __slots__ = ("imports", "stmts", "temp_variables", "_expr", "__used_expr")

    def __init__(self, *args, **kwargs):
        if args:
            # emulate kw-only args for future bits.
            raise TypeError("Yo: Hacker: don't pass me real args, dingus")

        self.imports = []
        self.stmts = []
        self.temp_variables = []
        self._expr = None

        self.__used_expr = False

        # XXX: Make sure we only have AST where we should.
        for kwarg in kwargs:
            if kwarg not in ["imports", "stmts", "expr", "temp_variables"]:
                raise TypeError(
                    "%s() got an unexpected keyword argument '%s'" % (
                        self.__class__.__name__, kwarg))
            setattr(self, kwarg, kwargs[kwarg])

    @property
    def expr(self):
        self.__used_expr = True
        return self._expr

    @expr.setter
    def expr(self, value):
        self.__used_expr = False
        self._expr = value

    def is_expr(self):
        """Check whether I am a pure expression"""
        return self._expr and not (self.imports or self.stmts)

    @property
    def force_expr(self):
        """Force the expression context of the Result.

        If there is no expression context, we return a "None" expression.
        """
        if not self.expr:
            # Spoof the position of the last statement for our generated None
            lineno = 0
            col_offset = 0
            if self.stmts:
                lineno = self.stmts[-1].lineno
                col_offset = self.stmts[-1].col_offset

            return ast.Name(id=ast_str("None"),
                            arg=ast_str("None"),
                            ctx=ast.Load(),
                            lineno=lineno,
                            col_offset=col_offset)
            # XXX: Likely raise Exception here - this will assertionfail
            #      pypy since the ast will be out of numerical order.
        else:
            return self.expr

    def expr_as_stmt(self):
        """Convert the Result's expression context to a statement

        This is useful when we want to use the stored expression in a
        statement context (for instance in a code branch).

        We drop bare names because they can't have any side effect, and they
        make the generated code ugly.

        If there is no expression context, return an empty result.
        """
        if self.expr and not isinstance(self.expr, ast.Name):
            return Result() + ast.Expr(lineno=self.expr.lineno,
                                       col_offset=self.expr.col_offset,
                                       value=self.expr)
        else:
            return Result()

    def rename(self, new_name):
        """Rename the Result's temporary variables to a `new_name`.

        We know how to handle ast.Names and ast.FunctionDefs.
        """
        new_name = ast_str(new_name)
        for var in self.temp_variables:
            if isinstance(var, ast.Name):
                var.id = new_name
                var.arg = new_name
            elif isinstance(var, ast.FunctionDef):
                var.name = new_name
            else:
                raise TypeError("Don't know how to rename a %s!" % (
                    var.__class__.__name__))
        self.temp_variables = []

    def __add__(self, other):
        # If we add an ast statement, convert it first
        if isinstance(other, ast.stmt):
            return self + Result(stmts=[other])

        # If we add an ast expression, clobber the expression context
        if isinstance(other, ast.expr):
            return self + Result(expr=other)

        if not isinstance(other, Result):
            raise TypeError("Can't add %r with non-compiler result %r" % (
                self, other))

        # Check for expression context clobbering
        if self.expr and not self.__used_expr:
            traceback.print_stack()
            print("Bad boy clobbered expr %s with %s" % (
                ast.dump(self.expr),
                ast.dump(other.expr)))

        # Fairly obvious addition
        result = Result()
        result.imports = self.imports + other.imports
        result.stmts = self.stmts + other.stmts
        result.expr = other.expr
        result.temp_variables = other.temp_variables
        return result

    def __str__(self):
        return "Result(imports=[%s], stmts=[%s], expr=%s)" % (
            ", ".join(ast.dump(x) for x in self.imports),
            ", ".join(ast.dump(x) for x in self.stmts),
            ast.dump(self.expr) if self.expr else None,
        )


def _collect(results):
    """Collect the expression contexts from a list of results

    This returns a list of the expression contexts, and the sum of the Result
    objects passed as arguments.
    """
    compiled_exprs = []
    ret = Result()
    for result in results:
        ret += result
        compiled_exprs.append(ret.force_expr)
    return compiled_exprs, ret


def _branch(results):
    """Make a branch out of a list of Result objects

    This generates a Result from the given sequence of Results, forcing each
    expression context as a statement before the next result is used.

    We keep the expression context of the last argument for the returned Result
    """
    results = list(results)
    ret = Result()
    for result in results[:-1]:
        ret += result
        ret += result.expr_as_stmt()

    for result in results[-1:]:
        ret += result

    return ret


def _raise_wrong_args_number(expression, error):
    raise HyTypeError(expression,
                      error % (expression.pop(0),
                               len(expression)))


def checkargs(exact=None, min=None, max=None):
    def _dec(fn):
        def checker(self, expression):
            if exact is not None and (len(expression) - 1) != exact:
                _raise_wrong_args_number(
                    expression, "`%%s' needs %d arguments, got %%d" % exact)

            if min is not None and (len(expression) - 1) < min:
                _raise_wrong_args_number(
                    expression,
                    "`%%s' needs at least %d arguments, got %%d" % (min))

            if max is not None and (len(expression) - 1) > max:
                _raise_wrong_args_number(
                    expression,
                    "`%%s' needs at most %d arguments, got %%d" % (max))

            return fn(self, expression)

        return checker
    return _dec


class HyASTCompiler(object):

    def __init__(self):
        self.returnable = False
        self.anon_fn_count = 0
        self.anon_var_count = 0

    def get_anon_var(self):
        self.anon_var_count += 1
        return "_hy_anon_var_%s" % self.anon_var_count

    def get_anon_fn(self):
        self.anon_fn_count += 1
        return "_hy_anon_fn_%d" % self.anon_fn_count

    def compile_atom(self, atom_type, atom):
        if atom_type in _compile_table:
            ret = _compile_table[atom_type](self, atom)
            if not isinstance(ret, Result):
                ret = Result() + ret
            return ret
        else:
            return None

    def compile(self, tree):
        try:
            _type = type(tree)
            ret = self.compile_atom(_type, tree)
            if ret:
                return ret
        except HyCompileError:
            # compile calls compile, so we're going to have multiple raise
            # nested; so let's re-raise this exception, let's not wrap it in
            # another HyCompileError!
            raise
        except Exception as e:
            raise HyCompileError(e, sys.exc_info()[2])

        raise HyCompileError(Exception("Unknown type: `%s'" % _type))

    def _compile_collect(self, exprs):
        return _collect(self.compile(expr) for expr in exprs)

    def _compile_branch(self, exprs):
        return _branch(self.compile(expr) for expr in exprs)

    def _parse_lambda_list(self, exprs):
        """ Return FunctionDef parameter values from lambda list."""
        ret = Result()
        args = []
        defaults = []
        varargs = None
        kwargs = None
        lambda_keyword = None

        for expr in exprs:

            if isinstance(expr, HyLambdaListKeyword):
                if expr not in expr._valid_types:
                    raise HyCompileError("{0} is not a valid "
                                         "lambda-keyword.".format(repr(expr)))
                if expr == "&rest" and lambda_keyword is None:
                    lambda_keyword = expr
                elif expr == "&optional":
                    lambda_keyword = expr
                elif expr == "&key":
                    lambda_keyword = expr
                elif expr == "&kwargs":
                    lambda_keyword = expr
                else:
                    raise HyCompileError("{0} is in an invalid "
                                         "position.".format(repr(expr)))
                # we don't actually care about this token, so we set
                # our state and continue to the next token...
                continue

            if lambda_keyword is None:
                args.append(expr)
            elif lambda_keyword == "&rest":
                if varargs:
                    raise HyCompileError("There can only be one "
                                         "&rest argument")
                varargs = str(expr)
            elif lambda_keyword == "&key":
                if type(expr) != HyDict:
                    raise TypeError("There can only be one &key "
                                    "argument")
                else:
                    if len(defaults) > 0:
                        raise HyCompileError("There can only be "
                                             "one &key argument")
                    # As you can see, Python has a funny way of
                    # defining keyword arguments.
                    for k, v in expr.items():
                        args.append(k)
                        ret += self.compile(v)
                        defaults.append(ret.force_expr)
            elif lambda_keyword == "&optional":
                # not implemented yet.
                pass
            elif lambda_keyword == "&kwargs":
                if kwargs:
                    raise HyCompileError("There can only be one "
                                         "&kwargs argument")
                kwargs = str(expr)

        return ret, args, defaults, varargs, kwargs

    def _storeize(self, name):
        """Transform `target` into an ast.Store() context"""
        if isinstance(name, Result):
            if not name.is_expr():
                raise TypeError("Can't assign to a non-expr")
            name = name.expr

        if isinstance(name, ast.Tuple):
            for x in name.elts:
                x = self._storeize(x)
        name.ctx = ast.Store()
        return name

    @builds(list)
    def compile_raw_list(self, entries):
        ret = self._compile_branch(entries)
        ret += ret.expr_as_stmt()
        return ret

    @builds("do")
    @builds("progn")
    def compile_progn(self, expression):
        expression.pop(0)
        return self._compile_branch(expression)

    @builds("if")
    @checkargs(min=2, max=3)
    def compile_if(self, expression):
        expression.pop(0)
        cond = self.compile(expression.pop(0))

        body = self.compile(expression.pop(0))
        orel = Result()
        if expression:
            orel = self.compile(expression.pop(0))

        # We want to hoist the statements from the condition
        ret = cond

        if body.stmts or orel.stmts:
            # We have statements in our bodies
            # Get a temporary variable for the result storage
            var = self.get_anon_var()
            name = ast.Name(id=ast_str(var), arg=ast_str(var),
                            ctx=ast.Store(),
                            lineno=expression.start_line,
                            col_offset=expression.start_column)

            # Store the result of the body
            body += ast.Assign(targets=[name],
                               value=body.force_expr,
                               lineno=expression.start_line,
                               col_offset=expression.start_column)

            # and of the else clause
            orel += ast.Assign(targets=[name],
                               value=orel.force_expr,
                               lineno=expression.start_line,
                               col_offset=expression.start_column)

            # Then build the if
            ret += ast.If(test=ret.force_expr,
                          body=body.stmts,
                          orelse=orel.stmts,
                          lineno=expression.start_line,
                          col_offset=expression.start_column)

            # And make our expression context our temp variable
            expr_name = ast.Name(id=ast_str(var), arg=ast_str(var),
                                 ctx=ast.Load(),
                                 lineno=expression.start_line,
                                 col_offset=expression.start_column)

            ret += Result(expr=expr_name, temp_variables=[expr_name, name])
        else:
            # Just make that an if expression
            ret += ast.IfExp(test=ret.force_expr,
                             body=body.force_expr,
                             orelse=orel.force_expr,
                             lineno=expression.start_line,
                             col_offset=expression.start_column)
        return ret

    @builds("print")
    def compile_print_expression(self, expr):
        call = expr.pop(0)  # print
        values, ret = self._compile_collect(expr)

        if sys.version_info[0] >= 3:
            call = self.compile(call)
            ret += call
            ret += ast.Call(func=call.expr,
                            args=values,
                            keywords=[],
                            starargs=None,
                            kwargs=None,
                            lineno=expr.start_line,
                            col_offset=expr.start_column)
        else:
            ret += ast.Print(
                lineno=expr.start_line,
                col_offset=expr.start_column,
                dest=None,
                values=values,
                nl=True)

        return ret

    @builds("assert")
    @checkargs(1)
    def compile_assert_expression(self, expr):
        expr.pop(0)  # assert
        e = expr.pop(0)
        ret = self.compile(e)
        ret += ast.Assert(test=ret.force_expr,
                          msg=None,
                          lineno=e.start_line,
                          col_offset=e.start_column)

        return ret

    @builds("global")
    @checkargs(1)
    def compile_global_expression(self, expr):
        expr.pop(0)  # global
        e = expr.pop(0)
        return ast.Global(names=[ast_str(e)],
                          lineno=e.start_line,
                          col_offset=e.start_column)

    @builds("lambda")
    @checkargs(2)
    def compile_lambda_expression(self, expr):
        expr.pop(0)
        sig = expr.pop(0)
        body = self.compile(expr.pop(0))

        body += ast.Lambda(
            lineno=expr.start_line,
            col_offset=expr.start_column,
            args=ast.arguments(args=[
                ast.Name(arg=ast_str(x), id=ast_str(x),
                         ctx=ast.Param(),
                         lineno=x.start_line,
                         col_offset=x.start_column)
                for x in sig],
                vararg=None,
                kwarg=None,
                defaults=[],
                kwonlyargs=[],
                kw_defaults=[]),
            body=body.force_expr)

        return body

    @builds("yield")
    @checkargs(max=1)
    def compile_yield_expression(self, expr):
        expr.pop(0)
        ret = Result()

        value = None
        if expr != []:
            ret += self.compile(expr.pop(0))
            value = ret.force_expr

        ret += ast.Yield(
            value=value,
            lineno=expr.start_line,
            col_offset=expr.start_column)

        return ret

    @builds(",")
    def compile_tuple(self, expr):
        expr.pop(0)
        elts, ret = self._compile_collect(expr)
        ret += ast.Tuple(elts=elts,
                         lineno=expr.start_line,
                         col_offset=expr.start_column,
                         ctx=ast.Load())
        return ret

    @builds("list_comp")
    @checkargs(min=2, max=3)
    def compile_list_comprehension(self, expr):
        # (list-comp expr (target iter) cond?)
        expr.pop(0)
        expression = expr.pop(0)
        tar_it = iter(expr.pop(0))
        targets = zip(tar_it, tar_it)

        cond = self.compile(expr.pop(0)) if expr != [] else Result()

        generator_res = Result()
        generators = []
        for target, iterable in targets:
            comp_target = self.compile(target)
            target = self._storeize(comp_target)
            generator_res += self.compile(iterable)
            generators.append(ast.comprehension(
                target=target,
                iter=generator_res.force_expr,
                ifs=[]))

        if cond.expr:
            generators[-1].ifs.append(cond.expr)

        compiled_expression = self.compile(expression)
        ret = compiled_expression + generator_res + cond
        ret += ast.ListComp(
            lineno=expr.start_line,
            col_offset=expr.start_column,
            elt=compiled_expression.force_expr,
            generators=generators)

        return ret

    @builds("kwapply")
    @checkargs(2)
    def compile_kwapply_expression(self, expr):
        expr.pop(0)  # kwapply
        call = self.compile(expr.pop(0))
        kwargs = expr.pop(0)

        if type(call.expr) != ast.Call:
            raise HyTypeError(expr, "kwapplying a non-call")

        if type(kwargs) != HyDict:
            raise TypeError("kwapplying with a non-dict")

        keywords = []
        ret = Result()
        for x in kwargs:
            ret += self.compile(kwargs[x])
            keywords.append(ast.keyword(arg=ast_str(x),
                                        value=ret.force_expr))

        call.expr.keywords = keywords

        return ret + call

    @builds("not")
    @builds("~")
    @checkargs(1)
    def compile_unary_operator(self, expression):
        ops = {"not": ast.Not,
               "~": ast.Invert}
        operator = expression.pop(0)
        operand = self.compile(expression.pop(0))

        operand += ast.UnaryOp(op=ops[operator](),
                               operand=operand.expr,
                               lineno=operator.start_line,
                               col_offset=operator.start_column)
        return operand

    @builds("and")
    @builds("or")
    @checkargs(min=2)
    def compile_logical_or_and_and_operator(self, expression):
        ops = {"and": ast.And,
               "or": ast.Or}
        operator = expression.pop(0)
        values, ret = self._compile_collect(expression)

        ret += ast.BoolOp(op=ops[operator](),
                          lineno=operator.start_line,
                          col_offset=operator.start_column,
                          values=values)
        return ret

    @builds("=")
    @builds("!=")
    @builds("<")
    @builds("<=")
    @builds(">")
    @builds(">=")
    @builds("is")
    @builds("in")
    @builds("is_not")
    @builds("not_in")
    @checkargs(min=2)
    def compile_compare_op_expression(self, expression):
        ops = {"=": ast.Eq, "!=": ast.NotEq,
               "<": ast.Lt, "<=": ast.LtE,
               ">": ast.Gt, ">=": ast.GtE,
               "is": ast.Is, "is_not": ast.IsNot,
               "in": ast.In, "not_in": ast.NotIn}

        inv = expression.pop(0)
        op = ops[inv]
        ops = [op() for x in range(1, len(expression))]

        e = expression[0]
        exprs, ret = self._compile_collect(expression)

        return ret + ast.Compare(left=exprs[0],
                                 ops=ops,
                                 comparators=exprs[1:],
                                 lineno=e.start_line,
                                 col_offset=e.start_column)

    @builds("+")
    @builds("%")
    @builds("/")
    @builds("//")
    @builds("*")
    @builds("**")
    @builds("<<")
    @builds(">>")
    @builds("|")
    @builds("^")
    @builds("&")
    @checkargs(min=2)
    def compile_maths_expression(self, expression):
        ops = {"+": ast.Add,
               "/": ast.Div,
               "//": ast.FloorDiv,
               "*": ast.Mult,
               "-": ast.Sub,
               "%": ast.Mod,
               "**": ast.Pow,
               "<<": ast.LShift,
               ">>": ast.RShift,
               "|": ast.BitOr,
               "^": ast.BitXor,
               "&": ast.BitAnd}

        inv = expression.pop(0)
        op = ops[inv]

        ret = self.compile(expression.pop(0))
        for child in expression:
            left_expr = ret.force_expr
            ret += self.compile(child)
            right_expr = ret.force_expr
            ret += ast.BinOp(left=left_expr,
                             op=op(),
                             right=right_expr,
                             lineno=child.start_line,
                             col_offset=child.start_column)
        return ret

    @builds("-")
    @checkargs(min=1)
    def compile_maths_expression_sub(self, expression):
        if len(expression) > 2:
            return self.compile_maths_expression(expression)
        else:
            arg = expression[1]
            ret = self.compile(arg)
            ret += ast.UnaryOp(op=ast.USub(),
                               operand=ret.force_expr,
                               lineno=arg.start_line,
                               col_offset=arg.start_column)
            return ret

    @builds("+=")
    @builds("/=")
    @builds("//=")
    @builds("*=")
    @builds("_=")
    @builds("%=")
    @builds("**=")
    @builds("<<=")
    @builds(">>=")
    @builds("|=")
    @builds("^=")
    @builds("&=")
    @checkargs(2)
    def compile_augassign_expression(self, expression):
        ops = {"+=": ast.Add,
               "/=": ast.Div,
               "//=": ast.FloorDiv,
               "*=": ast.Mult,
               "_=": ast.Sub,
               "%=": ast.Mod,
               "**=": ast.Pow,
               "<<=": ast.LShift,
               ">>=": ast.RShift,
               "|=": ast.BitOr,
               "^=": ast.BitXor,
               "&=": ast.BitAnd}

        op = ops[expression[0]]

        target = self._storeize(self.compile(expression[1]))
        ret = self.compile(expression[2])

        ret += ast.AugAssign(
            target=target,
            value=ret.force_expr,
            op=op(),
            lineno=expression.start_line,
            col_offset=expression.start_column)

        return ret

    @builds(HyExpression)
    def compile_expression(self, expression):
        fn = expression[0]
        func = None
        if isinstance(fn, HyString):
            ret = self.compile_atom(fn, expression)
            if ret:
                return ret
            if fn.startswith("."):
                # (.split "test test") -> "test test".split()

                # Get the attribute name
                ofn = fn
                fn = HySymbol(ofn[1:])
                fn.replace(ofn)

                # Get the object we want to take an attribute from
                func = self.compile(expression.pop(1))

                # And get the attribute
                func += ast.Attribute(lineno=fn.start_line,
                                      col_offset=fn.start_column,
                                      value=func.force_expr,
                                      attr=ast_str(fn),
                                      ctx=ast.Load())

        if not func:
            func = self.compile(fn)
        args, ret = self._compile_collect(expression[1:])

        ret += ast.Call(func=func.expr,
                        args=args,
                        keywords=[],
                        starargs=None,
                        kwargs=None,
                        lineno=expression.start_line,
                        col_offset=expression.start_column)

        return func + ret

    @builds("def")
    @builds("setf")
    @builds("setv")
    @checkargs(2)
    def compile_def_expression(self, expression):
        expression.pop(0)
        name = expression.pop(0)
        result = self.compile(expression.pop(0))

        if result.temp_variables and isinstance(name, HyString):
            result.rename(name)
            return result

        ld_name = self.compile(name)
        st_name = self._storeize(copy.deepcopy(ld_name))

        result += ast.Assign(
            lineno=expression.start_line,
            col_offset=expression.start_column,
            targets=[st_name], value=result.force_expr)

        result += ld_name
        return result

    @builds("foreach")
    @checkargs(min=1)
    def compile_for_expression(self, expression):
        expression.pop(0)  # for
        target_name, iterable = expression.pop(0)
        target = self._storeize(self.compile(target_name))

        ret = Result()

        orel = Result()
        # (foreach [] body (else …))
        if expression and expression[-1][0] == HySymbol("else"):
            else_expr = expression.pop()
            if len(else_expr) > 2:
                raise HyTypeError(
                    else_expr,
                    "`else' statement in `foreach' should have at most one argument")
            elif len(else_expr) == 2:
                orel += self.compile(else_expr[1])
                orel += orel.expr_as_stmt()

        ret += self.compile(iterable)

        body = self._compile_branch(expression)
        body += body.expr_as_stmt()

        ret += ast.For(lineno=expression.start_line,
                       col_offset=expression.start_column,
                       target=target,
                       iter=ret.force_expr,
                       body=body.stmts,
                       orelse=orel.stmts)

        return ret

    @builds("while")
    @checkargs(min=2)
    def compile_while_expression(self, expr):
        expr.pop(0)  # "while"
        ret = self.compile(expr.pop(0))

        body = self._compile_branch(expr)
        body += body.expr_as_stmt()

        ret += ast.While(test=ret.force_expr,
                         body=body.stmts,
                         orelse=[],
                         lineno=expr.start_line,
                         col_offset=expr.start_column)

        return ret

    @builds(HyList)
    def compile_list(self, expression):
        elts, ret = self._compile_collect(expression)
        ret += ast.List(elts=elts,
                        ctx=ast.Load(),
                        lineno=expression.start_line,
                        col_offset=expression.start_column)
        return ret

    @builds("fn")
    @checkargs(min=1)
    def compile_function_def(self, expression):
        expression.pop(0)

        name = self.get_anon_fn()

        arglist = expression.pop(0)
        ret, args, defaults, stararg, kwargs = self._parse_lambda_list(arglist)
        body = self._compile_branch(expression)
        if body.expr:
            body += ast.Return(value=body.expr,
                               lineno=body.expr.lineno,
                               col_offset=body.expr.col_offset)

        if not body.stmts:
            body += ast.Pass(lineno=expression.start_line,
                             col_offset=expression.start_column)

        ret += ast.FunctionDef(name=name,
                               lineno=expression.start_line,
                               col_offset=expression.start_column,
                               args=ast.arguments(
                                   args=[
                                       ast.Name(
                                           arg=ast_str(x), id=ast_str(x),
                                           ctx=ast.Param(),
                                           lineno=x.start_line,
                                           col_offset=x.start_column)
                                       for x in args],
                                   vararg=stararg,
                                   kwarg=kwargs,
                                   kwonlyargs=[],
                                   kw_defaults=[],
                                   defaults=defaults),
                               body=body.stmts,
                               decorator_list=[])

        ast_name = ast.Name(id=name,
                            arg=name,
                            ctx=ast.Load(),
                            lineno=expression.start_line,
                            col_offset=expression.start_column)

        ret += Result(expr=ast_name, temp_variables=[ast_name, ret.stmts[-1]])

        return ret

    @builds(HyInteger)
    def compile_integer(self, number):
        return ast.Num(n=int(number),
                       lineno=number.start_line,
                       col_offset=number.start_column)

    @builds(HyFloat)
    def compile_float(self, number):
        return ast.Num(n=float(number),
                       lineno=number.start_line,
                       col_offset=number.start_column)

    @builds(HyComplex)
    def compile_complex(self, number):
        return ast.Num(n=complex(number),
                       lineno=number.start_line,
                       col_offset=number.start_column)

    @builds(HySymbol)
    def compile_symbol(self, symbol):
        if "." in symbol:
            glob, local = symbol.rsplit(".", 1)
            glob = HySymbol(glob).replace(symbol)
            ret = self.compile_symbol(glob)

            ret = ast.Attribute(
                lineno=symbol.start_line,
                col_offset=symbol.start_column,
                value=ret,
                attr=ast_str(local),
                ctx=ast.Load()
            )
            return ret

        return ast.Name(id=ast_str(symbol),
                        arg=ast_str(symbol),
                        ctx=ast.Load(),
                        lineno=symbol.start_line,
                        col_offset=symbol.start_column)

    @builds(HyString)
    def compile_string(self, string):
        return ast.Str(s=str_type(string),
                       lineno=string.start_line,
                       col_offset=string.start_column)

    @builds(HyKeyword)
    def compile_keyword(self, keyword):
        return ast.Str(s=str_type(keyword),
                       lineno=keyword.start_line,
                       col_offset=keyword.start_column)

    @builds(HyDict)
    def compile_dict(self, m):
        keyvalues, ret = self._compile_collect(sum(m.items(), ()))

        ret += ast.Dict(lineno=m.start_line,
                        col_offset=m.start_column,
                        keys=keyvalues[::2],
                        values=keyvalues[1::2])
        return ret


def hy_compile(tree, root=None):
    " Compile a HyObject tree into a Python AST tree. "
    compiler = HyASTCompiler()
    tlo = root
    if root is None:
        tlo = ast.Module

    result = compiler.compile(tree)
    result += result.expr_as_stmt()

    body = result.imports + result.stmts

    return tlo(body=body)
