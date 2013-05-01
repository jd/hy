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

        raise HyCompileError(
            Exception("Unknown type: `%s'" % (str(type(tree)))))

    def _compile_collect(self, exprs):
        return _collect(self.compile(expr) for expr in exprs)

    def _compile_branch(self, exprs):
        return _branch(self.compile(expr) for expr in exprs)

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

        ret += ast.Print(
            lineno=expr.start_line,
            col_offset=expr.start_column,
            dest=None,
            values=values,
            nl=True)

        return ret

    @builds("lambda")
    def compile_lambda_expression(self, expr):
        expr.pop(0)
        sig = expr.pop(0)
        body = self.compile(expr.pop(0))

        # assert expr is empty
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

    @builds("not")
    @builds("~")
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

    @builds(HyExpression)
    def compile_expression(self, expression):
        fn = expression[0]
        if isinstance(fn, HyString):
            ret = self.compile_atom(fn, expression)
            if ret:
                return ret

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
    def compile_def_expression(self, expression):
        expression.pop(0)
        name = expression.pop(0)
        result = self.compile(expression.pop(0))

        if result.temp_variables:
            result.rename(name)
            return result

        ld_name = self.compile(name).force_expr
        st_name = ast.Name(id=ld_name.id, arg=ld_name.arg,
                           ctx=ast.Store(),
                           lineno=ld_name.lineno,
                           col_offset=ld_name.col_offset)

        result += ast.Assign(
            lineno=expression.start_line,
            col_offset=expression.start_column,
            targets=[st_name], value=result.force_expr)

        result += ld_name
        return result

    @builds(HyList)
    def compile_list(self, expression):
        elts, ret = self._compile_collect(expression)
        ret += ast.List(elts=elts,
                        ctx=ast.Load(),
                        lineno=expression.start_line,
                        col_offset=expression.start_column)
        return ret

    @builds("fn")
    def compile_function_def(self, expression):
        expression.pop(0)

        name = self.get_anon_fn()

        arg_list = self.compile(expression.pop(0))
        body = self._compile_branch(expression)
        if body.expr:
            body += ast.Return(value=body.expr,
                               lineno=body.expr.lineno,
                               col_offset=body.expr.col_offset)
        ret = Result()
        ret += ast.FunctionDef(name=name,
                               lineno=expression.start_line,
                               col_offset=expression.start_column,
                               args=ast.arguments(
                                   args=[
                                       ast.Name(
                                           arg=x.arg, id=x.id,
                                           ctx=ast.Param(),
                                           lineno=x.lineno,
                                           col_offset=x.col_offset)
                                       for x in arg_list.expr.elts],
                                   vararg=None,
                                   kwarg=None,
                                   kwonlyargs=[],
                                   kw_defaults=[],
                                   defaults=[]),
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

            ret += ast.Attribute(
                lineno=symbol.start_line,
                col_offset=symbol.start_column,
                value=ret.expr,
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
