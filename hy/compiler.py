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
import ast
import sys


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
    __slots__ = ("imports", "stmts", "_expr", "ref", "__used_expr")

    def __init__(self, *args, **kwargs):
        if args:
            # emulate kw-only args for future bits.
            raise TypeError("Yo: Hacker: don't pass me real args, dingus")

        self.imports = []
        self.stmts = []
        self._expr = None
        self.ref = None

        self.__used_expr = False

        # XXX: Make sure we only have AST where we should.
        for kwarg in kwargs:
            if kwarg not in ["imports", "stmts", "expr", "ref"]:
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
        if not self.expr:
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
        else:
            return self.expr

    def expr_as_stmt(self):
        if self.expr:
            return Result() + ast.Expr(lineno=self.expr.lineno,
                                       col_offset=self.expr.col_offset,
                                       value=self.expr)
        else:
            return Result()

    def __add__(self, other):
        if isinstance(other, ast.stmt):
            return self + Result(stmts=[other])
        if isinstance(other, ast.expr):
            return self + Result(expr=other)
        if not isinstance(other, Result):
            raise TypeError("Can't add %r with non-compiler result %r" % (
                self, other))

        if self.expr and not self.__used_expr:
            import traceback
            traceback.print_stack()
            print("Bad boy clobbered expr %s with %s" % (
                ast.dump(self.expr),
                ast.dump(other.expr)))

        result = Result()
        result.imports = self.imports + other.imports
        result.stmts = self.stmts + other.stmts
        result.expr = other.expr
        result.ref = other.ref
        return result

    def __str__(self):
        return "Result(imports=[%s], stmts=[%s], expr=%s, ref=%s)" % (
            ", ".join(ast.dump(x) for x in self.imports),
            ", ".join(ast.dump(x) for x in self.stmts),
            ast.dump(self.expr) if self.expr else None,
            ast.dump(self.ref) if self.ref else None,
        )


def _collect(results):
    compiled_exprs = []
    ret = Result()
    for result in results:
        ret += result
        compiled_exprs.append(ret.force_expr)
    return compiled_exprs, ret


def _branch(results):
    results = list(results)
    ret = Result()
    for result in results[:-1]:
        ret += result
        ret += result.expr_as_stmt()

    # We don't want to convert the last expr to a stmt, to use it as the return value
    for result in results[-1:]:
        ret += result

    return ret

class HyASTCompiler(object):

    def __init__(self):
        self.returnable = False
        self.anon_fn_count = 0


    def compile(self, tree):
        _type = type(tree)
        if _type in _compile_table:
            ret = _compile_table[_type](self, tree)
            if not isinstance(ret, Result):
                ret = Result() + ret
            return ret

        raise TypeError(Exception("Unknown type: `%s'" % (
            str(type(tree)))))

    def _compile_collect(self, exprs):
        return _collect(self.compile(expr) for expr in exprs)

    def _compile_branch(self, exprs):
        return _branch(self.compile(expr) for expr in exprs)

    @builds(list)
    def compile_raw_list(self, entries):
        ret = Result()
        for x in entries:
            x = self.compile(x)
            ret += x
            ret += x.expr_as_stmt()
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

    @builds("fn")
    def compile_function_def(self, expression):
        expression.pop(0)

        self.anon_fn_count += 1
        name = "_hy_anon_fn_%d" % (self.anon_fn_count)

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

        return ret

    @builds(HyExpression)
    def compile_expression(self, expression):
        fn = expression[0]
        if isinstance(fn, HyString):
            if fn in _compile_table:
                return _compile_table[fn](self, expression)

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

    @builds(HyList)
    def compile_list(self, expression):
        elts, ret = self._compile_collect(expression)
        ret += ast.List(elts=elts,
                        ctx=ast.Load(),
                        lineno=expression.start_line,
                        col_offset=expression.start_column)
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
