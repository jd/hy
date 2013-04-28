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
    __slots__ = ("imports", "stmts", "exprs", "ref")

    def __init__(self, *args, **kwargs):
        if args:
            # emulate kw-only args for future bits.
            raise HyCompileError("Yo: Hacker: don't pass me real args, dingus")

        self.imports = []
        self.stmts = []
        self.exprs = []
        self.ref = None

        # XXX: Check that kwarg type matches expected stuff.
        # XXX: Make sure we only have AST where we should.
        for kwarg in kwargs:
            setattr(self, kwarg, kwargs[kwarg])

    @property
    def expr(self):
        if len(self.exprs) != 1:
            raise Exception("Expr suckage.")
        return self.exprs.pop(0)

    @property
    def stmt(self):
        if len(self.stmts) != 1:
            raise Exception("Stmt suckage.")
        return self.stmts.pop(0)

    def __add__(self, other):
        if not isinstance(other, Result):
            raise HyCompileError("Can't add with non-compiler result")

        result = Result()
        result.imports = self.imports + other.imports
        result.stmts = self.stmts + other.stmts
        result.exprs = self.exprs + other.exprs
        result.ref = other.ref
        return result


class HyASTCompiler(object):

    def __init__(self):
        self.returnable = False

    def is_returnable(self, v):
        return temporary_attribute_value(self, "returnable", v)

    def compile(self, tree):
        _type = type(tree)
        if _type in _compile_table:
            return _compile_table[_type](self, tree)

        raise HyCompileError(Exception("Unknown type: `%s'" % (
            str(type(tree)))))

    @builds(list)
    def compile_raw_list(self, entries):
        return [self.compile(x) for x in entries]

    @builds("print")
    def compile_print_expression(self, expr):
        call = expr.pop(0)  # print
        values = self._sum(expr)

        ret = ast.Print(
            lineno=expr.start_line,
            col_offset=expr.start_column,
            dest=None,
            values=values.exprs,
            nl=True)
        values.exprs = [ret]
        return values

    @builds("not")
    @builds("~")
    def compile_unary_operator(self, expression):
        ops = {"not": ast.Not,
               "~": ast.Invert}
        operator = expression.pop(0)
        operand = self.compile(expression.pop(0))

        operand.exprs.append(ast.UnaryOp(op=ops[operator](),
                                         operand=operand.expr,
                                         lineno=operator.start_line,
                                         col_offset=operator.start_column))
        return operand

    def _sum(self, expr):
        return reduce(lambda x, y: x + y,
                      (self.compile(x) for x in expr))

    @builds("and")
    @builds("or")
    def compile_logical_or_and_and_operator(self, expression):
        ops = {"and": ast.And,
               "or": ast.Or}
        operator = expression.pop(0)
        values = self._sum(expression)

        ret = ast.BoolOp(op=ops[operator](),
                         lineno=operator.start_line,
                         col_offset=operator.start_column,
                         values=values.exprs)
        values.exprs = [ret]
        return values

    @builds(HyExpression)
    def compile_expression(self, expression):
        fn = expression[0]
        if isinstance(fn, HyString):
            if fn in _compile_table:
                return _compile_table[fn](self, expression)

        func = self.compile(fn)
        args = (self.compile(x) for x in expression[1:])

        func.exprs.append(
            ast.Call(func=func.expr,
                     args=args.exprs,
                     keywords=[],
                     starargs=None,
                     kwargs=None,
                     lineno=expression.start_line,
                     col_offset=expression.start_column))
        args.exprs = []
        return args + func

    @builds(HyList)
    def compile_list(self, expr):
        elts = self._sum(expr)
        elts.exprs.append(ast.List(elts=elts.exprs,
                                   ctx=ast.Load(),
                                   lineno=expr.start_line,
                                   col_offset=expr.start_column))
        return elts

    @builds(HyInteger)
    def compile_integer(self, number):
        return Result(exprs=[ast.Num(n=int(number),
                                     lineno=number.start_line,
                                     col_offset=number.start_column)])

    @builds(HyFloat)
    def compile_float(self, number):
        return Result(exprs=[ast.Num(n=float(number),
                                     lineno=number.start_line,
                                     col_offset=number.start_column)])

    @builds(HyComplex)
    def compile_complex(self, number):
        return Result(exprs=[ast.Num(n=complex(number),
                                     lineno=number.start_line,
                                     col_offset=number.start_column)])

    @builds(HySymbol)
    def compile_symbol(self, symbol):
        if "." in symbol:
            glob, local = symbol.rsplit(".", 1)
            glob = HySymbol(glob).replace(symbol)
            ret = self.compile_symbol(glob)

            ret.exprs.append(ast.Attribute(
                lineno=symbol.start_line,
                col_offset=symbol.start_column,
                value=ret.expr,
                attr=ast_str(local),
                ctx=ast.Load()
            ))
            return ret

        return Result(exprs=[ast.Name(id=ast_str(symbol),
                                      arg=ast_str(symbol),
                                      ctx=ast.Load(),
                                      lineno=symbol.start_line,
                                      col_offset=symbol.start_column)])

    @builds(HyString)
    def compile_string(self, string):
        return Result(exprs=[ast.Str(s=str_type(string),
                                     lineno=string.start_line,
                                     col_offset=string.start_column)])

    @builds(HyKeyword)
    def compile_keyword(self, keyword):
        return Result(exprs=[ast.Str(s=str_type(keyword),
                                     lineno=keyword.start_line,
                                     col_offset=keyword.start_column)])

    @builds(HyDict)
    def compile_dict(self, m):
        ret = Result()
        keys = []
        vals = []
        for entry in m:
            k = self.compile(entry)
            v = self.compile(m[entry])
            keys.append(k.expr)
            vals.append(v.expr)
            ret += k + v

        ret.exprs.append(ast.Dict(
            lineno=m.start_line,
            col_offset=m.start_column,
            keys=keys,
            values=vals))
        return ret


def hy_compile(tree, root=None):
    " Compile a HyObject tree into a Python AST tree. "
    compiler = HyASTCompiler()
    tlo = root
    if root is None:
        tlo = ast.Module

    result = compiler.compile(tree)
    if isinstance(result, list):
        result = reduce(lambda x, y: x + y, result)

    ret = tlo(body=result.stmts + result.exprs)
    return ret
