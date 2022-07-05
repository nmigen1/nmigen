from abc import ABCMeta, abstractmethod
from collections import defaultdict
from dataclasses import dataclass, field
import enum
from fractions import Fraction
from numbers import Rational
from .._utils import final, flatten
from . import ast
from typing import overload, TYPE_CHECKING
if TYPE_CHECKING:  # :nobr:
    # make typechecker check final
    from typing import final  # :nocov:

__all__ = [
    'RNA',
    'RNE',
    'ROUND_DEFAULT',
    'ROUND_NEAREST_TIES_TO_AWAY',
    'ROUND_NEAREST_TIES_TO_EVEN',
    'ROUND_TOWARD_NEGATIVE',
    'ROUND_TOWARD_POSITIVE',
    'ROUND_TOWARD_ZERO',
    'RTN',
    'RTP',
    'RTZ',
    'RoundingModeEnum',
    'SmtBitVec',
    'SmtBitVecAdd',
    'SmtBitVecAnd',
    'SmtBitVecConcat',
    'SmtBitVecConst',
    'SmtBitVecDiv',
    'SmtBitVecExtract',
    'SmtBitVecFromInt',
    'SmtBitVecITE',
    'SmtBitVecInput',
    'SmtBitVecLShift',
    'SmtBitVecLt',
    'SmtBitVecMul',
    'SmtBitVecNeg',
    'SmtBitVecNot',
    'SmtBitVecOr',
    'SmtBitVecRShift',
    'SmtBitVecRem',
    'SmtBitVecXor',
    'SmtBool',
    'SmtBoolAnd',
    'SmtBoolConst',
    'SmtBoolITE',
    'SmtBoolImplies',
    'SmtBoolNot',
    'SmtBoolOr',
    'SmtBoolXor',
    'SmtDistinct',
    'SmtExpr',
    'SmtFloatingPoint',
    'SmtFloatingPointAbs',
    'SmtFloatingPointAdd',
    'SmtFloatingPointDiv',
    'SmtFloatingPointEq',
    'SmtFloatingPointFma',
    'SmtFloatingPointFromBits',
    'SmtFloatingPointFromFP',
    'SmtFloatingPointFromParts',
    'SmtFloatingPointFromReal',
    'SmtFloatingPointFromSignedBV',
    'SmtFloatingPointFromUnsignedBV',
    'SmtFloatingPointGE',
    'SmtFloatingPointGt',
    'SmtFloatingPointITE',
    'SmtFloatingPointIsInfinite',
    'SmtFloatingPointIsNaN',
    'SmtFloatingPointIsNegative',
    'SmtFloatingPointIsNormal',
    'SmtFloatingPointIsPositive',
    'SmtFloatingPointIsSubnormal',
    'SmtFloatingPointIsZero',
    'SmtFloatingPointLE',
    'SmtFloatingPointLt',
    'SmtFloatingPointMax',
    'SmtFloatingPointMin',
    'SmtFloatingPointMul',
    'SmtFloatingPointNaN',
    'SmtFloatingPointNeg',
    'SmtFloatingPointNegInfinity',
    'SmtFloatingPointNegZero',
    'SmtFloatingPointPosInfinity',
    'SmtFloatingPointPosZero',
    'SmtFloatingPointRem',
    'SmtFloatingPointRoundToIntegral',
    'SmtFloatingPointSqrt',
    'SmtFloatingPointSub',
    'SmtFloatingPointToReal',
    'SmtFloatingPointToSignedBV',
    'SmtFloatingPointToUnsignedBV',
    'SmtITE',
    'SmtInt',
    'SmtIntAbs',
    'SmtIntAdd',
    'SmtIntConst',
    'SmtIntEuclidDiv',
    'SmtIntEuclidRem',
    'SmtIntFloorDiv',
    'SmtIntFloorMod',
    'SmtIntFromBitVec',
    'SmtIntGE',
    'SmtIntGt',
    'SmtIntITE',
    'SmtIntLE',
    'SmtIntLt',
    'SmtIntMul',
    'SmtIntNeg',
    'SmtIntSub',
    'SmtIntToReal',
    'SmtReal',
    'SmtRealAdd',
    'SmtRealConst',
    'SmtRealDiv',
    'SmtRealGE',
    'SmtRealGt',
    'SmtRealITE',
    'SmtRealIsInt',
    'SmtRealLE',
    'SmtRealLt',
    'SmtRealMul',
    'SmtRealNeg',
    'SmtRealSub',
    'SmtRealToInt',
    'SmtRoundingMode',
    'SmtRoundingModeConst',
    'SmtRoundingModeITE',
    'SmtSame',
    'SmtSort',
    'SmtSortBitVec',
    'SmtSortBool',
    'SmtSortFloat128',
    'SmtSortFloat16',
    'SmtSortFloat32',
    'SmtSortFloat64',
    'SmtSortFloatingPoint',
    'SmtSortInt',
    'SmtSortReal',
    'SmtSortRoundingMode',
    'SmtValue',
]


@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSort(metaclass=ABCMeta):
    @abstractmethod
    def _smtlib2_expr(self, expr_state):
        return _InternedExpr(...)  # type: ignore :nocov:

    @abstractmethod
    def _ite_class(self):
        return SmtITE  # :nocov:


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortBool(SmtSort):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("Bool")

    @staticmethod
    def _ite_class():
        return SmtBoolITE


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortInt(SmtSort):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("Int")

    @staticmethod
    def _ite_class():
        return SmtIntITE


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortReal(SmtSort):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("Real")

    @staticmethod
    def _ite_class():
        return SmtRealITE


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortBitVec(SmtSort):
    width: int

    def __post_init__(self):
        assert isinstance(self.width, int) and self.width > 0, "invalid width"

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(("_", "BitVec", str(self.width)))

    @staticmethod
    def _ite_class():
        return SmtBitVecITE


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortRoundingMode(SmtSort):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("RoundingMode")

    @staticmethod
    def _ite_class():
        return SmtRoundingModeITE


@final
@dataclass(frozen=True, unsafe_hash=True, eq=True)
class SmtSortFloatingPoint(SmtSort):
    eb: int
    """ number of bits in the exponent """

    sb: int
    """ number of bits in the significand including the hidden bit """

    def __post_init__(self):
        assert isinstance(self.eb, int) and self.eb > 1, "invalid eb"
        assert isinstance(self.sb, int) and self.sb > 1, "invalid sb"

    @property
    def mantissa_field_width(self):
        """ number of bits needed for the mantissa field
            excluding the hidden bit
        """
        return self.sb - 1

    @property
    def sign_field_width(self):
        """ number of bits needed for the sign field -- this is always 1 """
        return 1

    @property
    def width(self):
        """ number of bits needed for the floating point value """
        return self.sign_field_width + self.eb + self.mantissa_field_width

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        if self == SmtSortFloat16():
            return expr_state.intern_expr("Float16")
        if self == SmtSortFloat32():
            return expr_state.intern_expr("Float32")
        if self == SmtSortFloat64():
            return expr_state.intern_expr("Float64")
        if self == SmtSortFloat128():
            return expr_state.intern_expr("Float128")
        return expr_state.intern_expr(("_", "FloatingPoint",
                                       str(self.eb), str(self.sb)))

    @staticmethod
    def _ite_class():
        return SmtFloatingPointITE


def SmtSortFloat16():
    return SmtSortFloatingPoint(eb=5, sb=11)


def SmtSortFloat32():
    return SmtSortFloatingPoint(eb=8, sb=24)


def SmtSortFloat64():
    return SmtSortFloatingPoint(eb=11, sb=53)


def SmtSortFloat128():
    return SmtSortFloatingPoint(eb=15, sb=113)


@final
@dataclass(frozen=True)
class _InternedExpr:
    id: int
    expr: "str | tuple[_InternedExpr, ...]"
    nesting_level: int = field(init=False)

    def __post_init__(self):
        nesting_level = 0
        if isinstance(self.expr, tuple):
            for i in self.expr:
                assert isinstance(i, _InternedExpr)
                nesting_level = max(nesting_level, 1 + i.nesting_level)
        object.__setattr__(self, "nesting_level", nesting_level)

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        if type(other) is not _InternedExpr:
            return NotImplemented
        return self.id == other.id

    def __str__(self):
        if isinstance(self.expr, str):
            return self.expr
        return f"var{self.id}"


@final
@dataclass
class _ExprState:
    input_bit_ranges: ast.ValueDict = field(default_factory=ast.ValueDict)
    input_width: int = 0
    interned_exprs: "dict[str | tuple[_InternedExpr, ...], _InternedExpr]" = \
        field(default_factory=dict)

    def intern_expr(self, expr):
        """ intern the smtlib2 expression `expr`, this is needed to avoid
            exponential blowup of the smtlib2 expression string for
            expressions like:
            ```
            a = SmtBitVec.make(sig)
            for i in range(100):
                # would create 2 ** 100 subexpressions without interning
                a *= a
            ```
        """
        if isinstance(expr, _InternedExpr):
            return expr
        elif isinstance(expr, str):
            assert "(" not in expr, \
                "should use lists/tuples instead of '(...)'"
            key = expr
        else:
            assert isinstance(expr, (list, tuple))
            assert len(expr) > 0, "invalid parenthesized expression"
            if expr[0] == '_':
                # can't assign indexed symbols to variables
                for i in expr:
                    assert isinstance(i, str), \
                        "index expression can't be nested"
                key = f"({' '.join(expr)})"
            else:
                key = tuple(self.intern_expr(i) for i in expr)
        if key in self.interned_exprs:
            return self.interned_exprs[key]
        retval = _InternedExpr(id=len(self.interned_exprs), expr=key)
        self.interned_exprs[key] = retval
        return retval

    def interned_expr_to_str(self, expr):
        """convert an _InternedExpr to a smtlib2 expression str"""
        assert isinstance(expr, _InternedExpr)
        levels: "dict[int, set[_InternedExpr]]" = defaultdict(set)
        # first, find all expressions that are needed by expr
        worklist = {expr}
        while len(worklist) != 0:
            cur_expr = worklist.pop()
            levels[cur_expr.nesting_level].add(cur_expr)
            if isinstance(cur_expr.expr, tuple):
                for sub_expr in cur_expr.expr:
                    if sub_expr not in levels[sub_expr.nesting_level]:
                        worklist.add(sub_expr)
        # now build the expression str one nesting_level at a time, using
        # `let` to avoid exponential blowup
        strs = []
        for level in range(1, len(levels)):
            assert level in levels, "levels should not have any gaps"
            strs.append("(let (")
            exprs = sorted(levels[level], key=lambda k: k.id)
            for i, cur_expr in enumerate(exprs):
                assert isinstance(cur_expr.expr, tuple)
                if i != 0:
                    strs.append(" ")
                strs.append(f"({cur_expr!s} (")
                for j, sub_expr in enumerate(cur_expr.expr):
                    if j != 0:
                        strs.append(" ")
                    strs.append(str(sub_expr))
                strs.append("))")
            strs.append(") ")
        strs.append(str(expr))
        strs.append(")" * (len(levels) - 1))
        return ''.join(strs)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtValue(metaclass=ABCMeta):
    @abstractmethod
    def sort(self):
        return SmtSort()  # type: ignore :nocov:

    @abstractmethod
    def _smtlib2_expr(self, expr_state):
        return _InternedExpr(...)  # type: ignore :nocov:

    def same(self, other, *rest):
        return SmtSame(self, other, *rest)

    def distinct(self, other, *rest):
        return SmtDistinct(self, other, *rest)

    def __bool__(self):
        raise TypeError("Attempted to convert SmtValue to Python boolean")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBool(SmtValue, ast.ValueCastable):
    @staticmethod
    def sort():
        return SmtSortBool()

    @staticmethod
    def make(value):
        value = ast.Value.cast(value)
        if isinstance(value, ast.Const):
            return SmtBoolConst(bool(value.value))
        return SmtBitVecInput(value).bool()

    # type deduction:
    @overload
    def ite(self, then_v: "SmtBool",
            else_v: "SmtBool") -> "SmtBoolITE": ...  # :nocov:

    @overload
    def ite(self, then_v: "SmtInt",
            else_v: "SmtInt") -> "SmtIntITE": ...  # :nocov:

    @overload
    def ite(self, then_v: "SmtReal",
            else_v: "SmtReal") -> "SmtRealITE": ...  # :nocov:

    @overload
    def ite(self, then_v: "SmtBitVec", else_v: "SmtBitVec") -> "SmtBitVecITE":
        ...  # :nocov:

    @overload
    def ite(self, then_v: "SmtRoundingMode",
            else_v: "SmtRoundingMode") -> "SmtRoundingModeITE": ...  # :nocov:

    @overload
    def ite(self, then_v: "SmtFloatingPoint", else_v: "SmtFloatingPoint"
            ) -> "SmtFloatingPointITE": ...  # :nocov:

    def ite(self, then_v, else_v):  # type: ignore
        return SmtITE.make(self, then_v, else_v)

    def __invert__(self):
        return SmtBoolNot(self)

    def __and__(self, other):
        return SmtBoolAnd(self, other)

    def __rand__(self, other):
        return SmtBoolAnd(other, self)

    def __xor__(self, other):
        return SmtBoolXor(self, other)

    def __rxor__(self, other):
        return SmtBoolXor(other, self)

    def __or__(self, other):
        return SmtBoolOr(self, other)

    def __ror__(self, other):
        return SmtBoolOr(other, self)

    def __eq__(self, other):
        return self.same(other)

    def __ne__(self, other):
        return self.distinct(other)

    def implies(self, *rest):
        return SmtBoolImplies(self, *rest)

    def to_bit_vec(self):
        return self.ite(SmtBitVecConst(1, width=1),
                        SmtBitVecConst(0, width=1))

    @ast.ValueCastable.lowermethod
    def as_value(self):
        return self.to_bit_vec().as_value()


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtITE(SmtValue):
    cond: SmtBool
    then_v: SmtValue
    else_v: SmtValue

    # type deduction:
    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtBool",
             else_v: "SmtBool") -> "SmtBoolITE": ...  # :nocov:

    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtInt",
             else_v: "SmtInt") -> "SmtIntITE": ...  # :nocov:

    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtReal",
             else_v: "SmtReal") -> "SmtRealITE": ...  # :nocov:

    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtBitVec",
             else_v: "SmtBitVec") -> "SmtBitVecITE": ...  # :nocov:

    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtRoundingMode",
             else_v: "SmtRoundingMode") -> "SmtRoundingModeITE": ...  # :nocov:

    @overload
    @staticmethod
    def make(cond: "SmtBool", then_v: "SmtFloatingPoint",
             else_v: "SmtFloatingPoint") -> "SmtFloatingPointITE":
        ...  # :nocov:

    @staticmethod
    def make(cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtValue)
        assert isinstance(else_v, SmtValue)
        sort = then_v.sort()
        assert sort == else_v.sort()
        return sort._ite_class()(cond, then_v, else_v)  # type: ignore

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtValue)
        assert isinstance(else_v, SmtValue)
        sort = then_v.sort()
        assert sort == else_v.sort()
        assert isinstance(self, sort._ite_class())
        object.__setattr__(self, "cond", cond)
        object.__setattr__(self, "then_v", then_v)
        object.__setattr__(self, "else_v", else_v)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        cond_s = self.cond._smtlib2_expr(expr_state)
        then_s = self.then_v._smtlib2_expr(expr_state)
        else_s = self.else_v._smtlib2_expr(expr_state)
        return expr_state.intern_expr(("ite", cond_s, then_s, else_s))


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtNAry(SmtValue):
    inputs: "tuple[SmtValue, ...]"

    @abstractmethod
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)  # :nocov:
        return _InternedExpr(...)  # type: ignore :nocov:

    def _expected_input_class(self):
        return SmtValue

    def __init__(self, *inputs):
        object.__setattr__(self, "inputs", inputs)
        assert len(inputs) > 0, "not enough inputs"

        for i in inputs:
            assert isinstance(i, self._expected_input_class())
            assert i.sort() == self.input_sort, "all input sorts must match"

    @property
    def input_sort(self):
        return self.inputs[0].sort()

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        expr = (op, *(i._smtlib2_expr(expr_state) for i in self.inputs))
        return expr_state.intern_expr(expr)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtUnary(SmtValue):
    inp: SmtValue

    @abstractmethod
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)  # :nocov:
        return _InternedExpr(...)  # type: ignore :nocov:

    @abstractmethod
    def _expected_input_class(self):
        return SmtValue  # :nocov:

    def __init__(self, inp):
        object.__setattr__(self, "inp", inp)
        assert isinstance(inp, self._expected_input_class())

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        inp = self.inp._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, inp))


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBinary(SmtValue):
    lhs: SmtValue
    rhs: SmtValue

    @abstractmethod
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)  # :nocov:
        return _InternedExpr(...)  # type: ignore :nocov:

    @abstractmethod
    def _expected_input_class(self):
        return SmtValue  # :nocov:

    @property
    def input_sort(self):
        return self.lhs.sort()

    def __init__(self, lhs, rhs):
        object.__setattr__(self, "lhs", lhs)
        object.__setattr__(self, "rhs", rhs)
        assert isinstance(lhs, self._expected_input_class())
        assert isinstance(rhs, self._expected_input_class())
        assert lhs.sort() == rhs.sort()

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        lhs = self.lhs._smtlib2_expr(expr_state)
        rhs = self.rhs._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, lhs, rhs))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtSame(_SmtNAry, SmtBool):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("=")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtDistinct(_SmtNAry, SmtBool):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("distinct")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False)
class SmtBoolConst(SmtBool):
    value: bool

    def __post_init__(self):
        assert isinstance(self.value, bool)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("true" if self.value else "false")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolNot(_SmtUnary, SmtBool):
    inp: SmtBool

    def _expected_input_class(self):
        return SmtBool

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("not")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBoolNAryMinBinary(_SmtNAry, SmtBool):
    inputs: "tuple[SmtBool, ...]"

    def _expected_input_class(self):
        return SmtBool

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolImplies(_SmtBoolNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("=>")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolAnd(_SmtBoolNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("and")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolOr(_SmtBoolNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("or")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolXor(_SmtBoolNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("xor")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBoolITE(SmtITE, SmtBool):
    then_v: SmtBool
    else_v: SmtBool

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtBool)
        assert isinstance(else_v, SmtBool)
        super().__init__(cond, then_v, else_v)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtReal(SmtValue):
    @staticmethod
    def sort():
        return SmtSortReal()

    @staticmethod
    def make(value):
        if isinstance(value, SmtInt):
            return SmtIntToReal(value)
        if isinstance(value, (ast.Value, ast.ValueCastable)):
            return SmtInt.make(value).to_real()
        assert isinstance(value, Rational), ("value must be a rational "
                                             "number, irrational numbers and "
                                             "floats aren't yet supported.")
        return SmtRealConst(value)

    def __neg__(self):
        return SmtRealNeg(self)

    def __pos__(self):
        return self

    def __add__(self, other):
        return SmtRealAdd(self, other)

    def __radd__(self, other):
        return SmtRealAdd(other, self)

    def __sub__(self, other):
        return SmtRealSub(self, other)

    def __rsub__(self, other):
        return SmtRealSub(other, self)

    def __mul__(self, other):
        return SmtRealMul(self, other)

    def __rmul__(self, other):
        return SmtRealMul(other, self)

    def __truediv__(self, other):
        return SmtRealDiv(self, other)

    def __rtruediv__(self, other):
        return SmtRealDiv(other, self)

    def __eq__(self, other):
        return SmtSame(self, other)

    def __ne__(self, other):
        return SmtDistinct(self, other)

    def __lt__(self, other):
        return SmtRealLt(self, other)

    def __le__(self, other):
        return SmtRealLE(self, other)

    def __gt__(self, other):
        return SmtRealGt(self, other)

    def __ge__(self, other):
        return SmtRealGE(self, other)

    def __abs__(self):
        return self.__lt__(SmtRealConst(0)).ite(-self, self)

    def floor(self):
        return SmtRealToInt(self)

    def trunc(self):
        return self.__lt__(SmtRealConst(0)).ite(-(-self).floor(),
                                                self.floor())

    def ceil(self):
        return -(-self).floor()

    def is_int(self):
        return SmtRealIsInt(self)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealConst(SmtReal):
    value: Fraction

    def __init__(self, value):
        assert isinstance(value, Rational), ("value must be a rational "
                                             "number, irrational numbers and "
                                             "floats aren't yet supported.")
        value = Fraction(value)
        object.__setattr__(self, "value", value)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        retval = f"{abs(self.value.numerator)}.0"
        if self.value.numerator < 0:
            retval = ("-", retval)
        if self.value.denominator != 1:
            retval = ("/", retval, f"{self.value.denominator}.0")
        return expr_state.intern_expr(retval)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealNeg(_SmtUnary, SmtReal):
    inp: SmtReal

    def _expected_input_class(self):
        return SmtReal

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("-")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealIsInt(_SmtUnary, SmtBool):
    inp: SmtReal

    def _expected_input_class(self):
        return SmtReal

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("is_int")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtRealNAryMinBinary(_SmtNAry, SmtReal):
    inputs: "tuple[SmtReal, ...]"

    def _expected_input_class(self):
        return SmtReal

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtRealCompareOp(_SmtNAry, SmtBool):
    inputs: "tuple[SmtReal, ...]"

    def _expected_input_class(self):
        return SmtReal

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealLt(_SmtRealCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("<")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealLE(_SmtRealCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("<=")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealGt(_SmtRealCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(">")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealGE(_SmtRealCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(">=")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealAdd(_SmtRealNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("+")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealSub(_SmtRealNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("-")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealMul(_SmtRealNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("*")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealDiv(_SmtRealNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("/")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealITE(SmtITE, SmtReal):
    then_v: SmtReal
    else_v: SmtReal

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtReal)
        assert isinstance(else_v, SmtReal)
        super().__init__(cond, then_v, else_v)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtInt(SmtValue):
    @staticmethod
    def sort():
        return SmtSortInt()

    @staticmethod
    def make(value):
        if isinstance(value, SmtBitVec):
            return value.to_int()
        value = ast.Value.cast(value)
        assert isinstance(value, ast.Value)
        if isinstance(value, ast.Const):
            return SmtIntConst(value.value)
        shape = value.shape()
        assert isinstance(shape, ast.Shape)
        if shape.width == 0:
            return SmtIntConst(0)
        return SmtBitVecInput.make(value).to_int(signed=shape.signed)

    def to_bit_vec(self, width):
        assert isinstance(width, int) and width >= 1, "invalid width"
        return SmtBitVecFromInt(self, width=width)

    def to_real(self):
        return SmtIntToReal(self)

    def __neg__(self):
        return SmtIntNeg(self)

    def __pos__(self):
        return self

    def __add__(self, other):
        return SmtIntAdd(self, other)

    def __radd__(self, other):
        return SmtIntAdd(other, self)

    def __sub__(self, other):
        return SmtIntSub(self, other)

    def __rsub__(self, other):
        return SmtIntSub(other, self)

    def __mul__(self, other):
        return SmtIntMul(self, other)

    def __rmul__(self, other):
        return SmtIntMul(other, self)

    def __floordiv__(self, other):
        return SmtIntFloorDiv(self, other)

    def __rfloordiv__(self, other):
        return SmtIntFloorDiv(other, self)

    def __mod__(self, other):
        return SmtIntFloorMod(self, other)

    def __rmod__(self, other):
        return SmtIntFloorMod(other, self)

    def euclid_div(self, other):
        return SmtIntEuclidDiv(self, other)

    def euclid_rem(self, other):
        return SmtIntEuclidRem(self, other)

    def __eq__(self, other):
        return SmtSame(self, other)

    def __ne__(self, other):
        return SmtDistinct(self, other)

    def __lt__(self, other):
        return SmtIntLt(self, other)

    def __le__(self, other):
        return SmtIntLE(self, other)

    def __gt__(self, other):
        return SmtIntGt(self, other)

    def __ge__(self, other):
        return SmtIntGE(self, other)

    def __abs__(self):
        return SmtIntAbs(self)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntConst(SmtInt):
    value: int

    def __init__(self, value):
        assert isinstance(value, int), "value must be an integer"
        object.__setattr__(self, "value", value)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        retval = f"{abs(self.value.numerator)}"
        if self.value.numerator < 0:
            retval = ("-", retval)
        return expr_state.intern_expr(retval)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntNeg(_SmtUnary, SmtInt):
    inp: SmtInt

    def _expected_input_class(self):
        return SmtInt

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("-")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntAbs(_SmtUnary, SmtInt):
    inp: SmtInt

    def _expected_input_class(self):
        return SmtInt

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("abs")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntToReal(_SmtUnary, SmtReal):
    inp: SmtInt

    def _expected_input_class(self):
        return SmtInt

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("to_real")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRealToInt(_SmtUnary, SmtInt):
    inp: SmtReal

    def _expected_input_class(self):
        return SmtReal

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("to_int")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtIntNAryMinBinary(_SmtNAry, SmtInt):
    inputs: "tuple[SmtInt, ...]"

    def _expected_input_class(self):
        return SmtInt

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtIntBinary(_SmtBinary, SmtInt):
    lhs: SmtInt
    rhs: SmtInt

    def _expected_input_class(self):
        return SmtInt


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtIntCompareOp(_SmtNAry, SmtBool):
    inputs: "tuple[SmtInt, ...]"

    def _expected_input_class(self):
        return SmtInt

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntLt(_SmtIntCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("<")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntLE(_SmtIntCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("<=")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntGt(_SmtIntCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(">")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntGE(_SmtIntCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(">=")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntAdd(_SmtIntNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("+")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntSub(_SmtIntNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("-")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntMul(_SmtIntNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("*")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtIntFloorDivMod(SmtInt):
    lhs: SmtInt
    rhs: SmtInt

    def __init__(self, lhs, rhs):
        assert isinstance(lhs, SmtInt)
        assert isinstance(rhs, SmtInt)
        object.__setattr__(self, "lhs", lhs)
        object.__setattr__(self, "rhs", rhs)
        super().__init__()

    def _smtlib2_expr_helper(self, expr_state, is_mod) -> "_InternedExpr":
        assert isinstance(expr_state, _ExprState)
        lhs = self.lhs._smtlib2_expr(expr_state)
        if isinstance(self.rhs, SmtIntConst) and self.rhs.value > 0:
            if is_mod:
                return expr_state.intern_expr(
                    ("mod", lhs, str(self.rhs.value)))
            return expr_state.intern_expr(("div", lhs, str(self.rhs.value)))
        rhs = self.rhs._smtlib2_expr(expr_state)
        ediv = ("div", lhs, rhs)
        erem = ("mod", lhs, rhs)
        if is_mod:
            unadjusted = erem
            adjusted = ("+", erem, rhs)
        else:
            unadjusted = ediv
            adjusted = ("-", ediv, "1")
        adj_needed = ("and", ("<", rhs, "0"), ("distinct", "0", erem))
        expr = ("ite", adj_needed, adjusted, unadjusted)
        return expr_state.intern_expr(expr)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntFloorDiv(_SmtIntFloorDivMod):
    def _smtlib2_expr(self, expr_state):
        return self._smtlib2_expr_helper(expr_state, is_mod=False)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntFloorMod(_SmtIntFloorDivMod):
    def _smtlib2_expr(self, expr_state):
        return self._smtlib2_expr_helper(expr_state, is_mod=True)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntEuclidDiv(_SmtIntNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("div")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntEuclidRem(_SmtIntBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("mod")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntITE(SmtITE, SmtInt):
    then_v: SmtInt
    else_v: SmtInt

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtInt)
        assert isinstance(else_v, SmtInt)
        super().__init__(cond, then_v, else_v)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVec(SmtValue, ast.ValueCastable):
    width: int

    def sort(self):
        return SmtSortBitVec(self.width)

    @staticmethod
    def make(value=None, *, width=None):
        assert width is None or isinstance(width, int), "invalid width"
        if isinstance(value, SmtBitVec):
            assert width is None or width == value.width, "width mismatch"
            return value
        if isinstance(value, int):
            assert width is not None, "missing width"
            assert width > 0, "invalid width"
            return SmtBitVecConst(value, width=width)
        if isinstance(value, SmtInt):
            assert width is not None, "missing width"
            assert width > 0, "invalid width"
            return value.to_bit_vec(width=width)
        retval = SmtBitVecInput.make(value)
        assert width is None or width == retval.width, "width mismatch"
        return retval

    def __init__(self, *, width=None):
        assert isinstance(width, int) and width > 0, "invalid width"
        object.__setattr__(self, "width", width)
        super().__init__()

    def to_int(self, signed=False):
        return SmtIntFromBitVec(self, signed=signed)

    def to_real(self, signed=False):
        return self.to_int(signed=signed).to_real()

    def __neg__(self):
        return SmtBitVecNeg(self)

    def __invert__(self):
        return SmtBitVecNot(self)

    def __pos__(self):
        return self

    def __add__(self, other):
        return SmtBitVecAdd(self, other)

    def __radd__(self, other):
        return SmtBitVecAdd(other, self)

    def __sub__(self, other):
        assert isinstance(other, SmtBitVec)
        return self + -other

    def __rsub__(self, other):
        assert isinstance(other, SmtBitVec)
        return other + -self

    def __mul__(self, other):
        return SmtBitVecMul(self, other)

    def __rmul__(self, other):
        return SmtBitVecMul(other, self)

    def __floordiv__(self, other):
        return SmtBitVecDiv(self, other)

    def __rfloordiv__(self, other):
        return SmtBitVecDiv(other, self)

    def __mod__(self, other):
        return SmtBitVecRem(self, other)

    def __rmod__(self, other):
        return SmtBitVecRem(other, self)

    def __divmod__(self, other):
        return self // other, self % other

    def __rdivmod__(self, other):
        return other // self, other % self

    def __eq__(self, other):
        return SmtSame(self, other)

    def __ne__(self, other):
        return SmtDistinct(self, other)

    def __lt__(self, other):
        return SmtBitVecLt(self, other)

    def __le__(self, other):
        assert isinstance(other, SmtBitVec)
        return other >= self

    def __gt__(self, other):
        assert isinstance(other, SmtBitVec)
        return other < self

    def __ge__(self, other):
        return SmtBoolNot(SmtBitVecLt(self, other))

    def __abs__(self):
        lt = self[-1] != SmtBitVec.make(0, width=1)
        return lt.ite(-self, self)

    def __and__(self, other):
        return SmtBitVecAnd(self, other)

    def __rand__(self, other):
        return SmtBitVecAnd(other, self)

    def __or__(self, other):
        return SmtBitVecOr(self, other)

    def __ror__(self, other):
        return SmtBitVecOr(other, self)

    def __xor__(self, other):
        return SmtBitVecXor(self, other)

    def __rxor__(self, other):
        return SmtBitVecXor(other, self)

    def __lshift__(self, other):
        return SmtBitVecLShift(self, other)

    def __rlshift__(self, other):
        return SmtBitVecLShift(other, self)

    def __rshift__(self, other):
        return SmtBitVecRShift(self, other)

    def __rrshift__(self, other):
        return SmtBitVecRShift(other, self)

    def __getitem__(self, index):
        if isinstance(index, int):
            return SmtBitVecExtract(self, index)
        assert isinstance(index, slice)
        bits = [*range(self.width)][index]
        assert len(bits) > 0, "empty slice"
        r = range(min(bits), max(bits) + 1)
        if bits != [*r]:
            return SmtBitVecConcat(self[i] for i in bits)
        return SmtBitVecExtract(self, r)

    def bool(self):
        return self != SmtBitVecConst(0, width=self.width)

    @ast.ValueCastable.lowermethod
    def as_value(self):
        expr_state = _ExprState()
        expr = self.bool() if self.width == 1 else self
        expr = expr_state.interned_expr_to_str(expr._smtlib2_expr(expr_state))
        if expr_state.input_width == 0:
            # can't have 0-width input
            expr_state.input_bit_ranges[ast.Const(0, 1)] = range(1)
            expr_state.input_width = 1
        elif expr_state.input_width == 1:
            # 1-width input is a Bool rather than a BitVec, add another
            # input bit to work around that.
            v = ast.Const(0, 1)
            if v in expr_state.input_bit_ranges:
                # choose a different constant to not conflict
                v = ast.Const(1, 1)
            expr_state.input_bit_ranges[v] = range(1, 2)
            expr_state.input_width = 2

        return SmtExpr(width=self.width, expr=expr,
                       inp=ast.Cat(expr_state.input_bit_ranges.keys()))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecFromInt(SmtBitVec):
    inp: SmtInt

    def __init__(self, inp, *, width):
        assert isinstance(inp, SmtInt)
        object.__setattr__(self, "inp", inp)
        super().__init__(width=width)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        inp = self.inp._smtlib2_expr(expr_state)
        # smtlib2 has no easy int->bv conversion function in the standard

        def bit_v(index):
            v = inp
            if index != 0:
                v = ("div", v, str(2 ** index))
            v = ("=", "1", ("mod", v, "2"))
            return ("ite", v, "#b1", "#b0")
        bits = [bit_v(i) for i in range(self.width)]
        return expr_state.intern_expr(("concat", *reversed(bits)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtIntFromBitVec(SmtInt):
    inp: SmtBitVec
    signed: bool

    def __init__(self, inp, *, signed=False):
        assert isinstance(inp, SmtBitVec)
        signed = bool(signed)
        object.__setattr__(self, "inp", inp)
        object.__setattr__(self, "signed", signed)
        super().__init__()

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        inp = self.inp._smtlib2_expr(expr_state)
        # smtlib2 has no easy bv->int conversion function in the standard

        def is_bit_set(index):
            i_s = str(index)
            return ("=", "#b1", (("_", "extract", i_s, i_s), inp))

        def bit_value(index):
            if self.signed and index == self.inp.width - 1:
                # sign bit has negative value
                return ("-", str(2 ** index))
            return str(2 ** index)

        bit_values = [("ite", is_bit_set(i), bit_value(i), "0")
                      for i in range(self.inp.width)]
        if self.inp.width == 1:
            retval = bit_values[0]
        else:
            retval = ("+", *bit_values)
        return expr_state.intern_expr(retval)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecConcat(SmtBitVec):
    inputs: "tuple[SmtBitVec, ...]"
    """inputs in lsb to msb order"""

    def __init__(self, *inputs):
        inputs = tuple(flatten(inputs))
        object.__setattr__(self, "inputs", inputs)
        assert len(inputs) > 0, "not enough inputs"

        width = 0
        for i in inputs:
            assert isinstance(i, SmtBitVec)
            width += i.width

        super().__init__(width=width)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        args = [i._smtlib2_expr(expr_state) for i in self.inputs]
        return expr_state.intern_expr(("concat", *reversed(args)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecExtract(_SmtUnary, SmtBitVec):
    inp: SmtBitVec
    bit_range: range

    def __init__(self, inp, bit_range):
        assert isinstance(inp, SmtBitVec)
        if isinstance(bit_range, int):
            if bit_range < 0:
                bit_range += inp.width
            bit_range = range(bit_range, bit_range + 1)
        assert isinstance(bit_range, range)
        assert len(bit_range) > 0, "empty range"
        assert bit_range.step == 1, "unsupported range step"
        assert 0 <= bit_range.start < bit_range.stop <= inp.width, \
            "bit range out-of-range"
        object.__setattr__(self, "bit_range", bit_range)
        _SmtUnary.__init__(self, inp)
        SmtBitVec.__init__(self, width=len(bit_range))

    def _expected_input_class(self):
        return SmtBitVec

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(("_", "extract",
                                       str(self.bit_range.stop - 1),
                                       str(self.bit_range.start)))


@final
class SmtExpr(ast.Value):
    def __init__(self, *, width, inp, expr, src_loc_at=0):
        assert isinstance(width, int) and width >= 1
        assert isinstance(inp, ast.Cat) and inp.shape().width >= 1
        assert isinstance(expr, str)
        super().__init__(src_loc_at=src_loc_at)
        self.width = width
        self.inp = inp
        self.expr = expr

    def shape(self):
        return ast.unsigned(self.width)

    def _rhs_signals(self):
        return self.inp._rhs_signals()

    def __repr__(self):
        return f"(smt_expr {self.width} {self.inp!r} {self.expr!r})"


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecInput(SmtBitVec):
    value: ast.Value

    def __init_subclass__(cls):
        try:
            _ = SmtBitVecConst
        except NameError:
            # only possible when we're defining SmtBitVecConst
            return
        raise TypeError("subclassing SmtBitVecInput isn't supported")

    @staticmethod
    def make(value):
        value = ast.Value.cast(value)
        assert isinstance(value, ast.Value)
        if isinstance(value, ast.Const):
            return SmtBitVecConst(value)
        return SmtBitVecInput(value)

    def __init__(self, value):
        value = ast.Value.cast(value)
        assert isinstance(value, ast.Value)
        object.__setattr__(self, "value", value)
        super().__init__(width=self.value.shape().width)  # type: ignore

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        if self.value not in expr_state.input_bit_ranges:
            start = expr_state.input_width
            expr_state.input_width += self.width
            r = range(start, expr_state.input_width)
            expr_state.input_bit_ranges[self.value] = r
        else:
            r = expr_state.input_bit_ranges[self.value]
        return expr_state.intern_expr((("_", "extract",
                                        str(r.stop - 1), str(r.start)),
                                       "A"))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecConst(SmtBitVecInput):
    value: ast.Const

    def __init__(self, value, *, width=None):
        if isinstance(value, ast.Const):
            assert width is None
            # decompose -- needed since we switch to unsigned
            width = value.width
            value = value.value
        assert isinstance(value, int), "value must be an integer"
        assert isinstance(width, int) and width > 0, "invalid width"
        value = ast.Const(value, ast.unsigned(width))
        super().__init__(value)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        hex_digit_count, hex_digit_count_rem = divmod(self.width, 4)
        if hex_digit_count_rem == 0:
            digit_count = hex_digit_count
            digits = hex(self.value.value)
        else:
            digit_count = self.width
            digits = bin(self.value.value)
        retval = "#" + digits[1] + digits[2:].zfill(digit_count)
        return expr_state.intern_expr(retval)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBitVecUnary(_SmtUnary, SmtBitVec):
    inp: SmtBitVec

    def __init__(self, inp):
        assert isinstance(inp, SmtBitVec)
        _SmtUnary.__init__(self, inp)
        SmtBitVec.__init__(self, width=inp.width)

    def _expected_input_class(self):
        return SmtBitVec


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecNeg(_SmtBitVecUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvneg")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecNot(_SmtBitVecUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvnot")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBitVecNAryMinBinary(_SmtNAry, SmtBitVec):
    inputs: "tuple[SmtBitVec, ...]"

    def _expected_input_class(self):
        return SmtBitVec

    def __init__(self, *inputs):
        _SmtNAry.__init__(self, *inputs)
        assert len(self.inputs) >= 2, "not enough inputs"
        SmtBitVec.__init__(self, width=self.inputs[0].width)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBitVecBinary(_SmtBinary, SmtBitVec):
    lhs: SmtBitVec
    rhs: SmtBitVec

    def __init__(self, lhs, rhs):
        _SmtBinary.__init__(self, lhs, rhs)
        SmtBitVec.__init__(self, width=self.lhs.width)

    def _expected_input_class(self):
        return SmtBitVec


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtBitVecCompareOp(_SmtBinary, SmtBool):
    lhs: SmtBitVec
    rhs: SmtBitVec

    def __init__(self, lhs, rhs):
        _SmtBinary.__init__(self, lhs, rhs)
        SmtBool.__init__(self)

    def _expected_input_class(self):
        return SmtBitVec


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecLt(_SmtBitVecCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvult")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecAdd(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvadd")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecAnd(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvand")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecOr(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvor")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecXor(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvxor")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecMul(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvmul")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecDiv(_SmtBitVecNAryMinBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvudiv")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecRem(_SmtBitVecBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvurem")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecLShift(_SmtBitVecBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvshl")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecRShift(_SmtBitVecBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("bvlshr")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtBitVecITE(SmtITE, SmtBitVec):
    then_v: SmtBitVec
    else_v: SmtBitVec

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtBitVec)
        assert isinstance(else_v, SmtBitVec)
        SmtITE.__init__(self, cond, then_v, else_v)
        SmtBitVec.__init__(self, width=self.then_v.width)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRoundingMode(SmtValue):
    @staticmethod
    def make(value):
        return SmtRoundingModeConst(value)

    @staticmethod
    def sort():
        return SmtSortRoundingMode()

    def __eq__(self, other):
        return self.same(other)

    def __ne__(self, other):
        return self.distinct(other)


@final
class RoundingModeEnum(enum.Enum):
    RNE = "RNE"
    ROUND_DEFAULT = RNE
    ROUND_NEAREST_TIES_TO_EVEN = RNE
    RNA = "RNA"
    ROUND_NEAREST_TIES_TO_AWAY = RNA
    RTP = "RTP"
    ROUND_TOWARD_POSITIVE = RTP
    RTN = "RTN"
    ROUND_TOWARD_NEGATIVE = RTN
    RTZ = "RTZ"
    ROUND_TOWARD_ZERO = RTZ

    def __init__(self, value):
        assert isinstance(value, str)
        self._smtlib2_expr = value


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRoundingModeConst(SmtRoundingMode):
    value: RoundingModeEnum

    def __new__(cls, *args, **kwargs):
        value = RoundingModeEnum(*args, **kwargs)
        try:
            if value is RoundingModeEnum.RNE:
                return RNE
            elif value is RoundingModeEnum.RNA:
                return RNA
            elif value is RoundingModeEnum.RTP:
                return RTP
            elif value is RoundingModeEnum.RTN:
                return RTN
            else:
                assert value is RoundingModeEnum.RTZ
                return RTZ
        except NameError:
            # instance not created yet
            return super().__new__(cls)

    def __init__(self, value):
        assert isinstance(value, RoundingModeEnum)
        object.__setattr__(self, "value", value)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(self.value._smtlib2_expr)


RNE = SmtRoundingModeConst(RoundingModeEnum.RNE)
ROUND_NEAREST_TIES_TO_EVEN = SmtRoundingModeConst(
    RoundingModeEnum.ROUND_NEAREST_TIES_TO_EVEN)
ROUND_DEFAULT = SmtRoundingModeConst(
    RoundingModeEnum.ROUND_DEFAULT)
RNA = SmtRoundingModeConst(RoundingModeEnum.RNA)
ROUND_NEAREST_TIES_TO_AWAY = SmtRoundingModeConst(
    RoundingModeEnum.ROUND_NEAREST_TIES_TO_AWAY)
RTP = SmtRoundingModeConst(RoundingModeEnum.RTP)
ROUND_TOWARD_POSITIVE = SmtRoundingModeConst(
    RoundingModeEnum.ROUND_TOWARD_POSITIVE)
RTN = SmtRoundingModeConst(RoundingModeEnum.RTN)
ROUND_TOWARD_NEGATIVE = SmtRoundingModeConst(
    RoundingModeEnum.ROUND_TOWARD_NEGATIVE)
RTZ = SmtRoundingModeConst(RoundingModeEnum.RTZ)
ROUND_TOWARD_ZERO = SmtRoundingModeConst(RoundingModeEnum.ROUND_TOWARD_ZERO)

# check all rounding modes are accounted for:
# (we check rather than just make everything here so IDEs can more easily
# see the definitions)
for name, rm in RoundingModeEnum.__members__.items():
    assert globals()[name] is SmtRoundingModeConst(rm), f"mismatch {name}"
del rm, name


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtRoundingModeITE(SmtITE, SmtRoundingMode):
    then_v: SmtRoundingMode
    else_v: SmtRoundingMode

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtRoundingMode)
        assert isinstance(else_v, SmtRoundingMode)
        super().__init__(cond, then_v, else_v)


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPoint(SmtValue):
    eb: int
    sb: int

    def sort(self):
        return SmtSortFloatingPoint(eb=self.eb, sb=self.sb)

    def __init__(self, *, eb=None, sb=None, sort=None):
        if sort is not None:
            assert eb is sb is None and isinstance(sort, SmtSortFloatingPoint)
            eb = sort.eb
            sb = sort.sb
        assert isinstance(eb, int) and eb > 1, "invalid eb"
        assert isinstance(sb, int) and sb > 1, "invalid sb"
        object.__setattr__(self, "eb", eb)
        object.__setattr__(self, "sb", sb)

    @staticmethod
    def nan(*, eb=None, sb=None, sort=None):
        return SmtFloatingPointNaN(eb=eb, sb=sb, sort=sort)

    @staticmethod
    def zero(*, sign=None, eb=None, sb=None, sort=None):
        if sign is None:
            return SmtFloatingPointPosZero(eb=eb, sb=sb, sort=sort)
        if isinstance(sign, SmtBitVec):
            assert sign.width == 1, "invalid sign width"
            sign = sign.bool()
        assert isinstance(sign, SmtBool)
        return sign.ite(SmtFloatingPointNegZero(eb=eb, sb=sb, sort=sort),
                        SmtFloatingPointPosZero(eb=eb, sb=sb, sort=sort))

    @staticmethod
    def neg_zero(*, eb=None, sb=None, sort=None):
        return SmtFloatingPointNegZero(eb=eb, sb=sb, sort=sort)

    @staticmethod
    def infinity(*, sign=None, eb=None, sb=None, sort=None):
        if sign is None:
            return SmtFloatingPointPosInfinity(eb=eb, sb=sb, sort=sort)
        if isinstance(sign, SmtBitVec):
            assert sign.width == 1, "invalid sign width"
            sign = sign.bool()
        assert isinstance(sign, SmtBool)
        return sign.ite(SmtFloatingPointNegInfinity(eb=eb, sb=sb, sort=sort),
                        SmtFloatingPointPosInfinity(eb=eb, sb=sb, sort=sort))

    @staticmethod
    def neg_infinity(*, eb=None, sb=None, sort=None):
        return SmtFloatingPointNegInfinity(eb=eb, sb=sb, sort=sort)

    @staticmethod
    def from_parts(*, sign, exponent, mantissa):
        return SmtFloatingPointFromParts(sign=sign, exponent=exponent,
                                         mantissa=mantissa)

    def __abs__(self):
        return SmtFloatingPointAbs(self)

    def __neg__(self):
        return SmtFloatingPointNeg(self)

    def __pos__(self):
        return self

    def add(self, other, *, rm):
        return SmtFloatingPointAdd(self, other, rm=rm)

    def sub(self, other, *, rm):
        return SmtFloatingPointSub(self, other, rm=rm)

    def mul(self, other, *, rm):
        return SmtFloatingPointMul(self, other, rm=rm)

    def div(self, other, *, rm):
        return SmtFloatingPointDiv(self, other, rm=rm)

    def fma(self, factor, term, *, rm):
        """returns `self * factor + term`"""
        return SmtFloatingPointFma(self, factor, term, rm=rm)

    def sqrt(self, *, rm):
        return SmtFloatingPointSqrt(self, rm=rm)

    def rem(self, other):
        return SmtFloatingPointRem(self, other)

    def round_to_integral(self, *, rm):
        return SmtFloatingPointRoundToIntegral(self, rm=rm)

    def min(self, other):
        return SmtFloatingPointMin(self, other)

    def max(self, other):
        return SmtFloatingPointMax(self, other)

    def __eq__(self, other):
        return SmtFloatingPointEq(self, other)

    def __ne__(self, other):
        return ~SmtFloatingPointEq(self, other)

    def __lt__(self, other):
        return SmtFloatingPointLt(self, other)

    def __le__(self, other):
        return SmtFloatingPointLE(self, other)

    def __gt__(self, other):
        return SmtFloatingPointGt(self, other)

    def __ge__(self, other):
        return SmtFloatingPointGE(self, other)

    def is_normal(self):
        return SmtFloatingPointIsNormal(self)

    def is_subnormal(self):
        return SmtFloatingPointIsSubnormal(self)

    def is_zero(self):
        return SmtFloatingPointIsZero(self)

    def is_infinite(self):
        return SmtFloatingPointIsInfinite(self)

    def is_nan(self):
        return SmtFloatingPointIsNaN(self)

    def is_negative(self):
        return SmtFloatingPointIsNegative(self)

    def is_positive(self):
        return SmtFloatingPointIsPositive(self)

    @staticmethod
    def from_signed_bv(bv, *, rm, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromSignedBV(bv, rm=rm, eb=eb, sb=sb,
                                            sort=sort)

    @staticmethod
    def from_unsigned_bv(bv, *, rm, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromUnsignedBV(bv, rm=rm, eb=eb, sb=sb,
                                              sort=sort)

    @staticmethod
    def from_real(value, *, rm, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromReal(value, rm=rm, eb=eb, sb=sb,
                                        sort=sort)

    @staticmethod
    def from_int(value, *, rm, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromReal(SmtIntToReal(value), rm=rm, eb=eb,
                                        sb=sb, sort=sort)

    @staticmethod
    def from_fp(value, *, rm, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromFP(value, rm=rm, eb=eb,
                                      sb=sb, sort=sort)

    @staticmethod
    def from_bits(bv, *, eb=None, sb=None, sort=None):
        return SmtFloatingPointFromBits(bv, eb=eb, sb=sb, sort=sort)

    def to_real(self):
        return SmtFloatingPointToReal(self)

    def ceil(self):
        return self.round_to_integral(rm=ROUND_TOWARD_POSITIVE)

    def floor(self):
        return self.round_to_integral(rm=ROUND_TOWARD_NEGATIVE)

    def trunc(self):
        return self.round_to_integral(rm=ROUND_TOWARD_ZERO)

    def ceil_int(self):
        return SmtFloatingPointToReal(self).ceil()

    def floor_int(self):
        return SmtFloatingPointToReal(self).floor()

    def trunc_int(self):
        return SmtFloatingPointToReal(self).trunc()

    def to_unsigned_bv(self, *, rm, width):
        return SmtFloatingPointToUnsignedBV(self, rm=rm, width=width)

    def to_signed_bv(self, *, rm, width):
        return SmtFloatingPointToSignedBV(self, rm=rm, width=width)


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointITE(SmtITE, SmtFloatingPoint):
    then_v: SmtFloatingPoint
    else_v: SmtFloatingPoint

    def __init__(self, cond, then_v, else_v):
        assert isinstance(cond, SmtBool)
        assert isinstance(then_v, SmtFloatingPoint)
        assert isinstance(else_v, SmtFloatingPoint)
        SmtITE.__init__(self, cond, then_v, else_v)
        SmtFloatingPoint.__init__(self, sort=self.then_v.sort())


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointNaN(SmtFloatingPoint):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(("_", "NaN", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointPosZero(SmtFloatingPoint):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "+zero", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointNegZero(SmtFloatingPoint):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "-zero", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointPosInfinity(SmtFloatingPoint):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "+oo", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointNegInfinity(SmtFloatingPoint):
    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "-oo", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromParts(SmtFloatingPoint):
    sign: SmtBitVec
    exponent: SmtBitVec
    mantissa: SmtBitVec

    def __init__(self, sign, exponent, mantissa):
        if isinstance(sign, SmtBool):
            sign = sign.to_bit_vec()
        assert isinstance(sign, SmtBitVec) and sign.width == 1
        assert isinstance(exponent, SmtBitVec)
        assert isinstance(mantissa, SmtBitVec)
        object.__setattr__(self, "sign", sign)
        object.__setattr__(self, "exponent", exponent)
        object.__setattr__(self, "mantissa", mantissa)
        super().__init__(eb=exponent.width, sb=mantissa.width + 1)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        sign = self.sign._smtlib2_expr(expr_state)
        exponent = self.exponent._smtlib2_expr(expr_state)
        mantissa = self.mantissa._smtlib2_expr(expr_state)
        return expr_state.intern_expr(("fp", sign, exponent, mantissa))


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointUnary(_SmtUnary, SmtFloatingPoint):
    inp: SmtFloatingPoint

    def __init__(self, inp):
        assert isinstance(inp, SmtFloatingPoint)
        _SmtUnary.__init__(self, inp)
        SmtFloatingPoint.__init__(self, eb=inp.eb, sb=inp.sb)

    def _expected_input_class(self):
        return SmtFloatingPoint


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointAbs(_SmtFloatingPointUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.abs")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointNeg(_SmtFloatingPointUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.neg")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointBinaryRounded(_SmtBinary, SmtFloatingPoint):
    lhs: SmtFloatingPoint
    rhs: SmtFloatingPoint
    rm: SmtRoundingMode

    def __init__(self, lhs, rhs, *, rm):
        assert isinstance(rm, SmtRoundingMode)
        _SmtBinary.__init__(self, lhs, rhs)
        object.__setattr__(self, "rm", rm)
        SmtFloatingPoint.__init__(self, eb=self.lhs.eb, sb=self.rhs.sb)

    def _expected_input_class(self):
        return SmtFloatingPoint

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        rm = self.rm._smtlib2_expr(expr_state)
        lhs = self.lhs._smtlib2_expr(expr_state)
        rhs = self.rhs._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, rm, lhs, rhs))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointAdd(_SmtFloatingPointBinaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.add")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointSub(_SmtFloatingPointBinaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.sub")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointMul(_SmtFloatingPointBinaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.mul")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointDiv(_SmtFloatingPointBinaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.div")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFma(SmtFloatingPoint):
    """returns `self.factor1 * self.factor2 + self.term`"""
    factor1: SmtFloatingPoint
    factor2: SmtFloatingPoint
    term: SmtFloatingPoint
    rm: SmtRoundingMode

    def __init__(self, factor1, factor2, term, *, rm):
        assert isinstance(factor1, SmtFloatingPoint)
        assert isinstance(factor2, SmtFloatingPoint)
        assert isinstance(term, SmtFloatingPoint)
        assert factor1.sort() == factor2.sort() == term.sort(), "sort mismatch"
        assert isinstance(rm, SmtRoundingMode)
        object.__setattr__(self, "factor1", factor1)
        object.__setattr__(self, "factor2", factor2)
        object.__setattr__(self, "term", term)
        object.__setattr__(self, "rm", rm)
        super().__init__(eb=factor1.eb, sb=factor1.sb)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        rm = self.rm._smtlib2_expr(expr_state)
        factor1 = self.factor1._smtlib2_expr(expr_state)
        factor2 = self.factor2._smtlib2_expr(expr_state)
        term = self.term._smtlib2_expr(expr_state)
        return expr_state.intern_expr(("fp.fma", rm, factor1, factor2, term))


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointUnaryRounded(_SmtUnary, SmtFloatingPoint):
    inp: SmtFloatingPoint
    rm: SmtRoundingMode

    def __init__(self, inp, *, rm):
        assert isinstance(rm, SmtRoundingMode)
        _SmtUnary.__init__(self, inp)
        object.__setattr__(self, "rm", rm)
        SmtFloatingPoint.__init__(self, eb=inp.eb, sb=inp.sb)

    def _expected_input_class(self):
        return SmtFloatingPoint

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        rm = self.rm._smtlib2_expr(expr_state)
        inp = self.inp._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, rm, inp))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointSqrt(_SmtFloatingPointUnaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.sqrt")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointBinary(_SmtBinary, SmtFloatingPoint):
    lhs: SmtFloatingPoint
    rhs: SmtFloatingPoint

    def __init__(self, lhs, rhs):
        _SmtBinary.__init__(self, lhs, rhs)
        SmtFloatingPoint.__init__(self, eb=self.lhs.eb, sb=self.rhs.sb)

    def _expected_input_class(self):
        return SmtFloatingPoint


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointRem(_SmtFloatingPointBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.rem")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointRoundToIntegral(_SmtFloatingPointUnaryRounded):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.roundToIntegral")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointMin(_SmtFloatingPointBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.min")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointMax(_SmtFloatingPointBinary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.max")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointCompareOp(_SmtNAry, SmtBool):
    inputs: "tuple[SmtFloatingPoint, ...]"

    def _expected_input_class(self):
        return SmtFloatingPoint

    def __init__(self, *inputs):
        super().__init__(*inputs)
        assert len(self.inputs) >= 2, "not enough inputs"


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointEq(_SmtFloatingPointCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.eq")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointLt(_SmtFloatingPointCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.lt")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointLE(_SmtFloatingPointCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.leq")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointGt(_SmtFloatingPointCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.gt")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointGE(_SmtFloatingPointCompareOp):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.geq")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointToBoolUnary(_SmtUnary, SmtBool):
    inp: SmtFloatingPoint

    def _expected_input_class(self):
        return SmtFloatingPoint


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsNormal(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isNormal")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsSubnormal(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isSubnormal")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsZero(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isZero")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsInfinite(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isInfinite")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsNaN(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isNaN")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsNegative(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isNegative")


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointIsPositive(_SmtFloatingPointToBoolUnary):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.isPositive")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointRoundFrom(_SmtUnary, SmtFloatingPoint):
    rm: SmtRoundingMode

    def __init__(self, inp, *, rm, eb=None, sb=None, sort=None):
        assert isinstance(rm, SmtRoundingMode)
        SmtFloatingPoint.__init__(self, eb=eb, sb=sb, sort=sort)
        _SmtUnary.__init__(self, inp)
        object.__setattr__(self, "rm", rm)

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        rm = self.rm._smtlib2_expr(expr_state)
        inp = self.inp._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, rm, inp))

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "to_fp", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromSignedBV(_SmtFloatingPointRoundFrom):
    inp: SmtBitVec

    def _expected_input_class(self):
        return SmtBitVec


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromUnsignedBV(_SmtFloatingPointRoundFrom):
    inp: SmtBitVec

    def _expected_input_class(self):
        return SmtBitVec

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "to_fp_unsigned", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromReal(_SmtFloatingPointRoundFrom):
    inp: SmtReal

    def _expected_input_class(self):
        return SmtReal


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromFP(_SmtFloatingPointRoundFrom):
    inp: SmtFloatingPoint

    def _expected_input_class(self):
        return SmtFloatingPoint


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointFromBits(_SmtUnary, SmtFloatingPoint):
    inp: SmtBitVec

    def __init__(self, inp, *, eb=None, sb=None, sort=None):
        SmtFloatingPoint.__init__(self, eb=eb, sb=sb, sort=sort)
        inp = SmtBitVec.make(inp, width=self.sort().width)
        _SmtUnary.__init__(self, inp)

    def _expected_input_class(self):
        return SmtBitVec

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(
            ("_", "to_fp", str(self.eb), str(self.sb)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointToReal(_SmtUnary, SmtReal):
    inp: SmtFloatingPoint

    def _expected_input_class(self):
        return SmtFloatingPoint

    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr("fp.to_real")


@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class _SmtFloatingPointToBV(_SmtUnary, SmtBitVec):
    inp: SmtFloatingPoint
    rm: SmtRoundingMode

    def __init__(self, inp, *, rm, width):
        assert isinstance(rm, SmtRoundingMode)
        SmtBitVec.__init__(self, width=width)
        _SmtUnary.__init__(self, inp)
        object.__setattr__(self, "rm", rm)

    def _expected_input_class(self):
        return SmtFloatingPoint

    def _smtlib2_expr(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        op = self._smtlib2_expr_op(expr_state)
        rm = self.rm._smtlib2_expr(expr_state)
        inp = self.inp._smtlib2_expr(expr_state)
        return expr_state.intern_expr((op, rm, inp))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointToUnsignedBV(_SmtFloatingPointToBV):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(("_", "fp.to_ubv", str(self.width)))


@final
@dataclass(frozen=True, unsafe_hash=False, eq=False, init=False)
class SmtFloatingPointToSignedBV(_SmtFloatingPointToBV):
    def _smtlib2_expr_op(self, expr_state):
        assert isinstance(expr_state, _ExprState)
        return expr_state.intern_expr(("_", "fp.to_sbv", str(self.width)))
