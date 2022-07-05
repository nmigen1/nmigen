from fractions import Fraction
from nmigen.hdl.smtlib2 import *
from nmigen.hdl import smtlib2
from nmigen.hdl.ast import (AnyConst, Assert, Assume, Mux, Cat, Const,
                            ValueDict, Signal, Value, Array, signed, unsigned)
from nmigen.hdl.dsl import Module
from .utils import FHDLTestCase


class SmtTestCase(FHDLTestCase):
    maxDiff = None

    def assertSmtExpr(self, v, ty, expected_expr, input_bit_ranges=(),
                      input_width=0):
        self.assertIs(type(v), ty)
        state = smtlib2._ExprState()
        expr = state.interned_expr_to_str(v._smtlib2_expr(state))
        if expr != expected_expr:
            lets = expr
            sp = "("
            let = ""
            found_let = False
            while lets != "":
                if let != "":
                    print(f"{sp}{let!r}")
                    sp = " "
                    found_let = True
                vars, let, lets = lets.partition("(let (")
                var = ""
                while vars != "":
                    s, next_var, vars = vars.partition("(var")
                    s = var + s
                    var = next_var
                    if var == "" and vars == "" and let == "" \
                            and lets == "" and found_let and s.endswith(")"):
                        # split off last var
                        s, var2, vars = s.rpartition(") var")
                        if s == "" and var2 == "":
                            s = vars
                            vars = ""
                        else:
                            s += ") "
                            vars = "var" + vars
                    if s != "":
                        print(f"{sp}{s!r}")
                        sp = " "
            if let != "":
                print(f"{sp}{let!r}")
                sp = " "
            print(")")
        self.assertEqual(expr, expected_expr)
        self.assertEqual(state.input_bit_ranges, ValueDict(input_bit_ranges))
        self.assertEqual(state.input_width, input_width)

    def assertSmt(self, *, inputs, assertions=(), assumptions=(),
                  assert_eqs=(), assume_eqs=(), solver="z3", **kwargs):
        m = Module()
        inputs = list(inputs)
        for sig in inputs:
            assert isinstance(sig, Signal)
            any_const = AnyConst(sig.shape())
            any_const.src_loc = sig.src_loc  # makes it easier to debug
            m.d.comb += sig.eq(any_const)

        def get_sig(v, name):
            v = Value.cast(v)
            sig = Signal(v.shape(), name=name)
            m.d.comb += sig.eq(v)
            return sig
        for i, v in enumerate(assertions):
            m.d.comb += Assert(get_sig(v, f"assert_{i}"))
        for i, v in enumerate(assumptions):
            m.d.comb += Assume(get_sig(v, f"assume_{i}"))
        for i, (lhs, rhs) in enumerate(assert_eqs):
            lhs = get_sig(lhs, f"assert_eq_lhs_{i}")
            rhs = get_sig(rhs, f"assert_eq_rhs_{i}")
            m.d.comb += Assert(lhs == rhs)
        for i, (lhs, rhs) in enumerate(assume_eqs):
            lhs = get_sig(lhs, f"assume_eq_lhs_{i}")
            rhs = get_sig(rhs, f"assume_eq_rhs_{i}")
            m.d.comb += Assume(lhs == rhs)
        self.assertFormal(m, solver=solver, **kwargs)

    def assertSmtSame(self, expr, expected, *, inputs, assertions=(),
                      assumptions=(), assert_eqs=(), assume_eqs=(),
                      solver="z3", **kwargs):
        self.assertSmt(inputs=inputs, assumptions=assumptions,
                       assertions=assertions,
                       assert_eqs=((expr, expected), *assert_eqs),
                       assume_eqs=assume_eqs, solver=solver, **kwargs)


class TestMod(SmtTestCase):
    def test_mod_exports_everything_sorted(self):
        # check that the smtlib2 module exports everything defined in it but
        # not its imports and that `__all__` is properly sorted.
        exclusions = [
            "ABCMeta", "Fraction", "Rational", "TYPE_CHECKING",
            "abstractmethod", "ast", "dataclass", "dsl", "enum", "field",
            "final", "flatten", "ir", "overload", "defaultdict",
        ]
        expected = []
        for i in dir(smtlib2):
            if i not in exclusions and not i.startswith("_"):
                expected.append(i)
        self.assertSequenceEqual(smtlib2.__all__, sorted(expected))


class TestExprState(SmtTestCase):
    def test_expr_state(self):
        expr_state = smtlib2._ExprState()
        interned_exprs = {}
        self.assertEqual(expr_state.interned_exprs, interned_exprs)

        def check(interned_expr, repr_str, str_str, expr_str):
            with self.subTest(interned_expr=repr(interned_expr)):
                self.assertEqual(repr(interned_expr), repr_str)
                self.assertEqual(str(interned_expr), str_str)
                self.assertEqual(expr_state.interned_exprs, interned_exprs)
                self.assertEqual(
                    expr_state.interned_expr_to_str(interned_expr), expr_str)

        _123 = expr_state.intern_expr("123")
        interned_exprs["123"] = _123
        check(_123,
              "_InternedExpr(id=0, expr='123', nesting_level=0)",
              "123",
              "123")
        a = expr_state.intern_expr("A")
        interned_exprs["A"] = a
        check(a,
              "_InternedExpr(id=1, expr='A', nesting_level=0)",
              "A",
              "A")
        self.assertNotEqual(_123, a)
        self.assertEqual(_123, _123)
        self.assertNotEqual(_123, 123)
        self.assertNotEqual(123, _123)
        a1 = expr_state.intern_expr((("_", "extract", "1", "1"), a))
        interned_exprs["(_ extract 1 1)"] = a1.expr[0]
        interned_exprs[(a1.expr[0], a)] = a1
        check(a1,
              ("_InternedExpr(id=3, expr=("
               "_InternedExpr(id=2, expr='(_ extract 1 1)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1)"),
              "var3",
              "(let ((var3 ((_ extract 1 1) A))) var3)")
        a2 = expr_state.intern_expr((("_", "extract", "2", "2"), a))
        interned_exprs["(_ extract 2 2)"] = a2.expr[0]
        interned_exprs[(a2.expr[0], a)] = a2
        check(a2,
              ("_InternedExpr(id=5, expr=("
               "_InternedExpr(id=4, expr='(_ extract 2 2)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1)"),
              "var5",
              "(let ((var5 ((_ extract 2 2) A))) var5)")
        bvadd_a1_a1_a2 = expr_state.intern_expr(("bvadd", a1, a1, a2))
        bvadd = bvadd_a1_a1_a2.expr[0]
        interned_exprs["bvadd"] = bvadd
        interned_exprs[(bvadd, a1, a1, a2)] = bvadd_a1_a1_a2
        check(bvadd_a1_a1_a2,
              ("_InternedExpr(id=7, expr=("
               "_InternedExpr(id=6, expr='bvadd', nesting_level=0), "
               "_InternedExpr(id=3, expr=("
               "_InternedExpr(id=2, expr='(_ extract 1 1)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1), _InternedExpr(id=3, expr=("
               "_InternedExpr(id=2, expr='(_ extract 1 1)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1), _InternedExpr(id=5, expr=("
               "_InternedExpr(id=4, expr='(_ extract 2 2)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1)), nesting_level=2)"),
              "var7",
              ("(let ((var3 ((_ extract 1 1) A)) "
               "(var5 ((_ extract 2 2) A))) "
               "(let ((var7 (bvadd var3 var3 var5))) var7))"))
        bvxor_a1_bvadd_a1_a2 = expr_state.intern_expr(("bvxor", a1,
                                                       ("bvadd", a1, a2)))
        bvxor = bvxor_a1_bvadd_a1_a2.expr[0]
        bvadd_a1_a2 = bvxor_a1_bvadd_a1_a2.expr[2]
        interned_exprs["bvxor"] = bvxor
        interned_exprs[(bvadd, a1, a2)] = bvadd_a1_a2
        interned_exprs[(bvxor, a1, bvadd_a1_a2)] = bvxor_a1_bvadd_a1_a2
        check(bvxor_a1_bvadd_a1_a2,
              ("_InternedExpr(id=10, expr=("
               "_InternedExpr(id=8, expr='bvxor', nesting_level=0), "
               "_InternedExpr(id=3, expr=("
               "_InternedExpr(id=2, expr='(_ extract 1 1)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1), _InternedExpr(id=9, expr=("
               "_InternedExpr(id=6, expr='bvadd', nesting_level=0), "
               "_InternedExpr(id=3, expr=("
               "_InternedExpr(id=2, expr='(_ extract 1 1)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1), _InternedExpr(id=5, expr=("
               "_InternedExpr(id=4, expr='(_ extract 2 2)', nesting_level=0), "
               "_InternedExpr(id=1, expr='A', nesting_level=0)), "
               "nesting_level=1)), nesting_level=2)), nesting_level=3)"),
              "var10",
              ("(let ((var3 ((_ extract 1 1) A)) "
               "(var5 ((_ extract 2 2) A))) "
               "(let ((var9 (bvadd var3 var5))) "
               "(let ((var10 (bvxor var3 var9))) var10)))"))


class TestSmtExpr(SmtTestCase):
    def test_repr(self):
        expr = SmtExpr(width=1, inp=Cat(Const(0, 1)), expr="#b0")
        self.assertRepr(expr, "(smt_expr 1 (cat (const 1'd0)) '#b0')")


class TestSorts(SmtTestCase):
    def test_sort_bool(self):
        self.assertSmtExpr(SmtSortBool(), SmtSortBool, "Bool")

    def test_sort_int(self):
        self.assertSmtExpr(SmtSortInt(), SmtSortInt, "Int")

    def test_sort_real(self):
        self.assertSmtExpr(SmtSortReal(), SmtSortReal, "Real")

    def test_sort_bv(self):
        self.assertSmtExpr(SmtSortBitVec(1), SmtSortBitVec, "(_ BitVec 1)")
        self.assertSmtExpr(SmtSortBitVec(16), SmtSortBitVec, "(_ BitVec 16)")

    def test_sort_rm(self):
        self.assertSmtExpr(SmtSortRoundingMode(),
                           SmtSortRoundingMode, "RoundingMode")

    def test_sort_fp(self):
        self.assertSmtExpr(SmtSortFloat16(), SmtSortFloatingPoint, "Float16")
        self.assertSmtExpr(SmtSortFloat32(), SmtSortFloatingPoint, "Float32")
        self.assertSmtExpr(SmtSortFloat64(), SmtSortFloatingPoint, "Float64")
        self.assertSmtExpr(SmtSortFloat128(), SmtSortFloatingPoint, "Float128")
        self.assertSmtExpr(SmtSortFloatingPoint(3, 5),
                           SmtSortFloatingPoint, "(_ FloatingPoint 3 5)")
        self.assertSmtExpr(SmtSortFloatingPoint(2, 2),
                           SmtSortFloatingPoint, "(_ FloatingPoint 2 2)")


class TestBool(SmtTestCase):
    def test_bool_make(self):
        self.assertSmtExpr(SmtBool.make(False), SmtBoolConst, "false")
        self.assertSmtExpr(SmtBool.make(True), SmtBoolConst, "true")
        sig = Signal()
        self.assertSmtExpr(SmtBool.make(sig), SmtDistinct,
                           ('(let ('
                            '(var4 ((_ extract 0 0) A))) '
                            '(let ('
                            '(var5 (distinct #b0 var4))) var5))'
                            ),
                           input_bit_ranges=[(sig, range(0, 1))],
                           input_width=1)
        sig2 = Signal(2)
        self.assertSmtExpr(SmtBool.make(sig2.bool()), SmtDistinct,
                           ('(let ('
                            '(var4 ((_ extract 0 0) A))) '
                            '(let ('
                            '(var5 (distinct #b0 var4))) var5))'
                            ),
                           input_bit_ranges=[(sig2.bool(), range(0, 1))],
                           input_width=1)

    def test_bool_same(self):
        a = Signal()
        b = Signal()
        c = Signal()
        expr = SmtBool.make(a).same(SmtBool.make(b), SmtBool.make(c))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A)) '
             '(var11 ((_ extract 2 2) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8)) '
             '(var12 (distinct #b0 var11))) '
             '(let ('
             '(var13 (= var6 var9 var12))) var13)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
                (c, range(2, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c))

    def test_bool_distinct(self):
        # only check 2 inputs since if we were to check 3 inputs it would
        # always return false since there are only 2 possible Bool values
        # but you'd need at least 3 to make distinct return True since every
        # input needs to be different than all others.
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a).distinct(SmtBool.make(b))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var7 ((_ extract 1 1) A))) '
             '(let ('
             '(var5 (distinct #b0 var4)) '
             '(var8 (distinct #b0 var7))) '
             '(let ('
             '(var9 (distinct var5 var8))) var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a != b, inputs=(a, b))

    def test_bool_ite(self):
        a = Signal()
        b = Signal()
        c = Signal()
        expr = SmtBool.make(a).ite(SmtBool.make(b), SmtBool.make(c))
        self.assertSmtExpr(
            expr,
            SmtBoolITE,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var7 ((_ extract 1 1) A)) '
             '(var10 ((_ extract 2 2) A))) '
             '(let ('
             '(var5 (distinct #b0 var4)) '
             '(var8 (distinct #b0 var7)) '
             '(var11 (distinct #b0 var10))) '
             '(let ('
             '(var13 (ite var5 var8 var11))) var13)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
                (c, range(2, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr, Mux(a, b, c), inputs=(a, b, c))

    def test_bool_bool(self):
        with self.assertRaises(TypeError):
            bool(SmtBool.make(False))

    def test_bool_invert(self):
        a = Signal()
        expr = ~SmtBool.make(a)
        self.assertSmtExpr(
            expr,
            SmtBoolNot,
            ('(let ('
             '(var5 ((_ extract 0 0) A))) '
             '(let ('
             '(var6 (distinct #b0 var5))) '
             '(let ('
             '(var7 (not var6))) var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
            ],
            input_width=1,
        )
        self.assertSmtSame(expr, ~a, inputs=(a,))

    def test_bool_and(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a) & SmtBool.make(b)
        self.assertSmtExpr(
            expr,
            SmtBoolAnd,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8))) '
             '(let ('
             '(var10 (and var6 var9))) var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBool.make(b).__rand__(SmtBool.make(a))))
        self.assertSmtSame(expr, a & b, inputs=(a, b))

    def test_bool_xor(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a) ^ SmtBool.make(b)
        self.assertSmtExpr(
            expr,
            SmtBoolXor,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8))) '
             '(let ('
             '(var10 (xor var6 var9))) var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBool.make(b).__rxor__(SmtBool.make(a))))
        self.assertSmtSame(expr, a ^ b, inputs=(a, b))

    def test_bool_or(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a) | SmtBool.make(b)
        self.assertSmtExpr(
            expr,
            SmtBoolOr,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8))) '
             '(let ('
             '(var10 (or var6 var9))) var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBool.make(b).__ror__(SmtBool.make(a))))
        self.assertSmtSame(expr, a | b, inputs=(a, b))

    def test_bool_eq(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a) == SmtBool.make(b)
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8))) '
             '(let ('
             '(var10 (= var6 var9))) var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a == b, inputs=(a, b))

    def test_bool_ne(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a) != SmtBool.make(b)
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var7 ((_ extract 1 1) A))) '
             '(let ('
             '(var5 (distinct #b0 var4)) '
             '(var8 (distinct #b0 var7))) '
             '(let ('
             '(var9 (distinct var5 var8))) var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a != b, inputs=(a, b))

    def test_bool_implies(self):
        a = Signal()
        b = Signal()
        expr = SmtBool.make(a).implies(SmtBool.make(b))
        self.assertSmtExpr(
            expr,
            SmtBoolImplies,
            ('(let ('
             '(var5 ((_ extract 0 0) A)) '
             '(var8 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct #b0 var5)) '
             '(var9 (distinct #b0 var8))) '
             '(let ('
             '(var10 (=> var6 var9))) var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a.implies(b), inputs=(a, b))


class TestReal(SmtTestCase):
    def test_real_make(self):
        self.assertSmtExpr(SmtReal.make(0), SmtRealConst, "0.0")
        self.assertSmtExpr(SmtReal.make(1), SmtRealConst, "1.0")
        self.assertSmtExpr(SmtReal.make(-1), SmtRealConst,
                           '(let ((var2 (- 1.0))) var2)')
        self.assertSmtExpr(SmtReal.make(-Fraction(1, 2)),
                           SmtRealConst, ('(let ('
                                          '(var3 (- 1.0))) '
                                          '(let ('
                                          '(var5 (/ var3 2.0))) var5))'
                                          ))
        self.assertSmtExpr(SmtReal.make(-Fraction(30, 20)),
                           SmtRealConst, ('(let ('
                                          '(var3 (- 3.0))) '
                                          '(let ('
                                          '(var5 (/ var3 2.0))) var5))'
                                          ))
        self.assertSmtExpr(SmtReal.make(SmtInt.make(1)),
                           SmtIntToReal, '(let ((var2 (to_real 1))) var2)')
        sig = Signal(4)
        expr = SmtReal.make(sig)
        self.assertSmtExpr(expr, SmtIntToReal,
                           ('(let ('
                            '(var3 ((_ extract 3 0) A))) '
                            '(let ('
                            '(var9 ((_ extract 0 0) var3)) '
                            '(var15 ((_ extract 1 1) var3)) '
                            '(var20 ((_ extract 2 2) var3)) '
                            '(var25 ((_ extract 3 3) var3))) '
                            '(let ('
                            '(var10 (= #b1 var9)) '
                            '(var16 (= #b1 var15)) '
                            '(var21 (= #b1 var20)) '
                            '(var26 (= #b1 var25))) '
                            '(let ('
                            '(var13 (ite var10 1 0)) '
                            '(var18 (ite var16 2 0)) '
                            '(var23 (ite var21 4 0)) '
                            '(var28 (ite var26 8 0))) '
                            '(let ('
                            '(var29 (+ var13 var18 var23 var28))) '
                            '(let ('
                            '(var30 (to_real var29))) var30))))))'
                            ),
                           input_bit_ranges=[(sig, range(0, 4))],
                           input_width=4)
        expr = expr.floor().to_bit_vec(width=sig.width)
        self.assertSmtExpr(
            expr, SmtBitVecFromInt,
            ('(let ('
             '(var4 ((_ extract 3 0) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var21 ((_ extract 2 2) var4)) '
             '(var26 ((_ extract 3 3) var4))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var22 (= #b1 var21)) '
             '(var27 (= #b1 var26))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var24 (ite var22 4 0)) '
             '(var29 (ite var27 8 0))) '
             '(let ('
             '(var30 (+ var14 var19 var24 var29))) '
             '(let ('
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (to_int var31))) '
             '(let ('
             '(var36 (div var32 8)) '
             '(var41 (div var32 4)) '
             '(var45 (div var32 2)) '
             '(var49 (mod var32 2))) '
             '(let ('
             '(var37 (mod var36 2)) '
             '(var42 (mod var41 2)) '
             '(var46 (mod var45 2)) '
             '(var50 (= 1 var49))) '
             '(let ('
             '(var38 (= 1 var37)) '
             '(var43 (= 1 var42)) '
             '(var47 (= 1 var46)) '
             '(var51 (ite var50 #b1 #b0))) '
             '(let ('
             '(var40 (ite var38 #b1 #b0)) '
             '(var44 (ite var43 #b1 #b0)) '
             '(var48 (ite var47 #b1 #b0))) '
             '(let ('
             '(var52 (concat var40 var44 var48 var51))) var52))))))))))))'
             ),
            input_bit_ranges=[(sig, range(0, 4))],
            input_width=4)
        self.assertSmtSame(expr, sig, inputs=(sig,))

    def test_real_ite(self):
        expr = SmtBool.make(False).ite(SmtReal.make(1), SmtReal.make(0))
        self.assertSmtExpr(expr, SmtRealITE,
                           ('(let ('
                            '(var4 (ite false 1.0 0.0))) var4)'
                            ))

    def test_real_neg_pos(self):
        expr = -SmtReal.make(1)
        self.assertIs(expr, +expr)
        self.assertSmtExpr(expr, SmtRealNeg, '(let ((var2 (- 1.0))) var2)')
        sig = Signal(4)
        expr = -SmtReal.make(sig)
        self.assertIs(expr, +expr)
        self.assertSmtExpr(expr, SmtRealNeg,
                           ('(let ('
                            '(var4 ((_ extract 3 0) A))) '
                            '(let ('
                            '(var10 ((_ extract 0 0) var4)) '
                            '(var16 ((_ extract 1 1) var4)) '
                            '(var21 ((_ extract 2 2) var4)) '
                            '(var26 ((_ extract 3 3) var4))) '
                            '(let ('
                            '(var11 (= #b1 var10)) '
                            '(var17 (= #b1 var16)) '
                            '(var22 (= #b1 var21)) '
                            '(var27 (= #b1 var26))) '
                            '(let ('
                            '(var14 (ite var11 1 0)) '
                            '(var19 (ite var17 2 0)) '
                            '(var24 (ite var22 4 0)) '
                            '(var29 (ite var27 8 0))) '
                            '(let ('
                            '(var30 (+ var14 var19 var24 var29))) '
                            '(let ('
                            '(var31 (to_real var30))) '
                            '(let ('
                            '(var32 (- var31))) var32)))))))'
                            ),
                           input_bit_ranges=[(sig, range(0, 4))],
                           input_width=4)
        expr = expr.floor().to_bit_vec(width=sig.width)
        self.assertSmtExpr(
            expr, SmtBitVecFromInt,
            ('(let ('
             '(var5 ((_ extract 3 0) A))) '
             '(let ('
             '(var11 ((_ extract 0 0) var5)) '
             '(var17 ((_ extract 1 1) var5)) '
             '(var22 ((_ extract 2 2) var5)) '
             '(var27 ((_ extract 3 3) var5))) '
             '(let ('
             '(var12 (= #b1 var11)) '
             '(var18 (= #b1 var17)) '
             '(var23 (= #b1 var22)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var15 (ite var12 1 0)) '
             '(var20 (ite var18 2 0)) '
             '(var25 (ite var23 4 0)) '
             '(var30 (ite var28 8 0))) '
             '(let ('
             '(var31 (+ var15 var20 var25 var30))) '
             '(let ('
             '(var32 (to_real var31))) '
             '(let ('
             '(var33 (- var32))) '
             '(let ('
             '(var34 (to_int var33))) '
             '(let ('
             '(var38 (div var34 8)) '
             '(var43 (div var34 4)) '
             '(var47 (div var34 2)) '
             '(var51 (mod var34 2))) '
             '(let ('
             '(var39 (mod var38 2)) '
             '(var44 (mod var43 2)) '
             '(var48 (mod var47 2)) '
             '(var52 (= 1 var51))) '
             '(let ('
             '(var40 (= 1 var39)) '
             '(var45 (= 1 var44)) '
             '(var49 (= 1 var48)) '
             '(var53 (ite var52 #b1 #b0))) '
             '(let ('
             '(var42 (ite var40 #b1 #b0)) '
             '(var46 (ite var45 #b1 #b0)) '
             '(var50 (ite var49 #b1 #b0))) '
             '(let ('
             '(var54 (concat var42 var46 var50 var53))) var54)))))))))))))'
             ),
            input_bit_ranges=[(sig, range(0, 4))],
            input_width=4)
        self.assertSmtSame(expr, (-sig)[:4], inputs=(sig,))

    def test_real_add(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) + SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealAdd,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var22 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var4)) '
             '(var15 ((_ extract 1 1) var4)) '
             '(var23 ((_ extract 0 0) var22)) '
             '(var26 ((_ extract 1 1) var22))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var24 (= #b1 var23)) '
             '(var27 (= #b1 var26))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var25 (ite var24 1 0)) '
             '(var28 (ite var27 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var29 (+ var25 var28))) '
             '(let ('
             '(var20 (to_real var19)) '
             '(var30 (to_real var29))) '
             '(let ('
             '(var31 (+ var20 var30))) var31)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__radd__(SmtReal.make(a))))
        self.assertSmtSame(expr.floor().to_bit_vec(width=3),
                           a + b, inputs=(a, b))

    def test_real_add_rat(self):
        a = Fraction(3, 5)
        b = Fraction(7, 9)
        expr = SmtReal.make(a) + SmtReal.make(b)
        self.assertSmtExpr(expr, SmtRealAdd, ('(let ('
                                              '(var4 (/ 3.0 5.0)) '
                                              '(var7 (/ 7.0 9.0))) '
                                              '(let ('
                                              '(var8 (+ var4 var7))) var8))'
                                              ))
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__radd__(SmtReal.make(a))))
        expr = expr == SmtReal.make(a + b)
        self.assertSmtExpr(expr, SmtSame,
                           ('(let ('
                            '(var5 (/ 3.0 5.0)) '
                            '(var8 (/ 7.0 9.0)) '
                            '(var12 (/ 62.0 45.0))) '
                            '(let ('
                            '(var9 (+ var5 var8))) '
                            '(let ('
                            '(var13 (= var9 var12))) var13)))'
                            ))
        self.assertSmtSame(expr, True, inputs=())

    def test_real_sub(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) - SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealSub,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (- var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rsub__(SmtReal.make(a))))
        self.assertSmtSame(expr.floor().to_bit_vec(width=3),
                           a - b, inputs=(a, b))

    def test_real_sub_rat(self):
        a = Fraction(3, 5)
        b = Fraction(7, 9)
        expr = SmtReal.make(a) - SmtReal.make(b)
        self.assertSmtExpr(expr, SmtRealSub,
                           ('(let ('
                            '(var4 (/ 3.0 5.0)) '
                            '(var7 (/ 7.0 9.0))) '
                            '(let ('
                            '(var8 (- var4 var7))) var8))'
                            ))
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rsub__(SmtReal.make(a))))
        expr = expr == SmtReal.make(a - b)
        self.assertSmtExpr(expr, SmtSame,
                           ('(let ('
                            '(var5 (/ 3.0 5.0)) '
                            '(var8 (/ 7.0 9.0)) '
                            '(var11 (- 8.0))) '
                            '(let ('
                            '(var9 (- var5 var8)) '
                            '(var13 (/ var11 45.0))) '
                            '(let ('
                            '(var14 (= var9 var13))) var14)))'
                            ))
        self.assertSmtSame(expr, True, inputs=())

    def test_real_mul(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) * SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealMul,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (* var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rmul__(SmtReal.make(a))))
        self.assertSmtSame(expr.floor().to_bit_vec(width=4),
                           a * b, inputs=(a, b))

    def test_real_mul_rat(self):
        a = Fraction(3, 5)
        b = Fraction(7, 9)
        expr = SmtReal.make(a) * SmtReal.make(b)
        self.assertSmtExpr(expr, SmtRealMul, ('(let ('
                                              '(var4 (/ 3.0 5.0)) '
                                              '(var7 (/ 7.0 9.0))) '
                                              '(let ('
                                              '(var8 (* var4 var7))) var8))'
                                              ))
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rmul__(SmtReal.make(a))))
        expr = expr == SmtReal.make(a * b)
        self.assertSmtExpr(expr, SmtSame,
                           ('(let ('
                            '(var5 (/ 3.0 5.0)) '
                            '(var8 (/ 7.0 9.0)) '
                            '(var11 (/ 7.0 15.0))) '
                            '(let ('
                            '(var9 (* var5 var8))) '
                            '(let ('
                            '(var12 (= var9 var11))) var12)))'
                            ))
        self.assertSmtSame(expr, True, inputs=())

    def test_real_div(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) / SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealDiv,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (/ var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rtruediv__(SmtReal.make(a))))
        self.assertSmtSame(expr.floor().to_bit_vec(width=3),
                           a // b,
                           inputs=(a, b), assumptions=(b != 0,),
                           solver="cvc5")

    def test_real_div_rat(self):
        a = Fraction(3, 5)
        b = Fraction(7, 9)
        expr = SmtReal.make(a) / SmtReal.make(b)
        self.assertSmtExpr(expr, SmtRealDiv, ('(let ('
                                              '(var3 (/ 3.0 5.0)) '
                                              '(var6 (/ 7.0 9.0))) '
                                              '(let ('
                                              '(var7 (/ var3 var6))) var7))'
                                              ))
        self.assertEqual(repr(expr),
                         repr(SmtReal.make(b).__rtruediv__(SmtReal.make(a))))
        expr = expr == SmtReal.make(a / b)
        self.assertSmtExpr(expr, SmtSame,
                           ('(let ('
                            '(var4 (/ 3.0 5.0)) '
                            '(var7 (/ 7.0 9.0)) '
                            '(var11 (/ 27.0 35.0))) '
                            '(let ('
                            '(var8 (/ var4 var7))) '
                            '(let ('
                            '(var12 (= var8 var11))) var12)))'
                            ))
        self.assertSmtSame(expr, True, inputs=())

    def test_real_same(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtReal.make(a).same(SmtReal.make(b), SmtReal.make(c))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ("(let ((var4 ((_ extract 1 0) A)) "
             "(var22 ((_ extract 3 2) A)) "
             "(var32 ((_ extract 5 4) A))) "
             "(let ((var9 ((_ extract 0 0) var4)) "
             "(var15 ((_ extract 1 1) var4)) "
             "(var23 ((_ extract 0 0) var22)) "
             "(var26 ((_ extract 1 1) var22)) "
             "(var33 ((_ extract 0 0) var32)) "
             "(var36 ((_ extract 1 1) var32))) "
             "(let ((var10 (= #b1 var9)) "
             "(var16 (= #b1 var15)) "
             "(var24 (= #b1 var23)) "
             "(var27 (= #b1 var26)) "
             "(var34 (= #b1 var33)) "
             "(var37 (= #b1 var36))) "
             "(let ((var13 (ite var10 1 0)) "
             "(var18 (ite var16 2 0)) "
             "(var25 (ite var24 1 0)) "
             "(var28 (ite var27 2 0)) "
             "(var35 (ite var34 1 0)) "
             "(var38 (ite var37 2 0))) "
             "(let ((var19 (+ var13 var18)) "
             "(var29 (+ var25 var28)) "
             "(var39 (+ var35 var38))) "
             "(let ((var20 (to_real var19)) "
             "(var30 (to_real var29)) "
             "(var40 (to_real var39))) "
             "(let ((var41 (= var20 var30 var40))) "
             "var41)))))))"),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c))

    def test_real_distinct(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtReal.make(a).distinct(SmtReal.make(b), SmtReal.make(c))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A)) '
             '(var33 ((_ extract 5 4) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23)) '
             '(var34 ((_ extract 0 0) var33)) '
             '(var37 ((_ extract 1 1) var33))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27)) '
             '(var35 (= #b1 var34)) '
             '(var38 (= #b1 var37))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0)) '
             '(var36 (ite var35 1 0)) '
             '(var39 (ite var38 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29)) '
             '(var40 (+ var36 var39))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30)) '
             '(var41 (to_real var40))) '
             '(let ('
             '(var42 (distinct var21 var31 var41))) var42)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a != b) & (a != c) & (b != c),
                           inputs=(a, b, c))

    def test_real_eq(self):
        a = Signal()
        b = Signal()
        expr = SmtReal.make(a) == SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var14 ((_ extract 1 1) A))) '
             '(let ('
             '(var7 ((_ extract 0 0) var4)) '
             '(var15 ((_ extract 0 0) var14))) '
             '(let ('
             '(var8 (= #b1 var7)) '
             '(var16 (= #b1 var15))) '
             '(let ('
             '(var11 (ite var8 1 0)) '
             '(var17 (ite var16 1 0))) '
             '(let ('
             '(var12 (to_real var11)) '
             '(var18 (to_real var17))) '
             '(let ('
             '(var19 (= var12 var18))) var19))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a == b, inputs=(a, b))

    def test_real_ne(self):
        a = Signal()
        b = Signal()
        expr = SmtReal.make(a) != SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var15 ((_ extract 1 1) A))) '
             '(let ('
             '(var8 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 0 0) var15))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var17 (= #b1 var16))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var18 (ite var17 1 0))) '
             '(let ('
             '(var13 (to_real var12)) '
             '(var19 (to_real var18))) '
             '(let ('
             '(var20 (distinct var13 var19))) var20))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a != b, inputs=(a, b))

    def test_real_lt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) < SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealLt,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (< var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a < b, inputs=(a, b))

    def test_real_le(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) <= SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealLE,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (<= var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a <= b, inputs=(a, b))

    def test_real_gt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) > SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealGt,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (> var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a > b, inputs=(a, b))

    def test_real_ge(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtReal.make(a) >= SmtReal.make(b)
        self.assertSmtExpr(
            expr,
            SmtRealGE,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var23 ((_ extract 3 2) A))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var24 ((_ extract 0 0) var23)) '
             '(var27 ((_ extract 1 1) var23))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var25 (= #b1 var24)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var25 1 0)) '
             '(var29 (ite var28 2 0))) '
             '(let ('
             '(var20 (+ var14 var19)) '
             '(var30 (+ var26 var29))) '
             '(let ('
             '(var21 (to_real var20)) '
             '(var31 (to_real var30))) '
             '(let ('
             '(var32 (>= var21 var31))) var32)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a >= b, inputs=(a, b))

    def test_real_abs(self):
        a = Signal(signed(3))
        expr = abs(SmtReal.make(a))
        self.assertSmtExpr(
            expr,
            SmtRealITE,
            ('(let ('
             '(var4 ((_ extract 2 0) A)) '
             '(var25 (- 4))) '
             '(let ('
             '(var10 ((_ extract 0 0) var4)) '
             '(var16 ((_ extract 1 1) var4)) '
             '(var21 ((_ extract 2 2) var4))) '
             '(let ('
             '(var11 (= #b1 var10)) '
             '(var17 (= #b1 var16)) '
             '(var22 (= #b1 var21))) '
             '(let ('
             '(var14 (ite var11 1 0)) '
             '(var19 (ite var17 2 0)) '
             '(var26 (ite var22 var25 0))) '
             '(let ('
             '(var27 (+ var14 var19 var26))) '
             '(let ('
             '(var28 (to_real var27))) '
             '(let ('
             '(var30 (< var28 0.0)) '
             '(var31 (- var28))) '
             '(let ('
             '(var32 (ite var30 var31 var28))) var32))))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr.floor().to_bit_vec(width=3),
                           abs(a), inputs=(a,))

    def test_real_floor(self):
        sig = Signal(signed(4))
        expr = (SmtReal.make(sig) / SmtReal.make(4)).floor()
        self.assertSmtExpr(
            expr,
            SmtRealToInt,
            ('(let ('
             '(var5 ((_ extract 3 0) A)) '
             '(var31 (- 8))) '
             '(let ('
             '(var11 ((_ extract 0 0) var5)) '
             '(var17 ((_ extract 1 1) var5)) '
             '(var22 ((_ extract 2 2) var5)) '
             '(var27 ((_ extract 3 3) var5))) '
             '(let ('
             '(var12 (= #b1 var11)) '
             '(var18 (= #b1 var17)) '
             '(var23 (= #b1 var22)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var15 (ite var12 1 0)) '
             '(var20 (ite var18 2 0)) '
             '(var25 (ite var23 4 0)) '
             '(var32 (ite var28 var31 0))) '
             '(let ('
             '(var33 (+ var15 var20 var25 var32))) '
             '(let ('
             '(var34 (to_real var33))) '
             '(let ('
             '(var36 (/ var34 4.0))) '
             '(let ('
             '(var37 (to_int var36))) '
             'var37))))))))'
             ),
            input_bit_ranges=[
                (sig, range(0, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           ((sig.as_signed() >> 2) + Const(0, signed(3)))[:3],
                           inputs=(sig,))

    def test_real_trunc(self):
        sig = Signal(signed(4))
        expr = (SmtReal.make(sig) / SmtReal.make(4)).trunc()
        self.assertSmtExpr(
            expr,
            SmtIntITE,
            ('(let ('
             '(var5 ((_ extract 3 0) A)) '
             '(var31 (- 8))) '
             '(let ('
             '(var11 ((_ extract 0 0) var5)) '
             '(var17 ((_ extract 1 1) var5)) '
             '(var22 ((_ extract 2 2) var5)) '
             '(var27 ((_ extract 3 3) var5))) '
             '(let ('
             '(var12 (= #b1 var11)) '
             '(var18 (= #b1 var17)) '
             '(var23 (= #b1 var22)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var15 (ite var12 1 0)) '
             '(var20 (ite var18 2 0)) '
             '(var25 (ite var23 4 0)) '
             '(var32 (ite var28 var31 0))) '
             '(let ('
             '(var33 (+ var15 var20 var25 var32))) '
             '(let ('
             '(var34 (to_real var33))) '
             '(let ('
             '(var36 (/ var34 4.0))) '
             '(let ('
             '(var38 (< var36 0.0)) '
             '(var40 (- var36)) '
             '(var43 (to_int var36))) '
             '(let ('
             '(var41 (to_int var40))) '
             '(let ('
             '(var42 (- var41))) '
             '(let ('
             '(var44 (ite var38 var42 var43))) '
             'var44)))))))))))'
             ),
            input_bit_ranges=[
                (sig, range(0, 4)),
            ],
            input_width=4,
        )
        expected = Array(Const(int(Const.normalize(i, sig.shape()) / 4),
                               signed(3))
                         for i in range(2 ** sig.width))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           expected[sig.as_unsigned()].as_unsigned(),
                           inputs=(sig,))

    def test_real_ceil(self):
        sig = Signal(signed(4))
        expr = (SmtReal.make(sig) / SmtReal.make(4)).ceil()
        self.assertSmtExpr(
            expr,
            SmtIntNeg,
            ('(let ('
             '(var6 ((_ extract 3 0) A)) '
             '(var31 (- 8))) '
             '(let ('
             '(var12 ((_ extract 0 0) var6)) '
             '(var18 ((_ extract 1 1) var6)) '
             '(var23 ((_ extract 2 2) var6)) '
             '(var28 ((_ extract 3 3) var6))) '
             '(let ('
             '(var13 (= #b1 var12)) '
             '(var19 (= #b1 var18)) '
             '(var24 (= #b1 var23)) '
             '(var29 (= #b1 var28))) '
             '(let ('
             '(var16 (ite var13 1 0)) '
             '(var21 (ite var19 2 0)) '
             '(var26 (ite var24 4 0)) '
             '(var32 (ite var29 var31 0))) '
             '(let ('
             '(var33 (+ var16 var21 var26 var32))) '
             '(let ('
             '(var34 (to_real var33))) '
             '(let ('
             '(var36 (/ var34 4.0))) '
             '(let ('
             '(var37 (- var36))) '
             '(let ('
             '(var38 (to_int var37))) '
             '(let ('
             '(var39 (- var38))) '
             'var39))))))))))'
             ),
            input_bit_ranges=[
                (sig, range(0, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           (-(-sig >> 2))[:3],
                           inputs=(sig,))

    def test_real_is_int(self):
        sig = Signal(signed(4))
        expr = (SmtReal.make(sig) / SmtReal.make(4)).is_int()
        self.assertSmtExpr(
            expr,
            SmtRealIsInt,
            ('(let ('
             '(var5 ((_ extract 3 0) A)) '
             '(var31 (- 8))) '
             '(let ('
             '(var11 ((_ extract 0 0) var5)) '
             '(var17 ((_ extract 1 1) var5)) '
             '(var22 ((_ extract 2 2) var5)) '
             '(var27 ((_ extract 3 3) var5))) '
             '(let ('
             '(var12 (= #b1 var11)) '
             '(var18 (= #b1 var17)) '
             '(var23 (= #b1 var22)) '
             '(var28 (= #b1 var27))) '
             '(let ('
             '(var15 (ite var12 1 0)) '
             '(var20 (ite var18 2 0)) '
             '(var25 (ite var23 4 0)) '
             '(var32 (ite var28 var31 0))) '
             '(let ('
             '(var33 (+ var15 var20 var25 var32))) '
             '(let ('
             '(var34 (to_real var33))) '
             '(let ('
             '(var36 (/ var34 4.0))) '
             '(let ('
             '(var37 (is_int var36))) '
             'var37))))))))'
             ),
            input_bit_ranges=[
                (sig, range(0, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr,
                           sig % 4 == 0,
                           inputs=(sig,))


class TestInt(SmtTestCase):
    def test_int_make(self):
        self.assertSmtExpr(SmtInt.make(0), SmtIntConst, "0")
        self.assertSmtExpr(SmtInt.make(1), SmtIntConst, "1")
        self.assertSmtExpr(SmtInt.make(-1), SmtIntConst,
                           '(let ((var2 (- 1))) var2)')
        self.assertSmtExpr(SmtInt.make(Const(128, signed(8))), SmtIntConst,
                           '(let ((var2 (- 128))) var2)')
        sig0 = Signal(0)
        self.assertSmtExpr(SmtInt.make(sig0), SmtIntConst, "0")
        self.assertSmtExpr(SmtInt.make(SmtBitVec.make(1, width=1)),
                           SmtIntFromBitVec,
                           ('(let ('
                            '(var4 ((_ extract 0 0) #b1))) '
                            '(let ('
                            '(var5 (= #b1 var4))) '
                            '(let ('
                            '(var8 (ite var5 1 0))) '
                            'var8)))'
                            ))
        sig_u4 = Signal(4)
        self.assertSmtExpr(SmtInt.make(sig_u4),
                           SmtIntFromBitVec,
                           ('(let ('
                            '(var2 ((_ extract 3 0) A))) '
                            '(let ('
                            '(var8 ((_ extract 0 0) var2)) '
                            '(var14 ((_ extract 1 1) var2)) '
                            '(var19 ((_ extract 2 2) var2)) '
                            '(var24 ((_ extract 3 3) var2))) '
                            '(let ('
                            '(var9 (= #b1 var8)) '
                            '(var15 (= #b1 var14)) '
                            '(var20 (= #b1 var19)) '
                            '(var25 (= #b1 var24))) '
                            '(let ('
                            '(var12 (ite var9 1 0)) '
                            '(var17 (ite var15 2 0)) '
                            '(var22 (ite var20 4 0)) '
                            '(var27 (ite var25 8 0))) '
                            '(let ('
                            '(var28 (+ var12 var17 var22 var27))) '
                            'var28)))))'
                            ),
                           input_bit_ranges=[(sig_u4, range(0, 4))],
                           input_width=4)
        sig_s4 = Signal(signed(4))
        expr = SmtInt.make(sig_s4)
        self.assertSmtExpr(expr, SmtIntFromBitVec,
                           ('(let ('
                            '(var2 ((_ extract 3 0) A)) '
                            '(var28 (- 8))) '
                            '(let ('
                            '(var8 ((_ extract 0 0) var2)) '
                            '(var14 ((_ extract 1 1) var2)) '
                            '(var19 ((_ extract 2 2) var2)) '
                            '(var24 ((_ extract 3 3) var2))) '
                            '(let ('
                            '(var9 (= #b1 var8)) '
                            '(var15 (= #b1 var14)) '
                            '(var20 (= #b1 var19)) '
                            '(var25 (= #b1 var24))) '
                            '(let ('
                            '(var12 (ite var9 1 0)) '
                            '(var17 (ite var15 2 0)) '
                            '(var22 (ite var20 4 0)) '
                            '(var29 (ite var25 var28 0))) '
                            '(let ('
                            '(var30 (+ var12 var17 var22 var29))) '
                            'var30)))))'
                            ),
                           input_bit_ranges=[(sig_s4, range(0, 4))],
                           input_width=4)
        expr = expr.to_bit_vec(width=5)
        self.assertSmtExpr(
            expr, SmtBitVecFromInt,
            ('(let ('
             '(var2 ((_ extract 3 0) A)) '
             '(var28 (- 8))) '
             '(let ('
             '(var8 ((_ extract 0 0) var2)) '
             '(var14 ((_ extract 1 1) var2)) '
             '(var19 ((_ extract 2 2) var2)) '
             '(var24 ((_ extract 3 3) var2))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var20 (= #b1 var19)) '
             '(var25 (= #b1 var24))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var22 (ite var20 4 0)) '
             '(var29 (ite var25 var28 0))) '
             '(let ('
             '(var30 (+ var12 var17 var22 var29))) '
             '(let ('
             '(var35 (div var30 16)) '
             '(var40 (div var30 8)) '
             '(var44 (div var30 4)) '
             '(var48 (div var30 2)) '
             '(var52 (mod var30 2))) '
             '(let ('
             '(var36 (mod var35 2)) '
             '(var41 (mod var40 2)) '
             '(var45 (mod var44 2)) '
             '(var49 (mod var48 2)) '
             '(var53 (= 1 var52))) '
             '(let ('
             '(var37 (= 1 var36)) '
             '(var42 (= 1 var41)) '
             '(var46 (= 1 var45)) '
             '(var50 (= 1 var49)) '
             '(var54 (ite var53 #b1 #b0))) '
             '(let ('
             '(var39 (ite var37 #b1 #b0)) '
             '(var43 (ite var42 #b1 #b0)) '
             '(var47 (ite var46 #b1 #b0)) '
             '(var51 (ite var50 #b1 #b0))) '
             '(let ('
             '(var55 (concat var39 var43 var47 var51 var54))) '
             'var55))))))))))'
             ),
            input_bit_ranges=[(sig_s4, range(0, 4))],
            input_width=4)
        self.assertSmtSame(expr, (sig_s4 + Const(0, 5))[:5], inputs=(sig_s4,))

    def test_int_ite(self):
        expr = SmtBool.make(False).ite(SmtInt.make(1), SmtInt.make(0))
        self.assertSmtExpr(expr, SmtIntITE,
                           ('(let ('
                            '(var4 (ite false 1 0))) var4)'
                            ))
        self.assertIs(expr, +expr)  # type: ignore

    def test_int_neg(self):
        a = Signal(signed(3))
        expr = -SmtInt.make(a)
        self.assertSmtExpr(
            expr,
            SmtIntNeg,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var23 (- 4))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var20 ((_ extract 2 2) var3))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var21 (= #b1 var20))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var21 var23 0))) '
             '(let ('
             '(var25 (+ var13 var18 var24))) '
             '(let ('
             '(var26 (- var25))) '
             'var26))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr.to_bit_vec(width=4),
                           (-a)[:4], inputs=(a,))

    def test_int_add(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) + SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntAdd,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var20 ((_ extract 3 2) A))) '
             '(let ('
             '(var8 ((_ extract 0 0) var3)) '
             '(var14 ((_ extract 1 1) var3)) '
             '(var21 ((_ extract 0 0) var20)) '
             '(var24 ((_ extract 1 1) var20))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var22 (= #b1 var21)) '
             '(var25 (= #b1 var24))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var23 (ite var22 1 0)) '
             '(var26 (ite var25 2 0))) '
             '(let ('
             '(var18 (+ var12 var17)) '
             '(var27 (+ var23 var26))) '
             '(let ('
             '(var28 (+ var18 var27))) '
             'var28))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(b).__radd__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           a + b, inputs=(a, b))

    def test_int_sub(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) - SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntSub,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (- var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(b).__rsub__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           a - b, inputs=(a, b))

    def test_int_mul(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) * SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntMul,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (* var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(b).__rmul__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=4),
                           a * b, inputs=(a, b))

    def test_int_floor_div(self):
        a = Signal(signed(3))
        b = Signal(signed(3))
        expr = SmtInt.make(a) // SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntFloorDiv,
            ('(let ('
             '(var2 ((_ extract 2 0) A)) '
             '(var23 (- 4)) '
             '(var27 ((_ extract 5 3) A))) '
             '(let ('
             '(var8 ((_ extract 0 0) var2)) '
             '(var14 ((_ extract 1 1) var2)) '
             '(var19 ((_ extract 2 2) var2)) '
             '(var28 ((_ extract 0 0) var27)) '
             '(var31 ((_ extract 1 1) var27)) '
             '(var34 ((_ extract 2 2) var27))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var20 (= #b1 var19)) '
             '(var29 (= #b1 var28)) '
             '(var32 (= #b1 var31)) '
             '(var35 (= #b1 var34))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var24 (ite var20 var23 0)) '
             '(var30 (ite var29 1 0)) '
             '(var33 (ite var32 2 0)) '
             '(var36 (ite var35 var23 0))) '
             '(let ('
             '(var25 (+ var12 var17 var24)) '
             '(var37 (+ var30 var33 var36))) '
             '(let ('
             '(var40 (< var37 0)) '
             '(var43 (mod var25 var37)) '
             '(var47 (div var25 var37))) '
             '(let ('
             '(var44 (distinct 0 var43)) '
             '(var48 (- var47 1))) '
             '(let ('
             '(var45 (and var40 var44))) '
             '(let ('
             '(var49 (ite var45 var48 var47))) '
             'var49)))))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(b).__rfloordiv__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           (a // b)[:3], inputs=(a, b),
                           assumptions=(b != 0,))

    def test_int_floor_mod(self):
        a = Signal(signed(3))
        b = Signal(signed(3))
        expr = SmtInt.make(a) % SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntFloorMod,
            ('(let ('
             '(var2 ((_ extract 2 0) A)) '
             '(var23 (- 4)) '
             '(var27 ((_ extract 5 3) A))) '
             '(let ('
             '(var8 ((_ extract 0 0) var2)) '
             '(var14 ((_ extract 1 1) var2)) '
             '(var19 ((_ extract 2 2) var2)) '
             '(var28 ((_ extract 0 0) var27)) '
             '(var31 ((_ extract 1 1) var27)) '
             '(var34 ((_ extract 2 2) var27))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var20 (= #b1 var19)) '
             '(var29 (= #b1 var28)) '
             '(var32 (= #b1 var31)) '
             '(var35 (= #b1 var34))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var24 (ite var20 var23 0)) '
             '(var30 (ite var29 1 0)) '
             '(var33 (ite var32 2 0)) '
             '(var36 (ite var35 var23 0))) '
             '(let ('
             '(var25 (+ var12 var17 var24)) '
             '(var37 (+ var30 var33 var36))) '
             '(let ('
             '(var40 (< var37 0)) '
             '(var43 (mod var25 var37))) '
             '(let ('
             '(var44 (distinct 0 var43)) '
             '(var46 (+ var43 var37))) '
             '(let ('
             '(var45 (and var40 var44))) '
             '(let ('
             '(var47 (ite var45 var46 var43))) '
             'var47)))))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(b).__rmod__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           (a % b)[:3], inputs=(a, b), assumptions=(b != 0,))

    def test_int_floor_div_const(self):
        a = Signal(signed(3))
        expr = SmtInt.make(a) // SmtInt.make(3)
        self.assertSmtExpr(
            expr,
            SmtIntFloorDiv,
            ('(let ('
             '(var2 ((_ extract 2 0) A)) '
             '(var23 (- 4))) '
             '(let ('
             '(var8 ((_ extract 0 0) var2)) '
             '(var14 ((_ extract 1 1) var2)) '
             '(var19 ((_ extract 2 2) var2))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var20 (= #b1 var19))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var24 (ite var20 var23 0))) '
             '(let ('
             '(var25 (+ var12 var17 var24))) '
             '(let ('
             '(var28 (div var25 3))) '
             'var28))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(3).__rfloordiv__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           (a // 3)[:3], inputs=(a,))

    def test_int_floor_mod_const(self):
        a = Signal(signed(3))
        expr = SmtInt.make(a) % SmtInt.make(3)
        self.assertSmtExpr(
            expr,
            SmtIntFloorMod,
            ('(let ('
             '(var2 ((_ extract 2 0) A)) '
             '(var23 (- 4))) '
             '(let ('
             '(var8 ((_ extract 0 0) var2)) '
             '(var14 ((_ extract 1 1) var2)) '
             '(var19 ((_ extract 2 2) var2))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var20 (= #b1 var19))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var24 (ite var20 var23 0))) '
             '(let ('
             '(var25 (+ var12 var17 var24))) '
             '(let ('
             '(var28 (mod var25 3))) '
             'var28))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertEqual(repr(expr),
                         repr(SmtInt.make(3).__rmod__(SmtInt.make(a))))
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           (a % 3)[:3], inputs=(a,))

    def test_int_euclid_div(self):
        a = Signal(signed(3))
        b = Signal(signed(3))
        expr = SmtInt.make(a).euclid_div(SmtInt.make(b))
        self.assertSmtExpr(
            expr,
            SmtIntEuclidDiv,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var24 (- 4)) '
             '(var28 ((_ extract 5 3) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var20 ((_ extract 2 2) var3)) '
             '(var29 ((_ extract 0 0) var28)) '
             '(var32 ((_ extract 1 1) var28)) '
             '(var35 ((_ extract 2 2) var28))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var21 (= #b1 var20)) '
             '(var30 (= #b1 var29)) '
             '(var33 (= #b1 var32)) '
             '(var36 (= #b1 var35))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var25 (ite var21 var24 0)) '
             '(var31 (ite var30 1 0)) '
             '(var34 (ite var33 2 0)) '
             '(var37 (ite var36 var24 0))) '
             '(let ('
             '(var26 (+ var13 var18 var25)) '
             '(var38 (+ var31 var34 var37))) '
             '(let ('
             '(var39 (div var26 var38))) '
             'var39))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        div_table = []
        for a_v in range(2 ** a.width):
            for b_v in range(2 ** b.width):
                a_v = Const.normalize(a_v, a.shape())
                b_v = Const.normalize(b_v, b.shape())
                if b_v == 0:
                    q = 0
                else:
                    q = a_v // b_v
                    if a_v % b_v < 0:
                        if b_v < 0:
                            q += 1
                        else:
                            q -= 1
                div_table.append(Const(q, a.shape()))
        div_table = Array(div_table)
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           div_table[Cat(b, a)][:3], inputs=(a, b),
                           assumptions=(b != 0,))

    def test_int_euclid_rem(self):
        a = Signal(signed(3))
        b = Signal(signed(3))
        expr = SmtInt.make(a).euclid_rem(SmtInt.make(b))
        self.assertSmtExpr(
            expr,
            SmtIntEuclidRem,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var24 (- 4)) '
             '(var28 ((_ extract 5 3) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var20 ((_ extract 2 2) var3)) '
             '(var29 ((_ extract 0 0) var28)) '
             '(var32 ((_ extract 1 1) var28)) '
             '(var35 ((_ extract 2 2) var28))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var21 (= #b1 var20)) '
             '(var30 (= #b1 var29)) '
             '(var33 (= #b1 var32)) '
             '(var36 (= #b1 var35))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var25 (ite var21 var24 0)) '
             '(var31 (ite var30 1 0)) '
             '(var34 (ite var33 2 0)) '
             '(var37 (ite var36 var24 0))) '
             '(let ('
             '(var26 (+ var13 var18 var25)) '
             '(var38 (+ var31 var34 var37))) '
             '(let ('
             '(var39 (mod var26 var38))) '
             'var39))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(expr.input_sort, SmtSortInt())
        rem_table = []
        for a_v in range(2 ** a.width):
            for b_v in range(2 ** b.width):
                a_v = Const.normalize(a_v, a.shape())
                b_v = Const.normalize(b_v, b.shape())
                if b_v == 0:
                    r = 0
                else:
                    r = a_v % b_v
                    if r < 0:
                        r += abs(b_v)
                rem_table.append(Const(r, a.shape()))
        rem_table = Array(rem_table)
        self.assertSmtSame(expr.to_bit_vec(width=3),
                           rem_table[Cat(b, a)][:3], inputs=(a, b),
                           assumptions=(b != 0,))

    def test_int_same(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtInt.make(a).same(SmtInt.make(b), SmtInt.make(c))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var20 ((_ extract 3 2) A)) '
             '(var29 ((_ extract 5 4) A))) '
             '(let ('
             '(var8 ((_ extract 0 0) var3)) '
             '(var14 ((_ extract 1 1) var3)) '
             '(var21 ((_ extract 0 0) var20)) '
             '(var24 ((_ extract 1 1) var20)) '
             '(var30 ((_ extract 0 0) var29)) '
             '(var33 ((_ extract 1 1) var29))) '
             '(let ('
             '(var9 (= #b1 var8)) '
             '(var15 (= #b1 var14)) '
             '(var22 (= #b1 var21)) '
             '(var25 (= #b1 var24)) '
             '(var31 (= #b1 var30)) '
             '(var34 (= #b1 var33))) '
             '(let ('
             '(var12 (ite var9 1 0)) '
             '(var17 (ite var15 2 0)) '
             '(var23 (ite var22 1 0)) '
             '(var26 (ite var25 2 0)) '
             '(var32 (ite var31 1 0)) '
             '(var35 (ite var34 2 0))) '
             '(let ('
             '(var18 (+ var12 var17)) '
             '(var27 (+ var23 var26)) '
             '(var36 (+ var32 var35))) '
             '(let ('
             '(var37 (= var18 var27 var36))) '
             'var37))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c))

    def test_int_distinct(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtInt.make(a).distinct(SmtInt.make(b), SmtInt.make(c))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A)) '
             '(var30 ((_ extract 5 4) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21)) '
             '(var31 ((_ extract 0 0) var30)) '
             '(var34 ((_ extract 1 1) var30))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25)) '
             '(var32 (= #b1 var31)) '
             '(var35 (= #b1 var34))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0)) '
             '(var33 (ite var32 1 0)) '
             '(var36 (ite var35 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27)) '
             '(var37 (+ var33 var36))) '
             '(let ('
             '(var38 (distinct var19 var28 var37))) '
             'var38))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a != b) & (a != c) & (b != c),
                           inputs=(a, b, c))

    def test_int_eq(self):
        a = Signal()
        b = Signal()
        expr = SmtInt.make(a) == SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var3 ((_ extract 0 0) A)) '
             '(var12 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 ((_ extract 0 0) var3)) '
             '(var13 ((_ extract 0 0) var12))) '
             '(let ('
             '(var7 (= #b1 var6)) '
             '(var14 (= #b1 var13))) '
             '(let ('
             '(var10 (ite var7 1 0)) '
             '(var15 (ite var14 1 0))) '
             '(let ('
             '(var16 (= var10 var15))) '
             'var16)))))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a == b, inputs=(a, b))

    def test_int_ne(self):
        a = Signal()
        b = Signal()
        expr = SmtInt.make(a) != SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var3 ((_ extract 0 0) A)) '
             '(var13 ((_ extract 1 1) A))) '
             '(let ('
             '(var7 ((_ extract 0 0) var3)) '
             '(var14 ((_ extract 0 0) var13))) '
             '(let ('
             '(var8 (= #b1 var7)) '
             '(var15 (= #b1 var14))) '
             '(let ('
             '(var11 (ite var8 1 0)) '
             '(var16 (ite var15 1 0))) '
             '(let ('
             '(var17 (distinct var11 var16))) '
             'var17)))))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a != b, inputs=(a, b))

    def test_int_lt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) < SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntLt,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (< var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a < b, inputs=(a, b))

    def test_int_le(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) <= SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntLE,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (<= var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a <= b, inputs=(a, b))

    def test_int_gt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) > SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntGt,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (> var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a > b, inputs=(a, b))

    def test_int_ge(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtInt.make(a) >= SmtInt.make(b)
        self.assertSmtExpr(
            expr,
            SmtIntGE,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var21 ((_ extract 3 2) A))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var22 ((_ extract 0 0) var21)) '
             '(var25 ((_ extract 1 1) var21))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var23 (= #b1 var22)) '
             '(var26 (= #b1 var25))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var24 (ite var23 1 0)) '
             '(var27 (ite var26 2 0))) '
             '(let ('
             '(var19 (+ var13 var18)) '
             '(var28 (+ var24 var27))) '
             '(let ('
             '(var29 (>= var19 var28))) '
             'var29))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a >= b, inputs=(a, b))

    def test_int_abs(self):
        a = Signal(signed(3))
        expr = abs(SmtInt.make(a))
        self.assertSmtExpr(
            expr,
            SmtIntAbs,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var24 (- 4))) '
             '(let ('
             '(var9 ((_ extract 0 0) var3)) '
             '(var15 ((_ extract 1 1) var3)) '
             '(var20 ((_ extract 2 2) var3))) '
             '(let ('
             '(var10 (= #b1 var9)) '
             '(var16 (= #b1 var15)) '
             '(var21 (= #b1 var20))) '
             '(let ('
             '(var13 (ite var10 1 0)) '
             '(var18 (ite var16 2 0)) '
             '(var25 (ite var21 var24 0))) '
             '(let ('
             '(var26 (+ var13 var18 var25))) '
             '(let ('
             '(var27 (abs var26))) '
             'var27))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr.to_bit_vec(width=4),
                           abs(a)[:4], inputs=(a,))


class TestBitVec(SmtTestCase):
    def test_bit_vec_ite(self):
        expr = SmtBool.make(False).ite(SmtBitVec.make(1, width=1),
                                       SmtBitVec.make(0, width=1))
        self.assertSmtExpr(expr, SmtBitVecITE,
                           ('(let ('
                            '(var4 (ite false #b1 #b0))) '
                            'var4)'
                            ))
        expr = SmtBool.make(True).ite(SmtBitVec.make(0xF, width=4),
                                      SmtBitVec.make(0, width=4))
        self.assertSmtExpr(expr, SmtBitVecITE,
                           ('(let ('
                            '(var4 (ite true #xf #x0))) '
                            'var4)'
                            ))

    def test_bit_vec_same(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtBitVec.make(a).same(SmtBitVec.make(b), SmtBitVec.make(c))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A)) '
             '(var7 ((_ extract 5 4) A))) '
             '(let ('
             '(var8 (= var3 var5 var7))) '
             'var8))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c))

    def test_bit_vec_distinct(self):
        a = Signal(2)
        b = Signal(2)
        c = Signal(2)
        expr = SmtBitVec.make(a).distinct(SmtBitVec.make(b), SmtBitVec.make(c))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A)) '
             '(var7 ((_ extract 5 4) A))) '
             '(let ('
             '(var8 (distinct var3 var5 var7))) '
             'var8))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a != b) & (a != c) & (b != c),
                           inputs=(a, b, c))

    def test_bit_vec_make(self):
        self.assertSmtExpr(SmtBitVec.make(0, width=8), SmtBitVecConst, '#x00')
        self.assertSmtExpr(SmtBitVec.make(1, width=5), SmtBitVecConst,
                           '#b00001')
        self.assertSmtExpr(SmtBitVec.make(-1, width=4), SmtBitVecConst, '#xf')
        self.assertSmtExpr(SmtBitVec.make(Const(128, signed(8))),
                           SmtBitVecConst, '#x80')
        with self.assertRaises(AssertionError):
            sig0 = Signal(0)
            SmtBitVec.make(sig0)
        self.assertSmtExpr(SmtBitVec.make(SmtInt.make(1), width=4),
                           SmtBitVecFromInt,
                           ('(let ('
                            '(var7 (div 1 8)) '
                            '(var15 (div 1 4)) '
                            '(var19 (div 1 2)) '
                            '(var23 (mod 1 2))) '
                            '(let ('
                            '(var9 (mod var7 2)) '
                            '(var16 (mod var15 2)) '
                            '(var20 (mod var19 2)) '
                            '(var24 (= 1 var23))) '
                            '(let ('
                            '(var10 (= 1 var9)) '
                            '(var17 (= 1 var16)) '
                            '(var21 (= 1 var20)) '
                            '(var25 (ite var24 #b1 #b0))) '
                            '(let ('
                            '(var13 (ite var10 #b1 #b0)) '
                            '(var18 (ite var17 #b1 #b0)) '
                            '(var22 (ite var21 #b1 #b0))) '
                            '(let ('
                            '(var26 (concat var13 var18 var22 var25))) '
                            'var26)))))'
                            ))
        self.assertSmtExpr(SmtBitVec.make(SmtBitVec.make(1, width=4)),
                           SmtBitVecConst, '#x1')
        sig_u4 = Signal(4)
        self.assertSmtExpr(SmtBitVec.make(sig_u4),
                           SmtBitVecInput,
                           ('(let ('
                            '(var2 ((_ extract 3 0) A))) '
                            'var2)'
                            ),
                           input_bit_ranges=[(sig_u4, range(0, 4))],
                           input_width=4)
        sig_s4 = Signal(signed(4))
        expr = SmtBitVec.make(sig_s4)
        self.assertSmtExpr(expr, SmtBitVecInput,
                           ('(let ('
                            '(var2 ((_ extract 3 0) A))) '
                            'var2)'
                            ),
                           input_bit_ranges=[(sig_s4, range(0, 4))],
                           input_width=4)
        self.assertSmtSame(expr, sig_s4.as_unsigned(), inputs=(sig_s4,))

    def test_bit_vec_input_subclassing(self):
        with self.assertRaises(TypeError):
            class Subclass(SmtBitVecInput):
                pass

    def test_bit_vec_input_const_0(self):
        # specifically bypass the code path for handling constants
        expr = SmtBitVecInput(Const(0, 1))
        self.assertSmtExpr(expr, SmtBitVecInput,
                           ('(let ('
                            '(var2 ((_ extract 0 0) A))) '
                            'var2)'
                            ),
                           input_bit_ranges=[(Const(0, 1), range(0, 1))],
                           input_width=1)
        self.assertSmtSame(expr, 0, inputs=())

    def test_bit_vec_to_int(self):
        sig = Signal(2)
        expr = SmtBitVec.make(sig).to_int()
        self.assertSmtExpr(expr, SmtIntFromBitVec,
                           ('(let ('
                            '(var2 ((_ extract 1 0) A))) '
                            '(let ('
                            '(var8 ((_ extract 0 0) var2)) '
                            '(var14 ((_ extract 1 1) var2))) '
                            '(let ('
                            '(var9 (= #b1 var8)) '
                            '(var15 (= #b1 var14))) '
                            '(let ('
                            '(var12 (ite var9 1 0)) '
                            '(var17 (ite var15 2 0))) '
                            '(let ('
                            '(var18 (+ var12 var17))) '
                            'var18)))))'
                            ),
                           input_bit_ranges=[(sig, range(0, 2))],
                           input_width=2)
        self.assertSmtSame(expr.to_bit_vec(2), sig, inputs=(sig,))

    def test_bit_vec_to_real(self):
        sig = Signal(2)
        expr = SmtBitVec.make(sig).to_real()
        self.assertSmtExpr(expr, SmtIntToReal,
                           ('(let ('
                            '(var3 ((_ extract 1 0) A))) '
                            '(let ('
                            '(var9 ((_ extract 0 0) var3)) '
                            '(var15 ((_ extract 1 1) var3))) '
                            '(let ('
                            '(var10 (= #b1 var9)) '
                            '(var16 (= #b1 var15))) '
                            '(let ('
                            '(var13 (ite var10 1 0)) '
                            '(var18 (ite var16 2 0))) '
                            '(let ('
                            '(var19 (+ var13 var18))) '
                            '(let ('
                            '(var20 (to_real var19))) '
                            'var20))))))'
                            ),
                           input_bit_ranges=[(sig, range(0, 2))],
                           input_width=2)
        self.assertSmtSame(expr.floor().to_bit_vec(2), sig, inputs=(sig,))

    def test_bit_vec_neg(self):
        a = Signal(signed(3))
        expr = -SmtBitVec.make(a)
        self.assertSmtExpr(
            expr,
            SmtBitVecNeg,
            ('(let ('
             '(var3 ((_ extract 2 0) A))) '
             '(let ('
             '(var4 (bvneg var3))) '
             'var4))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertIs(expr, +expr)
        self.assertSmtSame(expr,
                           (-a)[:3], inputs=(a,))

    def test_bit_vec_not(self):
        a = Signal(signed(3))
        expr = ~SmtBitVec.make(a)
        self.assertSmtExpr(
            expr,
            SmtBitVecNot,
            ('(let ('
             '(var3 ((_ extract 2 0) A))) '
             '(let ('
             '(var4 (bvnot var3))) '
             'var4))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr,
                           (~a)[:3], inputs=(a,))

    def test_bit_vec_add(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) + SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecAdd,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvadd var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__radd__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a + b)[:2], inputs=(a, b))

    def test_bit_vec_sub(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) - SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecAdd,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var6 ((_ extract 3 2) A))) '
             '(let ('
             '(var7 (bvneg var6))) '
             '(let ('
             '(var8 (bvadd var3 var7))) '
             'var8)))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__rsub__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a - b)[:2], inputs=(a, b))

    def test_bit_vec_mul(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) * SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecMul,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvmul var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__rmul__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a * b)[:2], inputs=(a, b))

    def test_bit_vec_div(self):
        a = Signal(3)
        b = Signal(3)
        expr = SmtBitVec.make(a) // SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecDiv,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var5 ((_ extract 5 3) A))) '
             '(let ('
             '(var6 (bvudiv var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(repr(expr), repr(
            SmtBitVec.make(b).__rfloordiv__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a // b)[:3], inputs=(a, b),
                           assumptions=(b != 0,))

    def test_bit_vec_rem(self):
        a = Signal(3)
        b = Signal(3)
        expr = SmtBitVec.make(a) % SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecRem,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var5 ((_ extract 5 3) A))) '
             '(let ('
             '(var6 (bvurem var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(repr(expr), repr(
            SmtBitVec.make(b).__rmod__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a % b)[:3], inputs=(a, b),
                           assumptions=(b != 0,))

    def test_bit_vec_divmod(self):
        a = Signal(3)
        b = Signal(3)
        q, r = divmod(SmtBitVec.make(a), SmtBitVec.make(b))
        self.assertSmtExpr(
            q,
            SmtBitVecDiv,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var5 ((_ extract 5 3) A))) '
             '(let ('
             '(var6 (bvudiv var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertSmtExpr(
            r,
            SmtBitVecRem,
            ('(let ('
             '(var3 ((_ extract 2 0) A)) '
             '(var5 ((_ extract 5 3) A))) '
             '(let ('
             '(var6 (bvurem var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
                (b, range(3, 6)),
            ],
            input_width=6,
        )
        self.assertEqual(repr((q, r)), repr(
            SmtBitVec.make(b).__rdivmod__(SmtBitVec.make(a))))

    def test_bit_vec_eq(self):
        a = Signal()
        b = Signal()
        expr = SmtBitVec.make(a) == SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var3 ((_ extract 0 0) A)) '
             '(var5 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (= var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a == b, inputs=(a, b))

    def test_bit_vec_ne(self):
        a = Signal()
        b = Signal()
        expr = SmtBitVec.make(a) != SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var3 ((_ extract 0 0) A)) '
             '(var5 ((_ extract 1 1) A))) '
             '(let ('
             '(var6 (distinct var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
                (b, range(1, 2)),
            ],
            input_width=2,
        )
        self.assertSmtSame(expr, a != b, inputs=(a, b))

    def test_bit_vec_lt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) < SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecLt,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvult var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a < b, inputs=(a, b))

    def test_bit_vec_le(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) <= SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBoolNot,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var6 ((_ extract 3 2) A))) '
             '(let ('
             '(var7 (bvult var4 var6))) '
             '(let ('
             '(var8 (not var7))) '
             'var8)))'
             ),
            input_bit_ranges=[
                (b, range(0, 2)),
                (a, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a <= b, inputs=(a, b))

    def test_bit_vec_gt(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) > SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecLt,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvult var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (b, range(0, 2)),
                (a, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a > b, inputs=(a, b))

    def test_bit_vec_ge(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) >= SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBoolNot,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var6 ((_ extract 3 2) A))) '
             '(let ('
             '(var7 (bvult var4 var6))) '
             '(let ('
             '(var8 (not var7))) '
             'var8)))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, a >= b, inputs=(a, b))

    def test_bit_vec_abs(self):
        a = Signal(signed(3))
        expr = abs(SmtBitVec.make(a))
        self.assertSmtExpr(
            expr,
            SmtBitVecITE,
            ('(let ('
             '(var4 ((_ extract 2 0) A))) '
             '(let ('
             '(var5 ((_ extract 2 2) var4)) '
             '(var9 (bvneg var4))) '
             '(let ('
             '(var7 (distinct var5 #b0))) '
             '(let ('
             '(var11 (ite var7 var9 var4))) '
             'var11))))'
             ),
            input_bit_ranges=[
                (a, range(0, 3)),
            ],
            input_width=3,
        )
        self.assertSmtSame(expr,
                           abs(a)[:3], inputs=(a,))

    def test_bit_vec_and(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) & SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecAnd,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvand var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__rand__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a & b)[:2], inputs=(a, b))

    def test_bit_vec_or(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) | SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecOr,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvor var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__ror__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a | b)[:2], inputs=(a, b))

    def test_bit_vec_xor(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) ^ SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecXor,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvxor var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr),
                         repr(SmtBitVec.make(b).__rxor__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a ^ b)[:2], inputs=(a, b))

    def test_bit_vec_lshift(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) << SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecLShift,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvshl var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr), repr(
                         SmtBitVec.make(b).__rlshift__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a << b)[:2], inputs=(a, b))

    def tst_bit_vec_slice(self, s, ty: "type[SmtBitVec]" = SmtBitVecExtract,
                          *, expected_expr):
        a = Signal(3)
        expr = SmtBitVec.make(a)[s]
        self.assertSmtExpr(expr, ty, expected_expr,
                           input_bit_ranges=[(a, range(0, 3))], input_width=3)
        self.assertSmtSame(expr, a[s], inputs=(a,))

    def test_bit_vec_slice_0(self):
        self.tst_bit_vec_slice(0, expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_1_1(self):
        self.tst_bit_vec_slice(slice(0, 1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_1_2(self):
        self.tst_bit_vec_slice(slice(0, 1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_1_none(self):
        self.tst_bit_vec_slice(slice(0, 1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_2_1(self):
        self.tst_bit_vec_slice(slice(0, 2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_2_2(self):
        self.tst_bit_vec_slice(slice(0, 2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_2_none(self):
        self.tst_bit_vec_slice(slice(0, 2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n1_1(self):
        self.tst_bit_vec_slice(slice(0, -1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n1_2(self):
        self.tst_bit_vec_slice(slice(0, -1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n1_none(self):
        self.tst_bit_vec_slice(slice(0, -1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n2_1(self):
        self.tst_bit_vec_slice(slice(0, -2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n2_2(self):
        self.tst_bit_vec_slice(slice(0, -2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_n2_none(self):
        self.tst_bit_vec_slice(slice(0, -2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_none_1(self):
        self.tst_bit_vec_slice(slice(0, None, 1), expected_expr=(
            '(let ('
            '(var2 ((_ extract 2 0) A))) '
            '(let ('
            '(var3 ((_ extract 2 0) var2))) '
            'var3))'
        ))

    def test_bit_vec_slice_0_none_2(self):
        self.tst_bit_vec_slice(slice(0, None, 2), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3)) '
            '(var6 ((_ extract 2 2) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_0_none_n1(self):
        self.tst_bit_vec_slice(slice(0, None, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_none_n2(self):
        self.tst_bit_vec_slice(slice(0, None, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_0_none_none(self):
        self.tst_bit_vec_slice(slice(0, None, None), expected_expr=(
            '(let ('
            '(var2 ((_ extract 2 0) A))) '
            '(let ('
            '(var3 ((_ extract 2 0) var2))) '
            'var3))'
        ))

    def test_bit_vec_slice_1(self):
        self.tst_bit_vec_slice(1, expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_0_n1(self):
        self.tst_bit_vec_slice(slice(1, 0, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_0_n2(self):
        self.tst_bit_vec_slice(slice(1, 0, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_2_1(self):
        self.tst_bit_vec_slice(slice(1, 2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_2_2(self):
        self.tst_bit_vec_slice(slice(1, 2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_2_none(self):
        self.tst_bit_vec_slice(slice(1, 2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_n1_1(self):
        self.tst_bit_vec_slice(slice(1, -1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_n1_2(self):
        self.tst_bit_vec_slice(slice(1, -1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_n1_none(self):
        self.tst_bit_vec_slice(slice(1, -1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_none_1(self):
        self.tst_bit_vec_slice(slice(1, None, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_none_2(self):
        self.tst_bit_vec_slice(slice(1, None, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_none_n1(self):
        self.tst_bit_vec_slice(slice(1, None, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3)) '
            '(var6 ((_ extract 0 0) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_1_none_n2(self):
        self.tst_bit_vec_slice(slice(1, None, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_1_none_none(self):
        self.tst_bit_vec_slice(slice(1, None, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2(self):
        self.tst_bit_vec_slice(2, expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_0_n1(self):
        self.tst_bit_vec_slice(slice(2, 0, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_2_0_n2(self):
        self.tst_bit_vec_slice(slice(2, 0, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_1_n1(self):
        self.tst_bit_vec_slice(slice(2, 1, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_1_n2(self):
        self.tst_bit_vec_slice(slice(2, 1, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_n2_n1(self):
        self.tst_bit_vec_slice(slice(2, -2, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_n2_n2(self):
        self.tst_bit_vec_slice(slice(2, -2, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_none_1(self):
        self.tst_bit_vec_slice(slice(2, None, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_none_2(self):
        self.tst_bit_vec_slice(slice(2, None, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_2_none_n1(self):
        self.tst_bit_vec_slice(slice(2, None, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3)) '
            '(var8 ((_ extract 0 0) var3))) '
            '(let ('
            '(var10 (concat var8 var6 var4))) '
            'var10)))'
        ))

    def test_bit_vec_slice_2_none_n2(self):
        self.tst_bit_vec_slice(slice(2, None, -2), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 0 0) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_2_none_none(self):
        self.tst_bit_vec_slice(slice(2, None, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1(self):
        self.tst_bit_vec_slice(-1, expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_0_n1(self):
        self.tst_bit_vec_slice(slice(-1, 0, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_n1_0_n2(self):
        self.tst_bit_vec_slice(slice(-1, 0, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_1_n1(self):
        self.tst_bit_vec_slice(slice(-1, 1, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_1_n2(self):
        self.tst_bit_vec_slice(slice(-1, 1, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_n2_n1(self):
        self.tst_bit_vec_slice(slice(-1, -2, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_n2_n2(self):
        self.tst_bit_vec_slice(slice(-1, -2, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_none_1(self):
        self.tst_bit_vec_slice(slice(-1, None, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_none_2(self):
        self.tst_bit_vec_slice(slice(-1, None, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n1_none_n1(self):
        self.tst_bit_vec_slice(slice(-1, None, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3)) '
            '(var8 ((_ extract 0 0) var3))) '
            '(let ('
            '(var10 (concat var8 var6 var4))) '
            'var10)))'
        ))

    def test_bit_vec_slice_n1_none_n2(self):
        self.tst_bit_vec_slice(slice(-1, None, -2), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 0 0) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_n1_none_none(self):
        self.tst_bit_vec_slice(slice(-1, None, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2(self):
        self.tst_bit_vec_slice(-2, expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_0_n1(self):
        self.tst_bit_vec_slice(slice(-2, 0, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_0_n2(self):
        self.tst_bit_vec_slice(slice(-2, 0, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_2_1(self):
        self.tst_bit_vec_slice(slice(-2, 2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_2_2(self):
        self.tst_bit_vec_slice(slice(-2, 2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_2_none(self):
        self.tst_bit_vec_slice(slice(-2, 2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_n1_1(self):
        self.tst_bit_vec_slice(slice(-2, -1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_n1_2(self):
        self.tst_bit_vec_slice(slice(-2, -1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_n1_none(self):
        self.tst_bit_vec_slice(slice(-2, -1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_none_1(self):
        self.tst_bit_vec_slice(slice(-2, None, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_none_2(self):
        self.tst_bit_vec_slice(slice(-2, None, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_none_n1(self):
        self.tst_bit_vec_slice(slice(-2, None, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3)) '
            '(var6 ((_ extract 0 0) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_n2_none_n2(self):
        self.tst_bit_vec_slice(slice(-2, None, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_n2_none_none(self):
        self.tst_bit_vec_slice(slice(-2, None, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 1) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_0_n1(self):
        self.tst_bit_vec_slice(slice(None, 0, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_none_0_n2(self):
        self.tst_bit_vec_slice(slice(None, 0, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_1_1(self):
        self.tst_bit_vec_slice(slice(None, 1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_1_2(self):
        self.tst_bit_vec_slice(slice(None, 1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_1_n1(self):
        self.tst_bit_vec_slice(slice(None, 1, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_1_n2(self):
        self.tst_bit_vec_slice(slice(None, 1, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_1_none(self):
        self.tst_bit_vec_slice(slice(None, 1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_2_1(self):
        self.tst_bit_vec_slice(slice(None, 2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_2_2(self):
        self.tst_bit_vec_slice(slice(None, 2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_2_none(self):
        self.tst_bit_vec_slice(slice(None, 2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n1_1(self):
        self.tst_bit_vec_slice(slice(None, -1, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n1_2(self):
        self.tst_bit_vec_slice(slice(None, -1, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n1_none(self):
        self.tst_bit_vec_slice(slice(None, -1, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 1 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n2_1(self):
        self.tst_bit_vec_slice(slice(None, -2, 1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n2_2(self):
        self.tst_bit_vec_slice(slice(None, -2, 2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n2_n1(self):
        self.tst_bit_vec_slice(slice(None, -2, -1), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n2_n2(self):
        self.tst_bit_vec_slice(slice(None, -2, -2), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_n2_none(self):
        self.tst_bit_vec_slice(slice(None, -2, None), expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3))) '
            'var4))'
        ))

    def test_bit_vec_slice_none_none_1(self):
        self.tst_bit_vec_slice(slice(None, None, 1), expected_expr=(
            '(let ('
            '(var2 ((_ extract 2 0) A))) '
            '(let ('
            '(var3 ((_ extract 2 0) var2))) '
            'var3))'
        ))

    def test_bit_vec_slice_none_none_2(self):
        self.tst_bit_vec_slice(slice(None, None, 2), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 0 0) var3)) '
            '(var6 ((_ extract 2 2) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_none_none_n1(self):
        self.tst_bit_vec_slice(slice(None, None, -1), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 1 1) var3)) '
            '(var8 ((_ extract 0 0) var3))) '
            '(let ('
            '(var10 (concat var8 var6 var4))) '
            'var10)))'
        ))

    def test_bit_vec_slice_none_none_n2(self):
        self.tst_bit_vec_slice(slice(None, None, -2), ty=SmtBitVecConcat,
                               expected_expr=(
            '(let ('
            '(var3 ((_ extract 2 0) A))) '
            '(let ('
            '(var4 ((_ extract 2 2) var3)) '
            '(var6 ((_ extract 0 0) var3))) '
            '(let ('
            '(var8 (concat var6 var4))) '
            'var8)))'
        ))

    def test_bit_vec_slice_none_none_none(self):
        self.tst_bit_vec_slice(slice(None, None, None), expected_expr=(
            '(let ('
            '(var2 ((_ extract 2 0) A))) '
            '(let ('
            '(var3 ((_ extract 2 0) var2))) '
            'var3))'
        ))

    def test_bit_vec_rshift(self):
        a = Signal(2)
        b = Signal(2)
        expr = SmtBitVec.make(a) >> SmtBitVec.make(b)
        self.assertSmtExpr(
            expr,
            SmtBitVecRShift,
            ('(let ('
             '(var3 ((_ extract 1 0) A)) '
             '(var5 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (bvlshr var3 var5))) '
             'var6))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertEqual(repr(expr), repr(
                         SmtBitVec.make(b).__rrshift__(SmtBitVec.make(a))))
        self.assertSmtSame(expr,
                           (a >> b)[:2], inputs=(a, b))


class TestRoundingMode(SmtTestCase):
    def test_make(self):
        for i in RoundingModeEnum:
            with self.subTest(i=str(i)):
                expr = SmtRoundingMode.make(i)
                self.assertIs(expr, getattr(smtlib2, i.name))
                self.assertSmtExpr(expr, SmtRoundingModeConst, i.name)

    def test_rounding_mode_ite(self):
        expr = SmtBool.make(False).ite(ROUND_TOWARD_POSITIVE,
                                       ROUND_NEAREST_TIES_TO_EVEN)
        self.assertSmtExpr(expr, SmtRoundingModeITE,
                           ('(let ('
                            '(var4 (ite false RTP RNE))) var4)'
                            ))

    FOUR_ROUNDING_MODES = (ROUND_NEAREST_TIES_TO_EVEN, ROUND_TOWARD_NEGATIVE,
                           ROUND_TOWARD_POSITIVE, ROUND_TOWARD_ZERO)

    @staticmethod
    def lookup(array, index, *, width=None):
        index = SmtBitVec.make(index, width=width)
        array = list(array)
        if len(array) > 2 ** index.width:
            array[2 ** index.width:] = []
        retval = array.pop()
        for i, value in enumerate(array):
            hit = SmtBitVecConst(i, width=index.width) == index
            retval = hit.ite(value, retval)
        return retval

    def test_rounding_mode_same(self):
        a = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        b = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        c = Signal(range(len(self.FOUR_ROUNDING_MODES)))

        expr = (self.lookup(self.FOUR_ROUNDING_MODES, a)
                ).same(self.lookup(self.FOUR_ROUNDING_MODES, b),
                       self.lookup(self.FOUR_ROUNDING_MODES, c))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var19 ((_ extract 3 2) A)) '
             '(var27 ((_ extract 5 4) A))) '
             '(let ('
             '(var5 (= #b10 var4)) '
             '(var8 (= #b01 var4)) '
             '(var11 (= #b00 var4)) '
             '(var20 (= #b10 var19)) '
             '(var21 (= #b01 var19)) '
             '(var22 (= #b00 var19)) '
             '(var28 (= #b10 var27)) '
             '(var29 (= #b01 var27)) '
             '(var30 (= #b00 var27))) '
             '(let ('
             '(var15 (ite var11 RNE RTZ)) '
             '(var23 (ite var22 RNE RTZ)) '
             '(var31 (ite var30 RNE RTZ))) '
             '(let ('
             '(var16 (ite var8 RTN var15)) '
             '(var24 (ite var21 RTN var23)) '
             '(var32 (ite var29 RTN var31))) '
             '(let ('
             '(var17 (ite var5 RTP var16)) '
             '(var25 (ite var20 RTP var24)) '
             '(var33 (ite var28 RTP var32))) '
             '(let ('
             '(var34 (= var17 var25 var33))) '
             'var34))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c))

    def test_rounding_mode_distinct(self):
        a = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        b = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        c = Signal(range(len(self.FOUR_ROUNDING_MODES)))

        expr = (self.lookup(self.FOUR_ROUNDING_MODES, a)
                ).distinct(self.lookup(self.FOUR_ROUNDING_MODES, b),
                           self.lookup(self.FOUR_ROUNDING_MODES, c))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var5 ((_ extract 1 0) A)) '
             '(var20 ((_ extract 3 2) A)) '
             '(var28 ((_ extract 5 4) A))) '
             '(let ('
             '(var6 (= #b10 var5)) '
             '(var9 (= #b01 var5)) '
             '(var12 (= #b00 var5)) '
             '(var21 (= #b10 var20)) '
             '(var22 (= #b01 var20)) '
             '(var23 (= #b00 var20)) '
             '(var29 (= #b10 var28)) '
             '(var30 (= #b01 var28)) '
             '(var31 (= #b00 var28))) '
             '(let ('
             '(var16 (ite var12 RNE RTZ)) '
             '(var24 (ite var23 RNE RTZ)) '
             '(var32 (ite var31 RNE RTZ))) '
             '(let ('
             '(var17 (ite var9 RTN var16)) '
             '(var25 (ite var22 RTN var24)) '
             '(var33 (ite var30 RTN var32))) '
             '(let ('
             '(var18 (ite var6 RTP var17)) '
             '(var26 (ite var21 RTP var25)) '
             '(var34 (ite var29 RTP var33))) '
             '(let ('
             '(var35 (distinct var18 var26 var34))) '
             'var35))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
                (c, range(4, 6)),
            ],
            input_width=6,
        )
        self.assertSmtSame(expr, (a != b) & (a != c) & (b != c),
                           inputs=(a, b, c))

    def test_rounding_mode_eq(self):
        a = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        b = Signal(range(len(self.FOUR_ROUNDING_MODES)))

        expr = self.lookup(self.FOUR_ROUNDING_MODES, a) \
            == self.lookup(self.FOUR_ROUNDING_MODES, b)
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var4 ((_ extract 1 0) A)) '
             '(var19 ((_ extract 3 2) A))) '
             '(let ('
             '(var5 (= #b10 var4)) '
             '(var8 (= #b01 var4)) '
             '(var11 (= #b00 var4)) '
             '(var20 (= #b10 var19)) '
             '(var21 (= #b01 var19)) '
             '(var22 (= #b00 var19))) '
             '(let ('
             '(var15 (ite var11 RNE RTZ)) '
             '(var23 (ite var22 RNE RTZ))) '
             '(let ('
             '(var16 (ite var8 RTN var15)) '
             '(var24 (ite var21 RTN var23))) '
             '(let ('
             '(var17 (ite var5 RTP var16)) '
             '(var25 (ite var20 RTP var24))) '
             '(let ('
             '(var26 (= var17 var25))) '
             'var26))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, (a == b), inputs=(a, b))

    def test_rounding_mode_ne(self):
        a = Signal(range(len(self.FOUR_ROUNDING_MODES)))
        b = Signal(range(len(self.FOUR_ROUNDING_MODES)))

        expr = self.lookup(self.FOUR_ROUNDING_MODES, a) \
            != self.lookup(self.FOUR_ROUNDING_MODES, b)
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var5 ((_ extract 1 0) A)) '
             '(var20 ((_ extract 3 2) A))) '
             '(let ('
             '(var6 (= #b10 var5)) '
             '(var9 (= #b01 var5)) '
             '(var12 (= #b00 var5)) '
             '(var21 (= #b10 var20)) '
             '(var22 (= #b01 var20)) '
             '(var23 (= #b00 var20))) '
             '(let ('
             '(var16 (ite var12 RNE RTZ)) '
             '(var24 (ite var23 RNE RTZ))) '
             '(let ('
             '(var17 (ite var9 RTN var16)) '
             '(var25 (ite var22 RTN var24))) '
             '(let ('
             '(var18 (ite var6 RTP var17)) '
             '(var26 (ite var21 RTP var25))) '
             '(let ('
             '(var27 (distinct var18 var26))) '
             'var27))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 2)),
                (b, range(2, 4)),
            ],
            input_width=4,
        )
        self.assertSmtSame(expr, (a != b), inputs=(a, b))


class TestFloatingPoint(SmtTestCase):
    def test_floating_point_init(self):
        sort = SmtSortFloat16()
        expr = SmtFloatingPoint.zero(sort=sort)
        expr2 = SmtFloatingPoint.zero(eb=sort.eb, sb=sort.sb)
        self.assertEqual(repr(expr), repr(expr2))

    def test_floating_point_ite(self):
        expr = SmtBool.make(False).ite(
            SmtFloatingPoint.infinity(sort=SmtSortFloat32()),
            SmtFloatingPoint.zero(sort=SmtSortFloat32()))
        self.assertSmtExpr(expr, SmtFloatingPointITE,
                           ('(let ('
                            '(var4 (ite false (_ +oo 8 24) (_ +zero 8 24)))) '
                            'var4)'
                            ))

    @staticmethod
    def nans_are_default(v, sort):
        """ returns 1 if v is the default NaN or not a NaN.
            this is useful for filtering out all other NaNs, leaving only a
            single NaN.
        """
        assert isinstance(sort, SmtSortFloatingPoint)
        assert isinstance(v, Value)
        assert v.shape() == unsigned(sort.sb + sort.eb)
        pos_inf = ((1 << sort.eb) - 1) << (sort.sb - 1)
        exponent_mantissa_mask = (1 << (sort.eb + sort.sb - 1)) - 1
        quiet_bit = 1 << (sort.sb - 2)
        default_nan = pos_inf | quiet_bit
        return (v & exponent_mantissa_mask <= pos_inf) | (v == default_nan)

    def test_floating_point_same(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        c = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort) \
            .same(SmtFloatingPoint.from_bits(b, sort=sort),
                  SmtFloatingPoint.from_bits(c, sort=sort))
        self.assertSmtExpr(
            expr,
            SmtSame,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A)) '
             '(var10 ((_ extract 47 32) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7)) '
             '(var11 ((_ to_fp 5 11) var10))) '
             '(let ('
             '(var12 (= var5 var8 var11))) '
             'var12)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
                (c, range(32, 48)),
            ],
            input_width=48,
        )
        self.assertSmtSame(expr, (a == b) & (b == c), inputs=(a, b, c),
                           assumptions=(self.nans_are_default(a, sort),
                                        self.nans_are_default(b, sort),
                                        self.nans_are_default(c, sort)))

    def test_floating_point_distinct(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        c = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort) \
            .distinct(SmtFloatingPoint.from_bits(b, sort=sort),
                      SmtFloatingPoint.from_bits(c, sort=sort))
        self.assertSmtExpr(
            expr,
            SmtDistinct,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A)) '
             '(var10 ((_ extract 47 32) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7)) '
             '(var11 ((_ to_fp 5 11) var10))) '
             '(let ('
             '(var12 (distinct var5 var8 var11))) '
             'var12)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
                (c, range(32, 48)),
            ],
            input_width=48,
        )
        self.assertSmtSame(expr, (a != b) & (a != c) & (b != c),
                           inputs=(a, b, c),
                           assumptions=(self.nans_are_default(a, sort),
                                        self.nans_are_default(b, sort),
                                        self.nans_are_default(c, sort)))

    def test_floating_point_nan(self):
        sort = SmtSortFloat16()
        expr = SmtFloatingPoint.nan(sort=sort)
        self.assertSmtExpr(expr, SmtFloatingPointNaN, '(_ NaN 5 11)')

    def test_floating_point_zero(self):
        sort = SmtSortFloat16()
        a = Signal()
        b = Signal(16)
        expr = SmtFloatingPoint.zero(sign=SmtBitVec.make(a), sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointITE,
            ('(let ('
             '(var4 ((_ extract 0 0) A))) '
             '(let ('
             '(var5 (distinct #b0 var4))) '
             '(let ('
             '(var9 (ite var5 (_ -zero 5 11) (_ +zero 5 11)))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
            ],
            input_width=1,
        )
        expr = SmtFloatingPoint.zero(sign=SmtBool.make(a), sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointITE,
            ('(let ('
             '(var4 ((_ extract 0 0) A))) '
             '(let ('
             '(var5 (distinct #b0 var4))) '
             '(let ('
             '(var9 (ite var5 (_ -zero 5 11) (_ +zero 5 11)))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
            ],
            input_width=1,
        )
        expr2 = SmtFloatingPoint.from_bits(b, sort=sort)
        self.assertSmtSame(expr.same(expr2), b == Cat(Const(0, 15), a),
                           inputs=(a, b))

    def test_floating_point_neg_zero(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        expr = SmtFloatingPoint.neg_zero(sort=sort)
        self.assertSmtExpr(expr, SmtFloatingPointNegZero, '(_ -zero 5 11)')
        expr2 = SmtFloatingPoint.from_bits(a, sort=sort)
        self.assertSmtSame(expr.same(expr2), a == 0x8000, inputs=(a,))

    def test_floating_point_infinity(self):
        sort = SmtSortFloat16()
        a = Signal()
        b = Signal(16)
        expr = SmtFloatingPoint.infinity(sign=SmtBitVec.make(a), sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointITE,
            ('(let ('
             '(var4 ((_ extract 0 0) A))) '
             '(let ('
             '(var5 (distinct #b0 var4))) '
             '(let ('
             '(var9 (ite var5 (_ -oo 5 11) (_ +oo 5 11)))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
            ],
            input_width=1,
        )
        expr = SmtFloatingPoint.infinity(sign=SmtBool.make(a), sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointITE,
            ('(let ('
             '(var4 ((_ extract 0 0) A))) '
             '(let ('
             '(var5 (distinct #b0 var4))) '
             '(let ('
             '(var9 (ite var5 (_ -oo 5 11) (_ +oo 5 11)))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 1)),
            ],
            input_width=1,
        )
        expr2 = SmtFloatingPoint.from_bits(b, sort=sort)
        self.assertSmtSame(expr.same(expr2), b == Cat(Const(0x7C00, 15), a),
                           inputs=(a, b))

    def test_floating_point_neg_infinity(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        expr = SmtFloatingPoint.neg_infinity(sort=sort)
        self.assertSmtExpr(expr, SmtFloatingPointNegInfinity, '(_ -oo 5 11)')
        expr2 = SmtFloatingPoint.from_bits(a, sort=sort)
        self.assertSmtSame(expr.same(expr2), a == 0xFC00, inputs=(a,))

    def test_floating_point_from_parts(self):
        sort = SmtSortFloat16()
        v = Signal(16)
        sign = Signal(1)
        exponent = Signal(5)
        mantissa = Signal(10)
        expr = SmtFloatingPoint.from_parts(sign=SmtBitVec.make(sign),
                                           exponent=SmtBitVec.make(exponent),
                                           mantissa=SmtBitVec.make(mantissa))
        self.assertEqual(expr.sort(), sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromParts,
            ('(let ('
             '(var2 ((_ extract 0 0) A)) '
             '(var4 ((_ extract 5 1) A)) '
             '(var6 ((_ extract 15 6) A))) '
             '(let ('
             '(var8 (fp var2 var4 var6))) '
             'var8))'
             ),
            input_bit_ranges=[
                (sign, range(0, 1)),
                (exponent, range(1, 6)),
                (mantissa, range(6, 16)),
            ],
            input_width=16,
        )
        expr2 = SmtFloatingPoint.from_bits(v, sort=sort)
        self.assertSmtSame(expr.same(expr2),
                           v == Cat(mantissa, exponent, sign),
                           inputs=(sign, exponent, mantissa, v),
                           assumptions=(self.nans_are_default(v, sort),
                                        self.nans_are_default(
                               Cat(mantissa, exponent, sign), sort)))

    def test_floating_point_from_parts_bool_sign(self):
        sort = SmtSortFloat16()
        v = Signal(16)
        sign = Signal(1)
        exponent = Signal(5)
        mantissa = Signal(10)
        expr = SmtFloatingPoint.from_parts(sign=SmtBool.make(sign),
                                           exponent=SmtBitVec.make(exponent),
                                           mantissa=SmtBitVec.make(mantissa))
        self.assertEqual(expr.sort(), sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromParts,
            ('(let ('
             '(var4 ((_ extract 0 0) A)) '
             '(var10 ((_ extract 5 1) A)) '
             '(var12 ((_ extract 15 6) A))) '
             '(let ('
             '(var5 (distinct #b0 var4))) '
             '(let ('
             '(var8 (ite var5 #b1 #b0))) '
             '(let ('
             '(var14 (fp var8 var10 var12))) '
             'var14))))'
             ),
            input_bit_ranges=[
                (sign, range(0, 1)),
                (exponent, range(1, 6)),
                (mantissa, range(6, 16)),
            ],
            input_width=16,
        )
        expr2 = SmtFloatingPoint.from_bits(v, sort=sort)
        self.assertSmtSame(expr.same(expr2),
                           v == Cat(mantissa, exponent, sign),
                           inputs=(sign, exponent, mantissa, v),
                           assumptions=(self.nans_are_default(v, sort),
                                        self.nans_are_default(
                               Cat(mantissa, exponent, sign), sort)))

    def test_floating_point_abs(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        expected = Signal(16)
        expr = abs(SmtFloatingPoint.from_bits(a, sort=sort))
        self.assertSmtExpr(
            expr,
            SmtFloatingPointAbs,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.abs var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(
            expr.same(SmtFloatingPoint.from_bits(expected, sort=sort)),
            expected == 0x7FFF & a,
            inputs=(a, expected),
            assumptions=(self.nans_are_default(a, sort),
                         self.nans_are_default(expected, sort)))

    def test_floating_point_neg_pos(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = -SmtFloatingPoint.from_bits(a, sort=sort)
        self.assertIs(expr, +expr)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointNeg,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.neg var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        is_nan = (a & 0x7FFF) > 0x7C00
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, Mux(is_nan, 0x7E00, 0x8000 ^ a)),),
            assumptions=(self.nans_are_default(a, sort),
                         self.nans_are_default(out, sort),
                         expr.same(out_fp)))

    def test_floating_point_add(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.add(b_fp, rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointAdd,
            ('(let ('
             '(var5 ((_ extract 15 0) A)) '
             '(var8 ((_ extract 31 16) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5)) '
             '(var9 ((_ to_fp 5 11) var8))) '
             '(let ('
             '(var10 (fp.add RNE var6 var9))) '
             'var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, out),
            assert_eqs=((out, 0x1645),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         expr.same(out_fp)))

    def test_floating_point_sub(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.sub(b_fp, rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointSub,
            ('(let ('
             '(var5 ((_ extract 15 0) A)) '
             '(var8 ((_ extract 31 16) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5)) '
             '(var9 ((_ to_fp 5 11) var8))) '
             '(let ('
             '(var10 (fp.sub RNE var6 var9))) '
             'var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, out),
            assert_eqs=((out, 0x8110),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         expr.same(out_fp)))

    def test_floating_point_mul(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.mul(b_fp, rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointMul,
            ('(let ('
             '(var5 ((_ extract 15 0) A)) '
             '(var8 ((_ extract 31 16) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5)) '
             '(var9 ((_ to_fp 5 11) var8))) '
             '(let ('
             '(var10 (fp.mul RNE var6 var9))) '
             'var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, out),
            assert_eqs=((out, 0x000A),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         expr.same(out_fp)))

    def test_floating_point_div(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.div(b_fp, rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointDiv,
            ('(let ('
             '(var5 ((_ extract 15 0) A)) '
             '(var8 ((_ extract 31 16) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5)) '
             '(var9 ((_ to_fp 5 11) var8))) '
             '(let ('
             '(var10 (fp.div RNE var6 var9))) '
             'var10)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, out),
            assert_eqs=((out, 0x3BD5),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         expr.same(out_fp)))

    def test_floating_point_fma(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        c = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        c_fp = SmtFloatingPoint.from_bits(c, sort=sort)
        out = Signal(16)
        expr = a_fp.fma(b_fp, c_fp, rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFma,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A)) '
             '(var10 ((_ extract 47 32) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7)) '
             '(var11 ((_ to_fp 5 11) var10))) '
             '(let ('
             '(var13 (fp.fma RNE var5 var8 var11))) '
             'var13)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
                (c, range(32, 48)),
            ],
            input_width=48,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, c, out),
            assert_eqs=((out, 0x001A),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         c == 0x0010,
                         expr.same(out_fp)))

    def test_floating_point_sqrt(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        out = Signal(16)
        expr = a_fp.sqrt(rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointSqrt,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.sqrt RNE var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x270B),),
            assumptions=(a == 0x1234,
                         expr.same(out_fp)))

    def test_floating_point_rem(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.rem(b_fp)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointRem,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.rem var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, b, out),
            assert_eqs=((out, 0x8110),),
            assumptions=(a == 0x1234,
                         b == 0x1256,
                         expr.same(out_fp)))

    def test_floating_point_round_to_integral(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        out = Signal(16)
        expr = a_fp.round_to_integral(rm=RNE)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointRoundToIntegral,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.roundToIntegral RNE var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x4A00),),
            assumptions=(a == 0x4A2B,
                         expr.same(out_fp)))

    def test_floating_point_min(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.min(b_fp)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointMin,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.min var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(b_is_nan, a,
                       Mux(a_is_nan, b,
                           Mux(a_ord < b_ord, a, b)))
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmtSame(out, expected, inputs=(a, b, out), assumptions=(
            self.nans_are_default(a, sort),
            self.nans_are_default(b, sort),
            self.nans_are_default(out, sort),
            # fp.min is defined to return an arbitrary zero when both inputs
            # are zeros, to avoid failing if it arbitrarily picks the wrong
            # zero, we eliminate cases where both inputs are zeros of
            # differing sign.
            (a != 0x8000) | (b != 0x0000),
            (a != 0x0000) | (b != 0x8000),
            expr.same(out_fp)))

    def test_floating_point_max(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        out = Signal(16)
        expr = a_fp.max(b_fp)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointMax,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.max var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(b_is_nan, a,
                       Mux(a_is_nan, b,
                           Mux(a_ord < b_ord, b, a)))
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmtSame(out, expected, inputs=(a, b, out), assumptions=(
            self.nans_are_default(a, sort),
            self.nans_are_default(b, sort),
            self.nans_are_default(out, sort),
            # fp.max is defined to return an arbitrary zero when both inputs
            # are zeros, to avoid failing if it arbitrarily picks the wrong
            # zero, we eliminate cases where both inputs are zeros of
            # differing sign.
            (a != 0x8000) | (b != 0x0000),
            (a != 0x0000) | (b != 0x8000),
            expr.same(out_fp)))

    def test_floating_point_eq(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp == b_fp
        self.assertSmtExpr(
            expr,
            SmtFloatingPointEq,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.eq var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, False,
                       Mux(a_is_zero & b_is_zero, True,
                           a_ord == b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_ne(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp != b_fp
        self.assertSmtExpr(
            expr,
            SmtBoolNot,
            ('(let ('
             '(var5 ((_ extract 15 0) A)) '
             '(var8 ((_ extract 31 16) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5)) '
             '(var9 ((_ to_fp 5 11) var8))) '
             '(let ('
             '(var10 (fp.eq var6 var9))) '
             '(let ('
             '(var11 (not var10))) '
             'var11))))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, True,
                       Mux(a_is_zero & b_is_zero, False,
                           a_ord != b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_le(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp <= b_fp
        self.assertSmtExpr(
            expr,
            SmtFloatingPointLE,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.leq var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, False,
                       Mux(a_is_zero & b_is_zero, True,
                           a_ord <= b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_ge(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp >= b_fp
        self.assertSmtExpr(
            expr,
            SmtFloatingPointGE,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.geq var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, False,
                       Mux(a_is_zero & b_is_zero, True,
                           a_ord >= b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_lt(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp < b_fp
        self.assertSmtExpr(
            expr,
            SmtFloatingPointLt,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.lt var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, False,
                       Mux(a_is_zero & b_is_zero, False,
                           a_ord < b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_gt(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        b = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        b_fp = SmtFloatingPoint.from_bits(b, sort=sort)
        expr = a_fp > b_fp
        self.assertSmtExpr(
            expr,
            SmtFloatingPointGt,
            ('(let ('
             '(var4 ((_ extract 15 0) A)) '
             '(var7 ((_ extract 31 16) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4)) '
             '(var8 ((_ to_fp 5 11) var7))) '
             '(let ('
             '(var9 (fp.gt var5 var8))) '
             'var9)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
                (b, range(16, 32)),
            ],
            input_width=32,
        )
        a_is_nan = (a & 0x7FFF) > 0x7C00
        b_is_nan = (b & 0x7FFF) > 0x7C00
        a_is_zero = (a & 0x7FFF) == 0
        b_is_zero = (b & 0x7FFF) == 0
        a_ord = Mux(a[-1], ~a, a ^ 0x8000)
        b_ord = Mux(b[-1], ~b, b ^ 0x8000)
        expected = Mux(a_is_nan | b_is_nan, False,
                       Mux(a_is_zero & b_is_zero, False,
                           a_ord > b_ord))
        self.assertSmtSame(expr, expected, inputs=(a, b))

    def test_floating_point_is_normal(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_normal()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsNormal,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isNormal var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = (a & 0x7C00 != 0) & (a & 0x7C00 != 0x7C00)
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_subnormal(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_subnormal()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsSubnormal,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isSubnormal var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = (a & 0x7C00 == 0) & (a & 0x7FFF != 0)
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_zero(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_zero()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsZero,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isZero var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = a & 0x7FFF == 0
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_infinite(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_infinite()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsInfinite,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isInfinite var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = a & 0x7FFF == 0x7C00
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_nan(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_nan()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsNaN,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isNaN var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = a & 0x7FFF > 0x7C00
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_negative(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_negative()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsNegative,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isNegative var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = (a & 0x7FFF <= 0x7C00) & (a & 0x8000 != 0)
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_is_positive(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.is_positive()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointIsPositive,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.isPositive var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        expected = (a & 0x7FFF <= 0x7C00) & (a & 0x8000 == 0)
        self.assertSmtSame(expr, expected, inputs=(a,))

    def test_floating_point_from_signed_bv(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_signed_bv(SmtBitVec.make(a),
                                               rm=RNE, sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromSignedBV,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) RNE var4))) '
             'var5))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0xEC8D),),
            assumptions=(a == 0xFFFF & -0x1234,
                         expr.same(out_fp)))

    def test_floating_point_from_unsigned_bv(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_unsigned_bv(SmtBitVec.make(a),
                                                 rm=RNE, sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromUnsignedBV,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp_unsigned 5 11) RNE var4))) '
             'var5))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x7B6E),),
            assumptions=(a == 0xFFFF & -0x1234,
                         expr.same(out_fp)))

    def test_floating_point_from_int_real(self):
        sort = SmtSortFloat32()
        a = Signal(32)
        out = Signal(32)
        expr = SmtFloatingPoint.from_real(SmtInt.make(a).to_real(),
                                          rm=RNE, sort=sort)
        expr2 = SmtFloatingPoint.from_int(SmtInt.make(a), rm=RNE, sort=sort)
        self.assertEqual(repr(expr), repr(expr2))
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromReal,
            ('(let ('
             '(var5 ((_ extract 31 0) A))) '
             '(let ('
             '(var11 ((_ extract 0 0) var5)) '
             '(var17 ((_ extract 1 1) var5)) '
             '(var22 ((_ extract 2 2) var5)) '
             '(var27 ((_ extract 3 3) var5)) '
             '(var32 ((_ extract 4 4) var5)) '
             '(var37 ((_ extract 5 5) var5)) '
             '(var42 ((_ extract 6 6) var5)) '
             '(var47 ((_ extract 7 7) var5)) '
             '(var52 ((_ extract 8 8) var5)) '
             '(var57 ((_ extract 9 9) var5)) '
             '(var62 ((_ extract 10 10) var5)) '
             '(var67 ((_ extract 11 11) var5)) '
             '(var72 ((_ extract 12 12) var5)) '
             '(var77 ((_ extract 13 13) var5)) '
             '(var82 ((_ extract 14 14) var5)) '
             '(var87 ((_ extract 15 15) var5)) '
             '(var92 ((_ extract 16 16) var5)) '
             '(var97 ((_ extract 17 17) var5)) '
             '(var102 ((_ extract 18 18) var5)) '
             '(var107 ((_ extract 19 19) var5)) '
             '(var112 ((_ extract 20 20) var5)) '
             '(var117 ((_ extract 21 21) var5)) '
             '(var122 ((_ extract 22 22) var5)) '
             '(var127 ((_ extract 23 23) var5)) '
             '(var132 ((_ extract 24 24) var5)) '
             '(var137 ((_ extract 25 25) var5)) '
             '(var142 ((_ extract 26 26) var5)) '
             '(var147 ((_ extract 27 27) var5)) '
             '(var152 ((_ extract 28 28) var5)) '
             '(var157 ((_ extract 29 29) var5)) '
             '(var162 ((_ extract 30 30) var5)) '
             '(var167 ((_ extract 31 31) var5))) '
             '(let ('
             '(var12 (= #b1 var11)) '
             '(var18 (= #b1 var17)) '
             '(var23 (= #b1 var22)) '
             '(var28 (= #b1 var27)) '
             '(var33 (= #b1 var32)) '
             '(var38 (= #b1 var37)) '
             '(var43 (= #b1 var42)) '
             '(var48 (= #b1 var47)) '
             '(var53 (= #b1 var52)) '
             '(var58 (= #b1 var57)) '
             '(var63 (= #b1 var62)) '
             '(var68 (= #b1 var67)) '
             '(var73 (= #b1 var72)) '
             '(var78 (= #b1 var77)) '
             '(var83 (= #b1 var82)) '
             '(var88 (= #b1 var87)) '
             '(var93 (= #b1 var92)) '
             '(var98 (= #b1 var97)) '
             '(var103 (= #b1 var102)) '
             '(var108 (= #b1 var107)) '
             '(var113 (= #b1 var112)) '
             '(var118 (= #b1 var117)) '
             '(var123 (= #b1 var122)) '
             '(var128 (= #b1 var127)) '
             '(var133 (= #b1 var132)) '
             '(var138 (= #b1 var137)) '
             '(var143 (= #b1 var142)) '
             '(var148 (= #b1 var147)) '
             '(var153 (= #b1 var152)) '
             '(var158 (= #b1 var157)) '
             '(var163 (= #b1 var162)) '
             '(var168 (= #b1 var167))) '
             '(let ('
             '(var15 (ite var12 1 0)) '
             '(var20 (ite var18 2 0)) '
             '(var25 (ite var23 4 0)) '
             '(var30 (ite var28 8 0)) '
             '(var35 (ite var33 16 0)) '
             '(var40 (ite var38 32 0)) '
             '(var45 (ite var43 64 0)) '
             '(var50 (ite var48 128 0)) '
             '(var55 (ite var53 256 0)) '
             '(var60 (ite var58 512 0)) '
             '(var65 (ite var63 1024 0)) '
             '(var70 (ite var68 2048 0)) '
             '(var75 (ite var73 4096 0)) '
             '(var80 (ite var78 8192 0)) '
             '(var85 (ite var83 16384 0)) '
             '(var90 (ite var88 32768 0)) '
             '(var95 (ite var93 65536 0)) '
             '(var100 (ite var98 131072 0)) '
             '(var105 (ite var103 262144 0)) '
             '(var110 (ite var108 524288 0)) '
             '(var115 (ite var113 1048576 0)) '
             '(var120 (ite var118 2097152 0)) '
             '(var125 (ite var123 4194304 0)) '
             '(var130 (ite var128 8388608 0)) '
             '(var135 (ite var133 16777216 0)) '
             '(var140 (ite var138 33554432 0)) '
             '(var145 (ite var143 67108864 0)) '
             '(var150 (ite var148 134217728 0)) '
             '(var155 (ite var153 268435456 0)) '
             '(var160 (ite var158 536870912 0)) '
             '(var165 (ite var163 1073741824 0)) '
             '(var170 (ite var168 2147483648 0))) '
             '(let ('
             '(var171 (+ var15 var20 var25 var30 var35 var40 var45 var50 '
             'var55 var60 var65 var70 var75 var80 var85 var90 var95 var100 '
             'var105 var110 var115 var120 var125 var130 var135 var140 var145 '
             'var150 var155 var160 var165 var170))) '
             '(let ('
             '(var172 (to_real var171))) '
             '(let ('
             '(var173 ((_ to_fp 8 24) RNE var172))) '
             'var173)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x4F6DCBAA),),
            assumptions=(a == 0xFFFFFFFF & -0x12345678,
                         expr.same(out_fp)),
            solver="cvc5")

    def test_floating_point_from_fp(self):
        sort = SmtSortFloat16()
        a = Signal(32)
        a_fp = SmtFloatingPoint.from_bits(a, sort=SmtSortFloat32())
        out = Signal(16)
        expr = SmtFloatingPoint.from_fp(a_fp, rm=RNE, sort=sort)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointFromFP,
            ('(let ('
             '(var5 ((_ extract 31 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 8 24) var5))) '
             '(let ('
             '(var7 ((_ to_fp 5 11) RNE var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 32)),
            ],
            input_width=32,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x57B7),),
            assumptions=(a == 0x42F6E9DF,  # 123.45678
                         expr.same(out_fp)))

    def test_floating_point_to_real(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).to_real()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointToReal,
            ('(let ('
             '(var4 ((_ extract 15 0) A))) '
             '(let ('
             '(var5 ((_ to_fp 5 11) var4))) '
             '(let ('
             '(var6 (fp.to_real var5))) '
             'var6)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmt(
            inputs=(a,),
            assertions=(expr.same(SmtReal.make(Fraction("1.9990234375"))),),
            assumptions=(a == 0x3FFF,),  # 1.9990234375 exactly
        )

    def test_floating_point_ceil(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).ceil()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointRoundToIntegral,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.roundToIntegral RTP var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x4A80),),
            assumptions=(a == 0x4A2B,
                         expr.same(out_fp)))

    def test_floating_point_floor(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).floor()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointRoundToIntegral,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.roundToIntegral RTN var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x4A00),),
            assumptions=(a == 0x4A2B,
                         expr.same(out_fp)))

    def test_floating_point_trunc(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).trunc()
        self.assertSmtExpr(
            expr,
            SmtFloatingPointRoundToIntegral,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.roundToIntegral RTZ var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        out_fp = SmtFloatingPoint.from_bits(out, sort=sort)
        self.assertSmt(
            inputs=(a, out),
            assert_eqs=((out, 0x4A00),),
            assumptions=(a == 0x4A2B,
                         expr.same(out_fp)))

    def test_floating_point_ceil_int(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).ceil_int()
        self.assertSmtExpr(
            expr,
            SmtIntNeg,
            ('(let ('
             '(var6 ((_ extract 15 0) A))) '
             '(let ('
             '(var7 ((_ to_fp 5 11) var6))) '
             '(let ('
             '(var8 (fp.to_real var7))) '
             '(let ('
             '(var9 (- var8))) '
             '(let ('
             '(var10 (to_int var9))) '
             '(let ('
             '(var11 (- var10))) '
             'var11))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(out, 13,
                           inputs=(a,),
                           assumptions=(a == 0x4A2B,),
                           assume_eqs=((out, expr.to_bit_vec(width=16)),)
                           )

    def test_floating_point_floor_int(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).floor_int()
        self.assertSmtExpr(
            expr,
            SmtRealToInt,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.to_real var6))) '
             '(let ('
             '(var8 (to_int var7))) '
             'var8))))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(out, 12,
                           inputs=(a,),
                           assumptions=(a == 0x4A2B,),
                           assume_eqs=((out, expr.to_bit_vec(width=16)),)
                           )

    def test_floating_point_trunc_int(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        out = Signal(16)
        expr = SmtFloatingPoint.from_bits(a, sort=sort).trunc_int()
        self.assertSmtExpr(
            expr,
            SmtIntITE,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 (fp.to_real var6))) '
             '(let ('
             '(var9 (< var7 0.0)) '
             '(var12 (- var7)) '
             '(var15 (to_int var7))) '
             '(let ('
             '(var13 (to_int var12))) '
             '(let ('
             '(var14 (- var13))) '
             '(let ('
             '(var17 (ite var9 var14 var15))) '
             'var17)))))))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(out, 12,
                           inputs=(a,),
                           assumptions=(a == 0x4A2B,),
                           assume_eqs=((out, expr.to_bit_vec(width=16)),)
                           )

    def test_floating_point_to_unsigned_bv(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.to_unsigned_bv(rm=ROUND_TOWARD_ZERO, width=16)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointToUnsignedBV,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 ((_ fp.to_ubv 16) RTZ var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(expr, 12, inputs=(a,), assumptions=(a == 0x4A2B,))

    def test_floating_point_to_signed_bv(self):
        sort = SmtSortFloat16()
        a = Signal(16)
        a_fp = SmtFloatingPoint.from_bits(a, sort=sort)
        expr = a_fp.to_signed_bv(rm=ROUND_TOWARD_ZERO, width=16)
        self.assertSmtExpr(
            expr,
            SmtFloatingPointToSignedBV,
            ('(let ('
             '(var5 ((_ extract 15 0) A))) '
             '(let ('
             '(var6 ((_ to_fp 5 11) var5))) '
             '(let ('
             '(var7 ((_ fp.to_sbv 16) RTZ var6))) '
             'var7)))'
             ),
            input_bit_ranges=[
                (a, range(0, 16)),
            ],
            input_width=16,
        )
        self.assertSmtSame(expr, Const(-12, unsigned(16)), inputs=(a,),
                           assumptions=(a == 0xCA2B,))
