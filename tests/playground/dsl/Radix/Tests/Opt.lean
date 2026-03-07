/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax
import Radix.Opt.ConstFold
import Radix.Opt.DeadCode
import Radix.Opt.ConstProp

/-! # Optimization Tests

Verify that optimizations transform programs correctly.
-/

namespace Radix.Tests

-- Constant folding: 3 + 4 should become 7
def test_cf_expr : Expr :=
  Expr.binop .add (Expr.lit (Value.uint64 3)) (Expr.lit (Value.uint64 4))

#guard match test_cf_expr.constFold with
  | Expr.lit (Value.uint64 7) => true
  | _ => false

-- Constant folding: true && false should become false
def test_cf_and_bool : Expr :=
  Expr.binop .and (Expr.lit (Value.bool true)) (Expr.lit (Value.bool false))

#guard match test_cf_and_bool.constFold with
  | Expr.lit (Value.bool false) => true
  | _ => false

-- Constant folding in statements: dead branch elimination
def test_cf_stmt := `[RStmt|
  if (true) {
    x := 1;
  } else {
    x := 2;
  }
]

#guard match test_cf_stmt.constFold with
  | Stmt.assign "x" (Expr.lit (Value.uint64 1)) => true
  | _ => false

-- Dead code elimination: skip sequences
def test_dce_skip :=
  Stmt.seq Stmt.skip (Stmt.assign "x" (Expr.lit (Value.uint64 1)))

#guard match test_dce_skip.deadCodeElim with
  | Stmt.assign "x" _ => true
  | _ => false

-- Dead code: false while loop
def test_dce_false_while :=
  Stmt.while (Expr.lit (Value.bool false)) (Stmt.assign "x" (Expr.lit (Value.uint64 1)))

#guard test_dce_false_while.deadCodeElim matches Stmt.skip

-- Constant propagation: x := 5; y := x + 1 → y := 6
def test_constprop := `[RStmt|
  x := 5;
  y := x + 1;
]

#guard match test_constprop.constPropagation with
  | Stmt.seq (Stmt.assign "x" (Expr.lit (Value.uint64 5)))
             (Stmt.assign "y" (Expr.lit (Value.uint64 6))) => true
  | _ => false

-- Constant folding: 5 + 3 → 8
def test_cf_add_const : Expr :=
  Expr.binop .add (Expr.lit (Value.uint64 5)) (Expr.lit (Value.uint64 3))

#guard match test_cf_add_const.constFold with
  | Expr.lit (Value.uint64 8) => true
  | _ => false

-- Constant folding: 6 * 7 → 42
def test_cf_mul_const : Expr :=
  Expr.binop .mul (Expr.lit (Value.uint64 6)) (Expr.lit (Value.uint64 7))

#guard match test_cf_mul_const.constFold with
  | Expr.lit (Value.uint64 42) => true
  | _ => false

-- Constant folding: 10 - 3 → 7
def test_cf_sub_const : Expr :=
  Expr.binop .sub (Expr.lit (Value.uint64 10)) (Expr.lit (Value.uint64 3))

#guard match test_cf_sub_const.constFold with
  | Expr.lit (Value.uint64 7) => true
  | _ => false

-- String constant folding
def test_cf_str : Expr :=
  Expr.binop .strAppend (Expr.lit (Value.str "hello")) (Expr.lit (Value.str " world"))

#guard match test_cf_str.constFold with
  | Expr.lit (Value.str "hello world") => true
  | _ => false

-- Optimization roundtrip: optimized program produces same result as original
private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

def test_opt_roundtrip := `[RStmt|
  x := 3 + 4;
  y := x * 1;
  z := y + 0;
]

#guard getResult test_opt_roundtrip "z" == getResult test_opt_roundtrip.constFold "z"
#guard getResult test_opt_roundtrip "z" == some (Value.uint64 7)

/-! ## Identity simplification tests -/

-- e + 0 → e when e has known uint64 type (literal)
#guard (Expr.binop .add (.lit (.uint64 5)) (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 5)

-- 0 + e → e when e has known uint64 type
#guard (Expr.binop .add (.lit (.uint64 0)) (.lit (.uint64 5))).constFold
    matches Expr.lit (Value.uint64 5)

-- e - 0 → e when e has known uint64 type
#guard (Expr.binop .sub (.lit (.uint64 7)) (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 7)

-- e * 1 → e when e has known uint64 type
#guard (Expr.binop .mul (.lit (.uint64 42)) (.lit (.uint64 1))).constFold
    matches Expr.lit (Value.uint64 42)

-- 1 * e → e when e has known uint64 type
#guard (Expr.binop .mul (.lit (.uint64 1)) (.lit (.uint64 42))).constFold
    matches Expr.lit (Value.uint64 42)

-- true && e → e when e has known bool type
#guard (Expr.binop .and (.lit (.bool true)) (.lit (.bool false))).constFold
    matches Expr.lit (Value.bool false)

-- e && true → e when e has known bool type
#guard (Expr.binop .and (.lit (.bool false)) (.lit (.bool true))).constFold
    matches Expr.lit (Value.bool false)

-- false || e → e when e has known bool type
#guard (Expr.binop .or (.lit (.bool false)) (.lit (.bool true))).constFold
    matches Expr.lit (Value.bool true)

-- e || false → e when e has known bool type
#guard (Expr.binop .or (.lit (.bool true)) (.lit (.bool false))).constFold
    matches Expr.lit (Value.bool true)

-- e ++ "" → e when e has known str type
#guard (Expr.binop .strAppend (.lit (.str "hello")) (.lit (.str ""))).constFold
    matches Expr.lit (Value.str "hello")

-- "" ++ e → e when e has known str type
#guard (Expr.binop .strAppend (.lit (.str "")) (.lit (.str "hello"))).constFold
    matches Expr.lit (Value.str "hello")

-- Identity NOT applied when type is unknown (variable)
#guard (Expr.binop .add (.var "x") (.lit (.uint64 0))).constFold
    matches Expr.binop .add (Expr.var "x") (Expr.lit (Value.uint64 0))

-- Identity applied to nested expressions with known type tags
-- (3 + 4) + 0 → 7  (first the inner 3+4 is folded to 7, then 7+0 is simplified)
#guard (Expr.binop .add (Expr.binop .add (.lit (.uint64 3)) (.lit (.uint64 4)))
    (.lit (.uint64 0))).constFold
    matches Expr.lit (Value.uint64 7)

-- e + 0 with e = nested binop that has inferable uint64 tag
-- (x is unknown, so inferTag returns none, so identity is NOT applied)
#guard (Expr.binop .add (Expr.binop .add (.var "x") (.lit (.uint64 1)))
    (.lit (.uint64 0))).constFold
    matches Expr.binop .add (Expr.binop .add (Expr.var "x") (Expr.lit (Value.uint64 1)))
                            (Expr.lit (Value.uint64 0))

end Radix.Tests
