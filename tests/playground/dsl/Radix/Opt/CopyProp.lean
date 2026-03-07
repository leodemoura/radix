/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt
import Std.Data.HashMap

/-! # Copy Propagation

Replace `x := y; ... x ...` with `... y ...` when safe.
Uses a substitution map tracking which variables are copies of others.
-/

namespace Radix
open Std

abbrev CopyMap := HashMap String String

mutual
/-- Apply copy propagation to an expression using the given copy map. -/
def Expr.copyProp (m : CopyMap) : Expr → Expr
  | .lit v => .lit v
  | .var x => .var (m.get? x |>.getD x)
  | .binop op l r => .binop op (l.copyProp m) (r.copyProp m)
  | .unop op e => .unop op (e.copyProp m)
  | .call f args => .call f (Expr.copyPropList m args)
  | .arrGet arr idx => .arrGet (arr.copyProp m) (idx.copyProp m)
  | .arrLen arr => .arrLen (arr.copyProp m)
  | .strLen s => .strLen (s.copyProp m)
  | .strGet s idx => .strGet (s.copyProp m) (idx.copyProp m)

def Expr.copyPropList (m : CopyMap) : List Expr → List Expr
  | [] => []
  | e :: es => e.copyProp m :: Expr.copyPropList m es
end

mutual
/-- Apply copy propagation to a statement. Returns the transformed statement
and an updated copy map. -/
def Stmt.copyProp (m : CopyMap) : Stmt → Stmt × CopyMap
  | .skip => (.skip, m)
  | .assign x (.var y) =>
    let y' := m.get? y |>.getD y
    (.assign x (.var y'), m.insert x y' |>.erase y |> fun m' =>
      m'.filter fun _ v => v != x)
  | .assign x e =>
    let e' := Expr.copyProp m e
    let m' := m.erase x |>.filter fun _ v => v != x
    (.assign x e', m')
  | .seq s₁ s₂ =>
    let (s₁', m₁) := s₁.copyProp m
    let (s₂', m₂) := s₂.copyProp m₁
    (.seq s₁' s₂', m₂)
  | .ite c t f =>
    let c' := Expr.copyProp m c
    let (t', _) := t.copyProp m
    let (f', _) := f.copyProp m
    (.ite c' t' f', {})
  | .while c b =>
    let c' := Expr.copyProp {} c
    let (b', _) := b.copyProp {}
    (.while c' b', {})
  | .decl x ty e =>
    let e' := Expr.copyProp m e
    let m' := m.erase x |>.filter fun _ v => v != x
    (.decl x ty e', m')
  | .alloc x ty sz =>
    let sz' := Expr.copyProp m sz
    let m' := m.erase x |>.filter fun _ v => v != x
    (.alloc x ty sz', m')
  | .free e => (.free (Expr.copyProp m e), m)
  | .arrSet arr idx val =>
    (.arrSet (Expr.copyProp m arr) (Expr.copyProp m idx) (Expr.copyProp m val), m)
  | .ret e => (.ret (Expr.copyProp m e), m)
  | .block stmts =>
    let (stmts', m') := Stmt.copyPropList m stmts
    (.block stmts', m')
  | .callStmt f args =>
    (.callStmt f (Expr.copyPropList m args), {})

def Stmt.copyPropList (m : CopyMap) : List Stmt → List Stmt × CopyMap
  | [] => ([], m)
  | s :: ss =>
    let (s', m') := s.copyProp m
    let (ss', m'') := Stmt.copyPropList m' ss
    (s' :: ss', m'')
end

def Stmt.copyPropagation (s : Stmt) : Stmt :=
  (s.copyProp {}).1

-- Correctness theorem statement
theorem Stmt.copyProp_correct (h : BigStep σ s r) :
    BigStep σ s.copyPropagation r := by
  sorry

end Radix
