/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt

/-! # Constant Folding

Fold constant expressions: `3 + 4 → 7`, `true && x → x`, etc.
Includes correctness proof showing the optimization preserves semantics.
-/

namespace Radix

def BinOp.simplify : BinOp → Expr → Expr → Expr
  | .add, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a + b))
  | .sub, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a - b))
  | .mul, .lit (.uint64 a), .lit (.uint64 b) => .lit (.uint64 (a * b))
  | .eq,  .lit a,           .lit b           => .lit (.bool (a == b))
  | .ne,  .lit a,           .lit b           => .lit (.bool (a != b))
  | .and, .lit (.bool a),   .lit (.bool b)   => .lit (.bool (a && b))
  | .or,  .lit (.bool a),   .lit (.bool b)   => .lit (.bool (a || b))
  | .strAppend, .lit (.str a), .lit (.str b) => .lit (.str (a ++ b))
  | op, a, b => .binop op a b

def UnaryOp.simplify : UnaryOp → Expr → Expr
  | .not, .lit (.bool b) => .lit (.bool !b)
  | op, e => .unop op e

mutual
def Expr.constFold : Expr → Expr
  | .lit v => .lit v
  | .var x => .var x
  | .binop op l r => BinOp.simplify op l.constFold r.constFold
  | .unop op e => UnaryOp.simplify op e.constFold
  | .call f args => .call f (Expr.constFoldList args)
  | .arrGet arr idx => .arrGet arr.constFold idx.constFold
  | .arrLen arr => .arrLen arr.constFold
  | .strLen s => .strLen s.constFold
  | .strGet s idx => .strGet s.constFold idx.constFold

def Expr.constFoldList : List Expr → List Expr
  | [] => []
  | e :: es => e.constFold :: Expr.constFoldList es
end

mutual
def Stmt.constFold : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x (Expr.constFold e)
  | .seq s₁ s₂ => .seq s₁.constFold s₂.constFold
  | .ite c t f =>
    match Expr.constFold c with
    | .lit (.bool true) => t.constFold
    | .lit (.bool false) => f.constFold
    | c' => .ite c' t.constFold f.constFold
  | .while c b =>
    match Expr.constFold c with
    | .lit (.bool false) => .skip
    | c' => .while c' b.constFold
  | .decl x ty e => .decl x ty (Expr.constFold e)
  | .alloc x ty sz => .alloc x ty (Expr.constFold sz)
  | .free e => .free (Expr.constFold e)
  | .arrSet arr idx val =>
    .arrSet (Expr.constFold arr) (Expr.constFold idx) (Expr.constFold val)
  | .ret e => .ret (Expr.constFold e)
  | .block stmts => .block (Stmt.constFoldList stmts)
  | .callStmt f args => .callStmt f (Expr.constFoldList args)

def Stmt.constFoldList : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.constFold :: Stmt.constFoldList ss
end

-- Helper: BinOp.simplify preserves evaluation semantics
@[simp] theorem BinOp.simplify_correct (op : BinOp) (e₁ e₂ : Expr) (σ : PState) :
    (BinOp.simplify op e₁ e₂).eval σ = (Expr.binop op e₁ e₂).eval σ := by
  simp [Expr.eval]; unfold BinOp.simplify
  split <;> simp_all [Expr.eval, BinOp.eval]

-- Helper: UnaryOp.simplify preserves evaluation semantics
@[simp] theorem UnaryOp.simplify_correct (op : UnaryOp) (e : Expr) (σ : PState) :
    (UnaryOp.simplify op e).eval σ = (Expr.unop op e).eval σ := by
  simp [Expr.eval]; unfold UnaryOp.simplify
  split <;> simp_all [Expr.eval, UnaryOp.eval]

-- Correctness: constant folding preserves expression evaluation
theorem Expr.eval_constFold (e : Expr) (σ : PState) :
    e.constFold.eval σ = e.eval σ := by
  induction e using Expr.constFold.induct (motive_2 := fun _ => True)
    generalizing σ with
  | case1 v => simp [Expr.constFold, Expr.eval]
  | case2 x => simp [Expr.constFold, Expr.eval]
  | case3 op l r ihl ihr =>
    simp only [Expr.constFold, BinOp.simplify_correct, Expr.eval, ihl, ihr]
  | case4 op e ih =>
    simp only [Expr.constFold, UnaryOp.simplify_correct, Expr.eval, ih]
  | case5 => simp only [Expr.constFold, Expr.eval]
  | case6 arr idx iha ihi => simp only [Expr.constFold, Expr.eval, iha, ihi]
  | case7 arr ih => simp only [Expr.constFold, Expr.eval, ih]
  | case8 s ih => simp only [Expr.constFold, Expr.eval, ih]
  | case9 s idx ihs ihi => simp only [Expr.constFold, Expr.eval, ihs, ihi]
  | case10 => trivial
  | case11 => trivial

-- Helper: constFold distributes over foldl of seq
private theorem constFold_foldl_seq (acc : Stmt) (stmts : List Stmt) :
    (stmts.foldl (init := acc) (· ;; ·)).constFold =
    (Stmt.constFoldList stmts).foldl (init := acc.constFold) (· ;; ·) := by
  induction stmts generalizing acc with
  | nil => simp [Stmt.constFoldList, List.foldl]
  | cons s ss ih =>
    simp only [List.foldl, Stmt.constFoldList]
    rw [ih]; simp [Stmt.constFold]

private theorem constFold_foldl_skip (stmts : List Stmt) :
    (stmts.foldl (init := Stmt.skip) (· ;; ·)).constFold =
    (Stmt.constFoldList stmts).foldl (init := Stmt.skip) (· ;; ·) := by
  have := constFold_foldl_seq Stmt.skip stmts
  simp [Stmt.constFold] at this; exact this

-- Helper: constFoldList preserves mapM eval
private theorem constFoldList_mapM_eval (args : List Expr) (σ : PState) :
    (Expr.constFoldList args).mapM (Expr.eval σ) = args.mapM (Expr.eval σ) := by
  induction args with
  | nil => simp [Expr.constFoldList]
  | cons e es ih =>
    simp only [Expr.constFoldList, List.mapM_cons, Expr.eval_constFold, ih]

-- Correctness: constant folding preserves big-step semantics
theorem Stmt.constFold_correct (h : BigStep σ s r) : BigStep σ s.constFold r := by
  induction h with
  | skip => exact BigStep.skip
  | assign he hs =>
    simp only [Stmt.constFold]
    exact BigStep.assign (by simp [Expr.eval_constFold, he]) hs
  | decl he hs =>
    simp only [Stmt.constFold]
    exact BigStep.decl (by simp [Expr.eval_constFold, he]) hs
  | seqNormal _ _ ih₁ ih₂ =>
    simp only [Stmt.constFold]; exact BigStep.seqNormal ih₁ ih₂
  | seqReturn _ ih₁ =>
    simp only [Stmt.constFold]; exact BigStep.seqReturn ih₁
  | ifTrue hc _ ih =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · exact ih
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.ifTrue hc' ih
  | ifFalse hc _ ih =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact ih
    · exact BigStep.ifFalse hc' ih
  | whileTrue hc _ _ ihb ihw =>
    simp only [Stmt.constFold] at ihw ⊢
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split at *
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.whileTrue hc' ihb ihw
  | whileReturn hc _ ihb =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · next heq => rw [heq, Expr.eval] at hc'; cases hc'
    · exact BigStep.whileReturn hc' ihb
  | whileFalse hc =>
    simp only [Stmt.constFold]
    have hc' := hc; rw [← Expr.eval_constFold] at hc'
    split
    · exact BigStep.skip
    · exact BigStep.whileFalse hc'
  | alloc hsz ha hs =>
    simp only [Stmt.constFold]
    exact BigStep.alloc (by simp [Expr.eval_constFold, hsz]) ha hs
  | free he hf =>
    simp only [Stmt.constFold]
    exact BigStep.free (by simp [Expr.eval_constFold, he]) hf
  | arrSet harr hidx hval hw =>
    simp only [Stmt.constFold]
    exact BigStep.arrSet
      (by simp [Expr.eval_constFold, harr])
      (by simp [Expr.eval_constFold, hidx])
      (by simp [Expr.eval_constFold, hval]) hw
  | ret he =>
    simp only [Stmt.constFold]
    exact BigStep.ret (by simp [Expr.eval_constFold, he])
  | block _ ih =>
    simp only [Stmt.constFold]
    exact BigStep.block (by rw [← constFold_foldl_skip]; exact ih)
  | callStmt hlook hargs hparams hframe hbody hpop _ =>
    simp only [Stmt.constFold]
    exact BigStep.callStmt hlook
      (by rw [constFoldList_mapM_eval]; exact hargs)
      hparams hframe hbody hpop

end Radix
