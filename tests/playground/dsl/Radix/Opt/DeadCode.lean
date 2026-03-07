/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Stmt

/-! # Dead Code Elimination

Remove unreachable branches and simplify trivial control flow.
-/

namespace Radix

mutual
/-- Collect variables that are read in an expression. -/
def Expr.readVars : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .binop _ l r => l.readVars ++ r.readVars
  | .unop _ e => e.readVars
  | .call _ args => Expr.readVarsList args
  | .arrGet a i => a.readVars ++ i.readVars
  | .arrLen a => a.readVars
  | .strLen s => s.readVars
  | .strGet s i => s.readVars ++ i.readVars

def Expr.readVarsList : List Expr → List String
  | [] => []
  | e :: es => e.readVars ++ Expr.readVarsList es
end

mutual
/-- Collect variables that are read in a statement. -/
def Stmt.readVars : Stmt → List String
  | .skip => []
  | .assign _ e => Expr.readVars e
  | .seq s₁ s₂ => s₁.readVars ++ s₂.readVars
  | .ite c t f => Expr.readVars c ++ t.readVars ++ f.readVars
  | .while c b => Expr.readVars c ++ b.readVars
  | .decl _ _ e => Expr.readVars e
  | .alloc _ _ sz => Expr.readVars sz
  | .free e => Expr.readVars e
  | .arrSet a i v => Expr.readVars a ++ Expr.readVars i ++ Expr.readVars v
  | .ret e => Expr.readVars e
  | .block stmts => Stmt.readVarsList stmts
  | .callStmt _ args => Expr.readVarsList args

def Stmt.readVarsList : List Stmt → List String
  | [] => []
  | s :: ss => s.readVars ++ Stmt.readVarsList ss
end

mutual
/-- Dead code elimination pass. -/
def Stmt.deadCodeElim : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq s₁ s₂ =>
    match s₁.deadCodeElim with
    | .skip => s₂.deadCodeElim
    | s₁' =>
      match s₂.deadCodeElim with
      | .skip => s₁'
      | s₂' => .seq s₁' s₂'
  | .ite c t f =>
    match c with
    | .lit (.bool true) => t.deadCodeElim
    | .lit (.bool false) => f.deadCodeElim
    | _ =>
      match t.deadCodeElim, f.deadCodeElim with
      | .skip, .skip => .skip
      | t', f' => .ite c t' f'
  | .while c b =>
    match c with
    | .lit (.bool false) => .skip
    | _ => .while c b.deadCodeElim
  | .decl x ty e => .decl x ty e
  | .alloc x ty sz => .alloc x ty sz
  | .free e => .free e
  | .arrSet a i v => .arrSet a i v
  | .ret e => .ret e
  | .block stmts => .block (Stmt.deadCodeElimList stmts)
  | .callStmt f args => .callStmt f args

def Stmt.deadCodeElimList : List Stmt → List Stmt
  | [] => []
  | s :: ss => s.deadCodeElim :: Stmt.deadCodeElimList ss
end

private theorem BigStep.skip_eq (h : BigStep σ .skip r) : r = .normal σ := by
  cases h; rfl

private theorem dce_seq_to_seq_dce (h : BigStep σ (Stmt.deadCodeElim (a ;; b)) r) :
    BigStep σ (a.deadCodeElim ;; b.deadCodeElim) r := by
  simp only [Stmt.deadCodeElim] at h
  split at h
  next heq =>
    rw [heq]; exact BigStep.seqNormal BigStep.skip h
  next =>
    split at h
    next _ heq =>
      rw [heq]
      cases r with
      | normal σ' => exact BigStep.seqNormal h BigStep.skip
      | returned v σ' => exact BigStep.seqReturn h
    next => exact h

private theorem BigStep.foldl_seq_mono (xs : List Stmt)
    (hab : ∀ σ r, BigStep σ a r → BigStep σ b r)
    (h : BigStep σ (xs.foldl (init := a) (· ;; ·)) r) :
    BigStep σ (xs.foldl (init := b) (· ;; ·)) r := by
  induction xs generalizing a b σ r with
  | nil => simp [List.foldl] at *; exact hab σ r h
  | cons x xs ih =>
    simp only [List.foldl] at *
    apply ih (a := a ;; x) (b := b ;; x)
    · intro σ' r' h'
      cases h' with
      | seqNormal h₁ h₂ => exact BigStep.seqNormal (hab σ' _ h₁) h₂
      | seqReturn h₁ => exact BigStep.seqReturn (hab σ' _ h₁)
    · exact h

private theorem dce_foldl_gen (acc : Stmt) (stmts : List Stmt) (σ : PState) (r : StmtResult)
    (h : BigStep σ (Stmt.deadCodeElim (stmts.foldl (init := acc) (· ;; ·))) r) :
    BigStep σ ((Stmt.deadCodeElimList stmts).foldl (init := acc.deadCodeElim) (· ;; ·)) r := by
  induction stmts generalizing acc σ r with
  | nil => simp [Stmt.deadCodeElimList, List.foldl] at *; exact h
  | cons s ss ih =>
    simp only [List.foldl, Stmt.deadCodeElimList]
    have h' := ih (acc ;; s) σ r h
    exact BigStep.foldl_seq_mono (Stmt.deadCodeElimList ss)
      (fun σ r h => dce_seq_to_seq_dce h) h'

private theorem dce_foldl_skip (stmts : List Stmt) (σ : PState) (r : StmtResult)
    (h : BigStep σ (Stmt.deadCodeElim (stmts.foldl (init := Stmt.skip) (· ;; ·))) r) :
    BigStep σ ((Stmt.deadCodeElimList stmts).foldl (init := Stmt.skip) (· ;; ·)) r := by
  have := dce_foldl_gen Stmt.skip stmts σ r h
  simp [Stmt.deadCodeElim] at this; exact this

-- Correctness: DCE preserves semantics
theorem Stmt.deadCodeElim_correct (h : BigStep σ s r) : BigStep σ s.deadCodeElim r := by
  induction h with
  | skip => exact BigStep.skip
  | assign he hs => exact BigStep.assign he hs
  | decl he hs => exact BigStep.decl he hs
  | seqNormal h₁ h₂ ih₁ ih₂ =>
    simp only [Stmt.deadCodeElim]
    split
    next heq => rw [heq] at ih₁; cases BigStep.skip_eq ih₁; exact ih₂
    next =>
      split
      next _ heq => rw [heq] at ih₂; cases BigStep.skip_eq ih₂; exact ih₁
      next => exact BigStep.seqNormal ih₁ ih₂
  | seqReturn h₁ ih₁ =>
    simp only [Stmt.deadCodeElim]
    split
    next heq => rw [heq] at ih₁; cases ih₁
    next =>
      split
      next => exact ih₁
      next => exact BigStep.seqReturn ih₁
  | ifTrue hc _ ih =>
    simp only [Stmt.deadCodeElim]
    split
    · exact ih
    · simp_all [Expr.eval]
    · split
      next ht _ => rw [ht] at ih; exact ih
      next => exact BigStep.ifTrue hc ih
  | ifFalse hc _ ih =>
    simp only [Stmt.deadCodeElim]
    split
    · simp_all [Expr.eval]
    · exact ih
    · split
      next _ hf => rw [hf] at ih; exact ih
      next => exact BigStep.ifFalse hc ih
  | whileTrue hc _ _ ihb ihw =>
    simp only [Stmt.deadCodeElim] at ihw ⊢
    split at *
    · simp_all [Expr.eval]
    · exact BigStep.whileTrue hc ihb ihw
  | whileReturn hc _ ihb =>
    simp only [Stmt.deadCodeElim]
    split
    · simp_all [Expr.eval]
    · exact BigStep.whileReturn hc ihb
  | whileFalse hc =>
    simp only [Stmt.deadCodeElim]
    split
    · exact BigStep.skip
    · exact BigStep.whileFalse hc
  | alloc hsz ha hs => exact BigStep.alloc hsz ha hs
  | free he hf => exact BigStep.free he hf
  | arrSet harr hidx hval hw => exact BigStep.arrSet harr hidx hval hw
  | ret he => exact BigStep.ret he
  | block _ ih =>
    simp only [Stmt.deadCodeElim]
    exact BigStep.block (dce_foldl_skip _ _ _ ih)
  | callStmt hlook hargs hparams hframe hbody hpop _ =>
    exact BigStep.callStmt hlook hargs hparams hframe hbody hpop

end Radix
