/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Interp
import Radix.Eval.Stmt

/-! # Interpreter Correctness

Proofs that the fuel-based interpreter (`Stmt.interp`) is correct with respect
to the relational big-step semantics (`BigStep`).

## Main results

- `Stmt.interp_fuel_mono`: fuel monotonicity — if `interp` succeeds with fuel
  `n`, it succeeds with the same result with any `m ≥ n`.
- `Stmt.interp_complete`: completeness — if `BigStep σ s r`, there exists enough
  fuel for `interp` to produce the same result.
-/

namespace Radix

/-! ## Helper definitions and lemmas -/

/-- Extract the optional return value from a statement result. -/
@[simp] def StmtResult.retVal : StmtResult → Option Value
  | .normal _ => none
  | .returned v _ => some v

@[simp] theorem evalExpr_ok {e : Expr} {σ : PState} {v : Value}
    (h : e.eval σ = some v) : evalExpr e σ = .ok v := by
  simp [evalExpr, h]

private theorem evalArgs_aux {args : List Expr} {σ : PState} {vs : List Value}
    (h : args.mapM (Expr.eval σ) = some vs) :
    args.mapM (fun e => evalExpr e σ) = .ok vs := by
  induction args generalizing vs with
  | nil =>
    simp only [List.mapM_nil] at h
    change some [] = some vs at h
    obtain rfl := Option.some.inj h
    rfl
  | cons a as ih =>
    simp only [List.mapM_cons] at h
    change Option.bind (a.eval σ) (fun v =>
      Option.bind (as.mapM (Expr.eval σ)) (fun vs' => some (v :: vs'))) = some vs at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h₂⟩ := h
    rw [Option.bind_eq_some_iff] at h₂
    obtain ⟨vs', hvs', h₃⟩ := h₂
    obtain rfl := Option.some.inj h₃
    rw [List.mapM_cons]
    simp [evalExpr_ok hv, ih hvs', bind, Except.bind, pure, Except.pure]

theorem evalArgs_ok {args : List Expr} {σ : PState} {vs : List Value}
    (h : args.mapM (Expr.eval σ) = some vs) : evalArgs args σ = .ok vs := by
  simp [evalArgs]
  exact evalArgs_aux h

theorem mkFrame_ok {params : List (String × Ty)} {vs : List Value} {frame : Frame}
    (hlen : params.length = vs.length)
    (hframe : frame = { env := (params.zip vs).foldl (fun env (p, v) => env.set p.1 v) Env.empty }) :
    mkFrame params vs = .ok frame := by
  unfold mkFrame
  simp only [ne_eq, bind, Except.bind, pure, Except.pure]
  split
  · next h => omega
  · exact congrArg Except.ok hframe.symm

@[simp] theorem andThen_ok_none {σ' : PState} {k : PState → InterpResult} :
    andThen (.ok none, σ') k = k σ' := rfl

@[simp] theorem andThen_ok_some {v : Value} {σ' : PState} {k : PState → InterpResult} :
    andThen (.ok (some v), σ') k = (.ok (some v), σ') := rfl

@[simp] theorem andThen_error {e : String} {σ' : PState} {k : PState → InterpResult} :
    andThen (.error e, σ') k = (.error e, σ') := rfl

/-! ## Fuel monotonicity -/

/-- If `interp` succeeds with fuel `n`, it succeeds with the same result with
any `m ≥ n`. -/
theorem Stmt.interp_fuel_mono {n m : Nat} (h : n ≤ m)
    {s : Stmt} {σ σ' : PState} {rv : Option Value}
    (hok : s.interp n σ = (.ok rv, σ')) :
    s.interp m σ = (.ok rv, σ') := by
  induction n generalizing m s σ σ' rv with
  | zero => simp [Stmt.interp] at hok
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.succ_add]
    unfold Stmt.interp at hok ⊢
    split at hok
    · -- skip
      exact hok
    · -- assign
      simp_all
    · -- decl
      simp_all
    · -- seq
      rename_i s₁ s₂
      simp only [andThen] at hok ⊢
      split at hok
      · rename_i σ₂ h₁
        rw [ih (Nat.le_add_right n m) h₁]
        exact ih (Nat.le_add_right n m) hok
      · rename_i v σ₂ h₁
        rw [ih (Nat.le_add_right n m) h₁]
        exact hok
      · simp at hok
    · -- ite
      split at hok <;> simp_all
      · exact ih (Nat.le_add_right n m) hok
      · exact ih (Nat.le_add_right n m) hok
    · -- while
      split at hok <;> simp_all
      · simp only [andThen] at hok ⊢
        split at hok
        · rename_i σ₂ hb
          rw [ih (Nat.le_add_right n m) hb]
          exact ih (Nat.le_add_right n m) hok
        · rename_i v σ₂ hb
          rw [ih (Nat.le_add_right n m) hb]
          exact hok
        · simp at hok
    · -- alloc
      split at hok <;> simp_all
    · -- free
      split at hok <;> simp_all
    · -- arrSet
      split at hok <;> simp_all
    · -- ret
      split at hok <;> simp_all
    · -- block
      exact ih (Nat.le_add_right n m) hok
    · -- callStmt
      rename_i name args
      simp only [] at hok ⊢
      split at hok
      · exact hok
      · rename_i fd hlook
        split at hok
        · exact hok
        · rename_i vs hargs
          split at hok
          · exact hok
          · rename_i frame hmk
            match hb : Stmt.interp n fd.body (σ.pushFrame frame) with
            | (.error msg, σ₂) =>
              rw [hb] at hok; simp at hok
            | (.ok rv₂, σ₂) =>
              rw [ih (Nat.le_add_right n m) hb]
              rw [hb] at hok
              exact hok
    · -- scope
      rename_i params args₂ body
      simp only [] at hok ⊢
      split at hok
      · exact hok
      · rename_i vs hargs
        split at hok
        · exact hok
        · rename_i frame hmk
          match hb : Stmt.interp n body (σ.pushFrame frame) with
          | (.error msg, σ₂) =>
            rw [hb] at hok; simp at hok
          | (.ok rv₂, σ₂) =>
            rw [ih (Nat.le_add_right n m) hb]
            rw [hb] at hok
            exact hok

/-! ## Completeness -/

/-- If `BigStep σ s r`, there exists enough fuel for `interp` to produce the
corresponding result. -/
theorem Stmt.interp_complete
    {σ : PState} {s : Stmt} {r : StmtResult}
    (h : BigStep σ s r) :
    ∃ fuel : Nat, s.interp fuel σ = (.ok r.retVal, r.state) := by
  induction h with
  | skip =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state]

  | assign he hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, he, hs]

  | decl he hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, he, hs]

  | seqNormal h₁ h₂ ih₁ ih₂ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    obtain ⟨n₂, hn₂⟩ := ih₂
    simp only [StmtResult.retVal, StmtResult.state] at hn₁
    refine ⟨max n₁ n₂ + 1, ?_⟩
    unfold Stmt.interp; simp only [andThen]
    rw [interp_fuel_mono (Nat.le_max_left n₁ n₂) hn₁]
    exact interp_fuel_mono (Nat.le_max_right n₁ n₂) hn₂

  | seqReturn h₁ ih₁ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    simp only [StmtResult.retVal, StmtResult.state] at hn₁ ⊢
    refine ⟨n₁ + 1, ?_⟩
    unfold Stmt.interp; simp only [andThen]
    rw [interp_fuel_mono (Nat.le_refl n₁) hn₁]

  | ifTrue hc ht iht =>
    obtain ⟨n, hn⟩ := iht
    refine ⟨n + 1, ?_⟩
    unfold Stmt.interp
    simp [evalExpr, hc, hn]

  | ifFalse hc hf ihf =>
    obtain ⟨n, hn⟩ := ihf
    refine ⟨n + 1, ?_⟩
    unfold Stmt.interp
    simp [evalExpr, hc, hn]

  | whileTrue hc hb hw ihb ihw =>
    obtain ⟨nb, hnb⟩ := ihb
    obtain ⟨nw, hnw⟩ := ihw
    simp only [StmtResult.retVal, StmtResult.state] at hnb
    refine ⟨max nb nw + 1, ?_⟩
    unfold Stmt.interp
    simp only [evalExpr, hc, andThen]
    rw [interp_fuel_mono (Nat.le_max_left nb nw) hnb]
    exact interp_fuel_mono (Nat.le_max_right nb nw) hnw

  | whileReturn hc hb ihb =>
    obtain ⟨nb, hnb⟩ := ihb
    simp only [StmtResult.retVal, StmtResult.state] at hnb ⊢
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp
    simp only [evalExpr, hc, andThen]
    rw [interp_fuel_mono (Nat.le_refl nb) hnb]

  | whileFalse hc =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, hc]

  | alloc hsz ha hs =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, hsz, ha, hs]

  | free he hf =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, he, hf]

  | arrSet harr hidx hval hw =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, harr, hidx, hval, hw]

  | ret he =>
    refine ⟨1, ?_⟩
    unfold Stmt.interp
    simp [StmtResult.retVal, StmtResult.state, evalExpr, he]

  | block hb ihb =>
    obtain ⟨n, hn⟩ := ihb
    exact ⟨n + 1, by unfold Stmt.interp; exact hn⟩

  | callStmt hlook hargs hparams hframe hbody hpop ihbody =>
    obtain ⟨nb, hnb⟩ := ihbody
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp; simp only [hlook, evalArgs_ok hargs, mkFrame_ok hparams hframe]
    rw [interp_fuel_mono (Nat.le_refl nb) hnb]
    simp_all [StmtResult.state]

  | scope hargs hlen hframe hbody hpop ihbody =>
    obtain ⟨nb, hnb⟩ := ihbody
    refine ⟨nb + 1, ?_⟩
    unfold Stmt.interp; simp only [evalArgs_ok hargs, mkFrame_ok hlen hframe]
    rw [interp_fuel_mono (Nat.le_refl nb) hnb]
    simp_all [StmtResult.state]

end Radix
