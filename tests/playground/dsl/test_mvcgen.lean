import Radix.TypeCheck
import Radix.Eval.Stmt
import Std.Tactic.Do

open Std.Do

namespace Radix

def Value.hasType' : Value → Ty → Prop
  | .uint64 _, .uint64 => True
  | .bool _,   .bool   => True
  | .unit,     .unit    => True
  | .str _,    .string  => True
  | .addr _,   .array _ => True
  | _, _ => False

-- Bridge: convert between wp⟦x⟧ mayThrow and plain Option reasoning
theorem Option.wp_mayThrow_of_forall {x : Option α} {P : α → Prop}
    (h : ∀ v, x = some v → P v) :
    (WP.wp x |>.apply (PostCond.mayThrow fun v => ⌜P v⌝)).down := by
  cases x with
  | some v => exact h v rfl
  | none => trivial

-- BinOp.eval preserves types (already proved)
private theorem BinOp.eval_preserves_type' {op : BinOp} {vl vr v : Value} {tl tr ty : Ty}
    (hvl : vl.hasType' tl) (hvr : vr.hasType' tr)
    (hty : op.typeOfResult tl tr = some ty)
    (hev : op.eval vl vr = some v) :
    v.hasType' ty := by
  cases op
  all_goals (first
    | (simp [BinOp.eval] at hev; subst hev
       simp [BinOp.typeOfResult] at hty; obtain ⟨_, rfl⟩ := hty
       simp [Value.hasType'])
    | (cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty; cases vl <;> simp [Value.hasType'] at hvl
       cases vr <;> simp [Value.hasType'] at hvr
       simp [BinOp.eval] at hev; subst hev; simp [Value.hasType'])
    | (cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty; cases vl <;> simp [Value.hasType'] at hvl
       cases vr <;> simp [Value.hasType'] at hvr
       simp [BinOp.eval] at hev; obtain ⟨_, rfl⟩ := hev; simp [Value.hasType']))

-- ============================================================
-- EXPERIMENT: mvcgen-based preservation proof for binop
-- ============================================================

theorem preservation_binop (σ : PState) (Γ : TyEnv) (sigs : FunSigs)
    (op : BinOp) (l r : Expr) (ty : Ty)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType' v ty)
    (hty : Expr.typeOf Γ sigs (.binop op l r) = some ty)
    (ihl : ∀ ty, Expr.typeOf Γ sigs l = some ty →
      ⦃⌜True⌝⦄ Expr.eval σ l ⦃⇓? v => ⌜Value.hasType' v ty⌝⦄)
    (ihr : ∀ ty, Expr.typeOf Γ sigs r = some ty →
      ⦃⌜True⌝⦄ Expr.eval σ r ⦃⇓? v => ⌜Value.hasType' v ty⌝⦄) :
    ⦃⌜True⌝⦄ Expr.eval σ (.binop op l r) ⦃⇓? v => ⌜Value.hasType' v ty⌝⦄ := by
  -- Extract types from hty
  simp only [Expr.typeOf, bind, Option.bind] at hty
  cases htl : Expr.typeOf Γ sigs l <;> simp [htl] at hty
  rename_i tl
  cases htr : Expr.typeOf Γ sigs r <;> simp [htr] at hty
  rename_i tr
  have sl := ihl tl htl
  have sr := ihr tr htr
  -- mvcgen decomposes the do block, using sl/sr for recursive eval calls
  mvcgen [Expr.eval, sl, sr]
  -- ONE VC: given vl.hasType' tl, vr.hasType' tr, show wp⟦op.eval vl vr⟧ ...
  case vc1.some.some.success.success =>
    intro hvr
    -- Bridge from wp to plain Option
    apply Option.wp_mayThrow_of_forall
    intro v hev
    exact BinOp.eval_preserves_type' ‹_› hvr hty hev

end Radix
