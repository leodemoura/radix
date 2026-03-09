# Radix DSL: Proof Techniques Report

## Overview

The Radix DSL has a relational big-step semantics (`BigStep`), a fuel-based
interpreter (`Stmt.interp`), and several optimizations (`inline`, `constProp`,
`copyProp`). Full correctness was established with zero sorry.

Key source files:
- `Radix/Eval/Stmt.lean` — `BigStep` relation
- `Radix/Eval/Interp.lean` — fuel-based interpreter
- `Radix/Proofs/InterpCorrectness.lean` — fuel monotonicity, completeness, soundness
- `Radix/Opt/Inline.lean` — inlining optimization + correctness proof

## Key Proof Architecture

### Interpreter correctness = soundness + completeness

Three theorems establish full equivalence between `Stmt.interp` and `BigStep`:

1. **`interp_fuel_mono`**: If `interp` succeeds with fuel `n`, it gives the same
   result with any `m ≥ n`. Proved by induction on `n`. Essential for combining
   sub-results that need different fuel amounts.

2. **`interp_complete`**: If `BigStep σ s r`, then
   `∃ fuel, s.interp fuel σ = (.ok r.retVal, r.state)`. Proved by induction on
   `BigStep`. Uses `fuel_mono` + `max` to unify fuel across sub-derivations.

3. **`interp_sound`**: If `s.interp fuel σ = (.ok rv, σ')`, then
   `BigStep σ s (toStmtResult rv σ')`. Proved by induction on `fuel`,
   case-splitting on `s`.

### Fuel-based recursion avoids mutual induction

The interpreter was originally `partial`. Converting to fuel-based recursion
(`termination_by fuel`) was the key enabler:
- All proofs use plain `Nat` induction on `fuel`.
- The IH is universally quantified over all statements and states.
- The `while` case (which recurses on the same statement) works because fuel
  decreases, not because the statement gets smaller.
- No need for mutual induction schemes.

### Induction on semantics, not function structure

`Stmt.inline` is defined by `mutual` recursion (with `Stmt.inlineList`), but the
correctness proof `Stmt.inline_correct` does induction on `BigStep`, not on the
mutual recursion structure. In each case, `simp only [Stmt.inline]` unfolds the
optimization, and the BigStep constructor + IH close the goal. The mutual
recursion is just structural plumbing that the proof never needs to follow.

### Helper lemma pairs (forward + reverse)

Forward helpers convert semantic facts to interpreter facts (for completeness):
- `evalExpr_ok`: `e.eval σ = some v → evalExpr e σ = .ok v`
- `evalArgs_ok`, `mkFrame_ok`

Reverse helpers go the other direction (for soundness):
- `evalExpr_ok'`: `evalExpr e σ = .ok v → e.eval σ = some v`
- `evalArgs_ok'`, `mkFrame_ok'`

### `andThen` simp lemmas

The interpreter's monadic plumbing uses `andThen`. Three `@[simp]` lemmas
decompose it in proofs:
- `andThen_ok_none`: normal completion → continue
- `andThen_ok_some`: early return → propagate
- `andThen_error`: error → propagate

### Named definitions avoid dependent match issues

The soundness proof needed `toStmtResult rv σ'` (a named `def`) instead of an
anonymous `match rv with ...` in the conclusion. Without this, Lean generates a
dependent match on the proof term `h`, causing the IH to produce terms that
don't unify with the goal when `h` gets renamed by tactics.

`toStmtResult_state` (`(toStmtResult rv σ).state = σ`, proved by
`cases rv <;> rfl`) bridges the gap when BigStep constructors expect
`bodyResult.state.popFrame` but the proof has `σ₂.popFrame`.

### `funs_preserved` invariant

`BigStep.funs_preserved : BigStep σ s r → r.state.funs = σ.funs` — the function
table is immutable during execution. This is essential for `inline_correct`: the
static function table used to decide what to inline must match the runtime table.
Threading `hfuns : σ.funs = funs` through the induction carries this invariant.

## Tricky Cases

| Case | Difficulty | Resolution |
|------|-----------|------------|
| `while` (soundness) | `andThen` decomposition | `split at h` on the andThen, yielding body-normal and body-return sub-cases |
| `callStmt`/`scope` | `popFrame` and `toStmtResult` mismatch | `cases rv₂ <;> exact hpop` to reduce the match |
| `arrSet` | 3-way match on evalExpr results | `split at h <;> (try simp at h)` to dispatch error cases in bulk |
| `block` | `inlineList` vs `foldl` | Helper lemmas `inlineList_eq_map` + `inline_foldl_seq` |
| `while` (inline) | Recursive call on same statement | IH from BigStep induction already handles it; `simp only [Stmt.inline] at ihw'` |
