# Proving Interpreter Correctness in Lean 4

A practical guide to establishing full equivalence between a fuel-based
interpreter and a relational big-step semantics. Based on the Radix DSL
(`tests/playground/dsl/Radix/`), but the pattern applies to any imperative
language with loops, early return, or function calls.

## The Setup

You need two definitions of your language's semantics:

1. **Relational semantics** (`BigStep`): an inductive proposition describing
   what it means for a statement to evaluate to a result. This is your
   specification — clear, declarative, easy to reason about.

2. **Fuel-based interpreter** (`Stmt.interp`): an executable function that takes
   a `Nat` fuel parameter and returns a result. This is your implementation —
   runnable, testable, but needs a termination argument.

The goal: prove they agree on all inputs.

## Step 0: Use Fuel, Not Mutual Recursion

If your interpreter handles `while` loops, it probably recurses on the same
statement (not a sub-statement). This breaks structural recursion and forces
either `partial`, `mutual`, or well-founded recursion.

**Use a fuel parameter instead.** Every recursive call decreases fuel:

```lean
def Stmt.interp (fuel : Nat) (s : Stmt) (σ : State) : Result :=
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    match s with
    | .while c b =>
      if eval c σ then
        -- both calls use `fuel`, not `fuel + 1`
        andThen (b.interp fuel σ) (s.interp fuel)
      else ...
    | ...
termination_by fuel
```

This is the single most important design choice. It makes all three correctness
proofs straightforward `Nat` inductions, with an IH universally quantified over
all statements and states. No mutual induction needed.

## Step 1: `andThen` Simp Lemmas

If your interpreter threads state through sequential composition (seq, while),
define an `andThen` combinator and give it `@[simp]` lemmas for each result
case:

```lean
@[simp] theorem andThen_ok_none : andThen (.ok none, σ') k = k σ' := rfl
@[simp] theorem andThen_ok_some : andThen (.ok (some v), σ') k = (.ok (some v), σ') := rfl
@[simp] theorem andThen_error   : andThen (.error e, σ') k = (.error e, σ') := rfl
```

These are used constantly in all three proofs. Without them, you'll be manually
unfolding `andThen` everywhere.

## Step 2: Helper Lemma Pairs

Your interpreter likely wraps pure evaluation functions (e.g., `Expr.eval`)
in error-handling wrappers (e.g., `evalExpr`). You need lemmas going both
directions:

**Forward** (for completeness — semantic fact → interpreter fact):
```lean
theorem evalExpr_ok (h : e.eval σ = some v) : evalExpr e σ = .ok v
```

**Reverse** (for soundness — interpreter fact → semantic fact):
```lean
theorem evalExpr_ok' (h : evalExpr e σ = .ok v) : e.eval σ = some v
```

Write both from the start. You'll need the forward direction for completeness
and the reverse for soundness.

## Step 3: Fuel Monotonicity

```lean
theorem interp_fuel_mono (h : n ≤ m) (hok : s.interp n σ = (.ok rv, σ')) :
    s.interp m σ = (.ok rv, σ')
```

**Proof**: Induction on `n`. The `zero` case is vacuous (interp always errors).
The `succ` case: unfold `interp` at both `hok` and the goal, then apply the IH
to each recursive sub-call.

**Why you need it**: Completeness combines results from sub-derivations that may
require different amounts of fuel. `fuel_mono` lets you bump everything to
`max n₁ n₂`.

**Proof pattern**: For each statement case, follow the structure of `interp`.
When you hit a recursive call in `hok`, use `ih (Nat.le_add_right n m)` to get
the same result with more fuel, then `rw` it into the goal.

## Step 4: Completeness

```lean
theorem interp_complete (h : BigStep σ s r) :
    ∃ fuel, s.interp fuel σ = (.ok r.retVal, r.state)
```

**Proof**: Induction on `BigStep`. Each case:
1. Extract fuel witnesses from the IH: `obtain ⟨n₁, hn₁⟩ := ih₁`
2. Provide `max n₁ n₂ + 1` (or `n + 1` for single-recursive cases)
3. `unfold Stmt.interp`
4. Rewrite with `fuel_mono` to unify fuel: `rw [interp_fuel_mono (le_max_left ..) hn₁]`
5. Close with the remaining IH or `simp`

The `+1` accounts for the `fuel + 1` pattern match in `interp`.

## Step 5: Soundness

```lean
theorem interp_sound (h : s.interp fuel σ = (.ok rv, σ')) :
    BigStep σ s (toStmtResult rv σ')
```

**Proof**: Induction on `fuel`. The `zero` case is vacuous. The `succ` case:
`unfold Stmt.interp at h`, then `match s` and work through each statement form.

### Important: use a named result conversion

Define a named function for converting interpreter output to a `BigStep` result:

```lean
@[simp] def toStmtResult (rv : Option Value) (σ' : State) : StmtResult :=
  match rv with | none => .normal σ' | some v => .returned v σ'
```

**Do not use an anonymous `match rv with ...` in the theorem statement.** Lean
will generate a dependent match on the proof term `h`. When tactics rename `h`
(which happens in every `split at h`), the IH produces terms with the wrong
proof witness that don't unify with the goal.

### Proof pattern for each case

The pattern is consistent across cases:

1. `simp only [] at h` (or nothing) — expose the match structure
2. `split at h` — case-split on the match in the interpreter
3. Error branches: `simp at h` (contradiction — `.error` ≠ `.ok`)
4. Success branches: `simp at h; obtain ⟨rfl, rfl⟩ := h` to extract equalities
5. Apply the BigStep constructor with reverse helpers and IH

### Tricky cases

**`while`**: The interpreter uses `andThen`. After `simp only [andThen] at h`,
do `split at h` to get three cases: body returns `none` (normal → recurse),
body returns `some v` (early return), or body errors. Apply the IH to both the
body and the recursive while call.

**`callStmt`/`scope`**: The BigStep constructor expects
`bodyResult.state.popFrame`, but the IH gives you `toStmtResult rv₂ σ₂` and
the proof has `σ₂.popFrame`. You need:

```lean
@[simp] theorem toStmtResult_state (rv : Option Value) (σ : State) :
    (toStmtResult rv σ).state = σ := by cases rv <;> rfl
```

Then bridge with:
```lean
have hpop' : (toStmtResult rv₂ σ₂).state.popFrame = some (fr, σ₃) := by
  cases rv₂ <;> exact hpop
```

**Multi-way matches** (e.g., `arrSet` matching three `evalExpr` results):
Use `split at h <;> (try simp at h)` to dispatch all error branches in bulk,
then handle the single success branch.

## Bonus: Optimization Correctness

Once you have `BigStep`, proving optimization correctness is often easier than
proving interpreter correctness. The pattern:

```lean
theorem opt_correct (h : BigStep σ s r) : BigStep σ (s.opt) r
```

**Induction on `BigStep`**, not on the optimization function. Even if `opt` is
defined by `mutual` recursion, the proof doesn't need to follow that structure.
In each case, `simp only [Stmt.opt]` unfolds the optimization, and the BigStep
constructor + IH close the goal.

This works because `BigStep` already provides the semantic decomposition you
need. The optimization just rearranges syntax; the proof shows the rearranged
syntax has the same semantics.

For optimizations that depend on runtime invariants (e.g., inlining needs the
function table to be immutable), prove the invariant separately:

```lean
theorem funs_preserved (h : BigStep σ s r) : r.state.funs = σ.funs
```

Then thread it as a hypothesis: `(hfuns : σ.funs = funs)`.

## Summary

| Step | Theorem | Induction on | Key technique |
|------|---------|-------------|---------------|
| 0 | — | — | Fuel parameter on interpreter |
| 1 | — | — | `andThen` simp lemmas |
| 2 | — | — | Forward + reverse helper pairs |
| 3 | `fuel_mono` | `fuel : Nat` | `rw` with IH at reduced fuel |
| 4 | `complete` | `BigStep` | `max` + `fuel_mono` to unify fuel |
| 5 | `sound` | `fuel : Nat` | Named `toStmtResult`, reverse helpers |
| — | `opt_correct` | `BigStep` | `simp only [Stmt.opt]` + constructor |

The Radix DSL source (`Radix/Proofs/InterpCorrectness.lean`, `Radix/Opt/Inline.lean`)
provides a complete worked example.
