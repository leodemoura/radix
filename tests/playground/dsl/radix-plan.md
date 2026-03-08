# Radix: Building a Verified DSL with Multi-Agent AI

An experiment in using multiple AI agent personas to build a non-trivial
verified artifact in Lean 4 — an imperative DSL with functions, dynamic
memory, formal semantics, verified compiler optimizations, and proofs.

## Motivation

Inspired by Dejan Jovanovic's multi-agent experiment (building a SAT/SMT
solver), the question: **can AI agents with distinct researcher personas
collaborate through GitHub issues and PRs to build something real?**

The target: **Radix**, an imperative embedded DSL in Lean 4 — small enough
to finish in days, rich enough to exercise formal verification (big-step
semantics, optimization correctness proofs, memory safety theorems).

## The Setup

10 agent personas based on real CS researchers, each assigned a role:

| Persona | Role |
|---------|------|
| Chris Lattner | Compiler Architect — AST, IR, module structure |
| Simon Peyton Jones | Language Designer — types, syntax macros, functions |
| Xavier Leroy | Verification Architect — proof strategy, correctness methodology |
| Derek Dreyer | Semantics & Memory — heap, state, big-step semantics |
| Adam Chlipala | Proof Engineer — determinism, type safety |
| Emina Torlak | DSL Bridge — type checking, test infrastructure |
| John Regehr | Testing Lead — edge cases, comprehensive coverage |
| Dan Grossman | Memory Safety — heap safety proofs, call stack safety |
| Nadia Polikarpova | Specification Writer — formal specs, pre/post conditions |
| Tiark Rompf | Staging & Codegen — interpreter, optimizations |

Workflow: each agent picks up an unblocked GitHub issue, creates a branch,
implements, opens a PR with reviewers, and squash-merges after approval.
Leo manages as project lead — issue comments, design decisions, priority.

## The Language

Radix is a small imperative language with:

- **Types**: `uint64`, `bool`, `unit`, `string`, `array T`, `fn`
- **Expressions**: arithmetic, comparisons, logical ops, string ops, array access
- **Statements**: assignment, sequencing, if/else, while, declarations, alloc/free, function calls, return, scoped blocks
- **Memory model**: bump-allocator heap (`HashMap Addr (Array Value)`), explicit alloc/free
- **Functions**: first-class declarations with call stack (frame push/pop)
- **Syntax macros**: `declare_syntax_cat` for writing Radix programs in natural syntax

Key design choices:
- Expressions are **pure** (no side effects, no function calls) — calls are statement-level only, which simplifies semantics
- `scope` constructor for frame-isolated inlined function bodies (used by the inliner)
- Heap never reuses freed addresses (simplifies memory safety proofs)
- All heap operations return `Option` for explicit failure modeling

## What Was Built

**25 modules, ~4,500 lines of Lean 4.** Everything builds clean.

### Core Language (8 modules)
```
Radix/AST.lean          — types, values, operators, expressions, statements
Radix/Env.lean          — variable environment (HashMap String Value)
Radix/Heap.lean         — bump-allocator heap with alloc/free/read/write
Radix/State.lean        — PState, Frame, call stack operations
Radix/Eval/Expr.lean    — expression evaluation
Radix/Eval/Stmt.lean    — big-step operational semantics (inductive)
Radix/Eval/Interp.lean  — fuel-based interpreter
Radix/TypeCheck.lean     — typing judgments, decidable checker
Radix/Syntax.lean        — concrete syntax macros
```

### Verified Optimizations (5 modules, 5 correctness theorems, 0 sorry)
```
Radix/Opt/ConstFold.lean   — constant folding          (constFold_correct)
Radix/Opt/DeadCode.lean    — dead code elimination     (deadCodeElim_correct)
Radix/Opt/CopyProp.lean    — copy propagation          (copyProp_correct)
Radix/Opt/ConstProp.lean   — constant propagation      (constPropagation_correct)
Radix/Opt/Inline.lean      — function inlining         (inline_correct)
```

Each optimization is a function `Stmt → Stmt` with a mechanized correctness
proof against the big-step semantics. No sorry in any optimization proof.

### Formal Proofs (3 modules)
```
Radix/Proofs/Determinism.lean     — BigStep.det: big-step is deterministic (no sorry)
Radix/Proofs/MemorySafety.lean    — no_use_after_free, no_double_free, read_within_bounds (no sorry)
Radix/Proofs/TypeSafety.lean      — preservation and progress (4 sorry — WIP)
```

### Test Suite (5 modules, 85+ tests)
```
Radix/Tests/Basic.lean       — arithmetic, variables, control flow, scoping, error cases
Radix/Tests/Functions.lean   — zero-arg, undefined errors, frame isolation, chained calls
Radix/Tests/Arrays.lean      — alloc, OOB read/write, boundary access, double free, use-after-free
Radix/Tests/Strings.lean     — empty string, OOB strGet, type errors, loop concat
Radix/Tests/Opt.lean         — chained optimizations, inlining threshold, scope, propagation invalidation
```

## Key Results

1. **5 verified compiler optimizations** — correctness theorems proved against big-step semantics, no sorry
2. **Determinism theorem** — big-step evaluation is deterministic, fully proved
3. **Memory safety properties** — no-use-after-free, no-double-free, read-within-bounds, fully proved
4. **85+ executable tests** covering edge cases across all language features
5. **Multi-agent coordination** worked — 21 issues tracked, dependency-ordered, reviewed and merged through PRs

## What Remains

Two open items:
- **Type safety proofs** — preservation and progress theorem statements exist, proofs have 4 sorry
- **Program-level memory safety** — current proofs are about the heap API; full program-level safety would need a linear type system

## Repository

Private mirror of `leanprover/lean4` at `leodemoura/radix`.
DSL lives at `tests/playground/dsl/`.
Build: `lake build` (25 modules).

## Takeaways

The multi-agent workflow produced a complete, non-trivial verified artifact
in a few days. The dependency-ordered issue structure (5 waves) was key —
it naturally parallelized work while maintaining coherence. The verification
aspects (proofs, correctness theorems) were the most challenging part for
the agents, requiring significant iteration, but the final proofs are
genuine — no sorry in the critical paths.
