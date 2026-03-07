/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

-- Core AST (types, values, operators, expressions, statements, programs)
import Radix.AST

-- Runtime infrastructure
import Radix.Heap
import Radix.Env
import Radix.State

-- Evaluation
import Radix.Eval.Expr
import Radix.Eval.Stmt
import Radix.Eval.Interp

-- Type checking
import Radix.TypeCheck

-- Concrete syntax
import Radix.Syntax

-- Optimizations
import Radix.Opt.ConstFold
import Radix.Opt.DeadCode
import Radix.Opt.CopyProp
import Radix.Opt.ConstProp
import Radix.Opt.Inline

-- Proofs
import Radix.Proofs.Determinism
import Radix.Proofs.TypeSafety
import Radix.Proofs.MemorySafety

-- Tests
import Radix.Tests.Basic
import Radix.Tests.Functions
import Radix.Tests.Arrays
import Radix.Tests.Strings
import Radix.Tests.Opt

/-! # Radix: Verified Embedded DSL for High-Performance Applications

An imperative DSL embedded in Lean 4 with functions, strings, dynamic memory,
formal semantics, verified optimizations, and proofs.
-/
