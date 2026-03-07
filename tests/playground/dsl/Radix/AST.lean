/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/


/-! # Radix AST

All core types for the Radix DSL: types, values, operators, expressions,
statements, function declarations, and programs.
-/

namespace Radix

/-! ## Types -/

inductive Ty where
  | uint64
  | bool
  | unit
  | string
  | array : Ty → Ty
  | fn : List Ty → Ty → Ty
  deriving Repr, Inhabited, BEq

/-! ## Values -/

abbrev Addr := Nat

inductive Value where
  | uint64 : UInt64 → Value
  | bool : Bool → Value
  | unit : Value
  | str : String → Value
  | addr : Addr → Value
  deriving Repr, Inhabited, DecidableEq, BEq

/-! ## Operators -/

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  | strAppend
  deriving Repr, DecidableEq, Inhabited, BEq

inductive UnaryOp where
  | not | neg
  deriving Repr, DecidableEq, Inhabited, BEq

/-! ## Expressions -/

inductive Expr where
  | lit : Value → Expr
  | var : String → Expr
  | binop : BinOp → Expr → Expr → Expr
  | unop : UnaryOp → Expr → Expr
  | call : String → List Expr → Expr
  | arrGet : Expr → Expr → Expr
  | arrLen : Expr → Expr
  | strLen : Expr → Expr
  | strGet : Expr → Expr → Expr
  deriving Repr, Inhabited

/-! ## Statements -/

inductive Stmt where
  | skip
  | assign : String → Expr → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : Expr → Stmt → Stmt → Stmt
  | while : Expr → Stmt → Stmt
  | decl : String → Ty → Expr → Stmt
  | alloc : String → Ty → Expr → Stmt
  | free : Expr → Stmt
  | arrSet : Expr → Expr → Expr → Stmt
  | ret : Expr → Stmt
  | block : List Stmt → Stmt
  | callStmt : String → List Expr → Stmt
  deriving Repr, Inhabited

infixr:130 " ;; " => Stmt.seq

/-! ## Function Declarations and Programs -/

structure FunDecl where
  name : String
  params : List (String × Ty)
  retTy : Ty
  body : Stmt
  deriving Repr, Inhabited

structure Program where
  funs : List FunDecl
  main : Stmt
  deriving Repr, Inhabited

end Radix
