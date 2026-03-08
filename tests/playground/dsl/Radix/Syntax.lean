/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Interp

/-! # Radix Concrete Syntax

Custom syntax categories for writing Radix programs naturally.

Two syntax quotations are provided:
- `` `[RExpr| ...] `` for expressions: arithmetic, comparisons, booleans,
  string append, string/numeric literals, and variable references.
- `` `[RStmt| ...] `` for statements: assignment, `if/else`, `while`, function
  calls, `return`, and array write.

Limitations: `arrGet`, `arrLen`, `strLen`, `strGet`, `alloc`, `free`, and `decl`
are not covered by the concrete syntax and must be constructed as raw AST.
-/

namespace Radix

-- Expression syntax
syntax "`[RExpr|" term "]" : term

macro_rules
  | `(`[RExpr| true])      => `(Expr.lit (.bool true))
  | `(`[RExpr| false])     => `(Expr.lit (.bool false))
  | `(`[RExpr| $n:num])    => `(Expr.lit (.uint64 $n))
  | `(`[RExpr| $s:str])    => `(Expr.lit (.str $s))
  | `(`[RExpr| $x:ident])  => `(Expr.var $(Lean.quote x.getId.toString))
  | `(`[RExpr| $x + $y])   => `(Expr.binop .add `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x - $y])   => `(Expr.binop .sub `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x * $y])   => `(Expr.binop .mul `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x / $y])   => `(Expr.binop .div `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x % $y])   => `(Expr.binop .mod `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x == $y])  => `(Expr.binop .eq `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x != $y])  => `(Expr.binop .ne `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x < $y])   => `(Expr.binop .lt `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x <= $y])  => `(Expr.binop .le `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x > $y])   => `(Expr.binop .gt `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x >= $y])  => `(Expr.binop .ge `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x && $y])  => `(Expr.binop .and `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x || $y])  => `(Expr.binop .or `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| $x ++ $y])  => `(Expr.binop .strAppend `[RExpr| $x] `[RExpr| $y])
  | `(`[RExpr| !$x])       => `(Expr.unop .not `[RExpr| $x])
  | `(`[RExpr| ($x)])      => `(`[RExpr| $x])

-- Statement syntax
declare_syntax_cat rstmt

syntax ident " := " term ";" : rstmt
syntax "if " "(" term ")" " {" rstmt* "}" (" else " "{" rstmt* "}")? : rstmt
syntax "while " "(" term ")" " {" rstmt* "}" : rstmt
syntax ident "(" term,* ")" ";" : rstmt
syntax "return " term ";" : rstmt
syntax ident "[" term "]" " := " term ";" : rstmt

syntax "`[RStmt|" rstmt* "]" : term

macro_rules
  | `(`[RStmt| ]) => `(Stmt.skip)
  | `(`[RStmt| $x:ident := $e:term;]) =>
    `(Stmt.assign $(Lean.quote x.getId.toString) `[RExpr| $e])
  | `(`[RStmt| if ($c) { $ts* } else { $es* }]) =>
    `(Stmt.ite `[RExpr| $c] `[RStmt| $ts*] `[RStmt| $es*])
  | `(`[RStmt| if ($c) { $ts* }]) =>
    `(Stmt.ite `[RExpr| $c] `[RStmt| $ts*] Stmt.skip)
  | `(`[RStmt| while ($c) { $bs* }]) =>
    `(Stmt.while `[RExpr| $c] `[RStmt| $bs*])
  | `(`[RStmt| $f:ident($args:term,*);]) => do
    let argExprs ← args.getElems.mapM fun a => `(`[RExpr| $a])
    `(Stmt.callStmt $(Lean.quote f.getId.toString) [$[$argExprs],*])
  | `(`[RStmt| return $e:term;]) =>
    `(Stmt.ret `[RExpr| $e])
  | `(`[RStmt| $arr:ident[$idx:term] := $val:term;]) =>
    `(Stmt.arrSet (Expr.var $(Lean.quote arr.getId.toString)) `[RExpr| $idx] `[RExpr| $val])
  | `(`[RStmt| $s $ss*]) =>
    `(Stmt.seq `[RStmt| $s] `[RStmt| $ss*])

end Radix
