/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Array Tests

Allocation, indexing, modification, free.
-/

namespace Radix.Tests

-- Allocate, write, read
def test_array_basic :=
  let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.lit (Value.uint64 5))
  let set0 := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 0)) (Expr.lit (Value.uint64 42))
  let set1 := Stmt.arrSet (Expr.var "arr") (Expr.lit (Value.uint64 1)) (Expr.lit (Value.uint64 99))
  let read := Stmt.assign "val" (Expr.arrGet (Expr.var "arr") (Expr.lit (Value.uint64 0)))
  let free := Stmt.free (Expr.var "arr")
  alloc ;; set0 ;; set1 ;; read ;; free

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

#guard getResult test_array_basic "val" == some (Value.uint64 42)

-- Array sum using manual AST (since RExpr doesn't support arr[i] reads)
def arraySumProgram : Program := {
  funs := [
    { name := "arraySum"
      params := [("n", Ty.uint64)]
      retTy := Ty.uint64
      body :=
        let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.var "n")
        let fill := `[RStmt|
          i := 0;
          while (i < n) {
            arr[i] := i + 1;
            i := i + 1;
          }
        ]
        let sumLoop :=
          let init1 := Stmt.assign "total" (Expr.lit (Value.uint64 0))
          let init2 := Stmt.assign "j" (Expr.lit (Value.uint64 0))
          let readJ := Stmt.assign "elem" (Expr.arrGet (Expr.var "arr") (Expr.var "j"))
          let addElem := Stmt.assign "total" (Expr.binop BinOp.add (Expr.var "total") (Expr.var "elem"))
          let incJ := Stmt.assign "j" (Expr.binop BinOp.add (Expr.var "j") (Expr.lit (Value.uint64 1)))
          let body := readJ ;; addElem ;; incJ
          let cond := Expr.binop BinOp.lt (Expr.var "j") (Expr.var "n")
          init1 ;; init2 ;; Stmt.while cond body
        let free := Stmt.free (Expr.var "arr")
        alloc ;; fill ;; sumLoop ;; free }
  ]
  main := `[RStmt| arraySum(10); ]
}

#guard (arraySumProgram.run 10000).isOk

-- Bubble sort (simplified — just tests alloc/fill/free cycle)
def bubbleSortProgram : Program := {
  funs := [
    { name := "bubbleSort"
      params := [("n", Ty.uint64)]
      retTy := Ty.unit
      body :=
        let alloc := Stmt.alloc "arr" Ty.uint64 (Expr.var "n")
        let fill := `[RStmt|
          k := 0;
          while (k < n) {
            arr[k] := n - k;
            k := k + 1;
          }
        ]
        let free := Stmt.free (Expr.var "arr")
        alloc ;; fill ;; free }
  ]
  main := `[RStmt| bubbleSort(5); ]
}

#guard (bubbleSortProgram.run 10000).isOk

end Radix.Tests
