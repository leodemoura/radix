/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Radix Examples

Executable programs demonstrating the DSL syntax and fuel-based interpreter.
Each example uses `#eval!` to run the program and display the result.
-/

namespace Radix

/-- Display a Radix value in readable format. -/
def Value.display : Value → String
  | .uint64 n => toString n
  | .bool b   => toString b
  | .unit     => "()"
  | .str s    => s!"\"{s}\""
  | .addr a   => s!"<addr {a}>"

end Radix

namespace Radix.Examples

/-- Run a statement and display the value of variable `x`. -/
private def run (s : Stmt) (x : String) : String :=
  match s.run with
  | .ok σ => match σ.getVar x with
    | some v => v.display
    | none => s!"variable '{x}' not found"
  | .error msg => s!"error: {msg}"

/-- Run a program and display the value of variable `x`. -/
private def runProg (p : Program) (x : String) : String :=
  match p.run with
  | .ok σ => match σ.getVar x with
    | some v => v.display
    | none => s!"variable '{x}' not found"
  | .error msg => s!"error: {msg}"

/-! ## Factorial (iterative) -/

def factorial := `[RStmt|
  n := 12;
  result := 1;
  while (n > 0) {
    result := result * n;
    n := n - 1;
  }
]

#eval! run factorial "result"
-- 479001600

/-! ## Fibonacci -/

def fibonacci := `[RStmt|
  a := 0;
  b := 1;
  i := 0;
  while (i < 20) {
    tmp := b;
    b := a + b;
    a := tmp;
    i := i + 1;
  }
]

#eval! run fibonacci "a"
-- 6765

/-! ## Collatz Conjecture

Starting at 27, count steps to reach 1. -/

def collatz := `[RStmt|
  n := 27;
  steps := 0;
  while (n != 1) {
    if (n % 2 == 0) {
      n := n / 2;
    } else {
      n := n * 3 + 1;
    }
    steps := steps + 1;
  }
]

#eval! run collatz "steps"
-- 111

/-! ## FizzBuzz -/

def fizzbuzz := `[RStmt|
  result := "";
  i := 1;
  while (i <= 15) {
    if (i % 15 == 0) {
      result := result ++ "FizzBuzz ";
    } else {
      if (i % 3 == 0) {
        result := result ++ "Fizz ";
      } else {
        if (i % 5 == 0) {
          result := result ++ "Buzz ";
        } else {
          result := result ++ ". ";
        }
      }
    }
    i := i + 1;
  }
]

#eval! run fizzbuzz "result"

/-! ## Array: Sum of Squares

Allocate an array, fill with 1²..10², compute the sum.
Array operations (`alloc`, `arrGet`, `arrSet`, `free`) use raw AST
constructors; arithmetic uses `\`[RExpr| ...]` syntax. -/

def sumOfSquares : Stmt :=
  Stmt.alloc "arr" (.array .uint64) (.lit (.uint64 10)) ;;
  `[RStmt| i := 0; ] ;;
  Stmt.while `[RExpr| i < 10]
    (Stmt.arrSet (.var "arr") (.var "i") `[RExpr| (i + 1) * (i + 1)] ;;
     `[RStmt| i := i + 1; ]) ;;
  `[RStmt| sum := 0; i := 0; ] ;;
  Stmt.while `[RExpr| i < 10]
    (Stmt.assign "sum" (.binop .add (.var "sum") (.arrGet (.var "arr") (.var "i"))) ;;
     `[RStmt| i := i + 1; ]) ;;
  Stmt.free (.var "arr")

#eval! run sumOfSquares "sum"
-- 385

/-! ## Bubble Sort

Sort [5, 3, 8, 1, 9, 2, 7, 4, 6, 0] in-place on a heap-allocated array. -/

def bubbleSort : Stmt :=
  Stmt.alloc "arr" (.array .uint64) (.lit (.uint64 10)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 0)) (.lit (.uint64 5)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 1)) (.lit (.uint64 3)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 2)) (.lit (.uint64 8)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 3)) (.lit (.uint64 1)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 4)) (.lit (.uint64 9)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 5)) (.lit (.uint64 2)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 6)) (.lit (.uint64 7)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 7)) (.lit (.uint64 4)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 8)) (.lit (.uint64 6)) ;;
  Stmt.arrSet (.var "arr") (.lit (.uint64 9)) (.lit (.uint64 0)) ;;
  `[RStmt| i := 0; ] ;;
  Stmt.while `[RExpr| i < 9]
    (`[RStmt| j := 0; ] ;;
     Stmt.while (.binop .lt (.var "j") (.binop .sub (.lit (.uint64 9)) (.var "i")))
       (Stmt.assign "a" (.arrGet (.var "arr") (.var "j")) ;;
        Stmt.assign "b" (.arrGet (.var "arr") (.binop .add (.var "j") (.lit (.uint64 1)))) ;;
        Stmt.ite (.binop .gt (.var "a") (.var "b"))
          (Stmt.arrSet (.var "arr") (.var "j") (.var "b") ;;
           Stmt.arrSet (.var "arr") (.binop .add (.var "j") (.lit (.uint64 1))) (.var "a"))
          Stmt.skip ;;
        `[RStmt| j := j + 1; ]) ;;
     `[RStmt| i := i + 1; ]) ;;
  Stmt.assign "first" (.arrGet (.var "arr") (.lit (.uint64 0))) ;;
  Stmt.assign "last" (.arrGet (.var "arr") (.lit (.uint64 9)))

#eval! run bubbleSort "first"  -- 0
#eval! run bubbleSort "last"   -- 9

/-! ## Function Call: Zero an Array

Demonstrates heap communication between caller and callee.
The function `zeroOut` receives an array address and zeros its elements
through the shared heap. -/

def zeroArray : Program := {
  funs := [
    { name := "zeroOut"
      params := [("a", .array .uint64), ("n", .uint64)]
      retTy := .unit
      body :=
        `[RStmt| i := 0; ] ;;
        Stmt.while `[RExpr| i < n]
          (Stmt.arrSet (.var "a") (.var "i") (.lit (.uint64 0)) ;;
           `[RStmt| i := i + 1; ])
    }
  ]
  main :=
    Stmt.alloc "arr" (.array .uint64) (.lit (.uint64 3)) ;;
    Stmt.arrSet (.var "arr") (.lit (.uint64 0)) (.lit (.uint64 10)) ;;
    Stmt.arrSet (.var "arr") (.lit (.uint64 1)) (.lit (.uint64 20)) ;;
    Stmt.arrSet (.var "arr") (.lit (.uint64 2)) (.lit (.uint64 30)) ;;
    `[RStmt| zeroOut(arr, 3); ] ;;
    Stmt.assign "val" (.arrGet (.var "arr") (.lit (.uint64 0)))
}

#eval! runProg zeroArray "val"
-- 0 (was 10 before the function call)

end Radix.Examples
