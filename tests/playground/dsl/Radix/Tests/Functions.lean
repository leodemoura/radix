/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Function Tests

Function calls, recursion via fuel-based interpreter.
-/

namespace Radix.Tests

-- Simple function: double
def doubleProgram : Program := {
  funs := [
    { name := "double"
      params := [("x", .uint64)]
      retTy := .uint64
      body := `[RStmt| result := x + x; ] }
  ]
  main := `[RStmt|
    a := 5;
    double(a);
  ]
}

#guard (doubleProgram.run 10000).isOk

-- Factorial (iterative)
def factProgram : Program := {
  funs := [
    { name := "fact"
      params := [("n", .uint64)]
      retTy := .uint64
      body := `[RStmt|
        result := 1;
        i := 1;
        while (i <= n) {
          result := result * i;
          i := i + 1;
        }
      ] }
  ]
  main := `[RStmt|
    n := 5;
    fact(n);
  ]
}

#guard (factProgram.run 10000).isOk

-- Fibonacci (iterative)
def fibProgram : Program := {
  funs := [
    { name := "fib"
      params := [("n", .uint64)]
      retTy := .uint64
      body := `[RStmt|
        a := 0;
        b := 1;
        i := 0;
        while (i < n) {
          temp := b;
          b := a + b;
          a := temp;
          i := i + 1;
        }
        result := a;
      ] }
  ]
  main := `[RStmt|
    fib(10);
  ]
}

#guard (fibProgram.run 10000).isOk

-- Multiple function calls
def multiCallProgram : Program := {
  funs := [
    { name := "add"
      params := [("a", .uint64), ("b", .uint64)]
      retTy := .uint64
      body := `[RStmt| result := a + b; ] },
    { name := "square"
      params := [("x", .uint64)]
      retTy := .uint64
      body := `[RStmt| result := x * x; ] }
  ]
  main := `[RStmt|
    x := 3;
    y := 4;
    add(x, y);
    square(x);
  ]
}

#guard (multiCallProgram.run 10000).isOk

end Radix.Tests
