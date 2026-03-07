/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # Basic Tests

Arithmetic, variables, control flow.
-/

namespace Radix.Tests

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

-- Simple assignment and arithmetic
def test_assign := `[RStmt|
  x := 3;
  y := 5;
  z := x + y;
]

#guard getResult test_assign "z" == some (Value.uint64 8)

-- If-then-else
def test_ite := `[RStmt|
  x := 10;
  if (x < 20) {
    y := 1;
  } else {
    y := 0;
  }
]

#guard getResult test_ite "y" == some (Value.uint64 1)

-- While loop: compute 1 + 2 + ... + 10
def test_while := `[RStmt|
  sum := 0;
  i := 1;
  while (i <= 10) {
    sum := sum + i;
    i := i + 1;
  }
]

#guard getResult test_while "sum" == some (Value.uint64 55)

-- Nested if
def test_nested_if := `[RStmt|
  x := 5;
  if (x > 3) {
    if (x < 10) {
      y := 1;
    } else {
      y := 2;
    }
  } else {
    y := 3;
  }
]

#guard getResult test_nested_if "y" == some (Value.uint64 1)

-- Boolean operations
def test_bool := `[RStmt|
  a := true;
  b := false;
  c := a && b;
  d := a || b;
  e := !b;
]

#guard getResult test_bool "c" == some (Value.bool false)
#guard getResult test_bool "d" == some (Value.bool true)
#guard getResult test_bool "e" == some (Value.bool true)

-- Multiplication and modulo
def test_arith := `[RStmt|
  x := 7;
  y := 3;
  prod := x * y;
  rem := x % y;
]

#guard getResult test_arith "prod" == some (Value.uint64 21)
#guard getResult test_arith "rem" == some (Value.uint64 1)

-- Countdown loop
def test_countdown := `[RStmt|
  n := 10;
  while (n > 0) {
    n := n - 1;
  }
]

#guard getResult test_countdown "n" == some (Value.uint64 0)

-- Equality and inequality
def test_comparison := `[RStmt|
  x := 5;
  y := 5;
  eq := x == y;
  ne := x != y;
]

#guard getResult test_comparison "eq" == some (Value.bool true)
#guard getResult test_comparison "ne" == some (Value.bool false)

end Radix.Tests
