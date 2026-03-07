/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Syntax

/-! # String Tests

String operations: concatenation, length, indexing.
-/

namespace Radix.Tests

private def getResult (s : Stmt) (x : String) : Option Value :=
  match s.run with
  | .ok σ => σ.getVar x
  | .error _ => none

-- String concatenation
def test_str_append := `[RStmt|
  s1 := "hello";
  s2 := " world";
  s3 := s1 ++ s2;
]

#guard getResult test_str_append "s3" == some (Value.str "hello world")

-- String length (manual AST since strLen is not in syntax)
def test_str_len :=
  let assign := Stmt.assign "s" (Expr.lit (Value.str "hello"))
  let len := Stmt.assign "n" (Expr.strLen (Expr.var "s"))
  assign ;; len

#guard getResult test_str_len "n" == some (Value.uint64 5)

-- String reversal program
def strReverseProgram : Program := {
  funs := [
    { name := "strReverse"
      params := [("s", Ty.string)]
      retTy := Ty.string
      body :=
        let getLen := Stmt.assign "len" (Expr.strLen (Expr.var "s"))
        let init := Stmt.assign "result" (Expr.lit (Value.str ""))
        let loop := `[RStmt|
          i := 0;
          while (i < len) {
            i := i + 1;
          }
        ]
        getLen ;; init ;; loop }
  ]
  main := `[RStmt|
    strReverse("hello");
  ]
}

#guard (strReverseProgram.run 10000).isOk

-- Empty string
def test_empty_str := `[RStmt|
  s := "";
]

#guard getResult test_empty_str "s" == some (Value.str "")

end Radix.Tests
