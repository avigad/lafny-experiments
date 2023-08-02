import Lafny.Do
open Mathlib.Tactic.Do

#eval show IO _ from withDoElemRef.set withDoElemCore

def foo : IO Nat := do' 
  let mut x := 5
  let mut inv : x < 6 := by decide
  let h ← loop' (label := foo)
    x := x - 1
    inv : x < 6 := by decide
    if (x < 2) then
      break' (label := foo) inv
  termination_by x
  decreasing_by simp

    
  return 1

def bar : IO Nat := do'
  let xs := [1, 2, 3]
  let mut sum := 0
  let h ← for'' x in xs // inv : sum < 5 := by decide do
    IO.println x
    sum := sum + 1
    holds_by s x => by sorry