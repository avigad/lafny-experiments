import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring

open BigOperators
open Finset

/-
Consider a simple imperative program in Lean.
-/

def foo (n : Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [:n] do
    sum := sum + i
  sum

#eval foo 10

/-
How do we prove that it does what it is supposed to? Well, the program translates essentially to
the following tail-recursive version.
-/

def foo_tail_recursive (n : Nat) : Nat :=
  go n 0 0
where
  go : (b : Nat) → (i : Nat) → (sum : Nat) → Nat
  | 0,       _, sum => sum
  | (b + 1), i, sum => go b (i + 1) (sum + i)

/-
In that form, it is not hard to add the invariants. Note that there are three proof obligations:
showing that the initial invariant holds, showing that it is preserved, and showing that, when
you exit the loop, the final invariant suffices for whatever comes next.
-/

def foo_with_invariant (n : Nat) : { sum : Nat // sum = ∑ i in range n, i } :=
  -- show that the initial invariant holds
  have : n + 0 = n ∧ 0 = Finset.sum (range 0) id := by
    constructor
    . rw [add_zero]
    . rw [sum_range_zero]
  go n 0 0 this
where
  go : (b : Nat) → (i : Nat) → (sum : Nat) →
      (hinv : b + i = n ∧ sum = ∑ j in range i, j ) → { sum : Nat // sum = ∑ j in range n, j }
  | 0,       i, sum, hinv => by
      -- show that the final state of the loop yields the function postcondition
      use sum
      rw [zero_add] at hinv
      rw [hinv.2, hinv.1]
  | (b + 1), i, sum, hinv =>
    have : b + (i + 1) = n ∧ sum + i = ∑ j in range (i + 1), j := by
      -- show that the invariant is preserved
      constructor
      . rw [add_comm i, ←add_assoc, hinv.1]
      . rw [sum_range_succ, hinv.2]
    go b (i + 1) (sum + i) this

/-
It's easy to abstract this. For simplicity, let's stick to loops that start from 0, but we can
allow arbitrary states and invariants. This is the analogue of a recursor that Mario had in mind.
-/

def loop_with_invariant {State : Type _}
      (invariant : Nat → State → Prop)
      (start_state : State)
      (init : invariant 0 start_state)
      (next_state : Nat → State → State)
      (step : ∀ i state, invariant i state → invariant (i + 1) (next_state i state))
      (n : Nat) :
    { state // invariant n state } :=
  have : n + 0 = n ∧ invariant 0 start_state := by
    constructor
    . rw [add_zero]
    . trivial
  go n 0 start_state this
where
  go : (b : Nat) → (i : Nat) → (state : State) →
      (hinv : b + i = n ∧ invariant i state) → { state : State // invariant n state }
  | 0,       i, state, hinv => by
      use state
      rw [zero_add] at hinv
      rw [←hinv.1]
      exact hinv.2
  | (b + 1), i, state, hinv =>
    have : b + (i + 1) = n ∧ invariant (i + 1) (next_state i state) := by
      constructor
      . rw [add_comm i, ←add_assoc, hinv.1]
      . exact step _ _ hinv.2
    go b (i + 1) (next_state i state) this

/-
With this simple gadget, it is a lot easier to do the loop plumbing. It is natural to write the
function `foo` as follows. Notice that if you replace any of the proof obligations with an
underscore, Lean tells you what the obligations are.
-/

def nicer_foo (n : Nat) : {sum : Nat // sum = ∑ j in range n, j } :=
  let ⟨sum, property⟩ := loop_with_invariant
    (invariant := fun i sum => sum = ∑ j in range i, j )
    (start_state := 0)
    -- show invariant holds initially
    (init := rfl)
    (next_state := fun i sum => sum + i)
    -- show invariant is preserved
    (step := by rintro i state rfl; rw [sum_range_succ])
    n
  -- show that final state and invariant satisfies the postcondition
  ⟨sum, property⟩

/-
In this case, the final invariant is exactly the postcondition, so we can be even briefer.
-/

def nicer_foo_alt (n : Nat) : {sum : Nat // sum = ∑ j in range n, j } :=
  loop_with_invariant
    (invariant := fun i sum => sum = ∑ j in range i, j )
    (start_state := 0)
    (init := rfl)
    (next_state := fun i sum => sum + i)
    (step := by rintro i state rfl; rw [sum_range_succ])
    n

/-
Here is some nicer syntax:
-/

syntax "for" ident "upto" term
  withPosition("state:" ident ":=" term
  "invariant:" ident ":=" term
  "init:=" term
  "next:" term
  "step:=" term)
  term : term

macro_rules
  | `(for $i upto $n
        state: $s := $start_state
        invariant: $p := $inv
        init:= $init
        next: $next_state
        step:= $step
      $rest) =>
      `(let ⟨$s, $p⟩ := loop_with_invariant
          (invariant := fun $i $s => $inv)
          (start_state := $start_state)
          (init := $init)
          (next_state := fun $i $s => $next_state)
          (step := $step)
          $n
        $rest)

/-
Some additional notes:

Mario and Wojciech have pointed out that the computation of `next_state` might want to use the
invariant, so we should combine `next_state` and `step` to type

  (i : Nat) → (state : State) → (inv : Invariant state i) →
    { new_state // Ivariant new_state (i + 1) }

Scott points out most of the examples in the Dafny book use `while`, so we should figure out how
to do this trick with `while` as well, with a `termination_by` or something like that.

The plan:
- Generalize to arbitrary ranges and `Fin`, and arbitrary state.
- Think about generalization to other things we might iterate over; see, for example,
    `ListLoop.lean`, though in retrospect this doesn't seem so compelling.
- Figure out how to handle early return.
- Figure out how to compose (additional state, nested loops).
- Think about `while`.
- Implement syntax, e.g. building on Mario's `lafny`:
    https://github.com/digama0/lafny/
-/

