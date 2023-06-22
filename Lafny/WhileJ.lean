import Lafny.Util
import Mathlib.Data.Nat.Parity
open BigOperators
open Finset

/-
Question: should the condition be a Boolean or a decidable Prop?

Note: I think decidable prop just based off that's what everything else does
-/

def while_loop_with_invariant {State Measure : Type _} [WellFoundedRelation Measure]
      (invariant : State → Prop)
      (cond : State → Bool)
      (meas : State → Measure)
      (init : {state : State // invariant state})
      (next : (state : State) → invariant state → cond state = true →
        {newState // invariant newState ∧ WellFoundedRelation.rel (meas newState) (meas state)}) :
    {state // invariant state ∧ cond state = false} :=
  loop init
where
  loop : {state : State // invariant state} → {state // invariant state ∧ cond state = false}
    | ⟨state, invState⟩ =>
        match h : cond state with
          | true  =>
              let ⟨newState, inv_newState, _⟩ := next state invState h
              loop ⟨newState, inv_newState⟩
          | false => ⟨state, invState, h⟩
    termination_by loop decreasing stateWithInv => meas stateWithInv.1

/-
This example represents:

  let mut x := n
  let mut y := 0
  while x > 0 do
    x := x - 2
    y := f y

with the invariant Even y.
-/

def whileExample (f : ℕ → ℕ) (hf : ∀ x, Even x → Even (f x)) (n : ℕ) :
    {p : ℕ × ℕ // Even p.2 ∧ p.1 = 0} :=
  let ⟨p, even_p, npos_p⟩ := while_loop_with_invariant
    (invariant := fun p : ℕ × ℕ => Even p.2)
    (cond := fun p => 0 < p.1)
    (meas := fun p => p.1)
    (init := ⟨(n, 0), by norm_num⟩)
    (next := fun p inv_p p1_gt =>
      have p1_pos : 0 < p.1 := by simpa using p1_gt
      have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by norm_num)
      ⟨(p.1 - 2, f p.2), ⟨hf _ inv_p, this⟩⟩)
  have : p.1 = 0 := by simpa using npos_p
  ⟨p, even_p, this⟩

#eval whileExample (fun n => 2 * n + 4) (fun n => by simp [parity_simps]) 12


open WellFoundedRelation

def while_loop_with_invariant' {State Measure : Type _} [WellFoundedRelation Measure]
      (invariant : State → Prop)
      (cond : State → Prop)
      [DecidablePred cond]
      (meas : State → Measure)
      (init : {state : State // invariant state})
      (next : (state : State) → invariant state → cond state →
        {newState // invariant newState ∧ WellFoundedRelation.rel (meas newState) (meas state)}) :
    {state // invariant state ∧ ¬ cond state} :=
  loop init
where
  loop : {state : State // invariant state} → {state // invariant state ∧ ¬ cond state}
    | ⟨state, invState⟩ =>
        if h : cond state then 
          let ⟨newState, inv_newState, _⟩ := next state invState h
          loop ⟨newState, inv_newState⟩
        else
          ⟨state, invState, h⟩
    termination_by loop decreasing stateWithInv => meas stateWithInv.1

def whileExample' (f : ℕ → ℕ) (hf : ∀ x, Even x → Even (f x)) (n : ℕ) :
    {p : ℕ × ℕ // Even p.2 ∧ p.1 = 0} :=
  let ⟨p, even_p, npos_p⟩ := while_loop_with_invariant'
    (invariant := fun p : ℕ × ℕ => Even p.2)
    (cond := fun p => 0 < p.1)
    (meas := fun p => p.1)
    (init := ⟨(n, 0), by norm_num⟩)
    (next := fun p inv_p p1_gt =>
      have p1_pos : 0 < p.1 := by simpa using p1_gt
      have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by norm_num)
      ⟨(p.1 - 2, f p.2), ⟨hf _ inv_p, this⟩⟩)
  have : p.1 = 0 := by simpa using npos_p
  ⟨p, even_p, this⟩
