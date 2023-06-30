import Lafny.Util
import Mathlib.Data.Nat.Parity
open BigOperators
open Finset

def while_loop_with_invariantM [Monad m] {State Measure : Type _} [WellFoundedRelation Measure]
    (invariant : State → Prop)
    (cond : State → Prop)
    [DecidablePred cond]
    (meas : State → Measure)
    (init : {state : State // invariant state})
    (next : (state : State) → invariant state → cond state →
      m {newState // invariant newState ∧ WellFoundedRelation.rel (meas newState) (meas state)}) :
    m {state // invariant state ∧ ¬ cond state} :=
  loop init
where
  loop : {state : State // invariant state} → m {state // invariant state ∧ ¬ cond state}
    | ⟨state, invState⟩ =>
        if h : cond state then do
          let ⟨newState, nSinv, _⟩ ← next state invState h
          loop ⟨newState, nSinv⟩
        else
          pure ⟨state, invState, h⟩
    termination_by loop decreasing stateWithInv => meas stateWithInv.1

def whileExample' (f : ℕ → ℕ) (hf : ∀ x, Even x → Even (f x)) (n : ℕ) :
  IO {p : ℕ × ℕ // Even p.2 ∧ p.1 = 0} := do
  let ⟨p, even_p, npos_p⟩ ← while_loop_with_invariantM
    (invariant := fun p : ℕ × ℕ => Even p.2)
    (cond := fun p => 0 < p.1)
    (meas := fun p => p.1)
    (init := ⟨(n, 0), by simp⟩)
    (next := fun p inv_p p1_gt =>
      have p1_pos : 0 < p.1 := by simpa using p1_gt
      have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by simp)
      do
        IO.println s!"foo {p.2}"
        pure ⟨(p.1 - 2, f p.2), ⟨hf _ inv_p, this⟩⟩)
  have : p.1 = 0 := by simpa using npos_p
  pure ⟨p, even_p, this⟩



#eval whileExample' (fun n => 2 * n + 4) (fun n => by simp [parity_simps]) 12

-- forIn {β} [Monad m] (x : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β

#check ForIn

/-
x = 0
y = 10
inv  y > 0
while (x < 100) {
  y += 10
  while (x < 50) {
    z = 0
    z += 5
    y += 1
    x += 1
  }
  x += 1

}
-/

-- You can't do this to this is kinda fake state :/
-- Note: This is a nonissue I misunderstood how the looping works currently

def whileExample'' (n : ℕ) :
  IO {p : ℕ × ℕ × ℕ  // p.1 = 0 ∧ p.2.1 > 0 } := do
  let ⟨p, _, _⟩ ← while_loop_with_invariantM
    (invariant := fun p : ℕ × ℕ × ℕ => p.2.1 > 0)
    (cond := fun p => p.1 < 100)
    (meas := fun p => p.1)
    (init := ⟨(n, 10, 0), by simp⟩)
    (next := fun p inv_p p1_gt =>
      -- have p1_pos : 0 < p.1 := by _
      -- have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by simp)
      do
        IO.println s!"foo {p.2}"
        let mut bar := 10
        let ⟨q, _, _⟩ ← while_loop_with_invariantM
          (invariant := fun p : Nat => True)
          (cond := fun p => p < 50)
          (meas := fun p => p)
          (init := ⟨0, by trivial⟩)
          (next := fun p _ _ => do
            IO.println s!"y: {p.2.1} z: {p.2.2}"
            bar ← bar + 10
            return ⟨p + 1, by sorry⟩)
        return ⟨(p.1 + 1, q + 10, q), by sorry⟩)
  return ⟨p, sorry⟩


-- #eval whileExample'' 5