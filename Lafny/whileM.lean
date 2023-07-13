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

def new_while_loop_with_invariantM [Monad m] {State obsType Measure : Type _} [WellFoundedRelation Measure]
    (cond : State → obsType → Bool)
    (meas : State → Measure)
    (init : State)
    (obs : State → m obsType)
    (next : (state : State) → (x : obsType) → cond state x →
      m {newState // WellFoundedRelation.rel (meas newState) (meas state)})
    (rest : (state : State) → (x : obsType) → ¬ (cond state x) → m κ) :
    m κ  :=
  loop init
where
  loop : State → m κ
    | state => do
        let x ← (obs state)
        if h : cond state x then do
          let ⟨newState, _⟩ ← next state x h
          loop newState
        else
          rest state x h
    termination_by loop decreasing stateWithInv => meas stateWithInv

def newWhileExample (f : Nat → Nat) (hf : ∀ x, Even x → Even (f x)) (n : Nat) : IO {p : ℕ × ℕ // Even p.2 ∧ p.1 = 0} := do
  new_while_loop_with_invariantM
    (State := {p : ℕ × ℕ // Even p.2})
    (cond := fun p () => p.1.1 > 0)
    (meas := fun p => p.1.1)
    (init := ⟨(n, 0), by simp⟩)
    (next := fun ⟨p, inv_p⟩ obs p1_gt =>
      have p1_pos : 0 < p.1 := by simpa using p1_gt
      have : p.1 - 2 < p.1 := tsub_lt_self p1_pos (by simp)
      do
        IO.println s!"foo {p.2}"
        pure ⟨⟨(p.1 - 2, f p.2), hf _ inv_p⟩, this⟩)
    (obs := fun _ => pure ())
    (rest := fun state obs notcond => pure ⟨state, state.2,
      by simpa using notcond⟩)

def loop_with_invariantM [Monad m] {κ State Measure : Type _} [WellFoundedRelation Measure]
      (meas : State → Measure)
      (init : State)
      (next : (state : State) →
        m (κ ⊕ {newState // WellFoundedRelation.rel (meas newState) (meas state)})) :
    m κ  :=
  loop init
where
  loop : State → m κ
    | state => do
        match (← next state) with
          | Sum.inl val => pure val
          | Sum.inr ⟨newState, _⟩  =>
              loop newState
  termination_by loop decreasing stateWithInv => meas stateWithInv

def loop_with_invariant_contM [Monad m] {κ State Measure : Type _} [WellFoundedRelation Measure]
      (meas : State → Measure)
      (cont : (State → m κ) → m κ)
      (next : (state : State) →
        ((newState : State) → WellFoundedRelation.rel (meas newState) (meas state) → m κ) →
          m κ) :
    m κ :=
  cont loop
where
  loop : State → m κ
    | state => next state (fun state' _ => loop state')
  termination_by loop decreasing stateWithInv => meas stateWithInv

-- reality check: the first set of data gives rise to the second
example [Monad m] {κ State Measure : Type _} [WellFoundedRelation Measure]
      (meas : State → Measure)
      (next : (state : State) →
        m (κ ⊕ {newState // WellFoundedRelation.rel (meas newState) (meas state)})) :
    (state : State) →
      ((newState : State) → WellFoundedRelation.rel (meas newState) (meas state) → m κ) → m κ :=
fun state f => do
  match ← next state with
    | Sum.inl k => return k
    | Sum.inr ⟨newState, hrel⟩ => f newState hrel

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

class whileM (m : Type u → Type v) (β : Type _)
  (cond : β → Prop) where
  whileM : ((b : β) → cond b → m β) → m PUnit
