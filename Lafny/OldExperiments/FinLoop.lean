import Lafny.Util
open BigOperators
open Finset

def fin_loop_with_invariant {State : Type _}
      (n : Nat)
      (invariant : Fin n.succ → State → Prop)
      (init : {s : State // invariant 0 s})
      (next : (i : Fin n) → (state : State) → (inv : invariant (Fin.castSucc i) state) → {new_state // invariant (Fin.succ i) new_state}) :
    { state // invariant (n : Fin n.succ) state } :=
    Fin.induction h0 ih n
    where
    h0 : {state // invariant 0 state} := by 
      exact init
    ih := by
      intro i s1
      specialize next i s1
      apply next
      exact s1.2

#eval fin_loop_with_invariant
    (n := 10)
    (invariant := fun i sum => sum = ∑ j in range i, j )
    (init := ⟨0, by simp⟩)
    (next := fun i s inv => ⟨s + i, by
      simp [sum_range_succ]
      exact inv⟩)

