import Lafny.Util

inductive LoopState (State : Type)
| Yield : State → LoopState State
| Done :  State → LoopState State


open LoopState

-- def proj (L : LoopState State ) :=
--   match L with
--   | Yield s => s
--   | Done s => s
  
def loop_with_invariant_ER {State : Type _}
      (invariant : (LoopState State) → Prop)
      (init : {state // invariant state})
      (next : ∀ state, invariant state → {new_state // invariant new_state})
      (n : Nat) :
    { state // invariant state } :=
  have : n + 0 = n ∧ invariant init := by
    constructor
    . rw [add_zero]
    . exact init.2
  go n 0 init this
where
  go : (b : Nat) → (i : Nat) → (state : LoopState State) →
      (hinv : b + i = n ∧ invariant state) → { state // invariant state }
  | 0,       i, state, hinv => by
    use state
    exact hinv.2
  | (b+1), i, (Yield state), hinv => 
    go b (i+1) (next (Yield state) hinv.2) {
      left := by
        rw [add_comm i, ←add_assoc, hinv.1]
      right := by
        exact (next (Yield state) hinv.2).2
    }
  | (b+1), i, (Done state), hinv => by
    use Done state
    exact hinv.2
    
def foo' := Id.run do
  let mut x := 0
  while x < 5 do
    x := x + 1
  return x

#print foo'

#check forIn

#check Lean.Loop.mk