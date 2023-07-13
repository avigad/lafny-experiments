import Lafny.whileM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm

open List Sorted


def selectionSort (L : List Nat) : {L' // Perm L L' ∧ (Sorted Nat.lt L')} := Id.run do
  have : Sorted Nat.lt (L.take 0) := by simp
  let κ ← loop_blockM 
    (meas := fun ((i, L'), _) => L.length - i)
    (init := ⟨⟨0, L⟩, this⟩)
    (next := fun ((i, L'), hL') => 
      if (i == L.length) then
        have : Perm L L' ∧ Sorted Nat.lt L' := by sorry
        return Sum.inl ⟨L', this⟩ 
      else
        let L₁[i] :=  
        return Sum.inr ⟨⟨i+1, L'.swap
    
    )
  return κ 
