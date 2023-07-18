import Lafny.whileM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm

open List Sorted
#check List.set
def swap (A : List Nat) (i₁ i₂ : Fin A.length) : {B : List Nat // Perm A B ∧ ∀ i < B.length, i ≠ i₁ → i ≠ i₂ → A[i]'(sorry) = B[i]'(sorry)} :=
  let v₁ := A[i₁]
  let v₂ := A[i₂]

  ⟨(A.set i₂ v₁).set i₁ v₂, by 
    constructor
    · sorry
    · intro i hi1 hi2 hi3
      simp at hi1
      sorry⟩

#eval swap [1, 2, 3, 4, 5] ⟨2, sorry⟩ ⟨3, sorry⟩

def findMinIdxLeft (L : List Nat) (i : Fin L.length) : {idx // i ≤ idx ∧  ∀ (jdx : Fin L.length), i ≤ jdx → L[idx]'(sorry) ≤ L[jdx]} := Id.run do
  let κ ← loop_blockM
    (meas := fun ⟨⟨j, minIdx⟩, _⟩ => L.length - j)
    (init := (⟨(i, i), sorry⟩ : {p : Nat × Nat // i ≤ p.2 ∧ ∀ (jdx : Fin L.length), i ≤ jdx → jdx ≤ p.1 → L[p.2]'(by sorry) ≤ L[jdx]}))
    (next := fun ⟨⟨j, minIdx⟩, hi⟩ =>
      if h : (j ≥ L.length) then
        Sum.inl ⟨⟨minIdx, sorry⟩, by
          constructor
          · exact hi.1
          · intro jdx hjdx
            exact (hi.2) jdx hjdx (sorry)⟩
      else
        if h' : L[j]'(by sorry) < L[minIdx]'(by sorry) then
          Sum.inr ⟨⟨⟨j+1, j⟩, sorry⟩, sorry⟩
        else 
          Sum.inr ⟨⟨⟨j+1, minIdx⟩, sorry⟩, sorry⟩)
  
  return κ 

#eval findMinIdxLeft [5, 3, 0, 2, 1, 4] ⟨3, sorry⟩

def selectionSort(A : List Nat) : {B : List Nat // Perm A B ∧ Sorted Nat.lt B} := Id.run do
  let κ ← loop_blockM
    (meas := fun ⟨⟨i, L⟩, _⟩ => L.length - i)
    (init := (⟨⟨0, A⟩, sorry⟩ : {p : Nat × (List Nat) // Perm A p.2 ∧ ∀ i < p.1, ∀ j ≤ i, p.2[j]'(by sorry) ≤ p.2[i]'(by sorry)} ))
    (next := fun ⟨⟨i, B⟩, hB⟩ =>
      if h : i ≥ A.length then
        return Sum.inl ⟨B, sorry⟩
      else
        let ⟨⟨minIdx, _⟩, _⟩ := findMinIdxLeft B ⟨i, sorry⟩
        let B := swap B ⟨i, sorry⟩ ⟨minIdx, sorry⟩
        return Sum.inr ⟨⟨⟨i+1, B⟩, sorry⟩, sorry⟩
    )

  return κ

#eval selectionSort [5, 3, 0, 2, 1, 4]
