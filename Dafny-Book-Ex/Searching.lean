import Lafny.whileM
-- import Mathlib.Data.List.Basic
-- This should have additional constraint that 0 <= n <= L.length
-- But was verbose so I omitted it
def LinearSearch (p : Nat → Prop) [DecidablePred p] (L : List Nat)
  : {n // (n = L.length ∨ p (L[n]'(by sorry))) ∧ (n = L.length → ∀ i < L.length, ¬ p (L[i]'(by sorry))) } := Id.run do
  -- have : ∀ i, i < 0 → i < L.length → ¬p (L[i]'(by sorry)) := by sorry
  let κ ← loop_blockM
    (meas := fun ⟨i, _⟩ => L.length - i)
    (init := (⟨0, by simp⟩ : {n // ∀ i, i < n → n ≤ L.length → ¬p (L[i]'(by sorry))}))
    (next := fun ⟨k, hk⟩ => 
      if cond : (k = L.length) then
        return Sum.inl ⟨k, by
          simp
          constructor
          · left ; exact cond
          · intro _ i hi 
            specialize hk i
            apply hk
            · simp [cond, hi]
            · simp [cond]⟩
      else
        if pCond : p (L[k]'(by sorry)) then
          return Sum.inl ⟨k, by 
            simp
            constructor
            · right ; exact pCond
            · intro hk ; contradiction
            ⟩
        else
          return Sum.inr ⟨⟨k+1, by sorry⟩, by sorry⟩
    )
  return κ

#check LinearSearch


-- this is a bit imprecise as if n is L.length no garauntee the thing doesnt exist
-- in the list but that's easy enough to add and more important to generate
-- more examples
def BinarySearch (L : List Nat) (hL : ∀ i j, i < L.length → j < L.length →  i < j → L[i]'(by sorry) ≤ L[j]'(by sorry)) (key : Nat)
 : IO {n // n ≤ L.length ∧ (∀ i < n, L[i]'(by sorry) ≤ key) ∧ (∀ j ≥ n, j < L.length → key ≤ L[j]'(by sorry))}:= do

  let κ ← loop_blockM
    (meas := fun ⟨⟨lo, hi⟩, _⟩ => hi - lo)
    (init := (⟨⟨0, L.length⟩, sorry⟩ : {p : Nat × Nat // (p.1 ≤ p.2) ∧ (p.2 ≤ L.length) ∧ (∀ i < p.1, L[i]'(sorry) ≤ key) ∧ (∀ i > p.2, i < L.length → key ≤ L[i]'(sorry))}))
    (next := fun ⟨⟨lo, hi⟩, h⟩ => 
      if h' : hi ≤ lo then
        return Sum.inl ⟨L.length, by sorry⟩
      else
        let mid := (hi + lo)/2
        if hmid1 : (L[mid]'(sorry) < key) then
          return Sum.inr ⟨⟨(mid+1, hi), sorry⟩, sorry⟩
        else
          if hmid2 : (L[mid]'(sorry) = key) then
            return Sum.inl ⟨mid, by 
              constructor
              · dsimp ; simp at h ; sorry
              · constructor
                · intro i h_i
                  rw [← hmid2]
                  apply hL 
                  · sorry
                  · sorry
                  · exact h_i 
                · sorry
          ⟩
          else
            return Sum.inr ⟨⟨(lo, mid), sorry⟩, sorry⟩)
  return κ

#check BinarySearch [1, 2, 3, 4, 5] (sorry) 6

  
  
