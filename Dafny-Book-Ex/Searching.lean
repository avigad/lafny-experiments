import Lafny.whileM

-- This should have additional constraint that 0 <= n <= L.length
-- But that was way too verbose so I omitted it
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



