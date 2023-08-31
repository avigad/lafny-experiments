import Lafny.whileM

def initArray (A : Array Nat) (d : Nat) :
    {B : Array Nat // B.size = A.size ∧ ∀ i < B.size, B[i]'(by sorry) = d} := Id.run do
  let κ ← loop_blockM
    (meas := fun ⟨⟨i, A⟩, _⟩ => A.size - i)
    (init := (⟨⟨0, A⟩, sorry⟩ : {p : Nat × Array Nat // p.2.size = A.size ∧ p.1 ≤ p.2.size ∧ ∀ i < p.1, (p.2[i]'(sorry)) = d}))
    (next := fun ⟨⟨i, A⟩, hA⟩ => Id.run do
      if hi : i = A.size then
        return Sum.inl ⟨A, by
          simp
          simp at hA
          constructor
          · exact hA.1
          · intro i hi'
            sorry⟩
      else
        let A' := A.set ⟨i, sorry⟩ d
        return Sum.inr ⟨⟨⟨i+1, A'⟩, sorry⟩, sorry⟩
    
    )
  return κ

#check initArray #[1, 2, 3] 5
#eval initArray #[1, 2, 3] 5
