import Lafny.whileM

def ex : {x // x = 102} := Id.run do
  let κ ← loop_blockM 
    (meas := fun ⟨x, _⟩ => 100 - x)
    (init  := (⟨0, by simp⟩ : {s // s % 3 = 0 ∧ s < 105}))
    (next := fun ⟨s, hs⟩ => do 
      if h : (s < 100) then
        return Sum.inr ⟨⟨s+3, sorry⟩, by sorry⟩
      else
        return Sum.inl ⟨s, sorry⟩)
        
  return κ
