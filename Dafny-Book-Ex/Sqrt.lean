import Lafny.whileM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
def sqrt (N : Nat) : {r // r * r ≤ N ∧ N < (r+1)*(r+1)} := Id.run do
  let mut r := 0
  let (κ : {r // r * r ≤ N ∧ N < (r+1)*(r+1)}) ← loop_blockM
    (meas := fun ⟨r, _⟩ => N - r*r)
    (init := (⟨r, by simp⟩ : {r // 0 ≤ r ∧ r*r ≤ N}))
    (next := fun ⟨r, hr⟩ => do
      if h : (r + 1)*(r + 1) ≤ N then
        have : r *r < (r+1) *(r+1) := by ring_nf; simp
        have : N - (r + 1) * (r + 1) < N - r * r := by 
          -- N is not 0 by h
          -- N - (r+1)(r+1) >= 0 by h
          -- N - r*r > 0
          -- N - (r+1)(r+1) < N - r*r
          sorry

        return Sum.inr ⟨⟨r+1, by simp [h]⟩, by simp ; decreasing_tactic⟩
      else
        return Sum.inl (by 
          use r 
          constructor
          · exact hr.2
          · simp at h ; exact h
        )
    )
  return κ

#eval sqrt 25
#check sqrt 25