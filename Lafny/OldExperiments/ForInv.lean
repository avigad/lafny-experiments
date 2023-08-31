import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Basic
import Std.Data.List.Lemmas
import Lafny.OldExperiments.Util 

#check forM
-- this mirrors what's in the do unchained paper, not 100% sure 
-- how it's relevant yet, but I think it's good to have around.
def myForM_forIn {β : Type _}
    (invariant : β → Prop)
    [Monad m] [ForM (StateT {st : β // invariant st} (ExceptT {st : β // invariant st} m)) ρ α]
    (container : ρ) 
    (init : {state // invariant state})
    (next : α → {state // invariant state} → m (ForInStep ({newState // invariant newState})))
    : m { res : β // invariant res} := do
  let g a (p : {st : β // invariant st}) := ExceptT.mk do
    match ← next a p with
      | .yield ⟨b', hinv'⟩ => pure (Except.ok (⟨⟩ , ⟨b', hinv'⟩))
      | .done ⟨b', hinv'⟩ => pure (Except.error (⟨b', hinv'⟩))

  match ← forM (m := StateT {st : β // invariant st} (ExceptT {st : β // invariant st} m)) (α := α) container g |>.run init |>.run with
  | .ok a => pure a.2
  | .error a => pure a


class Container (α : outParam (Type u)) (γ : Type v) extends Membership α γ where
  /-- Superset of the membership type class that requires a length -/
  size : γ → Nat

instance : Container α (List α) where
  size := List.length

instance : Container α (Finset α) where
  size := Finset.card

instance : Container α (Option α) where
  size := fun optx =>
    match optx with
    | none => 0
    | (some _) => 1


-- in theory this might be it, just put some fancy syntax around it.
-- I need to read Metaprogramming in Lean to figure out what to do next
-- here, but this is a very large step I think. 

class ForInv (m : Type u₁ → Type u₂) (α : outParam (Type u)) (ρ : Type v) where
  /-- `forIn x b f : m β` runs a for-loop in the monad `m` with additional state `β`.
  This traverses over the "contents" of `x`, and passes the elements `a : α` to
  `f : α → β → m (ForInStep β)`. `b : β` is the initial state, and the return value
  of `f` is the new state as well as a directive `.done` or `.yield`
  which indicates whether to abort early or continue iteration.

  The expression
  ```
  let mut b := ...
  for x in xs do
    b ← foo x b
  ```
  in a `do` block is syntactic sugar for:
  ```
  let b := ...
  let b ← forIn xs b (fun x b => do
    let b ← foo x b
    return .yield b)
  ```
  (Here `b` corresponds to the variables mutated in the loop.) -/
  forInv {β : Type u₁} [Monad m] [C: Container α ρ]
    (container : ρ)
    (invariant : Fin (C.size container).succ → β → Prop) 
    (b : {st : β // invariant 0 st}) 
    (next : (i : Fin (C.size container)) → {a : α // a ∈ container} → {st // invariant (Fin.castSucc i) st} → m (ForInStep {st // invariant (Fin.succ i) st}))
    : m { pr : (Fin (C.size container).succ) × β // invariant pr.1 pr.2}

def listForInv {α : outParam (Type u)} {β : Type v} {m : Type v → Type w} [Monad m]
    (L : List α)
    (invariant : Fin L.length.succ → β → Prop) 
    (init : {st // invariant 0 st}) 
    (next : (i : Fin (L.length)) → {st // invariant (Fin.castSucc i) st} → m (ForInStep {out // invariant (Fin.succ i) out})) 
    : m { pr : (Fin L.length.succ) × β // invariant pr.1 pr.2} :=
  let rec @[specialize] loop : (remaining : List α) → (hRem : ∀ x, x ∈ remaining → x ∈ L) → (i : Fin L.length.succ) → (b : {st // invariant i st}) →
    (hinv : remaining.length + i = L.length) → m {pr : (Fin L.length.succ) × β // invariant pr.1 pr.2}
  | [], _, i, state, hinv => pure ⟨(L.length, state), by 
      rw [List.length_nil, zero_add] at hinv
      convert state.2
      ext
      rw [hinv]
      simp⟩
  | x::xs, hRem, i, state, hinv =>
      have h1: xs.length + (i + 1) = L.length := by 
        apply Eq.trans _ hinv
        rw [add_comm _ 1, ←add_assoc, List.length_cons]
      have h2: (i : ℕ) < L.length :=
        lt_of_lt_of_eq (Nat.lt_of_succ_le (Nat.le_add_left _ _)) h1
      let i' : Fin (L.length) := ⟨i, h2⟩
      do
      match (← next i' state) with
      | ForInStep.done b' => 
          let ⟨b, binv⟩ := b'
          pure ⟨(Fin.succ i', b), binv⟩
      | ForInStep.yield b' => loop xs (fun x hx => hRem x (by simp[hx])) (Fin.succ i') b' h1
  loop L (by simp) 0 init (by simp)

#check listForInv

def sumSq (L : List Nat) : IO { m // ∃ idx, m = ((L.take idx).map (fun n => n^2)).sum} := do
  let mut state := 0
  let ⟨⟨idx, out⟩, inv⟩ ← listForInv L (fun i sum => sum = ((L.take i).map (fun n => n^2)).sum) ⟨state, by simp⟩
       (fun i ⟨st, invst⟩ => do
          IO.println s!"current index: {i}"
          return (.yield ⟨st + (L[i])^2 , 
        by
          simp [List.take_succ, List.get?_eq_get, invst]
       ⟩))
  state := out
  IO.println s!""
  return ⟨state, by use idx; exact inv⟩

#eval sumSq [1, 2, 3, 4, 5]

-- instance : ForInv m α (List α) where
--   forInv := listForInv 
  
-- def sumOfEven (L : List Nat) (h : ∀ x, x ∈ L → Even x) := Id.run do
--   let mut state : {n : Nat // Even n} := ⟨0, by simp⟩;
--   state ← listForInv L (fun sum => Even sum) state
--     (fun a sum => do 
--       let ⟨st, stInv⟩ := sum
--       let out := st + a.1
--       return .yield ⟨out, by 
--         simp
--         have sumEven : Even st := by simp [stInv]
--         have aEven : Even a.1 := by exact h a.1 a.2
--         apply Nat.even_add.2
--         exact ⟨fun _ => aEven, fun _ => sumEven⟩
--       ⟩
--     )
--   return state

-- #eval sumOfEven [2, 4] (by simp)
