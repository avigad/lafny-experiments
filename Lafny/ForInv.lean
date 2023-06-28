import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Basic
import Std.Data.List.Lemmas

def proj (x : ForInStep y') :=
  match x with 
  | .yield z => z
  | .done z => z

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


#check ForIn

-- in theory this might be it, just put some fancy syntax around it.
-- I need to read Metaprogramming in Lean to figure out what to do next
-- here, but this is a very large step I think.

class ForInv (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) where
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
  forInv {β : Type _} [Monad m] 
    (container : ρ)
    [Membership α ρ]
    (invariant : β → Prop) 
    (b : {st : β // invariant st}) 
    (next : {a : α // a ∈ container} → {st // invariant st} → m (ForInStep {st // invariant st}))
    : m {st // invariant st}

def listForInv {α : Type _} {β : Type v} {m : Type v → Type w} [Monad m]
    (xs : List α)
    (invariant : β → Prop) 
    (init : {st // invariant st}) 
    (next : {a // a ∈ xs} → {st // invariant st} → m (ForInStep {out // invariant out})) 
    : m {st // invariant st} :=
  let rec @[specialize] loop (L : List α) (hL : ∀ x ∈ L, x ∈ xs) (b : {st // invariant st}) :=
    match L with
    | [] => pure b
    | a::as => do
        match (← next ⟨a, by exact hL a (by exact (List.mem_cons_self a as))⟩ b) with
        | ForInStep.done b'  => pure b'
        | ForInStep.yield b' => loop as (fun x hx => hL x (by simp [hx])) b'
  loop xs (by simp) init

def sumOfEven (L : List Nat) (h : ∀ x, x ∈ L →  Even x) := Id.run do
  let mut sum := 0;
  sum ← listForInv L (fun sum => Even sum) ⟨sum, by simp⟩ 
    (fun a sum => do 
      let ⟨st, stInv⟩ ← sum
      let out := st + a.1
      return .yield ⟨out, by 
        simp
        have sumEven : Even st := by simp [stInv]
        have aEven : Even a.1 := by exact h a.1 a.2
        apply Nat.even_add.2
        exact ⟨fun _ => aEven, fun _ => sumEven⟩
      ⟩
    )
  return sum

#check sumOfEven [2, 4] (by simp)

instance : ForInv m (List α) α where
  forInv := listForInv

-- I'm not sure why this would be useful, but it seems kinda interesting
-- as a structure so why not
def optForInv {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (opta : Option α)
    (invariant : β → Prop)
    (init : {st // invariant st})
    (next : α → {st // invariant st} → m (ForInStep {st // invariant st}))
    : m {st // invariant st} :=
  let rec @[specialize] update
    | none, b => pure b
    | some a, b => do
      match (← next a b) with
      | ForInStep.done b' => pure b'
      | ForInStep.yield b' => pure b'
  update opta init

instance : ForInv m (Option α) α where
  forInv := optForInv