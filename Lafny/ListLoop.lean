import Lafny.Util

def list_loop_with_invariant {α State : Type _}
      (list : List α)
      (invariant : Fin list.length.succ → State → Prop)
      (start_state : State)
      (init : invariant 0 start_state)
      (next_state : Fin list.length → α → State → State)
      (step : ∀ i : Fin list.length, ∀ state,
        invariant (Fin.castSucc i) state → invariant (Fin.succ i) (next_state i list[i] state)) :
    { state // invariant (Fin.last list.length) state } :=
  have : list.length + 0 = list.length ∧ invariant 0 start_state := by
    constructor
    . rw [add_zero]
    . trivial
  go list 0 start_state this
where
  go : (remaining : List α) → (i : Fin list.length.succ) → (state : State) →
        (hinv : remaining.length + i = list.length ∧ invariant i state) →
          { state : State // invariant (Fin.last list.length) state }
  | [], i, state, hinv => by
      use state
      rw [List.length_nil, zero_add] at hinv
      convert hinv.2
      ext; rw [hinv.1]; simp
  | a :: as, i, state, hinv =>
    have h1: as.length + (i + 1) = list.length := by
      apply Eq.trans _ hinv.1
      rw [add_comm _ 1, ←add_assoc, List.length_cons]
    have h2: (i : ℕ) < list.length :=
      lt_of_lt_of_eq (Nat.lt_of_succ_le (Nat.le_add_left _ _)) h1
    let i' : Fin (list.length) := ⟨i, h2⟩
    go as (Fin.succ i') (next_state i' list[i'] state) ⟨h1, step _ _ hinv.2⟩

syntax "forL" ident "in" term "with" ident
  withPosition("state:" ident ":=" term
  "invariant:" ident ":=" term
  "init:=" term
  "next:" term
  "step:=" term)
  term : term

macro_rules
  | `(forL $a in $l with $i
        state: $s := $start_state
        invariant: $p := $inv
        init:= $init
        next: $next_state
        step:= $step
      $rest) =>
      `(let ⟨$s, $p⟩ := list_loop_with_invariant
          (list := $l)
          (invariant := fun $i $s => $inv)
          (start_state := $start_state)
          (init := $init)
          (next_state := fun $i $a $s => $next_state)
          (step := $step)
        $rest)

def listSumSq (list : List Nat) : { m // m = (list.map (fun n => n^2)).sum } :=
  forL a in list with i
    state: sum := 0
    invariant: inv := sum = ((list.take i).map (fun n => n^2)).sum
    init:= by simp
    next: sum + a^2
    step:= by simp [List.take_succ, List.get?_eq_get]
  ⟨sum, by simp [inv]⟩


def list_loop_with_invariant' {α State : Type _}
      (list : List α)
      (invariant : Fin list.length.succ → State → Prop)
      (init : { s : State // invariant 0 s})
      (next : (i : Fin list.length) → α → (state : State) → (inv : invariant (Fin.castSucc i) state) → {new_state // invariant (Fin.succ i) new_state}):
    { state // invariant (Fin.last list.length) state } :=
  have : list.length + 0 = list.length ∧ invariant 0 init.1 := by
    constructor
    . rw [add_zero]
    . exact init.2
  go list 0 init this
where
  go : (remaining : List α) → (i : Fin list.length.succ) → (state : State) →
        (hinv : remaining.length + i = list.length ∧ invariant i state) →
          { new_state : State // invariant (Fin.last list.length) new_state }
  | [], i, state, hinv => by
      use state
      rw [List.length_nil, zero_add] at hinv
      convert hinv.2
      ext; rw [hinv.1]; simp
  | a :: as, i, state, hinv =>
    have h1: as.length + (i + 1) = list.length := by
      apply Eq.trans _ hinv.1
      rw [add_comm _ 1, ←add_assoc, List.length_cons]
    have h2: (i : ℕ) < list.length :=
      lt_of_lt_of_eq (Nat.lt_of_succ_le (Nat.le_add_left _ _)) h1
    let i' : Fin (list.length) := ⟨i, h2⟩
    have h3 : invariant (Fin.succ i') ↑(next i' list[i'] state hinv.2) := by 
      exact (next i' list[i'] state hinv.2).2
    go as (Fin.succ i') (next i' list[i'] state hinv.2) ⟨h1, h3⟩