import Lafny.Util
import Mathlib.Data.Nat.Parity
import Lean.Elab.Term
open BigOperators
open Finset

def loop_blockM [Monad m] {State Measure : Type _} [WellFoundedRelation Measure]
    (meas : State → Measure)
    (init : State)
    (next : (state : State) → m (κ ⊕ {newState // WellFoundedRelation.rel (meas newState) (meas state)})) :
    m κ  :=
  loop init
where
  loop : State → m κ
    | state => do
        match (← next state) with
          | Sum.inl val => pure val
          | Sum.inr ⟨newState, _⟩  =>
              loop newState
  termination_by loop decreasing stateWithInv => meas stateWithInv


/-
Macro/Elab behavior

(init := r)
while cond : p // inv : q do
  body -- requires proofs


- cond : should be optional
- inv should be entirely optional -- if inv we return that on top of
    default return being ¬ cond

- state can be inferred to be the set of variables in p and body quotiented
    by inv if it exists

- init can be inferred, if SMT fails (really a sorry for now)
    then require the init on top
-/
open Lean Elab Term Meta
syntax "while' (" (ident " : ")? term (" // " ident " : " term)?")" term : term

macro_rules
| `(while' ($[$condName :]? $cond $[// $invName : $inv]?) $body) => 
  `($body)


#eval while' (h : 2 < 5 // inv : 3) Id.run do 
  let x := 5 
  let y := 4 
  return x

-- elab "while' " (ident " : ")? cond:term (" // " ident " : " term)? body:term : term <= t => do
--   let bodyExpr ← Term.elabTerm body none
--   let condExpr ← Term.elabTerm cond none
--   let condVars := condExpr.getUsedConstants'
--   logInfo "foo"
--   elabTerm body none

elab "while' " "("cond:term:10")" "("body:term:50")" : term => do
  let bodyExpr ← Term.elabTerm body none
  let condExpr ← Term.elabTerm cond none
  let condVars := condExpr.collectFVars
  logInfo s!"{← condVars}"
  return bodyExpr

variable (x : Nat)
#check while' (x < 5) (Id.run do return 5)