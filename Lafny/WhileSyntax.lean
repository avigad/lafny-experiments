import Lean
import Lean.Elab.Do
import Lean.Elab.App
import Lean.Elab.BuiltinNotation


open Lean Parser Meta

open Lean.Elab.Term

variable (m)
#synth ForIn m (List Nat) Nat

syntax terminationByElem :=
  ppDedent(ppLine) "termination_by " term ";"?

syntax decreasingByElem :=
  ppDedent(ppLine) "decreasing_by " tacticSeq

syntax holdsByElem :=
  ppDedent(ppLine) "holds_by " tacticSeq

syntax (name := whileElem)
  "while" (ident " : ")? termBeforeDo " do " doSeq
  (terminationByElem)? (decreasingByElem)? : doElem

syntax (name := loopElem) "loop'"  (" (" &"label" " := " ident ")")? doSeq
  (terminationByElem)? (decreasingByElem)? : doElem

syntax (name := breakElem) "break'"  (" (" &"label" " := " ident ")")? (ppSpace colGt term)? : doElem

syntax (name := forInvElem)
  "for''" (ident " in ")? termBeforeDo (" // invariant" (":" termBeforeDo)? " := " termBeforeDo)? " do " doSeq
  (holdsByElem)? : term


-- -- without invariant
-- macro_rules
--   | `(doElem| for x in $container)
-- /-
--   let this := _
--   for x in xs // invariant := this do
--     <body>
--   holds_by

-- -/

private def getMonadForInv (expectedType? : Option Expr) := do
    match expectedType? with
    | none => throwError "foo"
    | some expectedType =>
      match (← isTypeApp? expectedType) with
      | some (m, _) => return m
      | none => throwError "bar"

elab "for'" itr:(ident)? " in " col:termBeforeDo (" // invariant" ":")? invType:(termBeforeDo)? (" := ")? initProof:(termBeforeDo)? " do " seq:doSeq invProof:(holdsByElem)? : term <= t => do
  match (← Elab.Term.isLocalIdent? col) with
  | none => mkAppM ``List.get! #[← (elabTerm col none) , mkNatLit 0]
  | some colFVar =>  
    let m ← getMonadForInv t
    let colType ← inferType colFVar
    let innerType ← inferType colType 
    logInfo (← instantiateMVars colType)

    let elemType ← mkFreshExprMVar (mkSort (mkLevelSucc (← mkFreshLevelMVar)))
    match invType, initProof with
      | some invType, some invProof => 
        -- loop with invariants
        let elemType ← instantiateMVars elemType
        logInfo s!"{invType} {invProof} {elemType}"
      | none, none => 
        -- "regular" for loop
        logInfo s! "foo"

      | _, _ => throwError "must provide both type and proof"

    -- let forInvInstance ← try
    --       mkAppM ``ForIn #[m, colType, elemType]
    --     catch _ =>
    --       tryPostpone; throwError "failed to construct 'ForIn' instance for collection{indentExpr colType}\nand monad{indentExpr m}"
    mkAppM ``List.get! #[← (elabTerm col none), mkNatLit 1]





def ex : IO Nat :=
  let bar := [0, 2]
  for' x in bar // invariant : Unit := sorry do 
    sorry 
  holds_by sorry

#eval ex

def ex2 : Nat :=
  let bar := [0, 2]
  for' x in bar do
    sorry

#eval ex2
-- def ex' : IO Unit := do for _ in [1:5] do IO.println s!"hi"

-- #check elabTerm
-- #eval ex2

-- #check Term.forInMacro
-- -- #check Term.doFor
-- #check Elab.Term.elabForIn

macro_rules
  | `(doElem| while $h : $cond do $seq:doSeq $[termination_by $t]? $[decreasing_by $tac]?) =>
    `(doElem|
      let $h ← loop'
        if $h : $cond then
          $seq:doSeq
        else
          break' $h
      $[termination_by $t]? $[decreasing_by $tac]?)

macro_rules
  | `(doElem| while $cond:term do $seq:doSeq $[termination_by $t]? $[decreasing_by $tac]?) =>
    `(doElem|
      loop'
        if $cond then
          $seq:doSeq
        else
          break'
      $[termination_by $t]? $[decreasing_by $tac]?)

macro_rules
  | `(doElem| loop' $[(label := $l)]? $seq:doSeq $[termination_by $t]? $[decreasing_by $tac]?) =>
    `(doElem| do
        repeat $seq
        pure ())

macro_rules
  | `(doElem| break' $[(label := $l)]? $val) =>
    `(doElem| do let c := $val; break)
  | `(doElem| break' $[(label := $l)]? ) =>
    `(doElem| break)

#check (
  show Id Unit from do
  let mut x := 10
  let mut y := 15
  let mut inv : Inhabited (x + y < 100) := ⟨by decide⟩
  -- sugar for (fun x y => x + y < 100) x y
  let xc ← loop' (label := foo)
    x := x + 1
    y := y + 1
    -- inv := _
    break' (label := foo) 1
  termination_by 100 - x
  decreasing_by simp
  pure xc
)

-- #eval loop'