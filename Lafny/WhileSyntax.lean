import Lean
import Lean.Elab.Do



open Lean Parser
variable (m)
#synth ForIn m (List Nat) Nat

syntax terminationByElem :=
  ppDedent(ppLine) "termination_by " term ";"?

syntax decreasingByElem :=
  ppDedent(ppLine) "decreasing_by " tacticSeq

syntax (name := whileElem)
  "while" (ident " : ")? termBeforeDo " do " doSeq
  (terminationByElem)? (decreasingByElem)? : doElem

syntax (name := loopElem) "loop'"  (" (" &"label" " := " ident ")")? doSeq
  (terminationByElem)? (decreasingByElem)? : doElem
syntax (name := breakElem) "break'"  (" (" &"label" " := " ident ")")? (ppSpace colGt term)? : doElem

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

#check `(
  show Id Unit from do
  let mut x := 10
  let mut y := 15
  let mut inv : Inhabited (x + y < 100) := ⟨by decide⟩
  -- sugar for (fun x y => x + y < 100) x y
  let xc ← loop' (label := foo)
    x := x + 1
    y := y + 1
    inv := _
    break' (label := foo) 1
  termination_by 100 - x
  decreasing_by simp
  pure xc
)
