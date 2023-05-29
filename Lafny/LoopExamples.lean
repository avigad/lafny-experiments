import Mathlib.Data.Nat.Basic

def showSums : IO Unit := do
  let mut sum := 0
  for i in [:100] do
    sum := sum + i
    IO.println s!"i: {i}, sum: {sum}"

#eval showSums

def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then false else
    for i in [2:n] do
      if n % i = 0 then
        return false
      if i * i > n then
        return true
    true

#eval (List.range 10000).filter isPrime

def primes (n : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [2:n] do
    if isPrime i then
      result := result.push i
  result

#eval (primes 10000).size

def bar (n? : Option Nat) : IO Unit := do
  let some n := n? |
    IO.println "oops"
  IO.println n

#eval bar (some 2)
#eval bar none

def mulTable : Array (Array Nat) := Id.run do
  let mut table := #[]
  for i in [:10] do
    let mut row := #[]
    for j in [:10] do
      row := row.push ((i + 1) * (j + 1))
    table := table.push row
  table

#eval mulTable

def mulTable' : Array (Array Nat) := Id.run do
  let mut s : Array (Array Nat) := mkArray 10 (mkArray 10 0)
  for i in [:10] do
    for j in [:10] do
      s := s.set! i <| s[i]!.set! j ((i + 1) * (j + 1))
  s

#eval show IO Unit from do
  for i in [:10] do
    for j in [:10] do
      let numstr := toString mulTable[i]![j]!
      -- print 1-3 spaces
      IO.print <| " ".pushn ' ' (3 - numstr.length)
      IO.print numstr
    IO.println ""


#check Array.mkEmpty

def sqrArray (a : Array Nat) : Array Nat := Id.run do
  let mut b : Array Nat := Array.empty
  for elt in a do
    b := b.push <| elt * elt
  return b

#eval sqrArray (Array.range 100)

def reverse (a : Array Nat) : Array Nat := Id.run do
  let mut b : Array Nat := Array.mkEmpty a.size
  for i in [:a.size] do
    b := b.push a[a.size - i - 1]!
  return b

#eval reverse (Array.range 100)
