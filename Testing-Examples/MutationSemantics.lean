/-
  This is interestring. This loop suggests that inner-loops
  can only sometimes mutate outerloops. The `z` mutates as 
  it would in c, but the `x` does not. This conflicts with
  the description in do unchained:


  "Declaring a mutable variable should grant us access to its value in the
  subsequent code just like with immutable ones, but reassignment will have to be more limited: if
  there is another do block nested anywhere inside the first one, say within an argument to some
  monadic combinator, there is no way in general to propagate reassignments back to the outer block
  without true mutation. Neither changing the result type nor introducing a new monadic layer to
  do the propagation is guaranteed to work (or even typecheck) in all contexts of the inner block.
  Thus we will sensibly restrict reassignment of a variable to the same do block it was declared in
  using let mut." (page 4)
-/

def mutationSemantics := do
  let mut x := 10
  let mut z := 0
  for _ in [1:x] do
    -- z := z + 1
    -- IO.println x 
    -- IO.println z
    return
  IO.println s!"hi"
  
  
#check ForIn
  
#print mutationSemantics
#eval mutationSemantics
#print MProd

-- variable (n m: Nat) (p : Nat → Nat → Prop) (foo : p n m )
-- example : {q // p q.1 q.2} := ⟨Prod.mk n m, foo⟩

-- example : {⟨q₁, q₂⟩ : Nat × Nat// p q₁ q₂} := ⟨⟨n, m⟩, foo⟩