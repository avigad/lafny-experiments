def baz [Monad m] (bar : Nat → IO PUnit) := fun x => bar x

def foo : IO Nat := do
  let mut myVar := 0
  baz (fun x => do
      myVar := myVar + 10
      IO.println s!"{myVar}")
  return 0


def foo' : IO Nat := do
  let mut myVar := 0
  do
    myVar := myVar + 10
  IO.println s!"{myVar}"

  return 0

#eval foo'