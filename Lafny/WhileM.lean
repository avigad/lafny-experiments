import Lafny.Util
import Mathlib.Data.Nat.Parity
open BigOperators
open Finset


class WhileM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  WhileM [Monad m] : γ → (α → m PUnit) → m PUnit