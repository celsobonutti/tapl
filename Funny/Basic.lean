import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.Unbundled

example {α β : Prop} (imp : α → β) : ¬β → ¬α := by
  intro nb na
  apply nb
  apply imp
  exact na

example {α β : Prop} (or : α ∨ β) : ¬α → β := by
  intro na
  apply or.elim
  case left =>
    intro a
    contradiction
  case right =>
    intro b
    exact b
