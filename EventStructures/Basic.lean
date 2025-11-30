import Mathlib.Order.Basic

/-- An event structure with binary conflict. -/
structure EventStructure where
  Event : Type*
  [poEvent : PartialOrder Event]
  conflict : Event → Event → Prop
  conflict_irrefl : Irreflexive conflict
  conflict_symm : Symmetric conflict
  conflict_hereditary : ∀ {e₁ e₂ e₃}, conflict e₁ e₂ → e₂ ≤ e₃ → conflict e₁ e₃

namespace EventStructure

variable (es : EventStructure)

instance : PartialOrder es.Event := es.poEvent

/-- Notation for the conflict relation. -/
local infixl:50 " # " => es.conflict

end EventStructure
