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

/-- Consistency relation between events: two events are consistent if they are not in conflict. -/
@[simp] def consistent (e₁ e₂ : es.Event) : Prop := ¬ (e₁ # e₂)

/-- Consistency is reflexive. -/
lemma consistent_refl : Reflexive es.consistent :=
  es.conflict_irrefl
/-- Consistency is symmetric. -/
lemma consistent_symm : Symmetric es.consistent :=
  fun _ _ h h' => h (es.conflict_symm h')

/- Concurrency relation between events:
  two events are concurrent if they are consistent and causally independent. -/
@[simp] def concurrent (e₁ e₂ : es.Event) : Prop := es.consistent e₁ e₂ ∧ ¬ (e₁ ≤ e₂) ∧ ¬ (e₂ ≤ e₁)
local infixl:50 " ⋈ " => es.concurrent

/-- Concurrency is irreflexive. -/
lemma concurrent_irrefl : Irreflexive es.concurrent := by
  intro e h
  rcases h with ⟨_, hNotLe, _⟩
  exact hNotLe (le_rfl)

/-- Concurrency is symmetric. -/
lemma concurrent_symm : Symmetric es.concurrent := by
  intro e₁ e₂ h
  rcases h with ⟨hCons, hNotLe12, hNotLe21⟩
  refine ⟨?_, hNotLe21, hNotLe12⟩
  exact (consistent_symm es) hCons

/-- The past (downset) of an event: all events causally preceding it. -/
@[simp] def past (e : es.Event) : Set es.Event := {x | x ≤ e}

/-- The future (upset) of an event: all events causally succeeding it. -/
@[simp] def future (e : es.Event) : Set es.Event := {x | e ≤ x}

end EventStructure
