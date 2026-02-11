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

/-- Consistency relation: two events are consistent if they are not in conflict. -/
@[simp]
def consistent (e₁ e₂ : es.Event) : Prop := ¬ (e₁ # e₂)

/-- Consistency is reflexive. -/
lemma consistent_refl : Reflexive es.consistent := es.conflict_irrefl

/-- Consistency is symmetric. -/
lemma consistent_symm : Symmetric es.consistent :=
  fun _ _ h h' => h (es.conflict_symm h')

/-- Concurrency relation: two events are concurrent if they are
    consistent and causally independent. -/
@[simp]
def concurrent (e₁ e₂ : es.Event) : Prop :=
  es.consistent e₁ e₂ ∧ ¬ (e₁ ≤ e₂) ∧ ¬ (e₂ ≤ e₁)
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

/-- Minimal conflict relation: (e₁, e₂) is a minimal conflicting pair if they conflict
    and there is no proper reduction of either that still produces a conflict.
    Formally: e₁ # e₂ and for all e₁' ≤ e₁, e₂' ≤ e₂, if e₁' # e₂' then e₁' = e₁ ∧ e₂' = e₂ -/
@[simp]
def minimalConflict (e₁ e₂ : es.Event) : Prop :=
  es.conflict e₁ e₂ ∧
  ∀ e₁' e₂', e₁' ≤ e₁ → e₂' ≤ e₂ → es.conflict e₁' e₂' → e₁' = e₁ ∧ e₂' = e₂

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- Minimal conflict is symmetric. -/
lemma minimalConflict_symm : Symmetric es.minimalConflict := by
  intro e₁ e₂ ⟨hConf, hMin⟩
  refine ⟨es.conflict_symm hConf, ?_⟩
  intro e₂' e₁' he₂ he₁ hConf'
  have := hMin e₁' e₂' he₁ he₂ (es.conflict_symm hConf')
  exact ⟨this.2, this.1⟩

/-- If (e₁, e₂) is a minimal conflict, then e₁ and e₂ conflict. -/
lemma minimalConflict_conflict {e₁ e₂ : es.Event} (h : es.minimalConflict e₁ e₂) :
    es.conflict e₁ e₂ :=
  h.1

/-- If (e₁, e₂) is a minimal conflict and e₁' ≤ e₁, e₂' ≤ e₂ with e₁' ## e₂',
    then e₁' = e₁ and e₂' = e₂. -/
lemma minimalConflict_minimal {e₁ e₂ e₁' e₂' : es.Event} (h : es.minimalConflict e₁ e₂)
    (he₁ : e₁' ≤ e₁) (he₂ : e₂' ≤ e₂) (hConf : es.conflict e₁' e₂') :
    e₁' = e₁ ∧ e₂' = e₂ :=
  h.2 e₁' e₂' he₁ he₂ hConf

/-- The strict past of an event: all events strictly preceding it. -/
@[simp] def past (e : es.Event) : Set es.Event := {x | x < e}

/-- The future (upset) of an event: all events causally succeeding it. -/
@[simp] def future (e : es.Event) : Set es.Event := {x | e ≤ x}

end EventStructure
