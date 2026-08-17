import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic

/-- An event structure with binary conflict; events carry
labels in `Label`. The finite causes axiom is not assumed.
-/
structure PES (Label : Type*) where
  Event : Type*
  [poEvent : PartialOrder Event]
  conflict : Event → Event → Prop
  label : Event → Label
  conflict_irrefl : ∀ e, ¬ conflict e e
  conflict_symm : Std.Symm conflict
  conflict_hereditary : ∀ {e₁ e₂ e₃}, conflict e₁ e₂ → e₂ ≤ e₃ → conflict e₁ e₃

namespace PES

variable {L : Type*} (es : PES L)

instance : PartialOrder es.Event := es.poEvent

/-- Notation for the conflict relation. -/
local infixl:50 " # " => es.conflict

/-- Consistency relation: two events are consistent if they are not in conflict. -/
@[simp]
def consistent (e₁ e₂ : es.Event) : Prop := ¬ (e₁ # e₂)

/-- Consistency is reflexive. -/
instance consistent_refl : Std.Refl es.consistent := ⟨es.conflict_irrefl⟩

/-- Consistency is symmetric. -/
instance consistent_symm : Std.Symm es.consistent :=
  ⟨fun _ _ h h' => h (es.conflict_symm.symm _ _ h')⟩

/-- Two events are concurrent if they are consistent and causally independent. -/
@[simp]
def concurrent (e₁ e₂ : es.Event) : Prop :=
  es.consistent e₁ e₂ ∧ ¬ (e₁ ≤ e₂) ∧ ¬ (e₂ ≤ e₁)
local infixl:50 " ⋈ " => es.concurrent

/-- Concurrency is irreflexive. -/
lemma concurrent_irrefl : ∀ e, ¬ es.concurrent e e :=
  fun _ ⟨_, hNotLe, _⟩ => hNotLe le_rfl

/-- Concurrency is symmetric. -/
instance concurrent_symm : Std.Symm es.concurrent := by
  refine ⟨fun e₁ e₂ h => ?_⟩
  rcases h with ⟨hCons, hNotLe12, hNotLe21⟩
  refine ⟨?_, hNotLe21, hNotLe12⟩
  exact (consistent_symm es).symm _ _ hCons

/-- `e₁` and `e₂` are in minimal conflict when they conflict and no pair of
events below them does. -/
@[simp]
def minimalConflict (e₁ e₂ : es.Event) : Prop :=
  es.conflict e₁ e₂ ∧
  ∀ e₁' e₂', e₁' ≤ e₁ → e₂' ≤ e₂ → es.conflict e₁' e₂' → e₁' = e₁ ∧ e₂' = e₂

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- Minimal conflict is symmetric. -/
instance minimalConflict_symm : Std.Symm es.minimalConflict := by
  refine ⟨fun e₁ e₂ h => ?_⟩
  obtain ⟨hConf, hMin⟩ := h
  refine ⟨es.conflict_symm.symm _ _ hConf, ?_⟩
  intro e₂' e₁' he₂ he₁ hConf'
  have := hMin e₁' e₂' he₁ he₂ (es.conflict_symm.symm _ _ hConf')
  exact ⟨this.2, this.1⟩

/-- If (e₁, e₂) are in minimal conflict, then e₁ and e₂ conflict. -/
lemma minimalConflict_conflict {e₁ e₂ : es.Event} (h : es.minimalConflict e₁ e₂) :
    es.conflict e₁ e₂ :=
  h.1

/-- A conflicting pair below a minimal conflict is that conflict. -/
lemma minimalConflict_minimal {e₁ e₂ e₁' e₂' : es.Event} (h : es.minimalConflict e₁ e₂)
    (he₁ : e₁' ≤ e₁) (he₂ : e₂' ≤ e₂) (hConf : es.conflict e₁' e₂') :
    e₁' = e₁ ∧ e₂' = e₂ :=
  h.2 e₁' e₂' he₁ he₂ hConf

/-- The strict past of an event: all events strictly preceding it. -/
@[simp] def past (e : es.Event) : Set es.Event := {x | x < e}

/-- The future (upset) of an event: all events causally succeeding it. -/
@[simp] def future (e : es.Event) : Set es.Event := {x | e ≤ x}

/-- The past of any event is conflict-free. -/
lemma past_conflict_free {e e₁ e₂ : es.Event}
    (h₁ : e₁ ≤ e) (h₂ : e₂ ≤ e) : ¬ es.conflict e₁ e₂ :=
  fun hc => es.conflict_irrefl e
    (es.conflict_hereditary (es.conflict_symm.symm _ _ (es.conflict_hereditary hc h₂)) h₁)

end PES

/-- Decidable equality on events and a decidable strict order. -/
class DecidablePES {L : Type*} (es : PES L) where
  decEq : DecidableEq es.Event
  decLt : DecidableRel ((· < ·) : es.Event → es.Event → Prop)

set_option warn.classDefReducibility false in
attribute [instance] DecidablePES.decEq DecidablePES.decLt

instance PES.decLe {L : Type*} (es : PES L) [DecidablePES es] :
    DecidableRel ((· ≤ ·) : es.Event → es.Event → Prop) := fun a b =>
  if hab : a = b then isTrue (hab ▸ le_refl a)
  else if hlt : a < b then isTrue (le_of_lt hlt)
  else isFalse fun h => (lt_or_eq_of_le h).elim hlt hab
