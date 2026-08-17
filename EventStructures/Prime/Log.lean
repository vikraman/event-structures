import EventStructures.Prime.Configuration
import EventStructures.Family.Log

/-! # Logs of a prime event structure

Choice points are minimal conflicts. -/

variable {L : Type*} (es : PES L)
open PES
open Configuration

/-- Notation for minimal conflict. -/
local infixl:50 " ## " => es.minimalConflict

/-- An event is logged if it is in minimal conflict with some event. -/
@[simp]
def logged (e : es.Event) : Prop := ∃ e', e ## e'

/-- The log of `c`: its events in minimal conflict with something outside `c`. -/
@[simp]
def log (c : Conf es) : Set es.Event :=
  {e ∈ c.1 | ∃ e' ∉ c.1, e ## e'}

namespace Log

/-- The log is contained in the configuration. -/
lemma log_subset {c : Conf es} : log es c ⊆ c.1 := fun _ ⟨h, _⟩ => h

/-- Events in the log are logged. -/
lemma log_logged {c : Conf es} {e : es.Event} (h : e ∈ log es c) : logged es e := by
  simp only [log, Set.mem_setOf_eq] at h
  exact ⟨h.2.choose, h.2.choose_spec.2⟩

lemma log_mem_iff {c : Conf es} {e : es.Event} :
    e ∈ log es c ↔ e ∈ c.1 ∧ ∃ e' ∉ c.1, e ## e' :=
  Iff.rfl

lemma logged_iff {e : es.Event} : logged es e ↔ ∃ e', e ## e' :=
  Iff.rfl

/-- Minimal conflict is symmetric, so its partner is logged too. -/
lemma logged_symm {e e' : es.Event} (h : e ## e') : logged es e' :=
  ⟨e, es.minimalConflict_symm h⟩

lemma log_has_conflict_outside {c : Conf es} {e : es.Event} (he : e ∈ log es c) :
    ∃ e' ∉ c.1, e ## e' := by
  simp only [log, Set.mem_setOf_eq] at he
  exact he.2

end Log

namespace PES

/-- Compatibility with a log, for the conflict relation of `es`. -/
abbrev compatibleWithLog (σ : Computations es.toFamily) (l : Set es.Event) : Prop :=
  Log.compatibleWithLog es.toFamily es.conflict σ l

/-- A computation compatible with the log of a configuration. -/
def compatibleWithConfigLog (c : Conf es) (σ : Computations es.toFamily) : Prop :=
  compatibleWithLog es σ (log es c)

/-- Computations compatible with the log of a configuration. -/
def CompatibleWithConfigLog (c : Conf es) : Type _ :=
  Log.CompatibleComputations es.toFamily es.conflict (log es c)

/-- The label image of the log of a configuration. -/
@[simp] def labelLog (c : Conf es) : Set L := Log.labelLog es.toFamily (log es c)

lemma label_mem_labelLog {c : Conf es} {e : es.Event} (h : e ∈ log es c) :
    es.label e ∈ labelLog es c :=
  Log.label_mem_labelLog es.toFamily h

end PES
