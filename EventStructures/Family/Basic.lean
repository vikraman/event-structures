import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic

/-! # Configuration families

A configuration family is a collection of sets of events that are considered to be configurations.
Paths, traces, computations, rollback and replay are stated at the level of configuration families.
-/

/-- Events, the sets of them that count as configurations, and labels. -/
structure ConfFamily (Label : Type*) where
  Event : Type*
  Config : Set Event → Prop
  label : Event → Label
  empty_mem : Config ∅
  /-- A finite gap between configurations closes one event at a time. -/
  secured : ∀ {x y : Set Event}, Config x → Config y → y ⊆ x → (x \ y).Finite → x ≠ y →
    ∃ e ∈ x \ y, Config (x \ {e})

namespace ConfFamily

variable {L : Type*} (F : ConfFamily L)

/-- Configurations of `F`. -/
def Conf : Type _ := {X : Set F.Event // F.Config X}

/-- Finite configurations of `F`. -/
def FinConf : Type _ := {X : Finset F.Event // F.Config (X : Set F.Event)}

/-- The empty configuration. -/
def empty : Conf F := ⟨∅, F.empty_mem⟩

/-- `c` enables `e` when both `c` and `c ∪ {e}` are configurations. -/
def enables (c : Set F.Event) (e : F.Event) : Prop := F.Config c ∧ F.Config (c ∪ {e})

variable {F}

lemma enables_conf {c : Set F.Event} {e : F.Event} (h : F.enables c e) : F.Config c := h.1

lemma enables_extension {c : Set F.Event} {e : F.Event} (h : F.enables c e) :
    F.Config (c ∪ {e}) := h.2

lemma enables_of {c : Set F.Event} {e : F.Event} (hc : F.Config c)
    (hx : F.Config (c ∪ {e})) : F.enables c e := ⟨hc, hx⟩

variable (F)

/-- Singleton extensions commute. -/
lemma union_pair_comm {α : Type*} (s : Set α) (a b : α) :
    s ∪ {a} ∪ {b} = s ∪ {b} ∪ {a} := by
  ext x; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto

/-- Coinitial independence: separately and jointly extendable.
It is relative to `c`, since in a general event structure two events
may be independent at one configuration and not at another. -/
def Indep (c : Set F.Event) (e₁ e₂ : F.Event) : Prop :=
  e₁ ≠ e₂ ∧ F.enables c e₁ ∧ F.enables c e₂ ∧ F.Config (c ∪ {e₁} ∪ {e₂})

variable {F}

lemma Indep.symm {c : Set F.Event} {e₁ e₂ : F.Event} (h : F.Indep c e₁ e₂) :
    F.Indep c e₂ e₁ :=
  ⟨h.1.symm, h.2.2.1, h.2.1, by rw [union_pair_comm]; exact h.2.2.2⟩

/-- Independence is irreflexive. -/
lemma Indep.irrefl {c : Set F.Event} {e : F.Event} : ¬ F.Indep c e e :=
  fun h => h.1 rfl

variable (F)

/-- The binary consistency induced by the family. -/
def compat (e₁ e₂ : F.Event) : Prop := ∃ c, F.Config c ∧ e₁ ∈ c ∧ e₂ ∈ c

end ConfFamily
