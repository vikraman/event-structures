import EventStructures.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

variable {L : Type*} (es : EventStructure L)

/-- A set of events is a configuration if it is conflict-free and downward closed. -/
@[simp] def isConf (X : Set es.Event) : Prop :=
  (∀ {e₁ e₂}, e₁ ∈ X → e₂ ∈ X → ¬ es.conflict e₁ e₂) ∧
  (∀ {e e'}, e ∈ X → e' ≤ e → e' ∈ X)

/-- Type of all configurations of an event structure. -/
def Conf : Type := {X : Set es.Event // isConf es X}

/-- Type of all finite configurations of an event structure. -/
def FinConf : Type := {X : Finset es.Event // isConf es (X : Set es.Event)}

namespace Configuration

/-- `c` enables `e`: consistent with `c`, and the past of `e` lies in `c`. -/
def enables (c : Set es.Event) (e : es.Event) : Prop :=
  isConf es c ∧
  (∀ e' ∈ c, es.consistent e e') ∧
  es.past e ⊆ c

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es

/-- If a configuration c enables an event e, then c ∪ {e} is also a configuration. -/
lemma enables_extension {c : Set es.Event} {e : es.Event} (h : c ⊢ e) :
    isConf es (c ∪ {e}) := by
  obtain ⟨⟨hConflictFree, hDownClosed⟩, hConsistent, hPast⟩ := h
  constructor
  · -- Conflict-free
    intro e₁ e₂ h₁ h₂
    obtain h₁ | h₁ := h₁
    · obtain h₂ | h₂ := h₂
      · exact hConflictFree h₁ h₂
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₂]
        intro hConf
        exact hConsistent e₁ h₁ (es.conflict_symm hConf)
    · rw [Set.mem_singleton_iff] at h₁
      obtain h₂ | h₂ := h₂
      · rw [h₁]
        intro hConf
        exact hConsistent e₂ h₂ hConf
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₁, h₂]
        exact es.conflict_irrefl e
  · -- Downward closed
    intro e' e'' h' h''
    obtain h' | h' := h'
    · exact Set.mem_union_left _ (hDownClosed h' h'')
    · rw [Set.mem_singleton_iff] at h'
      subst h'
      rcases lt_or_eq_of_le h'' with hlt | rfl
      · exact Set.mem_union_left _ (hPast hlt)
      · exact Set.mem_union_right _ rfl

/-- Configurations of `∅`. -/
lemma isConf_empty : isConf es ∅ :=
  ⟨fun h _ _ => (Set.notMem_empty _ h).elim, fun h _ => (Set.notMem_empty _ h).elim⟩

end Configuration

/-- An injective, monotone, conflict-reflecting map of event structures. -/
structure Emb {L : Type*} (E F : EventStructure L) where
  f : E.Event → F.Event
  inj : Function.Injective f
  mono : ∀ {x y}, x ≤ y → f x ≤ f y
  smono : ∀ {x y}, x < y → f x < f y
  conf : ∀ {x y}, E.conflict x y → F.conflict (f x) (f y)

namespace Emb

variable {L : Type*} {E F : EventStructure L} (ι : Emb E F)

lemma finite {c : Set F.Event} (h : c.Finite) : {y | ι.f y ∈ c}.Finite :=
  h.preimage ι.inj.injOn

lemma conf_restrict {c : Set F.Event} (h : _root_.isConf F c) :
    _root_.isConf E {y | ι.f y ∈ c} :=
  ⟨fun h₁ h₂ hcf => h.1 h₁ h₂ (ι.conf hcf), fun hy hle => h.2 hy (ι.mono hle)⟩

lemma enables_restrict {c : Set F.Event} {x : E.Event} (hc : _root_.isConf F c)
    (h : Configuration.enables F c (ι.f x)) :
    Configuration.enables E {y | ι.f y ∈ c} x :=
  ⟨ι.conf_restrict hc, fun _ hy hcf => h.2.1 _ hy (ι.conf hcf), fun _ hy => h.2.2 (ι.smono hy)⟩

end Emb

/-- Restricting along an injection commutes with adding one event. -/
lemma preimage_insert {α β : Type*} {ι : α → β} (hι : Function.Injective ι)
    (c : Set β) (x : α) : {y | ι y ∈ c ∪ {ι x}} = {y | ι y ∈ c} ∪ {x} := by
  ext y
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (hι h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg ι h)

