import EventStructures.Prime.Basic
import EventStructures.Family.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

variable {L : Type*} (es : PES L)

/-- A set of events is a configuration if it is conflict-free and downward closed. -/
@[simp] def isConf (X : Set es.Event) : Prop :=
  (∀ {e₁ e₂}, e₁ ∈ X → e₂ ∈ X → ¬ es.conflict e₁ e₂) ∧
  (∀ {e e'}, e ∈ X → e' ≤ e → e' ∈ X)

/-- Type of all configurations of an event structure. -/
def Conf : Type := {X : Set es.Event // isConf es X}

/-- Type of all finite configurations of an event structure. -/
def FinConf : Type := {X : Finset es.Event // isConf es (X : Set es.Event)}

namespace Configuration

/-- `c` enables `e` if `e` is consistent with `c`, and the past of `e` lies in `c`. -/
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
structure Emb {L : Type*} (E F : PES L) where
  f : E.Event → F.Event
  inj : Function.Injective f
  mono : ∀ {x y}, x ≤ y → f x ≤ f y
  smono : ∀ {x y}, x < y → f x < f y
  conf : ∀ {x y}, E.conflict x y → F.conflict (f x) (f y)

namespace Emb

variable {L : Type*} {E F : PES L} (ι : Emb E F)

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


/-! ## Bridge to configuration families -/

namespace PES

variable {L : Type*} (P : PES L)

/-- A prime event structure gives a configuration family. -/
def toFamily : ConfFamily L where
  Event := P.Event
  Config := isConf P
  label := P.label
  empty_mem := Configuration.isConf_empty P
  secured := by
    intro x y hx hy hyx hfin hne
    have hxy : (x \ y).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
      exact hne (Set.Subset.antisymm h hyx)
    obtain ⟨e, hemem, hmax⟩ := hfin.exists_maximal hxy
    refine ⟨e, hemem, fun h₁ h₂ => hx.1 h₁.1 h₂.1, ?_⟩
    rintro z w ⟨hzx, hzne⟩ hle
    refine ⟨hx.2 hzx hle, ?_⟩
    rintro rfl
    have hzdiff : z ∈ x \ y := ⟨hzx, fun hzy => hemem.2 (hy.2 hzy hle)⟩
    exact hzne (Set.mem_singleton_iff.mpr (le_antisymm (hmax hzdiff hle) hle))

@[simp] lemma toFamily_Event : P.toFamily.Event = P.Event := rfl

@[simp] lemma toFamily_Config : P.toFamily.Config = isConf P := rfl

/-- The family enabling relation agrees with the prime one. -/
@[simp] lemma enables_iff {c : Set P.Event} {e : P.Event} :
    P.toFamily.enables c e ↔ Configuration.enables P c e := by
  constructor
  · rintro ⟨hc, hext⟩
    refine ⟨hc, fun e' he' => hext.1 (Or.inr rfl) (Or.inl he'), ?_⟩
    intro x hx
    rcases hext.2 (Or.inr rfl : e ∈ c ∪ {e}) (le_of_lt hx) with h | h
    · exact h
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact absurd hx (lt_irrefl _)
  · exact fun h => ⟨h.1, Configuration.enables_extension P h⟩


/-- Derived independence coincides with concurrency, for distinct fresh events.
This is what recovers the prime notion rather than assuming it. -/
lemma indep_iff_concurrent {c : Set P.Event} {e₁ e₂ : P.Event}
    (h₁ : Configuration.enables P c e₁) (h₂ : Configuration.enables P c e₂)
    (hf₁ : e₁ ∉ c) (hf₂ : e₂ ∉ c) (hne : e₁ ≠ e₂) :
    P.toFamily.Indep c e₁ e₂ ↔ P.concurrent e₁ e₂ := by
  constructor
  · rintro ⟨-, -, hst⟩
    refine ⟨hst.1 (Or.inl (Or.inr rfl)) (Or.inr rfl), ?_, ?_⟩
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact hf₁ (h₂.2.2 hlt)
      · exact hne rfl
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact hf₂ (h₁.2.2 hlt)
      · exact hne rfl
  · intro hconc
    have hc1 : isConf P (c ∪ {e₁}) := ((PES.enables_iff P).mpr h₁).2
    refine ⟨(PES.enables_iff P).mpr h₁, (PES.enables_iff P).mpr h₂, ?_, ?_⟩
    · rintro x y (hx | rfl) (hy | rfl)
      · exact hc1.1 hx hy
      · rcases hx with hx | rfl
        · exact fun hcf => h₂.2.1 x hx (P.conflict_symm hcf)
        · exact hconc.1
      · rcases hy with hy | rfl
        · exact h₂.2.1 y hy
        · exact fun hcf => hconc.1 (P.conflict_symm hcf)
      · exact P.conflict_irrefl _
    · rintro x y (hx | rfl) hle
      · exact Or.inl (hc1.2 hx hle)
      · rcases lt_or_eq_of_le hle with hlt | rfl
        · exact Or.inl (Or.inl (h₂.2.2 hlt))
        · exact Or.inr rfl

end PES
