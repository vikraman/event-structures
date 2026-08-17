import EventStructures.Prime.Basic
import EventStructures.Prime.Configuration
import EventStructures.LTS.Basic
import EventStructures.Stable.LTSI
import EventStructures.Family.LTSI

/-! # The LTSI of a prime event structure -/

variable {L : Type*}

namespace PES

variable (es : PES L)

open Configuration

local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent

/-- The empty configuration. -/
def emptyConfig : Conf es :=
  ⟨∅, fun h _ _ => (Set.notMem_empty _ h).elim,
      fun h _ => (Set.notMem_empty _ h).elim⟩

/-- Forward step: extend by a fresh enabled event. -/
def esStep (c₁ : Conf es) (a : L) (c₂ : Conf es) : Prop :=
  ∃ e, (c₁.1 ⊢ e) ∧ e ∉ c₁.1 ∧ es.label e = a ∧ c₂.1 = c₁.1 ∪ {e}

/-- Coinitial independence: concurrent fresh enabled events. -/
def esIndep (c : Conf es) (a : L) (c₁ : Conf es) (b : L) (c₂ : Conf es) : Prop :=
  ∃ e₁ e₂, (c.1 ⊢ e₁) ∧ (c.1 ⊢ e₂) ∧ e₁ ∉ c.1 ∧ e₂ ∉ c.1 ∧
    es.label e₁ = a ∧ es.label e₂ = b ∧
    c₁.1 = c.1 ∪ {e₁} ∧ c₂.1 = c.1 ∪ {e₂} ∧ e₁ ⋈ e₂

/-- LTSI of an event structure. -/
def toLTSI : LTSI L where
  State := Conf es
  init := emptyConfig es
  step := esStep es
  indep := esIndep es

/-- The prime and family step relations agree. -/
lemma esStep_iff {c₁ c₂ : Conf es} {a : L} :
    ConfFamily.esStep es.toFamily c₁ a c₂ ↔ esStep es c₁ a c₂ := by
  constructor
  · rintro ⟨e, hen, hfr, hlbl, htgt⟩
    exact ⟨e, (PES.enables_iff es).mp hen, hfr, hlbl, htgt⟩
  · rintro ⟨e, hen, hfr, hlbl, htgt⟩
    exact ⟨e, (PES.enables_iff es).mpr hen, hfr, hlbl, htgt⟩

/-- The prime and family independence relations agree. -/
lemma esIndep_iff {c c₁ c₂ : Conf es} {a b : L} :
    ConfFamily.esIndep es.toFamily c a c₁ b c₂ ↔ esIndep es c a c₁ b c₂ := by
  constructor
  · rintro ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩
    have h₁ := (PES.enables_iff es).mp hind.2.1
    have h₂ := (PES.enables_iff es).mp hind.2.2.1
    exact ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂,
      (PES.indep_iff_concurrent es h₁ h₂ f₁ f₂).mp hind⟩
  · rintro ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hconc⟩
    exact ⟨e₁, e₂, (PES.indep_iff_concurrent es h₁ h₂ f₁ f₂).mpr hconc,
      f₁, f₂, l₁, l₂, t₁, t₂⟩

/-- The prime LTSI *is* the family LTSI. -/
lemma toLTSI_eq : toLTSI es = ConfFamily.toLTSI es.toFamily := by
  unfold toLTSI ConfFamily.toLTSI
  congr 1
  · funext c a c'; exact propext (Iff.symm (esStep_iff es))
  · funext c a c₁ b c₂; exact propext (Iff.symm (esIndep_iff es))

/-- The event-structure LTSI satisfies LPV. -/
theorem toLTSI_LPV : LTSI.LPV (toLTSI es) :=
  toLTSI_eq es ▸ ConfFamily.toLTSI_LPV es.toFamily

/-- Reversible step. -/
def esRStep : Conf es → DirLabel L → Conf es → Prop :=
  ConfFamily.esRStep es.toFamily

/-- Reversible coinitial independence. -/
def esRIndep : Conf es → DirLabel L → Conf es → DirLabel L → Conf es → Prop :=
  ConfFamily.esRIndep es.toFamily

/-- Reversible LTSI of an event structure. -/
def toRLTSI : RLTSI L :=
  ConfFamily.toRLTSI es.toFamily

/-- Prime event structures are stable, so the reverse LPV axioms hold. -/
theorem toRLTSI_LPV : RLTSI.LPV (toRLTSI es) :=
  ConfFamily.toRLTSI_LPV es.stable

end PES
