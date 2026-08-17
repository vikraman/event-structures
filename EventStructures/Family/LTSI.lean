import EventStructures.Family.Basic
import EventStructures.LTS.Basic

/-! # The LTSI of a configuration family

States are configurations, steps add one enabled fresh event, and independence
is the derived diamond condition. The forward LPV axioms hold for any family.
-/

open ConfFamily

variable {L : Type*} (F : ConfFamily L)

namespace ConfFamily

/-- Forward step: extend by a fresh enabled event. -/
def esStep (c₁ : Conf F) (a : L) (c₂ : Conf F) : Prop :=
  ∃ e, F.enables c₁.val e ∧ e ∉ c₁.val ∧ F.label e = a ∧ c₂.val = c₁.val ∪ {e}

/-- Coinitial independence of two labelled steps. -/
def esIndep (c : Conf F) (a : L) (c₁ : Conf F) (b : L) (c₂ : Conf F) : Prop :=
  ∃ e₁ e₂, F.Indep c.val e₁ e₂ ∧ e₁ ∉ c.val ∧ e₂ ∉ c.val ∧
    F.label e₁ = a ∧ F.label e₂ = b ∧
    c₁.val = c.val ∪ {e₁} ∧ c₂.val = c.val ∪ {e₂}

/-- The LTSI of a configuration family. -/
def toLTSI : LTSI L where
  State := Conf F
  init := ConfFamily.empty F
  step := esStep F
  indep := esIndep F

/-- The forward LPV axioms hold for every configuration family. -/
theorem toLTSI_LPV : LTSI.LPV (toLTSI F) where
  indep_step_left
    | ⟨e, _, h, hfr, _, hlbl, _, htgt, _⟩ => ⟨e, h.2.1, hfr, hlbl, htgt⟩
  indep_step_right
    | ⟨_, e, h, _, hfr, _, hlbl, _, htgt⟩ => ⟨e, h.2.2.1, hfr, hlbl, htgt⟩
  indep_irrefl := by
    rintro s a s' ⟨e₁, e₂, hind, hfr₁, -, -, -, htgt₁, htgt₂⟩
    refine hind.1 ?_
    have hset : s.val ∪ {e₁} = s.val ∪ {e₂} := htgt₁.symm.trans htgt₂
    rcases (hset ▸ Set.mem_union_right s.val (rfl : e₁ ∈ {e₁})) with h | h
    · exact (hfr₁ h).elim
    · exact h
  indep_symm
    | ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩ =>
      ⟨e₂, e₁, hind.symm, f₂, f₁, l₂, l₁, t₂, t₁⟩
  square := by
    rintro s a s₁ b s₂ ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩
    -- the closing state is `s ∪ {e₁} ∪ {e₂}`, which `Indep` already supplies
    have hu : F.Config (s.val ∪ {e₁} ∪ {e₂}) := hind.2.2.2
    refine ⟨⟨s.val ∪ {e₁} ∪ {e₂}, hu⟩, ⟨e₂, ⟨?_, ?_⟩, ?_, l₂, ?_⟩,
      ⟨e₁, ⟨?_, ?_⟩, ?_, l₁, ?_⟩⟩
    · rw [t₁]; exact hind.2.1.2
    · rw [t₁]; exact hu
    · rw [t₁]
      rintro (h | h)
      · exact f₂ h
      · exact hind.1.symm (Set.mem_singleton_iff.mp h)
    · rw [t₁]
    · rw [t₂]; exact hind.2.2.1.2
    · rw [t₂, union_pair_comm]; exact hu
    · rw [t₂]
      rintro (h | h)
      · exact f₁ h
      · exact hind.1 (Set.mem_singleton_iff.mp h)
    · rw [t₂]; exact union_pair_comm s.val e₁ e₂

end ConfFamily
