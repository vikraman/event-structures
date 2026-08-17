import EventStructures.Family.Basic
import EventStructures.Prime.Configuration
import Mathlib.Data.Set.Lattice

/-! # Stable families

Bounded intersections of configurations are configurations. Hence each event of
a configuration has a *least* history inside it, which makes rollback and
least/greatest replay well defined. -/

open ConfFamily

variable {L : Type*}

/-- Configurations bounded by a common configuration are closed under intersection. -/
def Stable (F : ConfFamily L) : Prop :=
  ∀ {S : Set (Set F.Event)} {z : Set F.Event}, S.Nonempty → (∀ x ∈ S, F.Config x) →
    F.Config z → (∀ x ∈ S, x ⊆ z) → F.Config (⋂₀ S)

/-- Configurations bounded by a common configuration are closed under union.
Unlike stability this is not about intersections; it holds for the
configurations of any event structure, since a subset of a configuration that
is consistent and secured is again one. -/
def Coherent (F : ConfFamily L) : Prop :=
  ∀ {S : Set (Set F.Event)} {z : Set F.Event}, (∀ x ∈ S, F.Config x) → 
    F.Config z → (∀ x ∈ S, x ⊆ z) → F.Config (⋃₀ S)

/-- Every prime event structure is coherent. -/
lemma PES.coherent (P : PES L) : Coherent P.toFamily := by
  intro S z hS hz hsub
  refine ⟨fun h₁ h₂ => ?_, fun he hle => ?_⟩
  · obtain ⟨m₁, hm₁, hx₁⟩ := h₁
    obtain ⟨m₂, hm₂, hx₂⟩ := h₂
    exact hz.1 (hsub m₁ hm₁ hx₁) (hsub m₂ hm₂ hx₂)
  · obtain ⟨m, hm, hx⟩ := he
    exact ⟨m, hm, (hS m hm).2 hx hle⟩

/-- Every prime event structure is stable. -/
lemma PES.stable (P : PES L) : Stable P.toFamily := by
  intro S z hne hS _ _
  obtain ⟨m, hm⟩ := hne
  exact ⟨fun h₁ h₂ => (hS m hm).1 (Set.mem_sInter.mp h₁ m hm) (Set.mem_sInter.mp h₂ m hm),
         fun he hle => Set.mem_sInter.mpr
           (fun n hn => (hS n hn).2 (Set.mem_sInter.mp he n hn) hle)⟩

namespace Stable

variable {F : ConfFamily L}

/-- The least subconfiguration of `c` containing `x`: its history inside `c`. -/
def hist (F : ConfFamily L) (c : Set F.Event) (x : F.Event) : Set F.Event :=
  ⋂₀ {m | F.Config m ∧ m ⊆ c ∧ x ∈ m}

variable {c : Set F.Event} {x : F.Event}

lemma hist_subset (hc : F.Config c) (hx : x ∈ c) : hist F c x ⊆ c :=
  fun _ hy => Set.mem_sInter.mp hy c ⟨hc, subset_rfl, hx⟩

lemma hist_mem : x ∈ hist F c x :=
  Set.mem_sInter.mpr (fun _ hm => hm.2.2)

/-- Any subconfiguration of `c` containing `x` contains its history. -/
lemma hist_least {m : Set F.Event} (hm : F.Config m) (hmc : m ⊆ c) (hxm : x ∈ m) :
    hist F c x ⊆ m :=
  fun _ hy => Set.mem_sInter.mp hy m ⟨hm, hmc, hxm⟩

/-- The history is itself a configuration, because of stability. -/
lemma hist_config (hF : Stable F) (hc : F.Config c) (hx : x ∈ c) :
    F.Config (hist F c x) :=
  hF ⟨c, hc, subset_rfl, hx⟩ (fun _ hm => hm.1) hc (fun _ hm => hm.2.1)

end Stable
