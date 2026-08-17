import EventStructures.Family.Basic
import EventStructures.Prime.Configuration
import EventStructures.General.Stable
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

/-- Configurations bounded by a common configuration are closed under union. -/
def Coherent (F : ConfFamily L) : Prop :=
  ∀ {S : Set (Set F.Event)} {z : Set F.Event}, (∀ x ∈ S, F.Config x) →
    F.Config z → (∀ x ∈ S, x ⊆ z) → F.Config (⋃₀ S)

/-- Every general event structure is coherent. -/
lemma GES.coherent (G : GES L) : Coherent G.toFamily := by
  intro S z hS hz hsub
  refine ⟨fun X hX => hz.1 X (hX.trans (Set.sUnion_subset hsub)), ?_⟩
  rintro e ⟨m, hm, hem⟩
  obtain ⟨n, hn⟩ := (hS m hm).2 e hem
  exact ⟨n, GES.secApprox_mono_set (Set.subset_sUnion_of_mem hm) n hn⟩

open GES in
/-- Every stable event structure is stable. -/
lemma SES.stable (S : SES L) : Stable S.toFamily := by
  intro T z hne hT hz hsub
  obtain ⟨x₀, hx₀⟩ := hne
  have hsx₀ : ⋂₀ T ⊆ x₀ := fun _ hw => Set.mem_sInter.mp hw x₀ hx₀
  have hx₀z : x₀ ⊆ z := hsub x₀ hx₀
  refine ⟨fun X hX => hz.1 X (hX.trans (hsx₀.trans hx₀z)), ?_⟩
  have key : ∀ n e, e ∈ ⋂₀ T → S.toGES.rank x₀ e = n →
      ∃ m, e ∈ S.toGES.secApprox (⋂₀ T) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro e he rfl
      have hex₀ : e ∈ x₀ := hsx₀ he
      obtain ⟨k, hk⟩ : ∃ k, S.toGES.rank x₀ e = k + 1 := by
        have : S.toGES.rank x₀ e ≠ 0 := by
          intro h0
          have hmem := rank_mem ((hT x₀ hx₀).2 e hex₀)
          rw [h0] at hmem
          exact hmem
        exact ⟨S.toGES.rank x₀ e - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem ((hT x₀ hx₀).2 e hex₀)
      have hXz : (↑X : Set S.Event) ⊆ z := (hXsub.trans (secApprox_subset k)).trans hx₀z
      obtain ⟨M, hMen, hMX, hMleast⟩ :=
        SES.exists_least_enabling hz hXen hXz (hx₀z hex₀)
      have hMint : (↑M : Set S.Event) ⊆ ⋂₀ T := fun g hg => Set.mem_sInter.mpr fun x hx => by
        obtain ⟨Y, hYen, hYx⟩ :=
          exists_enabling (hT x hx) (Set.mem_sInter.mp he x hx)
        exact hYx (hMleast Y hYen (hYx.trans (hsub x hx)) hg)
      obtain ⟨N, hN⟩ := exists_bound (x := ⋂₀ T) (X := M) fun g hg => by
        refine ih _ ?_ g (hMint hg) rfl
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub (hMX hg)))
      exact ⟨N + 1, he, M, hN, hMen⟩
  exact fun e he => key _ e he rfl

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
