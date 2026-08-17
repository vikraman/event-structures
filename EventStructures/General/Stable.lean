import EventStructures.General.Basic

/-! # Stable event structures

Stability axiom: two enabling sets for the same event, jointly
consistent with it, intersect in an enabling set. Causality is still
disjunctive, but each event acquires a least history inside a configuration. -/

/-- A general event structure whose enablings are closed under intersection. -/
structure SES (Label : Type*) extends GES Label where
  enable_inter : ∀ {X Y Z : Finset toGES.Event} {e}, enable X e → enable Y e →
    toGES.Consistent (↑X ∪ ↑Y ∪ {e}) → (↑Z : Set toGES.Event) = ↑X ∩ ↑Y → enable Z e

namespace SES

variable {L : Type*} (S : SES L)

/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => S.enable

/-- The configuration family of a stable event structure. -/
@[reducible] def toFamily : ConfFamily L := S.toGES.toFamily

@[simp] lemma toFamily_Config : S.toFamily.Config = S.toGES.isConf := rfl

variable {S}

open GES in
/-- Bounded binary intersections of configurations are configurations. -/
lemma inter_isConf {x y z : Set S.Event} (hx : S.toGES.isConf x) (hy : S.toGES.isConf y)
    (hz : S.toGES.isConf z) (hxz : x ⊆ z) (hyz : y ⊆ z) : S.toGES.isConf (x ∩ y) := by
  classical
  refine ⟨fun X hX => hz.1 X (hX.trans (fun _ hw => hxz hw.1)), ?_⟩
  have key : ∀ n e, e ∈ x → e ∈ y → S.toGES.rank x e = n →
      ∃ m, e ∈ S.toGES.secApprox (x ∩ y) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro e hex hey rfl
      obtain ⟨k, hk⟩ : ∃ k, S.toGES.rank x e = k + 1 := by
        have : S.toGES.rank x e ≠ 0 := by
          intro h0
          have hmem := rank_mem (hx.2 e hex)
          rw [h0] at hmem
          exact hmem
        exact ⟨S.toGES.rank x e - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hx.2 e hex)
      obtain ⟨j, hj⟩ := hy.2 e hey
      obtain ⟨k', hk'⟩ : ∃ k', j = k' + 1 := by
        cases j with
        | zero => exact hj.elim
        | succ k' => exact ⟨k', rfl⟩
      obtain ⟨-, Y, hYsub, hYen⟩ := hk' ▸ hj
      have hXx : ↑X ⊆ x := hXsub.trans (secApprox_subset k)
      have hYy : ↑Y ⊆ y := hYsub.trans (secApprox_subset k')
      have hcons : S.toGES.Consistent (↑X ∪ ↑Y ∪ {e}) :=
        fun W hW => hz.1 W (hW.trans (by
          rintro w ((hw | hw) | hw)
          · exact hxz (hXx hw)
          · exact hyz (hYy hw)
          · exact hxz (Set.mem_singleton_iff.mp hw ▸ hex)))
      have hen : (X ∩ Y) ⊢ e :=
        S.enable_inter hXen hYen hcons (by simp)
      obtain ⟨N, hN⟩ := exists_bound (x := x ∩ y) fun g hg => by
        rw [Finset.mem_inter] at hg
        refine ih _ ?_ g (hXx hg.1) (hYy hg.2) rfl
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg.1))
      exact ⟨N + 1, ⟨hex, hey⟩, X ∩ Y, hN, hen⟩
  exact fun e he => key _ e he.1 he.2 rfl

/-- Inside a bound `z`, an event has a least enabling set. -/
lemma exists_least_enabling {z : Set S.Event} (hz : S.toGES.isConf z) {e : S.Event}
    {X₀ : Finset S.Event} (hX₀ : X₀ ⊢ e) (hX₀z : ↑X₀ ⊆ z) (hez : e ∈ z) :
    ∃ M : Finset S.Event, (M ⊢ e) ∧ M ⊆ X₀ ∧
      ∀ Y : Finset S.Event, (Y ⊢ e) → ↑Y ⊆ z → M ⊆ Y := by
  classical
  have hmemP : ∀ {W : Finset S.Event},
      W ∈ X₀.powerset.filter (fun W => S.enable W e) ↔ W ⊆ X₀ ∧ (W ⊢ e) := by
    simp [Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨M, hM, hmin⟩ :=
    (X₀.powerset.filter (fun W => S.enable W e)).exists_min_image Finset.card
      ⟨X₀, hmemP.mpr ⟨subset_rfl, hX₀⟩⟩
  obtain ⟨hMX₀, hMen⟩ := hmemP.mp hM
  refine ⟨M, hMen, hMX₀, fun Y hYen hYz => ?_⟩
  have hcons : S.toGES.Consistent (↑M ∪ ↑Y ∪ {e}) :=
    fun W hW => hz.1 W (hW.trans (by
      rintro w ((hw | hw) | hw)
      · exact hX₀z (hMX₀ hw)
      · exact hYz hw
      · exact Set.mem_singleton_iff.mp hw ▸ hez))
  have hen : (M ∩ Y) ⊢ e := S.enable_inter hMen hYen hcons (by simp)
  have hcard := hmin (M ∩ Y) (hmemP.mpr ⟨(Finset.inter_subset_left).trans hMX₀, hen⟩)
  exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard) ▸
    Finset.inter_subset_right

end SES
