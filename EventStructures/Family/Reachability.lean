import EventStructures.Family.Path
import Mathlib.Data.Set.Card

/-! # Reachability

Any configuration is reachable from a subconfiguration by firing the events of
the gap one at a time. This is `secured`, and it needs no decidability. -/

open ConfFamily

variable {L : Type*} (F : ConfFamily L)

private lemma path_exists_aux : ∀ (n : ℕ) (c₀ c : Conf F),
    c₀.val ⊆ c.val → (c.val \ c₀.val).Finite → (c.val \ c₀.val).ncard = n →
    Nonempty (Path F c₀ c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c₀ c hsub hfin hcard
    by_cases heq : c.val = c₀.val
    · exact ⟨(Subtype.ext heq.symm : c₀ = c) ▸ Path.refl⟩
    obtain ⟨e, hemem, hconf⟩ := F.secured c.2 c₀.2 hsub hfin heq
    have hunion : (c.val \ {e}) ∪ {e} = c.val := by
      ext x
      constructor
      · rintro (⟨hx, -⟩ | hx)
        · exact hx
        · exact (Set.mem_singleton_iff.mp hx) ▸ hemem.1
      · intro hx
        by_cases hxe : x = e
        · exact Or.inr (Set.mem_singleton_iff.mpr hxe)
        · exact Or.inl ⟨hx, fun h => hxe (Set.mem_singleton_iff.mp h)⟩
    have hsub' : c₀.val ⊆ c.val \ {e} := fun x hx =>
      ⟨hsub hx, fun hxe => hemem.2 ((Set.mem_singleton_iff.mp hxe) ▸ hx)⟩
    have hdiff : (c.val \ {e}) \ c₀.val = (c.val \ c₀.val) \ {e} := by
      ext x; constructor
      · rintro ⟨⟨hx, hxe⟩, hx₀⟩; exact ⟨⟨hx, hx₀⟩, hxe⟩
      · rintro ⟨⟨hx, hx₀⟩, hxe⟩; exact ⟨⟨hx, hxe⟩, hx₀⟩
    have hss : (c.val \ c₀.val) \ {e} ⊂ c.val \ c₀.val :=
      Set.sdiff_singleton_ssubset.mpr hemem
    have hfin' : ((c.val \ {e}) \ c₀.val).Finite := by rw [hdiff]; exact hfin.subset hss.subset
    obtain ⟨p⟩ := ih ((c.val \ {e}) \ c₀.val).ncard
      (by rw [hdiff]; exact hcard ▸ Set.ncard_lt_ncard hss hfin)
      c₀ ⟨c.val \ {e}, hconf⟩ hsub' hfin' rfl
    have henab : F.enables (c.val \ {e}) e := ⟨hconf, by rw [hunion]; exact c.2⟩
    exact ⟨Path.path_comp F p (Path.step ⟨e, henab, hunion.symm⟩ Path.refl)⟩

/-- A configuration is reachable from any subconfiguration with a finite gap. -/
lemma path_exists {c₀ c : Conf F} (hsub : c₀.val ⊆ c.val)
    (hfin : (c.val \ c₀.val).Finite) : Nonempty (Path F c₀ c) :=
  path_exists_aux F _ c₀ c hsub hfin rfl

/-- The same, as an execution list. -/
lemma execList_exists {c₀ c : Conf F} (hsub : c₀.val ⊆ c.val)
    (hfin : (c.val \ c₀.val).Finite) :
    Nonempty (Σ t : List F.Event, Path.ExecList F c₀ t c) := by
  obtain ⟨p⟩ := path_exists F hsub hfin
  exact ⟨⟨Path.trace F p, Path.execList_of_path F p⟩⟩
