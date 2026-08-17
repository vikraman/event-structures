import EventStructures.Prime.Configuration
import EventStructures.Family.Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

variable {L : Type*} (es : PES L)

namespace Rollback

open Configuration ConfFamily
local infix:50 " ⊢ " => enables es


lemma rollback_subset_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 ⊆ c.1 \ es.future e := by
  intro x hx
  refine ⟨h.1 hx, ?_⟩
  intro hxFuture
  have hle : e ≤ x := hxFuture
  have hemem : e ∈ m.1 := (m.2).2 hx hle
  exact h.2.1 hemem

/-- Removing the future of `e` from a configuration keeps it a configuration. -/
lemma rollback_future_isConf {c : Conf es} {e : es.Event} :
    isConf es (c.1 \ es.future e) := by
  constructor
  · intro e₁ e₂ h₁ h₂
    rcases h₁ with ⟨h₁c, _⟩
    rcases h₂ with ⟨h₂c, _⟩
    exact c.2.1 h₁c h₂c
  · intro x y hx hy
    rcases hx with ⟨hxc, hxf⟩
    refine ⟨c.2.2 hxc hy, ?_⟩
    intro hyf
    have hle : e ≤ x := le_trans hyf hy
    exact hxf hle

/-- The canonical rollback configuration: remove all events causally after `e`. -/
def rollbackFuture (c : Conf es) (e : es.Event) : Conf es :=
  ⟨c.1 \ es.future e, rollback_future_isConf (es := es) (c := c)⟩

@[simp] lemma rollbackFuture_val (c : Conf es) (e : es.Event) :
    (rollbackFuture (es := es) c e).1 = c.1 \ es.future e :=
  rfl

@[simp] lemma rollbackFuture_mem {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (rollbackFuture (es := es) c e).1 ↔ x ∈ c.1 ∧ x ∉ es.future e :=
  Iff.rfl

/-- Redoability: `e` is enabled in `rollback(c,e)` when `e ∈ c`. -/
lemma rollback_redoable {c : Conf es} {e : es.Event} (he : e ∈ c.1) :
    (rollbackFuture (es := es) c e).1 ⊢ e := by
  constructor
  · exact rollback_future_isConf (es := es) (c := c)
  constructor
  · -- All events in rollback are consistent with e
    intro e' he'
    exact c.2.1 he he'.1
  · -- The strict past of e is contained in rollback
    intro x hx
    have hxc : x ∈ c.1 := c.2.2 he (le_of_lt hx)
    have hxnot : x ∉ es.future e := fun h => not_le_of_gt hx h
    exact ⟨hxc, hxnot⟩

/-- Causal safety: Rollback removes exactly the causal consequences of `e`. -/
lemma rollback_causal_safety {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (rollbackFuture (es := es) c e).1 → x ∉ es.future e :=
  fun hx => hx.2

/-- The canonical rollback is a rollback for `c` and `e`. -/
lemma rollback_future {c : Conf es} {e : es.Event} :
    isRollback es.toFamily c e (rollbackFuture (es := es) c e) := by
  constructor
  · exact fun _ hx => hx.1  -- Subset of c
  constructor
  · exact fun he => he.2 le_rfl  -- e not in rollback
  · -- Maximality
    intro m' hm'sub hm'not _ _ hx
    have hxc : _ ∈ c.1 := hm'sub hx
    have hxnot : _ ∉ es.future e := fun h => hm'not (m'.2.2 hx h)
    exact ⟨hxc, hxnot⟩

/-- Any rollback coincides with the canonical rollback. -/
@[simp] lemma rollback_eq_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 = c.1 \ es.future e := by
  apply Set.Subset.antisymm
  · exact rollback_subset_future (es := es) h
  · -- The canonical rollback is also a candidate, so m must contain it by maximality
    have hsub : c.1 \ es.future e ⊆ c.1 := fun x hx => hx.1
    have hnot : e ∉ c.1 \ es.future e := fun he => he.2 le_rfl
    exact h.2.2 (rollbackFuture (es := es) c e) hsub hnot (rollback_subset_future (es := es) h)

/-- Rollbacks are unique when they exist. -/
lemma rollback_unique {c : Conf es} {e : es.Event}
    {m₁ m₂ : Conf es} (h₁ : isRollback es.toFamily c e m₁) (h₂ : isRollback es.toFamily c e m₂) :
    m₁ = m₂ := by
  apply Subtype.ext
  rw [rollback_eq_future (es := es) h₁, rollback_eq_future (es := es) h₂]

/-- The rollback is the maximum element among rollback candidates. -/
lemma rollback_maximum {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) :
    ∀ m' : Conf es, m' ∈ RollbackCandidates es.toFamily c e → m'.1 ⊆ m.1 := by
  -- By uniqueness, m equals the canonical rollback
  have : m = rollbackFuture (es := es) c e :=
    rollback_unique (es := es) h (rollback_future (es := es))
  cases this
  -- Now show any candidate is a subset of the canonical rollback
  intro m' ⟨hm'sub, hm'not⟩ x hx
  exact ⟨hm'sub hx, fun hxFuture => hm'not (m'.2.2 hx hxFuture)⟩

/-- Correctness: `c` is reachable from `rollback(c,e)` when `c` is finite. -/
lemma rollback_correctness_finite {c : Conf es} {e : es.Event}
    (cF : Finset es.Event) (hcF : ∀ x, x ∈ cF ↔ x ∈ c.1) :
    Nonempty (Path es.toFamily (rollbackFuture (es := es) c e) c) := by
  have hcfin : (c.val : Set es.Event).Finite :=
    cF.finite_toSet.subset (fun x hx => Finset.mem_coe.mpr ((hcF x).mpr hx))
  exact path_exists es.toFamily (fun x hx => hx.1) (hcfin.subset (fun x hx => hx.1))

set_option linter.unusedDecidableInType false in
/-- Any path from a redo candidate `c'` to `c` is at least as long as the
number of events of `c` causally after `e`. -/
lemma rollback_minimality [DecidableEq es.Event] {c : Conf es} {e : es.Event}
    {c' : Conf es} (_hredo : c'.1 ⊢ e) (hsafe : ∀ x ∈ c'.1, x ∉ es.future e)
    (p' : Path es.toFamily c' c) :
    (c.1 ∩ es.future e).ncard ≤ Path.length es.toFamily p' := by
  have hexec : Path.ExecList es.toFamily c' (Path.trace es.toFamily p') c :=
    Path.execList_of_path es.toFamily p'
  set tr : List es.Event := Path.trace es.toFamily p' with htr
  have htgt : c.1 = c'.1 ∪ {x | x ∈ tr} :=
    Path.execList_target_eq_union es.toFamily hexec
  have hsub_set : c.1 ∩ es.future e ⊆ ↑tr.toFinset := by
    intro x ⟨hxc, hxfut⟩
    have hx_target : x ∈ c'.1 ∪ {y | y ∈ Path.trace es.toFamily p'} := htgt ▸ hxc
    rcases hx_target with hxc' | hxt
    · exact absurd hxfut (hsafe x hxc')
    · exact List.mem_toFinset.mpr hxt
  have hFsetFin : (tr.toFinset : Set es.Event).Finite :=
    tr.toFinset.finite_toSet
  calc (c.1 ∩ es.future e).ncard
      ≤ (↑tr.toFinset : Set es.Event).ncard :=
        Set.ncard_le_ncard hsub_set hFsetFin
    _ = tr.toFinset.card := Set.ncard_coe_finset _
    _ ≤ tr.length := List.toFinset_card_le _
    _ = Path.length es.toFamily p' := rfl

end Rollback
