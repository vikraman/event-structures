import EventStructures.Stable.Basic
import EventStructures.Family.Rollback

/-! # Rollback for a coherent family

`rollbackSet c e` is the union of all subconfigurations of `c` omitting `e`.
When the family is coherent it is a configuration, hence the greatest such
subconfiguration, and rollbacks are unique. -/

open ConfFamily Rollback

variable {L : Type*} {F : ConfFamily L}

namespace Stable

/-- The rollback set is a configuration. -/
lemma rollbackSet_config (hF : Coherent F) (c : Conf F) (e : F.Event) :
    F.Config (rollbackSet F c e) :=
  hF (fun _ hm => hm.1) c.2 (fun _ hm => hm.2.1)

/-- The rollback set, as a configuration. -/
def rollbackConf (hF : Coherent F) (c : Conf F) (e : F.Event) : Conf F :=
  ⟨rollbackSet F c e, rollbackSet_config hF c e⟩

/-- It is the greatest subconfiguration of `c` omitting `e`. -/
lemma rollbackConf_maximum (hF : Coherent F) (c : Conf F) (e : F.Event)
    (m : Conf F) (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) :
    m.val ⊆ (rollbackConf hF c e).val :=
  subset_rollbackSet F hmc hem

/-- Hence it is a rollback. -/
lemma isRollback_rollbackConf (hF : Coherent F) (c : Conf F) (e : F.Event) :
    isRollback F c e (rollbackConf hF c e) :=
  ⟨rollbackSet_subset F c e, rollbackSet_not_mem F c e,
   fun _ hm'c hem' _ => subset_rollbackSet F hm'c hem'⟩

/-- Rollbacks are unique: any rollback is the rollback set. -/
lemma rollback_unique (hF : Coherent F) {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m = rollbackConf hF c e :=
  Subtype.ext (Set.Subset.antisymm
    (subset_rollbackSet F h.1 h.2.1)
    (h.2.2 (rollbackConf hF c e) (rollbackSet_subset F c e) (rollbackSet_not_mem F c e)
      (subset_rollbackSet F h.1 h.2.1)))

end Stable
