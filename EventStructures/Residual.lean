import EventStructures.Basic
import EventStructures.Configuration

/-! # Residual event structures and isomorphisms -/

namespace EventStructure

variable {L : Type*}

open Configuration

/-- The residual of `E` at configuration `c`: events outside `c` that are
consistent with everything in `c`. -/
def residual (E : EventStructure L) (c : Conf E) : EventStructure L where
  Event := {e : E.Event // e ∉ c.1 ∧ ∀ x ∈ c.1, ¬ E.conflict e x}
  poEvent :=
    { le := fun x y => x.1 ≤ y.1
      lt := fun x y => x.1 < y.1
      le_refl _ := le_refl _
      le_trans _ _ _ := le_trans
      le_antisymm _ _ h h' := Subtype.ext (le_antisymm h h')
      lt_iff_le_not_ge _ _ := lt_iff_le_not_ge }
  conflict x y := E.conflict x.1 y.1
  label x := E.label x.1
  conflict_irrefl x := E.conflict_irrefl x.1
  conflict_symm _ _ h := E.conflict_symm h
  conflict_hereditary {_ _ z} hxy hyz := E.conflict_hereditary hxy (show _ ≤ z.1 from hyz)

/-- An isomorphism of event structures: a bijection preserving order, conflict,
and labels. -/
structure Iso (E F : EventStructure L) where
  toFun : E.Event → F.Event
  invFun : F.Event → E.Event
  left_inv : ∀ e, invFun (toFun e) = e
  right_inv : ∀ f, toFun (invFun f) = f
  map_le : ∀ {e e'}, e ≤ e' ↔ toFun e ≤ toFun e'
  map_conflict : ∀ {e e'}, E.conflict e e' ↔ F.conflict (toFun e) (toFun e')
  map_label : ∀ e, F.label (toFun e) = E.label e

@[inherit_doc] infix:25 " ≃ₑ " => Iso

namespace Iso

variable {E F : EventStructure L}

lemma map_lt (iso : E ≃ₑ F) {e e' : E.Event} : e < e' ↔ iso.toFun e < iso.toFun e' := by
  simp only [lt_iff_le_not_ge, iso.map_le]

/-- Enabling at empty is preserved by isomorphism. -/
lemma map_enables_empty (iso : E ≃ₑ F) {e : E.Event} :
    Configuration.enables E ∅ e ↔ Configuration.enables F ∅ (iso.toFun e) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, hpast⟩
    refine ⟨⟨fun h _ _ => h.elim, fun h _ => h.elim⟩, fun _ h => h.elim, ?_⟩
    intro y hy
    have hinv : iso.invFun y < e := by
      rw [iso.map_lt, iso.right_inv]; exact hy
    exact absurd (hpast hinv) (Set.notMem_empty _)
  · rintro ⟨_, _, hpast⟩
    refine ⟨⟨fun h _ _ => h.elim, fun h _ => h.elim⟩, fun _ h => h.elim, ?_⟩
    intro x hx
    exact absurd (hpast (iso.map_lt.mp hx)) (Set.notMem_empty _)

end Iso

/-- An event of the residual lifts to an event of `E` outside `c` that is
consistent with all of `c`. -/
@[simp] lemma residual_val_not_mem {E : EventStructure L} {c : Conf E}
    (e : (residual E c).Event) : e.1 ∉ c.1 := e.2.1

@[simp] lemma residual_val_consistent {E : EventStructure L} {c : Conf E}
    (e : (residual E c).Event) : ∀ x ∈ c.1, ¬ E.conflict e.1 x := e.2.2

/-- The residual at an empty configuration is isomorphic to the original. -/
def init_iso (E : EventStructure L) (c : Conf E) (hc : c.1 = ∅) :
    E ≃ₑ residual E c where
  toFun e := ⟨e, by rw [hc]; exact Set.notMem_empty e,
                 fun x hx _ => absurd hx (hc ▸ Set.notMem_empty x)⟩
  invFun e := e.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_le := Iff.rfl
  map_conflict := Iff.rfl
  map_label _ := rfl

/-- Enabling in the residual at empty corresponds to enabling in the original
at `c`. -/
lemma residual_enables_empty_iff {E : EventStructure L} {c : Conf E}
    (e : (residual E c).Event) :
    enables (residual E c) ∅ e ↔ enables E c.1 e.1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, hpast⟩
    refine ⟨c.2, ?_, ?_⟩
    · intro x hx hconf; exact e.2.2 x hx hconf
    · intro x hx
      have hx_lt : x < e.1 := hx
      by_cases hxc : x ∈ c.1
      · exact hxc
      · let hx_resid : (residual E c).Event :=
          ⟨x, hxc, fun y hy hconf =>
            e.2.2 y hy
              (E.conflict_symm (E.conflict_hereditary (E.conflict_symm hconf) hx_lt.le))⟩
        exact absurd (hpast (show hx_resid < e from hx_lt)) (Set.notMem_empty hx_resid)
  · rintro ⟨_, _, hpast⟩
    refine ⟨⟨fun h _ _ => h.elim, fun h _ => h.elim⟩, fun _ h => h.elim, ?_⟩
    intro x hx
    exact absurd (hpast hx) x.2.1

end EventStructure
