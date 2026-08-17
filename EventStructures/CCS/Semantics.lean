import EventStructures.Prime.Basic
import EventStructures.LTS.Basic
import EventStructures.Prime.LTSI
import EventStructures.Prime.Residual
import EventStructures.CCS.Syntax
import EventStructures.CCS.Par

/-! # Event-structure semantics of CCS, and its coincidence with the operational one -/

open PES Configuration

namespace CCS

variable {Name : Type*}

/-- Empty event structure. -/
def empty : PES (Action Name) where
  Event := PEmpty
  poEvent :=
    { le := fun _ _ => True
      lt := fun _ _ => False
      le_refl := fun _ => trivial
      le_trans := fun _ _ _ _ _ => trivial
      lt_iff_le_not_ge := fun a _ => a.elim
      le_antisymm := fun a _ _ _ => a.elim }
  conflict := fun _ _ => False
  label := PEmpty.elim
  conflict_irrefl := fun _ h => h
  conflict_symm := fun _ _ h => h
  conflict_hereditary := fun h _ => h

/-- Prefix `α.E`: new initial event below all of `E`. -/
def pfx (α : Action Name) (E : PES (Action Name)) :
    PES (Action Name) where
  Event := Option E.Event
  poEvent :=
    { le := fun x y => match x, y with
        | none, _ => True
        | some _, none => False
        | some e, some e' => e ≤ e'
      lt := fun x y => match x, y with
        | none, some _ => True
        | some _, none => False
        | some e, some e' => e < e'
        | none, none => False
      le_refl := by intro x; cases x <;> simp
      le_trans := by
        intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all only
        exact le_trans hxy hyz
      le_antisymm := by
        intro x y hxy hyx; cases x <;> cases y <;> simp_all only [Option.some.injEq]
        exact E.poEvent.le_antisymm _ _ hxy hyx
      lt_iff_le_not_ge := by
        intro x y; cases x <;> cases y <;>
          simp_all only [not_true_eq_false, and_false, not_false_eq_true, and_self]
        exact lt_iff_le_not_ge }
  conflict := fun x y => match x, y with
    | some e, some e' => E.conflict e e'
    | _, _ => False
  label
    | none => α
    | some e => E.label e
  conflict_irrefl := by intro x; cases x <;> simp [E.conflict_irrefl]
  conflict_symm := by
    intro x y h; cases x <;> cases y <;> simp_all only
    exact E.conflict_symm h
  conflict_hereditary := by
    intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all only
    exact E.conflict_hereditary hxy hyz

/-- Sum `E + F`: disjoint events, all cross-component pairs conflict. -/
def sum (E F : PES (Action Name)) : PES (Action Name) where
  Event := E.Event ⊕ F.Event
  poEvent :=
    { le := fun x y => match x, y with
        | .inl e, .inl e' => e ≤ e'
        | .inr f, .inr f' => f ≤ f'
        | _, _ => False
      lt := fun x y => match x, y with
        | .inl e, .inl e' => e < e'
        | .inr f, .inr f' => f < f'
        | _, _ => False
      le_refl := by intro x; cases x <;> simp
      le_trans := by
        intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all only
        · exact le_trans hxy hyz
        · exact le_trans hxy hyz
      le_antisymm := by
        intro x y hxy hyx; cases x <;> cases y <;> simp_all only [Sum.inl.injEq, Sum.inr.injEq]
        · exact E.poEvent.le_antisymm _ _ hxy hyx
        · exact F.poEvent.le_antisymm _ _ hxy hyx
      lt_iff_le_not_ge := by
        intro x y; cases x <;> cases y <;> simp_all only [not_false_eq_true, and_true]
        · exact lt_iff_le_not_ge
        · exact lt_iff_le_not_ge }
  conflict := fun x y => match x, y with
    | .inl e, .inl e' => E.conflict e e'
    | .inr f, .inr f' => F.conflict f f'
    | _, _ => True
  label
    | .inl e => E.label e
    | .inr f => F.label f
  conflict_irrefl := by
    intro x; cases x <;> simp [E.conflict_irrefl, F.conflict_irrefl]
  conflict_symm := by
    intro x y h; cases x <;> cases y <;> simp_all only
    · exact E.conflict_symm h
    · exact F.conflict_symm h
  conflict_hereditary := by
    intro x y z hxy hyz; cases x <;> cases y <;> cases z <;> simp_all only [ge_iff_le]
    · exact E.conflict_hereditary hxy hyz
    · exact F.conflict_hereditary hxy hyz

/-- Restriction `(ν)E`: keep events whose past doesn't use the bound name. -/
def restrict (E : PES (Action (Option Name))) : PES (Action Name) where
  Event := {e : E.Event // ∀ e' ≤ e, (E.label e').strip.isSome = true}
  poEvent :=
    { le := fun x y => x.1 ≤ y.1
      lt := fun x y => x.1 < y.1
      le_refl _ := le_refl _
      le_trans _ _ _ := le_trans
      le_antisymm _ _ h h' := Subtype.ext (le_antisymm h h')
      lt_iff_le_not_ge _ _ := lt_iff_le_not_ge }
  conflict x y := E.conflict x.1 y.1
  label x := (E.label x.1).strip.get (x.2 x.1 le_rfl)
  conflict_irrefl x := E.conflict_irrefl x.1
  conflict_symm _ _ h := E.conflict_symm h
  conflict_hereditary {_ _ z} hxy hyz := E.conflict_hereditary hxy (show _ ≤ z.1 from hyz)



/-- A configuration of `(ν)E` seen in `E`. -/
def unres {E : PES (Action (Option Name))} (c : Set (restrict E).Event) :
    Set E.Event := {y | ∃ h, (⟨y, h⟩ : (restrict E).Event) ∈ c}

variable {E : PES (Action (Option Name))} {c : Set (restrict E).Event}

lemma mem_unres {x : E.Event} (hx : ∀ e' ≤ x, (E.label e').strip.isSome = true) :
    x ∈ unres c ↔ (⟨x, hx⟩ : (restrict E).Event) ∈ c := by
  constructor
  · rintro ⟨h, hm⟩
    exact (Subtype.ext rfl : (⟨x, h⟩ : (restrict E).Event) = ⟨x, hx⟩) ▸ hm
  · intro h; exact ⟨hx, h⟩

lemma unres_eq_image : unres c = Subtype.val '' c := by
  ext y
  constructor
  · rintro ⟨h, hm⟩; exact ⟨⟨y, h⟩, hm, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩

lemma unres_finite (h : c.Finite) : (unres c).Finite := by
  rw [unres_eq_image]; exact h.image _

lemma unres_isConf (h : isConf (restrict E) c) : isConf E (unres c) := by
  constructor
  · rintro y z ⟨_, hyc⟩ ⟨_, hzc⟩; exact h.1 hyc hzc
  · rintro y z ⟨hy, hyc⟩ hle
    exact ⟨fun w hw => hy w (hw.trans hle), h.2 hyc hle⟩

lemma unres_enables {x : E.Event} {hx : ∀ e' ≤ x, (E.label e').strip.isSome = true}
    (h : Configuration.enables (restrict E) c ⟨x, hx⟩) :
    Configuration.enables E (unres c) x := by
  refine ⟨unres_isConf h.1, ?_, ?_⟩
  · rintro y ⟨_, hyc⟩; exact h.2.1 _ hyc
  · rintro y hy; exact ⟨fun w hw => hx w (hw.trans (le_of_lt hy)), h.2.2 hy⟩

lemma unres_insert {x : E.Event} (hx : ∀ e' ≤ x, (E.label e').strip.isSome = true) :
    unres (c ∪ {⟨x, hx⟩}) = unres c ∪ {x} := by
  ext y
  constructor
  · rintro ⟨h, hm | hm⟩
    · exact Or.inl ⟨h, hm⟩
    · exact Or.inr (congrArg Subtype.val hm)
  · rintro (⟨h, hm⟩ | hm)
    · exact ⟨h, Or.inl hm⟩
    · exact ⟨hm ▸ hx, Or.inr (Subtype.ext hm)⟩

/-- `E ↪ α.E`. -/
def embSome (α : Action Name) (E : PES (Action Name)) : Emb E (pfx α E) where
  f := some
  inj := Option.some_injective _
  mono h := h
  smono h := h
  conf h := h

/-- `E ↪ E + F`. -/
def embInl (E F : PES (Action Name)) : Emb E (sum E F) where
  f := Sum.inl
  inj := Sum.inl_injective
  mono h := h
  smono h := h
  conf h := h

/-- `F ↪ E + F`. -/
def embInr (E F : PES (Action Name)) : Emb F (sum E F) where
  f := Sum.inr
  inj := Sum.inr_injective
  mono h := h
  smono h := h
  conf h := h

@[simp] lemma embSome_f (α : Action Name) (E : PES (Action Name)) :
    (embSome α E).f = some := rfl
@[simp] lemma embInl_f (E F : PES (Action Name)) : (embInl E F).f = Sum.inl := rfl
@[simp] lemma embInr_f (E F : PES (Action Name)) : (embInr E F).f = Sum.inr := rfl

/-- Event-structure semantics of finitary CCS. -/
def semantics {Name : Type*} : Process Name → PES (Action Name)
  | .nil => empty
  | .pre α P => pfx α (semantics P)
  | .sum P Q => sum (semantics P) (semantics Q)
  | .par P Q => par (semantics P) (semantics Q)
  | .res P => restrict (semantics P)

/-- Operational LTSI from CCS step relation (no independence). -/
def opLTSI (P : Process Name) : LTSI (Action Name) where
  State := Process Name
  init := P
  step := Step
  indep _ _ _ _ _ := False

/-- Denotational LTSI from the event-structure semantics. -/
def denLTSI (P : Process Name) : LTSI (Action Name) :=
  toLTSI (semantics P)

end CCS
