import EventStructures.Prime.Basic
import EventStructures.LTS.Basic
import EventStructures.Prime.LTSI
import EventStructures.CCS.Syntax
import EventStructures.CCS.Par

/-! # Event-structure semantics of CCS, and its coincidence with the operational one -/

open PES Configuration ConfFamily

namespace CCS

variable {Name : Type*}

variable {Name : Type*}

/-- No events. -/
@[reducible] def empty : SES (Action Name) where
  Event := PEmpty
  Con _ := True
  enable _ _ := True
  label := PEmpty.elim
  con_empty := trivial
  con_subset _ _ := trivial
  enable_mono _ _ _ := trivial
  enable_inter _ _ _ _ := trivial

/-- Prefix `α.E`: a new event below everything, which every `E`-event needs. -/
@[reducible] def pfx (α : Action Name) (E : SES (Action Name)) : SES (Action Name) where
  Event := Option E.Event
  Con X := E.toGES.Consistent {e | some e ∈ (X : Set (Option E.Event))}
  enable X
    | none => True
    | some e => none ∈ X ∧ ∃ Y : Finset E.Event, (∀ e' ∈ Y, some e' ∈ X) ∧ E.enable Y e
  label
    | none => α
    | some e => E.label e
  con_empty := by
    intro Y hY
    have hE : Y = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      have := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
      simp at this
    exact hE ▸ E.con_empty
  con_subset h hsub := fun Y hY => h Y fun e he => hsub (hY he)
  enable_mono := by
    rintro X Y (_ | e) h hsub -
    · exact trivial
    · exact ⟨hsub h.1, h.2.imp fun _ hY => ⟨fun e' he' => hsub (hY.1 e' he'), hY.2⟩⟩
  enable_inter := by
    classical
    rintro X Y Z (_ | e) hX hY hcons hZ
    · exact trivial
    · obtain ⟨hnX, YX, hYX, henX⟩ := hX
      obtain ⟨hnY, YY, hYY, henY⟩ := hY
      have hmemZ : ∀ {u : Option E.Event}, u ∈ X → u ∈ Y → u ∈ Z := by
        intro u h₁ h₂
        have : u ∈ (Z : Set (Option E.Event)) :=
          hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
        exact_mod_cast this
      refine ⟨hmemZ hnX hnY, YX ∩ YY, ?_, E.enable_inter henX henY ?_ (Finset.coe_inter _ _)⟩
      · intro e' he'
        rw [Finset.mem_inter] at he'
        exact hmemZ (hYX e' he'.1) (hYY e' he'.2)
      · intro W hW
        refine (hcons (W.image some) fun u hu => ?_) W fun w hw => ?_
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
          rcases hW (by exact_mod_cast hw) with (h | h) | h
          · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
          · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
          · exact Or.inr (congrArg some h)
        · exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩

/-- Sum `E + F`: disjoint events, and no configuration mixes the two sides. -/
@[reducible] def sum (E F : SES (Action Name)) : SES (Action Name) where
  Event := E.Event ⊕ F.Event
  Con X :=
    (∀ e, Sum.inl e ∈ X → ∀ f, Sum.inr f ∈ X → False) ∧
    E.toGES.Consistent {e | Sum.inl e ∈ (X : Set (E.Event ⊕ F.Event))} ∧
    F.toGES.Consistent {f | Sum.inr f ∈ (X : Set (E.Event ⊕ F.Event))}
  enable X
    | .inl e => ∃ Y : Finset E.Event, (∀ e' ∈ Y, Sum.inl e' ∈ X) ∧ E.enable Y e
    | .inr f => ∃ Y : Finset F.Event, (∀ f' ∈ Y, Sum.inr f' ∈ X) ∧ F.enable Y f
  label
    | .inl e => E.label e
    | .inr f => F.label f
  con_empty := by
    refine ⟨fun e he => absurd he (Finset.notMem_empty _), ?_, ?_⟩
    · intro Y hY
      have hE : Y = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        have := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
        simp at this
      exact hE ▸ E.con_empty
    · intro Y hY
      have hE : Y = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun f hf => ?_
        have := hY (show f ∈ (Y : Set F.Event) by exact_mod_cast hf)
        simp at this
      exact hE ▸ F.con_empty
  con_subset h hsub :=
    ⟨fun e he f hf => h.1 e (hsub he) f (hsub hf),
     fun Y hY => h.2.1 Y fun e he => hsub (hY he),
     fun Y hY => h.2.2 Y fun f hf => hsub (hY hf)⟩
  enable_mono := by
    rintro X Y (e | f) h hsub -
    · exact h.imp fun _ hY => ⟨fun e' he' => hsub (hY.1 e' he'), hY.2⟩
    · exact h.imp fun _ hY => ⟨fun f' hf' => hsub (hY.1 f' hf'), hY.2⟩
  enable_inter := by
    classical
    have hmemZ : ∀ {X Y Z : Finset (E.Event ⊕ F.Event)},
        (Z : Set (E.Event ⊕ F.Event)) = ↑X ∩ ↑Y →
        ∀ {u}, u ∈ X → u ∈ Y → u ∈ Z := by
      intro X Y Z hZ u h₁ h₂
      have : u ∈ (Z : Set (E.Event ⊕ F.Event)) :=
        hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
      exact_mod_cast this
    rintro X Y Z (e | f) hX hY hcons hZ
    · obtain ⟨YX, hYX, henX⟩ := hX
      obtain ⟨YY, hYY, henY⟩ := hY
      refine ⟨YX ∩ YY, fun e' he' => ?_,
        E.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at he'
        exact hmemZ hZ (hYX e' he'.1) (hYY e' he'.2)
      · refine (hcons (W.image Sum.inl) fun u hu => ?_).2.1 W fun w hw => by
          exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
        · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
        · exact Or.inr (congrArg Sum.inl h)
    · obtain ⟨YX, hYX, henX⟩ := hX
      obtain ⟨YY, hYY, henY⟩ := hY
      refine ⟨YX ∩ YY, fun f' hf' => ?_,
        F.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at hf'
        exact hmemZ hZ (hYX f' hf'.1) (hYY f' hf'.2)
      · refine (hcons (W.image Sum.inr) fun u hu => ?_).2.2 W fun w hw => by
          exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
        · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
        · exact Or.inr (congrArg Sum.inr h)

/-- Restriction `(ν)E`: keep the visible events. An event is enabled only when
some fully visible enabling set is available. -/
@[reducible] def restrict (E : SES (Action (Option Name))) : SES (Action Name) where
  Event := {e : E.Event // (E.label e).strip.isSome = true}
  Con X := E.toGES.Consistent
    {e | ∃ h, (⟨e, h⟩ : {e : E.Event // (E.label e).strip.isSome = true}) ∈ (X : Set _)}
  enable X e := ∃ Y : Finset E.Event,
    (∀ e' ∈ Y, ∃ h, (⟨e', h⟩ : {e : E.Event // (E.label e).strip.isSome = true}) ∈ X) ∧
    E.enable Y e.1
  label e := (E.label e.1).strip.get e.2
  con_empty := by
    intro Y hY
    have hE : Y = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨hv, hmem⟩ := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
      exact absurd hmem (by simp)
    exact hE ▸ E.con_empty
  con_subset h hsub := by
    refine fun Y hY => h Y fun e he => ?_
    obtain ⟨hv, hm⟩ := hY he
    exact ⟨hv, hsub hm⟩
  enable_mono := by
    rintro X Y e ⟨W, hW, hen⟩ hsub -
    refine ⟨W, fun e' he' => ?_, hen⟩
    obtain ⟨hv, hm⟩ := hW e' he'
    exact ⟨hv, hsub hm⟩
  enable_inter := by
    classical
    rintro X Y Z e ⟨YX, hYX, henX⟩ ⟨YY, hYY, henY⟩ hcons hZ
    have hmemZ : ∀ {u}, u ∈ X → u ∈ Y → u ∈ Z := by
      intro u h₁ h₂
      have : u ∈ (Z : Set _) := hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
      exact_mod_cast this
    refine ⟨YX ∩ YY, fun e' he' => ?_,
      E.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
    · rw [Finset.mem_inter] at he'
      obtain ⟨h₁, hm₁⟩ := hYX e' he'.1
      obtain ⟨h₂, hm₂⟩ := hYY e' he'.2
      exact ⟨h₁, hmemZ hm₁ hm₂⟩
    · have hvis : ∀ w ∈ W, (E.label w).strip.isSome = true := by
        intro w hw
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact (hYX w (by exact_mod_cast h)).choose
        · exact (hYY w (by exact_mod_cast h)).choose
        · exact h ▸ e.2
      refine hcons (W.attach.image fun w => ⟨w.1, hvis w.1 w.2⟩) (fun u hu => ?_) W
        fun w hw => ⟨hvis w (by exact_mod_cast hw), ?_⟩
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast w.2) with (h | h) | h
        · obtain ⟨hv, hm⟩ := hYX w.1 (by exact_mod_cast h)
          exact Or.inl (Or.inl (by exact_mod_cast hm))
        · obtain ⟨hv, hm⟩ := hYY w.1 (by exact_mod_cast h)
          exact Or.inl (Or.inr (by exact_mod_cast hm))
        · exact Or.inr (Subtype.ext h)
      · have hmem : (⟨w, hvis w (by exact_mod_cast hw)⟩ :
            {e : E.Event // (E.label e).strip.isSome = true}) ∈
            W.attach.image (fun z => (⟨z.1, hvis z.1 z.2⟩ :
              {e : E.Event // (E.label e).strip.isSome = true})) :=
          Finset.mem_image.mpr ⟨⟨w, by exact_mod_cast hw⟩, Finset.mem_attach _ _, rfl⟩
        exact_mod_cast hmem

/-! ## Projections of configurations

Each construction projects to its components, and the projection of a
configuration is a configuration. -/

variable {E F : SES (Action Name)} {α : Action Name}

lemma pmapSet_pfx (s : Set (Option E.Event)) :
    GES.pmapSet (G := (pfx α E).toGES) (H := E.toGES) id s = {z | some z ∈ s} := by
  refine Set.Subset.antisymm ?_ fun z hz => ⟨some z, hz, rfl⟩
  rintro z ⟨u, hu, hev⟩
  exact (hev ▸ hu : some z ∈ s)

lemma pmapSet_inl (s : Set (E.Event ⊕ F.Event)) :
    GES.pmapSet (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft? s
      = {z | Sum.inl z ∈ s} := by
  refine Set.Subset.antisymm ?_ fun z hz => ⟨Sum.inl z, hz, rfl⟩
  rintro z ⟨u, hu, hev⟩
  cases u with
  | inl w => exact (by simpa using hev : w = z) ▸ hu
  | inr w => exact absurd hev (by simp)

lemma pmapSet_inr (s : Set (E.Event ⊕ F.Event)) :
    GES.pmapSet (G := (sum E F).toGES) (H := F.toGES) Sum.getRight? s
      = {z | Sum.inr z ∈ s} := by
  refine Set.Subset.antisymm ?_ fun z hz => ⟨Sum.inr z, hz, rfl⟩
  rintro z ⟨u, hu, hev⟩
  cases u with
  | inr w => exact (by simpa using hev : w = z) ▸ hu
  | inl w => exact absurd hev (by simp)

lemma pfx_con {c : Set (Option E.Event)} (h : (pfx α E).toGES.Consistent c) :
    E.toGES.Consistent {z | some z ∈ c} := by
  classical
  intro V hV
  refine h (V.image some) (fun u hu => ?_) V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : some v ∈ V.image some := Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this

/-- The `E`-part of a configuration of `α.E` is a configuration. -/
lemma pfx_isConf {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) : E.toGES.isConf {z | some z ∈ c} := by
  refine (pmapSet_pfx (α := α) c) ▸ GES.isConf_pmap (G := (pfx α E).toGES) (H := E.toGES) id
    (fun {s} h => (pmapSet_pfx (α := α) s) ▸ pfx_con (c := s) h)
    (fun {X u x} hX hu => ?_) hc
  cases u with
  | none => exact absurd hu (by simp)
  | some z =>
    obtain ⟨-, Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨some y, hY y hy, rfl⟩, (Option.some.inj hu) ▸ hen⟩

/-- Every other event of a configuration of `α.E` requires the prefix. -/
lemma pfx_none_mem {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) {z : E.Event} (hz : some z ∈ c) : none ∈ c := by
  obtain ⟨Y, hen, hYc⟩ := GES.exists_enabling hc hz
  exact hYc hen.1

lemma sum_con_L {c : Set (E.Event ⊕ F.Event)} (h : (sum E F).toGES.Consistent c) :
    E.toGES.Consistent {z | Sum.inl z ∈ c} := by
  classical
  intro V hV
  refine (h ((V.image Sum.inl : Finset (E.Event ⊕ F.Event))) fun u hu => ?_).2.1 V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : Sum.inl v ∈ (V.image Sum.inl : Finset (E.Event ⊕ F.Event)) :=
      Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this

lemma sum_con_R {c : Set (E.Event ⊕ F.Event)} (h : (sum E F).toGES.Consistent c) :
    F.toGES.Consistent {z | Sum.inr z ∈ c} := by
  classical
  intro V hV
  refine (h ((V.image Sum.inr : Finset (E.Event ⊕ F.Event))) fun u hu => ?_).2.2 V fun v hv => ?_
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact hV (by exact_mod_cast hv)
  · have : Sum.inr v ∈ (V.image Sum.inr : Finset (E.Event ⊕ F.Event)) :=
      Finset.mem_image.mpr ⟨v, by exact_mod_cast hv, rfl⟩
    exact_mod_cast this

/-- The `E`-part of a configuration of `E + F` is a configuration. -/
lemma sum_isConf_L {c : Set (E.Event ⊕ F.Event)}
    (hc : (sum E F).toGES.isConf c) : E.toGES.isConf {z | Sum.inl z ∈ c} := by
  refine (pmapSet_inl c) ▸ GES.isConf_pmap (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft?
    (fun {s} h => (pmapSet_inl s) ▸ sum_con_L (c := s) h) (fun {X u x} hX hu => ?_) hc
  cases u with
  | inl z =>
    obtain ⟨Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨Sum.inl y, hY y hy, rfl⟩, (by simpa using hu : z = x) ▸ hen⟩
  | inr z => exact absurd hu (by simp)

/-- The `F`-part of a configuration of `E + F` is a configuration. -/
lemma sum_isConf_R {c : Set (E.Event ⊕ F.Event)}
    (hc : (sum E F).toGES.isConf c) : F.toGES.isConf {z | Sum.inr z ∈ c} := by
  refine (pmapSet_inr c) ▸ GES.isConf_pmap (G := (sum E F).toGES) (H := F.toGES) Sum.getRight?
    (fun {s} h => (pmapSet_inr s) ▸ sum_con_R (c := s) h) (fun {X u x} hX hu => ?_) hc
  cases u with
  | inr z =>
    obtain ⟨Y, hY, hen⟩ := hX
    exact ⟨Y, fun y hy => ⟨Sum.inr y, hY y hy, rfl⟩, (by simpa using hu : z = x) ▸ hen⟩
  | inl z => exact absurd hu (by simp)

/-- A configuration of `E + F` never mixes the two sides. -/
lemma sum_not_mixed {c : Set (E.Event ⊕ F.Event)} (hc : (sum E F).toGES.isConf c)
    {z : E.Event} (hz : Sum.inl z ∈ c) {w : F.Event} (hw : Sum.inr w ∈ c) : False := by
  classical
  exact (hc.1 {Sum.inl z, Sum.inr w} (by
    intro u hu
    rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
    · exact hz
    · exact (Finset.mem_singleton.mp hu') ▸ hw)).1 z (Finset.mem_insert_self _ _) w
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

lemma restrict_con {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (h : (restrict E).toGES.Consistent c) :
    E.toGES.Consistent {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by
  classical
  intro V hV
  have hvis : ∀ v ∈ V, (E.label v).strip.isSome = true :=
    fun v hv => (hV (show v ∈ (V : Set E.Event) by exact_mod_cast hv)).choose
  refine h (V.attach.image fun v => ⟨v.1, hvis v.1 v.2⟩) (fun u hu => ?_) V fun v hv => ?_
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hV (show v.1 ∈ (V : Set E.Event) by exact_mod_cast v.2)).choose_spec
  · refine ⟨hvis v (by exact_mod_cast hv), ?_⟩
    have hmem : (⟨v, hvis v (by exact_mod_cast hv)⟩ : (restrict E).Event) ∈
        V.attach.image (fun z => (⟨z.1, hvis z.1 z.2⟩ : (restrict E).Event)) :=
      Finset.mem_image.mpr ⟨⟨v, by exact_mod_cast hv⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast hmem

lemma pmapSet_unres {E : SES (Action (Option Name))} (s : Set (restrict E).Event) :
    GES.pmapSet (G := (restrict E).toGES) (H := E.toGES) (fun e => some e.1) s
      = {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ s} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨u, hu, hev⟩
    have hy : u.1 = y := by simpa using hev
    subst hy
    exact ⟨u.2, hu⟩
  · rintro y ⟨hy, hm⟩
    exact ⟨⟨y, hy⟩, hm, rfl⟩

/-- The `E`-part of a configuration of `(ν)E` is a configuration. -/
lemma restrict_isConf {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (hc : (restrict E).toGES.isConf c) :
    E.toGES.isConf {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by
  have h := GES.isConf_pmap (G := (restrict E).toGES) (H := E.toGES)
    (fun e => some e.1) (fun {s} h => (pmapSet_unres s) ▸ restrict_con (c := s) h)
    (fun {X u x} hX hu => by
      obtain ⟨Y, hY, hen⟩ := hX
      have hx : u.1 = x := by simpa using hu
      refine ⟨Y, fun y hy => ?_, hx ▸ hen⟩
      obtain ⟨hv, hm⟩ := hY y hy
      exact ⟨⟨y, hv⟩, hm, rfl⟩) hc
  rw [pmapSet_unres c] at h
  exact h

/-! ## Extending a configuration -/

lemma someInv_insert {c : Set (Option E.Event)} {x : E.Event} :
    {z | some z ∈ c ∪ ({some x} : Set (Option E.Event))} = {z | some z ∈ c} ∪ {x} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (Option.some.inj (Set.mem_singleton_iff.mp hz))
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp hz]; rfl)

lemma pfx_isConf_insert {c : Set (Option E.Event)} {x : E.Event}
    (hc : (pfx α E).toGES.isConf c) (hnone : none ∈ c)
    (hx : E.toGES.isConf ({z | some z ∈ c} ∪ {x})) (_hfr : some x ∉ c) :
    (pfx α E).toGES.isConf (c ∪ {some x}) := by
  classical
  refine GES.isConf_insert_pmap (G := (pfx α E).toGES) (H := E.toGES) id hc rfl ?_ ?_
    ((pmapSet_pfx (α := α) c) ▸ hx)
  · intro W hW V hV
    refine hx.1 V fun z hz => ?_
    obtain ⟨u, hu, hev⟩ : ∃ u, u ∈ (W : Set (Option E.Event)) ∧ u = some z := ⟨some z, hV hz, rfl⟩
    subst hev
    rcases hW hu with h | h
    · exact Or.inl h
    · exact Or.inr (Option.some.inj (Set.mem_singleton_iff.mp h))
  · intro Y hY hen
    refine ⟨insert none (Y.image some), ?_, ⟨Finset.mem_insert_self _ _, Y, ?_, hen⟩⟩
    · intro u hu
      rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
      · exact hnone
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu'
        obtain ⟨v, hv, hev⟩ := hY y hy
        exact hev ▸ hv
    · intro y hy
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

lemma inlInv_insert {c : Set (E.Event ⊕ F.Event)} {x : E.Event} :
    {z | Sum.inl z ∈ c ∪ ({Sum.inl x} : Set (E.Event ⊕ F.Event))} = {z | Sum.inl z ∈ c} ∪ {x} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by simpa using Set.mem_singleton_iff.mp hz)
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp hz]; rfl)

lemma inrInv_insert {c : Set (E.Event ⊕ F.Event)} {y : F.Event} :
    {z | Sum.inr z ∈ c ∪ ({Sum.inr y} : Set (E.Event ⊕ F.Event))} = {z | Sum.inr z ∈ c} ∪ {y} := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by simpa using Set.mem_singleton_iff.mp hz)
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp hz]; rfl)

lemma sum_isConf_insert_L {c : Set (E.Event ⊕ F.Event)} {x : E.Event}
    (hc : (sum E F).toGES.isConf c) (hnoR : ¬ ∃ f, Sum.inr f ∈ c)
    (hx : E.toGES.isConf ({z | Sum.inl z ∈ c} ∪ {x})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inl x}) := by
  classical
  refine GES.isConf_insert_pmap (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft? hc rfl
    ?_ ?_ ((pmapSet_inl c) ▸ hx)
  · refine fun W hW => ⟨fun e he f hf => ?_, fun V hV => ?_, fun V hV => ?_⟩
    · rcases hW (by exact_mod_cast hf) with h | h
      · exact hnoR ⟨f, h⟩
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine hx.1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using Set.mem_singleton_iff.mp h)
    · refine (sum_isConf_R hc).1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
  · intro Y hY hen
    refine ⟨Y.image Sum.inl, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      obtain ⟨v, hv, hev⟩ := hY y hy
      cases v with
      | inl w => exact (by simpa using hev : w = y) ▸ hv
      | inr w => exact absurd hev (by simp)
    · intro y hy
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

lemma sum_isConf_insert_R {c : Set (E.Event ⊕ F.Event)} {y : F.Event}
    (hc : (sum E F).toGES.isConf c) (hnoL : ¬ ∃ e, Sum.inl e ∈ c)
    (hy : F.toGES.isConf ({z | Sum.inr z ∈ c} ∪ {y})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inr y}) := by
  classical
  refine GES.isConf_insert_pmap (G := (sum E F).toGES) (H := F.toGES) Sum.getRight? hc rfl
    ?_ ?_ ((pmapSet_inr c) ▸ hy)
  · refine fun W hW => ⟨fun e he f hf => ?_, fun V hV => ?_, fun V hV => ?_⟩
    · rcases hW (by exact_mod_cast he) with h | h
      · exact hnoL ⟨e, h⟩
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine (sum_isConf_L hc).1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
    · refine hy.1 V fun z hz => ?_
      rcases hW (hV hz) with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using Set.mem_singleton_iff.mp h)
  · intro Y hY hen
    refine ⟨Y.image Sum.inr, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      obtain ⟨v, hv, hev⟩ := hY z hz
      cases v with
      | inr w => exact (by simpa using hev : w = z) ▸ hv
      | inl w => exact absurd hev (by simp)
    · intro z hz
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

lemma restrict_isConf_insert {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    {x : E.Event} {hx : (E.label x).strip.isSome = true}
    (hc : (restrict E).toGES.isConf c)
    (hxc : E.toGES.isConf ({y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} ∪ {x})) :
    (restrict E).toGES.isConf (c ∪ {⟨x, hx⟩}) := by
  classical
  refine GES.isConf_insert_pmap (G := (restrict E).toGES) (H := E.toGES)
    (fun e => some e.1) hc rfl ?_ ?_ ((pmapSet_unres c) ▸ hxc)
  · intro W hW V hV
    refine hxc.1 V fun z hz => ?_
    obtain ⟨hv, hm⟩ := hV hz
    rcases hW hm with h | h
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr (congrArg Subtype.val (Set.mem_singleton_iff.mp h))
  · intro Y hY hen
    refine ⟨Y.attach.image fun y => (hY y.1 y.2).choose, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      exact (hY y.1 y.2).choose_spec.1
    · intro y hy
      have hval : ((hY y hy).choose).1 = y :=
        Option.some.inj (hY y hy).choose_spec.2
      refine ⟨hval ▸ ((hY y hy).choose).2, ?_⟩
      have hmem : (hY y hy).choose ∈
          Y.attach.image (fun z => (hY z.1 z.2).choose) :=
        Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
      have : (⟨y, hval ▸ ((hY y hy).choose).2⟩ : (restrict E).Event) = (hY y hy).choose :=
        Subtype.ext hval.symm
      rw [this]
      exact_mod_cast hmem

/-- A configuration of `(ν)E` seen in `E`. -/
def unres {E : SES (Action (Option Name))} (c : Set (restrict E).Event) :
    Set E.Event := {y | ∃ h, (⟨y, h⟩ : (restrict E).Event) ∈ c}

variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}

lemma mem_unres {x : E.Event} (hx : (E.label x).strip.isSome = true) :
    x ∈ unres c ↔ (⟨x, hx⟩ : (restrict E).Event) ∈ c := by
  constructor
  · rintro ⟨h, hm⟩; exact hm
  · intro h; exact ⟨hx, h⟩

lemma unres_eq_image : unres c = Subtype.val '' c := by
  ext y
  constructor
  · rintro ⟨h, hm⟩; exact ⟨⟨y, h⟩, hm, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z.2, hz⟩

lemma unres_finite (h : c.Finite) : (unres c).Finite := by
  rw [unres_eq_image]; exact h.image _

lemma unres_insert {x : E.Event} (hx : (E.label x).strip.isSome = true) :
    unres (c ∪ {⟨x, hx⟩}) = unres c ∪ {x} := by
  ext y
  constructor
  · rintro ⟨h, hm | hm⟩
    · exact Or.inl ⟨h, hm⟩
    · exact Or.inr (congrArg Subtype.val hm)
  · rintro (⟨h, hm⟩ | hm)
    · exact ⟨h, Or.inl hm⟩
    · exact ⟨hm ▸ hx, Or.inr (Subtype.ext hm)⟩

set_option linter.checkUnivs false in
/-- Event-structure semantics of finitary CCS, as stable event structures. -/
@[reducible] def semantics {Name : Type u} : Process Name → SES (Action Name)
  | .nil => empty
  | .pre α P => pfx α (semantics P)
  | .sum P Q => sum (semantics P) (semantics Q)
  | .par P Q => parSES (semantics P) (semantics Q)
  | .res P => restrict (semantics P)

/-- Operational LTSI from CCS step relation (no independence). -/
def opLTSI (P : Process Name) : LTSI (Action Name) where
  State := Process Name
  init := P
  step := Step
  indep _ _ _ _ _ := False

set_option linter.checkUnivs false in
/-- Denotational LTSI: configurations of the semantics. -/
def denLTSI (P : Process Name) : LTSI (Action Name) :=
  ConfFamily.toLTSI (semantics P).toFamily

end CCS
