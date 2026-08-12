import EventStructures.Basic
import EventStructures.LTSI
import EventStructures.CCS.Syntax
import EventStructures.CCS.Par
import EventStructures.CCS.Semantics

/-! # Bisimulation between the operational and denotational semantics of CCS

The bisimulation relates a configuration `c` of `⟦P⟧` to the *residual process*
`resid P c`, computed structurally. -/

open EventStructure Configuration

namespace CCS

universe u

open scoped Classical in
/-- The process remaining after a configuration has fired. -/
noncomputable def resid : ∀ {Name : Type u}, (P : Process Name) →
    Set (semantics P).Event → Process Name
  | _, .nil, _ => .nil
  | _, .pre α P, c => if none ∈ c then resid P {e | some e ∈ c} else .pre α P
  | _, .sum P Q, c =>
      if ∃ e, Sum.inl e ∈ c then resid P {e | Sum.inl e ∈ c}
      else if ∃ f, Sum.inr f ∈ c then resid Q {f | Sum.inr f ∈ c}
      else .sum P Q
  | _, .par P Q, c => .par (resid P (projL (flat c))) (resid Q (projR (flat c)))
  | _, .res P, c => .res (resid P (unres c))

variable {Name : Type u}

@[simp] lemma resid_nil (c : Set (semantics (.nil : Process Name)).Event) :
    resid .nil c = .nil := rfl

lemma resid_pre_pos {α : Action Name} {P : Process Name}
    {c : Set (semantics (.pre α P)).Event} (h : none ∈ c) :
    resid (.pre α P) c = resid P {e | some e ∈ c} := by
  rw [resid]; simp [h]

lemma resid_pre_neg {α : Action Name} {P : Process Name}
    {c : Set (semantics (.pre α P)).Event} (h : none ∉ c) :
    resid (.pre α P) c = .pre α P := by
  rw [resid]; simp [h]

lemma resid_sum_l {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h : ∃ e, Sum.inl e ∈ c) : resid (.sum P Q) c = resid P {e | Sum.inl e ∈ c} := by
  rw [resid]; simp [h]

lemma resid_sum_r {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h1 : ¬ ∃ e, Sum.inl e ∈ c) (h2 : ∃ f, Sum.inr f ∈ c) :
    resid (.sum P Q) c = resid Q {f | Sum.inr f ∈ c} := by
  rw [resid]; simp [h1, h2]

lemma resid_sum_none {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h1 : ¬ ∃ e, Sum.inl e ∈ c) (h2 : ¬ ∃ f, Sum.inr f ∈ c) :
    resid (.sum P Q) c = .sum P Q := by
  rw [resid]; simp [h1, h2]

lemma resid_par {P Q : Process Name} (c : Set (semantics (.par P Q)).Event) :
    resid (.par P Q) c = .par (resid P (projL (flat c))) (resid Q (projR (flat c))) := by
  rw [resid]

lemma resid_res {P : Process (Option Name)} (c : Set (semantics (.res P)).Event) :
    resid (.res P) c = .res (resid P (unres c)) := by
  rw [resid]

@[simp] lemma resid_empty : ∀ {Name : Type u} (P : Process Name), resid P ∅ = P
  | _, .nil => rfl
  | _, .pre α P => resid_pre_neg (by simp)
  | _, .sum P Q => resid_sum_none (by simp) (by simp)
  | _, .par P Q => by
      rw [resid_par]
      have h : flat (∅ : Set (semantics (.par P Q)).Event) = ∅ := by ext t; simp [flat]
      rw [h, projL_empty, projR_empty, resid_empty P, resid_empty Q]
  | _, .res P => by
      rw [resid_res]
      have h : unres (∅ : Set (semantics (.res P)).Event) = ∅ := by ext e; simp [unres]
      rw [h, resid_empty P]


/-- Completeness: every event enabled at `c` is a step of the residual process. -/
lemma den_to_op : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (e : (semantics P).Event), c.Finite → isConf (semantics P) c →
    Configuration.enables (semantics P) c e → e ∉ c →
    Step (resid P c) ((semantics P).label e) (resid P (c ∪ {e}))
  | _, .nil, _, e, _, _, _, _ => e.elim
  | _, .pre α P, c, e, hfin, hc, hen, hfr => by
    cases e with
    | none =>
        have hc0 : c = ∅ := by
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          cases x with
          | none => exact hfr hx
          | some z => exact hfr (hc.2 hx trivial)
        subst hc0
        rw [resid_pre_neg (by simp)]
        have h1 : (∅ ∪ {none} : Set (semantics (.pre α P)).Event) = {none} := by simp
        rw [h1, resid_pre_pos (by simp)]
        have h2 : {y : (semantics P).Event |
            some y ∈ ({none} : Set (semantics (.pre α P)).Event)} = ∅ := by ext y; simp
        rw [h2, resid_empty]
        exact Step.pre
    | some x =>
        have hnone : none ∈ c :=
          hen.2.2 (show (none : (semantics (.pre α P)).Event) < some x from trivial)
        rw [resid_pre_pos hnone, resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}),
          preimage_insert (Option.some_injective _)]
        exact den_to_op P _ x ((embSome α _).finite hfin) ((embSome α _).conf_restrict hc)
          ((embSome α _).enables_restrict hc hen) hfr
  | _, .sum P Q, c, e, hfin, hc, hen, hfr => by
    cases e with
    | inl x =>
        have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩; exact hen.2.1 _ hf trivial
        have hexNew : ∃ y, Sum.inl y ∈ c ∪ ({Sum.inl x} : Set (semantics (.sum P Q)).Event) :=
          ⟨x, Or.inr rfl⟩
        by_cases hex : ∃ y, Sum.inl y ∈ c
        · rw [resid_sum_l hex, resid_sum_l hexNew, preimage_insert Sum.inl_injective]
          exact den_to_op P _ x ((embInl _ _).finite hfin) ((embInl _ _).conf_restrict hc)
            ((embInl _ _).enables_restrict hc hen) hfr
        · have hc0 : {y : (semantics P).Event | Sum.inl y ∈ c} = ∅ := by
            ext y
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨y, h⟩
          rw [resid_sum_none hex hnoR, resid_sum_l hexNew,
            preimage_insert Sum.inl_injective, hc0]
          have ih := den_to_op P _ x ((embInl _ _).finite hfin) ((embInl _ _).conf_restrict hc)
            ((embInl _ _).enables_restrict hc hen) hfr
          simp only [embInl_f] at ih
          rw [hc0, resid_empty] at ih
          exact Step.sumL ih
    | inr y =>
        have hnoL : ¬ ∃ e, Sum.inl e ∈ c := by
          rintro ⟨e, he⟩; exact hen.2.1 _ he trivial
        have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
          rintro ⟨e, he | he⟩
          · exact hnoL ⟨e, he⟩
          · exact absurd he (by simp)
        have hexNew : ∃ z, Sum.inr z ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) :=
          ⟨y, Or.inr rfl⟩
        by_cases hex : ∃ z, Sum.inr z ∈ c
        · rw [resid_sum_r hnoL hex, resid_sum_r hnoL' hexNew, preimage_insert Sum.inr_injective]
          exact den_to_op Q _ y ((embInr _ _).finite hfin) ((embInr _ _).conf_restrict hc)
            ((embInr _ _).enables_restrict hc hen) hfr
        · have hc0 : {z : (semantics Q).Event | Sum.inr z ∈ c} = ∅ := by
            ext z
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨z, h⟩
          rw [resid_sum_none hnoL hex, resid_sum_r hnoL' hexNew,
            preimage_insert Sum.inr_injective, hc0]
          have ih := den_to_op Q _ y ((embInr _ _).finite hfin) ((embInr _ _).conf_restrict hc)
            ((embInr _ _).enables_restrict hc hen) hfr
          simp only [embInr_f] at ih
          rw [hc0, resid_empty] at ih
          exact Step.sumR ih
  | _, .res P, c, e, hfin, hc, hen, hfr => by
      obtain ⟨x, hx⟩ := e
      rw [resid_res, resid_res, unres_insert]
      refine Step.res ?_
      have ih := den_to_op P _ x (unres_finite hfin) (unres_isConf hc) (unres_enables hen)
        (fun h => hfr ((mem_unres hx).mp h))
      rwa [show (semantics P).label x
            = Action.map some ((semantics (.res P)).label ⟨x, hx⟩) from
          Action.map_some_of_strip (Option.some_get _).symm] at ih
  | _, .par P Q, c, q, hfin, hc, hen, hfr => by
      have hXfin := projL_finite (flat_finite hfin)
      have hYfin := projR_finite (flat_finite hfin)
      have hXconf := (isState_flat hc).2.2.1
      have hYconf := (isState_flat hc).2.2.2
      have hlbl : (semantics (.par P Q)).label q = q.top.label := rfl
      cases htop : q.top with
      | left x =>
        have hevL : q.top.evL = some x := by rw [htop]; rfl
        have hevR : q.top.evR = (none : Option (semantics Q).Event) := by rw [htop]; rfl
        obtain ⟨hxen, hxfr⟩ := comp_enables_L hc hen hfr hevL
        rw [resid_par, resid_par, flat_insert_projL hen.2.2 hevL,
          flat_insert_projR_none hen.2.2 hevR, hlbl, htop]
        exact Step.parL (den_to_op P _ x hXfin hXconf hxen hxfr)
      | right y =>
        have hevL : q.top.evL = (none : Option (semantics P).Event) := by rw [htop]; rfl
        have hevR : q.top.evR = some y := by rw [htop]; rfl
        obtain ⟨hyen, hyfr⟩ := comp_enables_R hc hen hfr hevR
        rw [resid_par, resid_par, flat_insert_projL_none hen.2.2 hevL,
          flat_insert_projR hen.2.2 hevR, hlbl, htop]
        exact Step.parR (den_to_op Q _ y hYfin hYconf hyen hyfr)
      | sync x y hpf =>
        have hevL : q.top.evL = some x := by rw [htop]; rfl
        have hevR : q.top.evR = some y := by rw [htop]; rfl
        obtain ⟨hxen, hxfr⟩ := comp_enables_L hc hen hfr hevL
        obtain ⟨hyen, hyfr⟩ := comp_enables_R hc hen hfr hevR
        obtain ⟨a, hax, hay⟩ := hpf
        rw [resid_par, resid_par, flat_insert_projL hen.2.2 hevL,
          flat_insert_projR hen.2.2 hevR, hlbl, htop]
        exact Step.parSync (a := a) (hax ▸ den_to_op P _ x hXfin hXconf hxen hxfr)
          (hay ▸ den_to_op Q _ y hYfin hYconf hyen hyfr)

/-- Soundness: every step of the residual process is an event enabled at `c`. -/
lemma op_to_den : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (α : Action Name) (Q' : Process Name), c.Finite → isConf (semantics P) c →
    Step (resid P c) α Q' →
    ∃ e, Configuration.enables (semantics P) c e ∧ e ∉ c ∧
      (semantics P).label e = α ∧ Q' = resid P (c ∪ {e})
  | _, .nil, c, α, Q', _, _, hstep => by
      rw [resid_nil] at hstep; cases hstep
  | _, .pre α₀ P, c, α, Q', hfin, hc, hstep => by
      by_cases hnone : none ∈ c
      · rw [resid_pre_pos hnone] at hstep
        obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α Q'
          ((embSome α₀ _).finite hfin) ((embSome α₀ _).conf_restrict hc) hstep
        refine ⟨some x, ⟨hc, ?_, ?_⟩, hxfr, hxlbl, ?_⟩
        · rintro (_ | z) hz
          · exact fun h => h
          · exact hxen.2.1 z hz
        · rintro (_ | z) hz
          · exact hnone
          · exact hxen.2.2 hz
        · rw [resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}),
            preimage_insert (Option.some_injective _)]
          exact hxQ
      · rw [resid_pre_neg hnone] at hstep
        cases hstep
        have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | none => exact hnone hz
          | some w => exact hnone (hc.2 hz trivial)
        subst hc0
        refine ⟨none, ⟨hc, fun z hz => absurd hz (by simp), fun z hz => by
            cases z <;> exact hz.elim⟩, by simp, rfl, ?_⟩
        rw [resid_pre_pos (by simp : none ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none})]
        have h2 : {y : (semantics P).Event |
            some y ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none}} = ∅ := by
          ext y; simp
        rw [h2, resid_empty]
  | _, .sum P Q, c, α, Q', hfin, hc, hstep => by
      by_cases hexL : ∃ e, Sum.inl e ∈ c
      · have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩
          obtain ⟨e, he⟩ := hexL
          exact hc.1 he hf trivial
        rw [resid_sum_l hexL] at hstep
        obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α Q'
          ((embInl _ _).finite hfin) ((embInl _ _).conf_restrict hc) hstep
        refine ⟨Sum.inl x, ⟨hc, ?_, ?_⟩, hxfr, hxlbl, ?_⟩
        · rintro (z | z) hz
          · exact hxen.2.1 z hz
          · exact absurd ⟨z, hz⟩ hnoR
        · rintro (z | z) hz
          · exact hxen.2.2 hz
          · exact hz.elim
        · rw [resid_sum_l ⟨x, Or.inr rfl⟩, preimage_insert Sum.inl_injective]
          exact hxQ
      by_cases hexR : ∃ f, Sum.inr f ∈ c
      · rw [resid_sum_r hexL hexR] at hstep
        obtain ⟨y, hyen, hyfr, hylbl, hyQ⟩ := op_to_den Q _ α Q'
          ((embInr _ _).finite hfin) ((embInr _ _).conf_restrict hc) hstep
        refine ⟨Sum.inr y, ⟨hc, ?_, ?_⟩, hyfr, hylbl, ?_⟩
        · rintro (z | z) hz
          · exact absurd ⟨z, hz⟩ hexL
          · exact hyen.2.1 z hz
        · rintro (z | z) hz
          · exact hz.elim
          · exact hyen.2.2 hz
        · have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
            rintro ⟨e, he | he⟩
            · exact hexL ⟨e, he⟩
            · exact absurd he (by simp)
          rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩, preimage_insert Sum.inr_injective]
          exact hyQ
      · have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | inl w => exact hexL ⟨w, hz⟩
          | inr w => exact hexR ⟨w, hz⟩
        subst hc0
        rw [resid_sum_none hexL hexR] at hstep
        have hcEP := Configuration.isConf_empty (semantics P)
        have hcEQ := Configuration.isConf_empty (semantics Q)
        have hcES := Configuration.isConf_empty (semantics (.sum P Q))
        cases hstep with
        | sumL hs =>
          obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ :=
            op_to_den P ∅ α _ Set.finite_empty hcEP (by rw [resid_empty]; exact hs)
          refine ⟨Sum.inl x, ⟨hcES, fun z hz => absurd hz (by simp), fun z hz => ?_⟩,
            by simp, hxlbl, ?_⟩
          · cases z with
            | inl w => exact hxen.2.2 hz
            | inr w => exact hz.elim
          · rw [resid_sum_l ⟨x, Or.inr rfl⟩]
            rw [preimage_insert Sum.inl_injective]; exact hxQ
        | sumR hs =>
          obtain ⟨y, hyen, hyfr, hylbl, hyQ⟩ :=
            op_to_den Q ∅ α _ Set.finite_empty hcEQ (by rw [resid_empty]; exact hs)
          have hnoL' : ¬ ∃ e, Sum.inl e ∈ (∅ : Set (semantics (.sum P Q)).Event) ∪ {Sum.inr y} := by
            rintro ⟨e, he | he⟩
            · exact he.elim
            · exact absurd he (by simp)
          refine ⟨Sum.inr y, ⟨hcES, fun z hz => absurd hz (by simp), fun z hz => ?_⟩,
            by simp, hylbl, ?_⟩
          · cases z with
            | inl w => exact hz.elim
            | inr w => exact hyen.2.2 hz
          · rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩]
            rw [preimage_insert Sum.inr_injective]; exact hyQ
  | _, .res P, c, α, Q', hfin, hc, hstep => by
      rw [resid_res] at hstep
      cases hstep with
      | @res _ A _ A' hs =>
        obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ :=
          op_to_den P _ _ A' (unres_finite hfin) (unres_isConf hc) hs
        have hx : ∀ x' ≤ x, ((semantics P).label x').strip.isSome = true := by
          intro x' hle
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact (hxen.2.2 hlt).choose x' le_rfl
          · rw [hxlbl]; simp
        refine ⟨⟨x, hx⟩, ⟨hc, ?_, ?_⟩, ?_, ?_, ?_⟩
        · rintro ⟨z, hz⟩ hzc; exact hxen.2.1 z ⟨hz, hzc⟩
        · rintro ⟨z, hz⟩ hlt; exact (mem_unres hz).mp (hxen.2.2 hlt)
        · exact fun hmem => hxfr ((mem_unres hx).mpr hmem)
        · change ((semantics P).label x).strip.get _ = α
          exact Option.some.inj
            ((Option.some_get _).trans (by rw [hxlbl]; exact Action.strip_map α))
        · rw [resid_res, unres_insert, hxQ]
  | _, .par P Q, c, α, Q', hfin, hc, hstep => by
      rw [resid_par] at hstep
      have hXfin := projL_finite (flat_finite hfin)
      have hYfin := projR_finite (flat_finite hfin)
      have hXconf := (isState_flat hc).2.2.1
      have hYconf := (isState_flat hc).2.2.2
      cases hstep with
      | @parL _ _ _ A' _ hs =>
        obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α A' hXfin hXconf hs
        obtain ⟨q, hqen, hqfr, hqtop⟩ := exists_event_tag hfin hc (Tag.left x)
          (by tag_side ⟨hxen, hxfr⟩) (by tag_side)
        have hevL : q.top.evL = some x := by rw [hqtop]; rfl
        have hevR : q.top.evR = (none : Option (semantics Q).Event) := by rw [hqtop]; rfl
        refine ⟨q, hqen, hqfr, ?_, ?_⟩
        · change q.top.label = α
          rw [hqtop]; exact hxlbl
        · rw [resid_par, flat_insert_projL hqen.2.2 hevL,
            flat_insert_projR_none hqen.2.2 hevR, ← hxQ]
      | @parR _ _ _ _ B' hs =>
        obtain ⟨y, hyen, hyfr, hylbl, hyQ⟩ := op_to_den Q _ α B' hYfin hYconf hs
        obtain ⟨q, hqen, hqfr, hqtop⟩ := exists_event_tag hfin hc (Tag.right y)
          (by tag_side) (by tag_side ⟨hyen, hyfr⟩)
        have hevL : q.top.evL = (none : Option (semantics P).Event) := by rw [hqtop]; rfl
        have hevR : q.top.evR = some y := by rw [hqtop]; rfl
        refine ⟨q, hqen, hqfr, ?_, ?_⟩
        · change q.top.label = α
          rw [hqtop]; exact hylbl
        · rw [resid_par, flat_insert_projL_none hqen.2.2 hevL,
            flat_insert_projR hqen.2.2 hevR, ← hyQ]
      | @parSync _ _ a _ _ _ hs1 hs2 =>
        obtain ⟨x, hxen, hxfr, hxlbl, hxQ⟩ := op_to_den P _ _ _ hXfin hXconf hs1
        obtain ⟨y, hyen, hyfr, hylbl, hyQ⟩ := op_to_den Q _ _ _ hYfin hYconf hs2
        obtain ⟨q, hqen, hqfr, hqtop⟩ :=
          exists_event_tag hfin hc (Tag.sync x y ⟨a, hxlbl, hylbl⟩)
            (by tag_side ⟨hxen, hxfr⟩) (by tag_side ⟨hyen, hyfr⟩)
        have hevL : q.top.evL = some x := by rw [hqtop]; rfl
        have hevR : q.top.evR = some y := by rw [hqtop]; rfl
        refine ⟨q, hqen, hqfr, ?_, ?_⟩
        · change q.top.label = Action.tau
          rw [hqtop]; rfl
        · rw [resid_par, flat_insert_projL hqen.2.2 hevL,
            flat_insert_projR hqen.2.2 hevR, ← hxQ, ← hyQ]

/-- Coincidence of the two semantics, via the residual process. -/
theorem op_den_bisim (P : Process Name) : Bisimilar (opLTSI P) (denLTSI P) := by
  refine ⟨fun Q c => c.1.Finite ∧ Q = resid P c.1, ⟨Set.finite_empty, (resid_empty P).symm⟩,
    ?_, ?_⟩
  · rintro Q c α Q' ⟨hfin, rfl⟩ hstep
    obtain ⟨e, hen, hfr, hlbl, hQ⟩ := op_to_den P c.1 α Q' hfin c.2 hstep
    exact ⟨⟨c.1 ∪ {e}, enables_extension (es := semantics P) hen⟩,
      ⟨e, hen, hfr, hlbl, rfl⟩, hfin.union (Set.finite_singleton e), hQ⟩
  · rintro Q c α c' ⟨hfin, rfl⟩ ⟨e, hen, hfr, hlbl, htgt⟩
    refine ⟨resid P c'.1, ?_, ?_, rfl⟩
    · rw [htgt, ← hlbl]
      exact den_to_op P c.1 e hfin c.2 hen hfr
    · rw [htgt]
      exact hfin.union (Set.finite_singleton e)

end CCS
