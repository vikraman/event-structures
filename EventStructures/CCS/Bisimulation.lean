import EventStructures.LTS.Basic
import EventStructures.CCS.Semantics

/-! # Coincidence of the operational and denotational semantics of CCS

The bisimulation relates a configuration `c` of `⟦P⟧` to the residual process
`resid P c`, computed structurally. -/

open CCS ConfFamily

namespace CCS

universe u

variable {Name : Type u}

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
  | _, .par P Q, c => .par (resid P (projL c)) (resid Q (projR c))
  | _, .res P, c => .res (resid P (unres c))

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
    resid (.par P Q) c = .par (resid P (projL c)) (resid Q (projR c)) := by
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
      have hL : projL (∅ : Set (semantics (.par P Q)).Event) = ∅ := by
        ext e; constructor
        · rintro ⟨u, hu, -⟩; exact hu
        · exact fun h => h.elim
      have hR : projR (∅ : Set (semantics (.par P Q)).Event) = ∅ := by
        ext f; constructor
        · rintro ⟨u, hu, -⟩; exact hu
        · exact fun h => h.elim
      rw [hL, hR, resid_empty P, resid_empty Q]
  | _, .res P => by
      rw [resid_res]
      have h : unres (∅ : Set (semantics (.res P)).Event) = ∅ := by
        ext y; constructor
        · rintro ⟨h, hm⟩; exact hm
        · exact fun h => h.elim
      rw [h, resid_empty P]

/-- Completeness: firing an enabled event is a step of the residual process. -/
lemma den_to_op : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (e : (semantics P).Event), (semantics P).toGES.isConf c →
    (semantics P).toGES.isConf (c ∪ {e}) → e ∉ c →
    Step (resid P c) ((semantics P).label e) (resid P (c ∪ {e}))
  | _, .nil, _, e, _, _, _ => e.elim
  | _, .pre α P, c, e, hc, hins, hfr => by
    cases e with
    | none =>
        have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | none => exact hfr hz
          | some w => exact hfr (pfx_none_mem hc hz)
        subst hc0
        rw [resid_pre_neg (by simp)]
        have h1 : (∅ ∪ {none} : Set (semantics (.pre α P)).Event) = {none} := by simp
        rw [h1, resid_pre_pos (by simp)]
        have h2 : {y : (semantics P).Event |
            some y ∈ ({none} : Set (semantics (.pre α P)).Event)} = ∅ := by ext y; simp
        rw [h2, resid_empty]
        exact Step.pre
    | some x =>
        have hnone : none ∈ c := by
          rcases pfx_none_mem hins (Or.inr rfl : some x ∈ c ∪ {some x}) with h | h
          · exact h
          · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
        rw [resid_pre_pos hnone, resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}),
          someInv_insert]
        exact den_to_op P _ x (pfx_isConf hc) (someInv_insert ▸ pfx_isConf hins)
          (fun h => hfr h)
  | _, .sum P Q, c, e, hc, hins, hfr => by
    cases e with
    | inl x =>
        have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩
          exact sum_not_mixed hins (Or.inr rfl : Sum.inl x ∈ c ∪ {Sum.inl x}) (Or.inl hf)
        have hexNew : ∃ y, Sum.inl y ∈ c ∪ ({Sum.inl x} : Set (semantics (.sum P Q)).Event) :=
          ⟨x, Or.inr rfl⟩
        have ih := den_to_op P _ x (sum_isConf_L hc) (inlInv_insert ▸ sum_isConf_L hins)
          (fun h => hfr h)
        by_cases hex : ∃ y, Sum.inl y ∈ c
        · rw [resid_sum_l hex, resid_sum_l hexNew, inlInv_insert]
          exact ih
        · have hc0 : {y : (semantics P).Event | Sum.inl y ∈ c} = ∅ := by
            ext y
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨y, h⟩
          rw [resid_sum_none hex hnoR, resid_sum_l hexNew, inlInv_insert, hc0]
          rw [hc0, resid_empty] at ih
          exact Step.sumL ih
    | inr y =>
        have hnoL : ¬ ∃ e, Sum.inl e ∈ c := by
          rintro ⟨e, he⟩
          exact sum_not_mixed hins (Or.inl he) (Or.inr rfl : Sum.inr y ∈ c ∪ {Sum.inr y})
        have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
          rintro ⟨e, he | he⟩
          · exact hnoL ⟨e, he⟩
          · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
        have hexNew : ∃ z, Sum.inr z ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) :=
          ⟨y, Or.inr rfl⟩
        have ih := den_to_op Q _ y (sum_isConf_R hc) (inrInv_insert ▸ sum_isConf_R hins)
          (fun h => hfr h)
        by_cases hex : ∃ z, Sum.inr z ∈ c
        · rw [resid_sum_r hnoL hex, resid_sum_r hnoL' hexNew, inrInv_insert]
          exact ih
        · have hc0 : {z : (semantics Q).Event | Sum.inr z ∈ c} = ∅ := by
            ext z
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨z, h⟩
          rw [resid_sum_none hnoL hex, resid_sum_r hnoL' hexNew, inrInv_insert, hc0]
          rw [hc0, resid_empty] at ih
          exact Step.sumR ih
  | _, .res P, c, e, hc, hins, hfr => by
      obtain ⟨x, hx⟩ := e
      rw [resid_res, resid_res, unres_insert]
      refine Step.res ?_
      have ih := den_to_op P _ x (restrict_isConf hc)
        (unres_insert (c := c) hx ▸ restrict_isConf hins)
        (fun h => hfr ((mem_unres hx).mp h))
      rwa [show (semantics P).label x
            = Action.map some ((semantics (.res P)).label ⟨x, hx⟩) from
          Action.map_some_of_strip (Option.some_get _).symm] at ih
  | _, .par P Q, c, t, hc, hins, hfr => by
      rcases t with x | y | ⟨x, y, hpf⟩
      · obtain ⟨hxen, hxfr⟩ := enables_projL hins hfr (rfl : (Tag.left x).evL = some x)
        rw [resid_par, resid_par, projL_insert (rfl : (Tag.left x).evL = some x),
          projR_insert_none (rfl : (Tag.left x : Tag _ (semantics Q)).evR = none)]
        exact Step.parL (den_to_op P _ x (projL_isConf hc) hxen hxfr)
      · obtain ⟨hyen, hyfr⟩ := enables_projR hins hfr (rfl : (Tag.right y).evR = some y)
        rw [resid_par, resid_par,
          projL_insert_none (rfl : (Tag.right y : Tag (semantics P) _).evL = none),
          projR_insert (rfl : (Tag.right y).evR = some y)]
        exact Step.parR (den_to_op Q _ y (projR_isConf hc) hyen hyfr)
      · obtain ⟨hxen, hxfr⟩ := enables_projL hins hfr (rfl : (Tag.sync x y hpf).evL = some x)
        obtain ⟨hyen, hyfr⟩ := enables_projR hins hfr (rfl : (Tag.sync x y hpf).evR = some y)
        obtain ⟨a, hax, hay⟩ := hpf
        rw [resid_par, resid_par, projL_insert (rfl : (Tag.sync x y _).evL = some x),
          projR_insert (rfl : (Tag.sync x y _).evR = some y)]
        exact Step.parSync (a := a)
          (hax ▸ den_to_op P _ x (projL_isConf hc) hxen hxfr)
          (hay ▸ den_to_op Q _ y (projR_isConf hc) hyen hyfr)

/-- Soundness: every step of the residual process fires an enabled event. -/
lemma op_to_den : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (α : Action Name) (Q' : Process Name), (semantics P).toGES.isConf c →
    Step (resid P c) α Q' →
    ∃ e, (semantics P).toGES.isConf (c ∪ {e}) ∧ e ∉ c ∧
      (semantics P).label e = α ∧ Q' = resid P (c ∪ {e})
  | _, .nil, c, α, Q', _, hstep => by
      rw [resid_nil] at hstep; cases hstep
  | _, .pre α₀ P, c, α, Q', hc, hstep => by
      by_cases hnone : none ∈ c
      · rw [resid_pre_pos hnone] at hstep
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α Q' (pfx_isConf hc) hstep
        refine ⟨some x, ?_, fun h => hxfr h, hxlbl, ?_⟩
        · exact pfx_isConf_insert hc hnone (someInv_insert ▸ hxins) (fun h => hxfr h)
        · rw [resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}), someInv_insert]
          exact hxQ
      · rw [resid_pre_neg hnone] at hstep
        cases hstep
        have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | none => exact hnone hz
          | some w => exact hnone (pfx_none_mem hc hz)
        subst hc0
        refine ⟨none, ?_, by simp, rfl, ?_⟩
        · refine ⟨fun W hW V hV => ?_, ?_⟩
          · have : V = ∅ := by
              refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
              obtain ⟨u, hu, hev⟩ : ∃ u, u ∈ (W : Set (Option (semantics P).Event)) ∧ u = some z :=
                ⟨some z, hV (by exact_mod_cast hz), rfl⟩
              rcases hW hu with h | h
              · exact h.elim
              · exact absurd (hev ▸ Set.mem_singleton_iff.mp h) (by simp)
            exact this ▸ (semantics P).con_empty
          · rintro z (hz | hz)
            · exact hz.elim
            · replace hz : z = none := hz
              subst hz
              exact ⟨1, Or.inr rfl, ∅, by simp, trivial⟩
        · rw [resid_pre_pos (by simp : none ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none})]
          have h2 : {y : (semantics P).Event |
              some y ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none}} = ∅ := by
            ext y; simp
          rw [h2, resid_empty]
  | _, .sum P Q, c, α, Q', hc, hstep => by
      by_cases hexL : ∃ e, Sum.inl e ∈ c
      · have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩
          obtain ⟨e, he⟩ := hexL
          exact sum_not_mixed hc he hf
        rw [resid_sum_l hexL] at hstep
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α Q' (sum_isConf_L hc) hstep
        refine ⟨Sum.inl x, sum_isConf_insert_L hc hnoR (inlInv_insert ▸ hxins),
          fun h => hxfr h, hxlbl, ?_⟩
        rw [resid_sum_l ⟨x, Or.inr rfl⟩, inlInv_insert]
        exact hxQ
      by_cases hexR : ∃ f, Sum.inr f ∈ c
      · rw [resid_sum_r hexL hexR] at hstep
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := op_to_den Q _ α Q' (sum_isConf_R hc) hstep
        have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
          rintro ⟨e, he | he⟩
          · exact hexL ⟨e, he⟩
          · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
        refine ⟨Sum.inr y, sum_isConf_insert_R hc hexL (inrInv_insert ▸ hyins),
          fun h => hyfr h, hylbl, ?_⟩
        rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩, inrInv_insert]
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
        have hcE : (semantics (.sum P Q)).toGES.isConf ∅ := GES.isConf_empty _
        cases hstep with
        | sumL hs =>
          obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ :=
            op_to_den P ∅ α _ (GES.isConf_empty _) (by rw [resid_empty]; exact hs)
          have hemp : {z : (semantics P).Event |
              Sum.inl z ∈ (∅ : Set (semantics (.sum P Q)).Event)} = ∅ := by ext z; simp
          refine ⟨Sum.inl x, sum_isConf_insert_L hcE hexR ?_, by simp, hxlbl, ?_⟩
          · rw [hemp]; exact hxins
          · rw [resid_sum_l ⟨x, Or.inr rfl⟩, inlInv_insert, hemp]; exact hxQ
        | sumR hs =>
          obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ :=
            op_to_den Q ∅ α _ (GES.isConf_empty _) (by rw [resid_empty]; exact hs)
          have hemp : {z : (semantics Q).Event |
              Sum.inr z ∈ (∅ : Set (semantics (.sum P Q)).Event)} = ∅ := by ext z; simp
          have hnoL' : ¬ ∃ e, Sum.inl e ∈ (∅ : Set (semantics (.sum P Q)).Event) ∪ {Sum.inr y} := by
            rintro ⟨e, he | he⟩
            · exact he.elim
            · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
          refine ⟨Sum.inr y, sum_isConf_insert_R hcE hexL ?_, by simp, hylbl, ?_⟩
          · rw [hemp]; exact hyins
          · rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩, inrInv_insert, hemp]; exact hyQ
  | _, .res P, c, α, Q', hc, hstep => by
      rw [resid_res] at hstep
      cases hstep with
      | @res _ A _ A' hs =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := op_to_den P _ _ A' (restrict_isConf hc) hs
        have hx : ((semantics P).label x).strip.isSome = true := by rw [hxlbl]; simp
        refine ⟨⟨x, hx⟩, restrict_isConf_insert hc (unres_insert (c := c) hx ▸ hxins),
          fun hmem => hxfr ((mem_unres hx).mpr hmem), ?_, ?_⟩
        · change ((semantics P).label x).strip.get _ = α
          exact Option.some.inj
            ((Option.some_get _).trans (by rw [hxlbl]; exact Action.strip_map α))
        · rw [resid_res, unres_insert, hxQ]
          rfl
  | _, .par P Q, c, α, Q', hc, hstep => by
      rw [resid_par] at hstep
      cases hstep with
      | @parL _ _ _ A' _ hs =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := op_to_den P _ α A' (projL_isConf hc) hs
        refine ⟨Tag.left x, isConf_insert_tag hc ?_ ?_, ?_, hxlbl, ?_⟩
        · rintro x' hx'
          exact ⟨(Option.some.inj hx') ▸ hxins, (Option.some.inj hx') ▸ hxfr⟩
        · rintro y' hy'; exact absurd hy' (by simp [Tag.evR])
        · exact fun hmem => hxfr ⟨_, hmem, rfl⟩
        · rw [resid_par, projL_insert (rfl : (Tag.left x).evL = some x),
            projR_insert_none (rfl : (Tag.left x : Tag _ (semantics Q)).evR = none), ← hxQ]
      | @parR _ _ _ _ B' hs =>
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := op_to_den Q _ α B' (projR_isConf hc) hs
        refine ⟨Tag.right y, isConf_insert_tag hc ?_ ?_, ?_, hylbl, ?_⟩
        · rintro x' hx'; exact absurd hx' (by simp [Tag.evL])
        · rintro y' hy'
          exact ⟨(Option.some.inj hy') ▸ hyins, (Option.some.inj hy') ▸ hyfr⟩
        · exact fun hmem => hyfr ⟨_, hmem, rfl⟩
        · rw [resid_par,
            projL_insert_none (rfl : (Tag.right y : Tag (semantics P) _).evL = none),
            projR_insert (rfl : (Tag.right y).evR = some y), ← hyQ]
      | @parSync _ _ a _ _ _ hs1 hs2 =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := op_to_den P _ _ _ (projL_isConf hc) hs1
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := op_to_den Q _ _ _ (projR_isConf hc) hs2
        refine ⟨Tag.sync x y ⟨a, hxlbl, hylbl⟩, isConf_insert_tag hc ?_ ?_, ?_, rfl, ?_⟩
        · rintro x' hx'
          exact ⟨(Option.some.inj hx') ▸ hxins, (Option.some.inj hx') ▸ hxfr⟩
        · rintro y' hy'
          exact ⟨(Option.some.inj hy') ▸ hyins, (Option.some.inj hy') ▸ hyfr⟩
        · exact fun hmem => hxfr ⟨_, hmem, rfl⟩
        · rw [resid_par, projL_insert (rfl : (Tag.sync x y _).evL = some x),
            projR_insert (rfl : (Tag.sync x y _).evR = some y), ← hxQ, ← hyQ]

/-- Coincidence of the two semantics, via the residual process. -/
theorem op_den_bisim (P : Process Name) : Bisimilar (opLTSI P) (denLTSI P) := by
  refine ⟨fun Q c => Q = resid P c.1, (resid_empty P).symm, ?_, ?_⟩
  · rintro Q c α Q' rfl hstep
    obtain ⟨e, hins, hfr, hlbl, hQ⟩ := op_to_den P c.1 α Q' c.2 hstep
    exact ⟨⟨c.1 ∪ {e}, hins⟩, ⟨e, ⟨c.2, hins⟩, hfr, hlbl, rfl⟩, hQ⟩
  · rintro Q c α c' rfl ⟨e, hen, hfr, hlbl, htgt⟩
    refine ⟨resid P c'.1, ?_, rfl⟩
    rw [htgt, ← hlbl]
    exact den_to_op P c.1 e c.2 hen.2 hfr

end CCS
