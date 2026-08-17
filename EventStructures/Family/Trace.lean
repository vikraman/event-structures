import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import EventStructures.Family.Basic

/-! # Traces up to independence

Trace equivalence over an arbitrary independence relation. Only symmetry of the
relation is ever needed, and only for `traceEquiv_symm`. -/

variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)

/-- Two traces are equivalent when one is obtained from the other by swapping
adjacent independent events. -/
inductive TraceEquiv : List α → List α → Prop
  | refl (t : List α) : TraceEquiv t t
  | swap {e₁ e₂ : α} {t₁ t₂ t₃ : List α} :
      (ind : R e₁ e₂) →
      TraceEquiv (t₁ ++ e₁ :: e₂ :: t₂) t₃ →
      TraceEquiv (t₁ ++ e₂ :: e₁ :: t₂) t₃

/-- Notation for trace equivalence. -/
local infixr:60 " ≈ₜ " => TraceEquiv R

/-- The label sequence of a trace. -/
@[simp] def labels (t : List α) : List L := t.map lbl

namespace Trace

/-- Two traces are label-equivalent if they map to the same label sequence. -/
def LabelEquiv (t₁ t₂ : List α) : Prop := labels lbl t₁ = labels lbl t₂

lemma labelEquiv_refl : Reflexive (LabelEquiv lbl) := fun _ => rfl

lemma labelEquiv_symm : Symmetric (LabelEquiv lbl) := fun _ _ h => h.symm

lemma labelEquiv_trans : Transitive (LabelEquiv lbl) :=
  fun _ _ _ h₁ h₂ => h₁.trans h₂

/-- A labelling respects independence if it assigns equal labels to independent events. -/
def LabelRespecting : Prop := ∀ {e₁ e₂ : α}, R e₁ e₂ → lbl e₁ = lbl e₂

/-- Swapping two adjacent events preserves the label sequence iff they share a label. -/
lemma labels_swap_iff {e₁ e₂ : α} {t₁ t₂ : List α} :
    labels lbl (t₁ ++ e₁ :: e₂ :: t₂) = labels lbl (t₁ ++ e₂ :: e₁ :: t₂) ↔
    lbl e₁ = lbl e₂ := by
  change (t₁ ++ e₁ :: e₂ :: t₂).map lbl = (t₁ ++ e₂ :: e₁ :: t₂).map lbl ↔ _
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons,
      List.map_cons, List.map_cons]
  constructor
  · intro h
    have := List.append_cancel_left h
    exact (List.cons.injEq _ _ _ _ |>.mp this).1
  · intro h; rw [h]

/-- Trace equivalence is reflexive. -/
lemma traceEquiv_refl : Reflexive (TraceEquiv R) :=
  TraceEquiv.refl

/-- Trace equivalence is transitive. -/
lemma traceEquiv_trans : Transitive (TraceEquiv R) := by
  intro t₁ t₂ t₃ h₁₂ h₂₃
  induction h₁₂ with
  | refl _ => exact h₂₃
  | swap ind _ ih => exact TraceEquiv.swap ind (ih h₂₃)

/-- Trace equivalence is symmetric when independence is. -/
lemma traceEquiv_symm (hsymm : Symmetric R) : Symmetric (TraceEquiv R) := by
  intro t₁ t₂ h
  induction h with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    exact traceEquiv_trans R ih (TraceEquiv.swap (hsymm ind) (TraceEquiv.refl _))

/-- Trace equivalence implies label equivalence for an independence-respecting labelling. -/
lemma traceEquiv_imp_labelEquiv (hresp : LabelRespecting R lbl)
    {t₁ t₂ : List α} (h : TraceEquiv R t₁ t₂) : LabelEquiv lbl t₁ t₂ := by
  induction h with
  | refl _ => rfl
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    have hlab : lbl e₁ = lbl e₂ := hresp ind
    have hsame : labels lbl (t₁' ++ e₂ :: e₁ :: t₂') = labels lbl (t₁' ++ e₁ :: e₂ :: t₂') :=
      (labels_swap_iff lbl).mpr hlab.symm
    exact hsame.trans ih

/-- Trace equivalence is an equivalence relation when independence is symmetric. -/
def traceEquivEquivalence (hsymm : Symmetric R) : Equivalence (TraceEquiv R) where
  refl := traceEquiv_refl R
  symm h := traceEquiv_symm R hsymm h
  trans h₁ h₂ := traceEquiv_trans R h₁ h₂

/-- Trans instance for calc proofs. -/
instance : Trans (TraceEquiv R) (TraceEquiv R) (TraceEquiv R) where
  trans h₁₂ h₂₃ := traceEquiv_trans R h₁₂ h₂₃

/-- Trace equivalence is a left congruence for append. -/
lemma traceEquiv_append_left {t₁ t₂ : List α} (h : t₁ ≈ₜ t₂) (t : List α) :
    (t ++ t₁) ≈ₜ (t ++ t₂) := by
  induction h generalizing t with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    calc (t ++ (t₁' ++ e₂ :: e₁ :: t₂'))
        = ((t ++ t₁') ++ e₂ :: e₁ :: t₂') := by simp
      _ ≈ₜ ((t ++ t₁') ++ e₁ :: e₂ :: t₂') := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t ++ (t₁' ++ e₁ :: e₂ :: t₂')) := by simp
      _ ≈ₜ (t ++ t₃') := ih t

/-- Trace equivalence is a right congruence for append. -/
lemma traceEquiv_append_right {t₁ t₂ : List α} (h : t₁ ≈ₜ t₂) (t : List α) :
    (t₁ ++ t) ≈ₜ (t₂ ++ t) := by
  induction h with
  | refl _ => exact TraceEquiv.refl _
  | @swap e₁ e₂ t₁' t₂' t₃' ind _ ih =>
    calc (t₁' ++ e₂ :: e₁ :: t₂' ++ t)
        = (t₁' ++ e₂ :: e₁ :: (t₂' ++ t)) := by simp
      _ ≈ₜ (t₁' ++ e₁ :: e₂ :: (t₂' ++ t)) := TraceEquiv.swap ind (TraceEquiv.refl _)
      _ = (t₁' ++ e₁ :: e₂ :: t₂' ++ t) := by simp
      _ ≈ₜ (t₃' ++ t) := ih

/-- Trace equivalence is a congruence for append. -/
lemma traceEquiv_append {t₁ t₂ t₃ t₄ : List α}
    (h₁ : t₁ ≈ₜ t₂) (h₂ : t₃ ≈ₜ t₄) : (t₁ ++ t₃) ≈ₜ (t₂ ++ t₄) :=
  traceEquiv_trans R (traceEquiv_append_right R h₁ t₃) (traceEquiv_append_left R h₂ t₂)

/-- Setoid of traces, for a symmetric independence relation. -/
def traceEquivSetoid (hsymm : Symmetric R) : Setoid (List α) where
  r := TraceEquiv R
  iseqv := traceEquivEquivalence R hsymm

end Trace


/-! ## Positional trace equivalence

At the family level independence is relative to the configuration reached so
far, so adjacent events may be transposed only where `Indep` licenses it. -/

/-- The configuration reached by running `t` from `c`. -/
def reach {L : Type*} (F : ConfFamily L) (c : Set F.Event) (t : List F.Event) : Set F.Event :=
  c ∪ {x | x ∈ t}

namespace ConfFamily

variable {L : Type*} {F : ConfFamily L}

/-- Traces equivalent from a configuration: adjacent independent events commute. -/
inductive TraceEquivFrom (F : ConfFamily L) : Set F.Event → List F.Event → List F.Event → Prop
  | refl (c : Set F.Event) (t : List F.Event) : TraceEquivFrom F c t t
  | swap {c : Set F.Event} {e₁ e₂ : F.Event} {t : List F.Event} :
      F.Indep c e₁ e₂ → TraceEquivFrom F c (e₁ :: e₂ :: t) (e₂ :: e₁ :: t)
  | cons {c : Set F.Event} {e : F.Event} {t₁ t₂ : List F.Event} :
      TraceEquivFrom F (c ∪ {e}) t₁ t₂ → TraceEquivFrom F c (e :: t₁) (e :: t₂)
  | trans {c : Set F.Event} {t₁ t₂ t₃ : List F.Event} :
      TraceEquivFrom F c t₁ t₂ → TraceEquivFrom F c t₂ t₃ → TraceEquivFrom F c t₁ t₃

namespace TraceEquivFrom

lemma symm {c : Set F.Event} {t₁ t₂ : List F.Event} :
    TraceEquivFrom F c t₁ t₂ → TraceEquivFrom F c t₂ t₁ := by
  intro h
  induction h with
  | refl c t => exact .refl c t
  | swap hind => exact .swap hind.symm
  | cons _ ih => exact .cons ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Equivalent traces use the same events, so reach the same configuration. -/
lemma reach_eq {c : Set F.Event} {t₁ t₂ : List F.Event} (h : TraceEquivFrom F c t₁ t₂) :
    reach F c t₁ = reach F c t₂ := by
  induction h with
  | refl => rfl
  | swap => ext x; simp [reach]; tauto
  | @cons c e t₁ t₂ _ ih =>
    have : ∀ t : List F.Event, reach F c (e :: t) = reach F (c ∪ {e}) t := by
      intro t; ext x; simp [reach]; tauto
    rw [this, this, ih]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma append_left {c : Set F.Event} {t₁ t₂ : List F.Event}
    (h : TraceEquivFrom F c t₁ t₂) (t : List F.Event) :
    TraceEquivFrom F c (t₁ ++ t) (t₂ ++ t) := by
  induction h with
  | refl c _ => exact .refl c _
  | swap hind => exact .swap hind
  | cons _ ih => exact .cons ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

lemma append_right {c : Set F.Event} (t : List F.Event) {t₁ t₂ : List F.Event}
    (h : TraceEquivFrom F (reach F c t) t₁ t₂) :
    TraceEquivFrom F c (t ++ t₁) (t ++ t₂) := by
  induction t generalizing c with
  | nil => simpa [reach] using h
  | cons e t ih =>
    refine .cons (ih ?_)
    have hre : reach F (c ∪ {e}) t = reach F c (e :: t) := by ext x; simp [reach]; tauto
    rw [hre]; exact h

end TraceEquivFrom

end ConfFamily
