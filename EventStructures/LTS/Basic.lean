import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-! # Labelled transition systems with independence (Lanese–Phillips–Ulidowski)
-/

variable {L : Type*}

/-- An LTSI. -/
structure LTSI (L : Type*) where
  State : Type*
  init : State
  step : State → L → State → Prop
  indep : State → L → State → L → State → Prop

namespace LTSI

variable (T : LTSI L)

local notation:55 c " -[" a "]→ " c' => T.step c a c'

/-- LPV axioms for an LTSI. -/
structure LPV : Prop where
  indep_step_left : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → (s -[a]→ s₁)
  indep_step_right : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → (s -[b]→ s₂)
  indep_irrefl : ∀ {s a s'}, ¬ T.indep s a s' a s'
  indep_symm : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ → T.indep s b s₂ a s₁
  square : ∀ {s a s₁ b s₂}, T.indep s a s₁ b s₂ →
    ∃ u, (s₁ -[b]→ u) ∧ (s₂ -[a]→ u)

end LTSI


/-- A (strong) bisimulation between two LTSIs: related initial states and
steps matched both ways. Independence is ignored. -/
structure Bisim (S T : LTSI L) (R : S.State → T.State → Prop) : Prop where
  init : R S.init T.init
  forward : ∀ {s t a s'}, R s t → S.step s a s' → ∃ t', T.step t a t' ∧ R s' t'
  backward : ∀ {s t a t'}, R s t → T.step t a t' → ∃ s', S.step s a s' ∧ R s' t'

/-- Existence of a bisimulation. -/
def Bisimilar (S T : LTSI L) : Prop := ∃ R, Bisim S T R

lemma Bisimilar.refl (S : LTSI L) : Bisimilar S S := by
  refine ⟨Eq, rfl, ?_, ?_⟩
  · rintro s t a s' rfl hs; exact ⟨s', hs, rfl⟩
  · rintro s t a t' rfl ht; exact ⟨t', ht, rfl⟩

lemma Bisimilar.symm {S T : LTSI L} : Bisimilar S T → Bisimilar T S := by
  rintro ⟨R, hinit, hfwd, hbwd⟩
  exact ⟨fun t s => R s t, hinit, fun h hs => hbwd h hs, fun h ht => hfwd h ht⟩

/-- A directed label. -/
inductive DirLabel (L : Type*) : Type _
  | fwd : L → DirLabel L
  | bwd : L → DirLabel L
  deriving DecidableEq

namespace DirLabel

@[simp]
def rev : DirLabel L → DirLabel L
  | fwd a => bwd a
  | bwd a => fwd a

@[simp]
def label : DirLabel L → L
  | fwd a => a
  | bwd a => a

def isFwd : DirLabel L → Prop
  | fwd _ => True
  | bwd _ => False

/-- Reversal is an involution. -/
lemma rev_rev (la : DirLabel L) : rev (rev la) = la := by cases la <;> rfl

end DirLabel

/-- A reversible LTSI: labels carry direction and forward steps are reversible. -/
structure RLTSI (L : Type*) extends LTSI (DirLabel L) where
  step_rev : ∀ {s a s'}, step s (DirLabel.fwd a) s' ↔ step s' (DirLabel.bwd a) s

namespace RLTSI

variable (T : RLTSI L)

local notation:55 c " -[" a "]→ " c' => T.step c a c'

/-- LPV axioms for a reversible LTSI. -/
structure LPV : Prop extends LTSI.LPV T.toLTSI where
  BTI : ∀ {s a s₁ b s₂},
    (s -[DirLabel.bwd a]→ s₁) → (s -[DirLabel.bwd b]→ s₂) →
    (a ≠ b ∨ s₁ ≠ s₂) →
    T.indep s (DirLabel.bwd a) s₁ (DirLabel.bwd b) s₂

end RLTSI
