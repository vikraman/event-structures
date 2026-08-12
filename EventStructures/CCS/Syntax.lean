import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-! # Finitary CCS: syntax and operational semantics -/

namespace CCS

/-- CCS labels: input or output on a name. -/
inductive Label (Name : Type*) where
  | inp : Name → Label Name
  | out : Name → Label Name

namespace Label

variable {Name Name' : Type*}

/-- Co-label: swap input/output. -/
def co : Label Name → Label Name
  | inp n => out n
  | out n => inp n

@[simp] lemma co_co (a : Label Name) : a.co.co = a := by cases a <;> rfl

/-- Rename the underlying name. -/
def map (f : Name → Name') : Label Name → Label Name'
  | inp n => inp (f n)
  | out n => out (f n)

/-- Strip a label down to `Name`, failing on the bound name `none`. -/
def strip : Label (Option Name) → Option (Label Name)
  | inp none => none
  | inp (some n) => some (inp n)
  | out none => none
  | out (some n) => some (out n)

@[simp] lemma strip_map (a : Label Name) : (a.map some).strip = some a := by cases a <;> rfl

end Label

/-- CCS actions: a visible label, or the internal action τ. -/
inductive Action (Name : Type*) where
  | vis : Label Name → Action Name
  | tau : Action Name

namespace Action

variable {Name Name' : Type*}

/-- Rename the underlying name. -/
def map (f : Name → Name') : Action Name → Action Name'
  | vis a => vis (a.map f)
  | tau => tau

/-- Strip an action down to `Name`, failing if it mentions the bound name. -/
def strip : Action (Option Name) → Option (Action Name)
  | vis a => a.strip.map vis
  | tau => some tau

@[simp] lemma strip_map (α : Action Name) : (α.map some).strip = some α := by
  cases α <;> simp [Action.map, Action.strip]

/-- `strip` inverts `map some`. -/
lemma map_some_of_strip : ∀ {b : Action (Option Name)} {a : Action Name},
    b.strip = some a → b = Action.map some a
  | vis l, a, h => by
      cases l with
      | inp n => cases n with
        | none => simp [Action.strip, Label.strip] at h
        | some m => cases a with
          | vis l' => simp [Action.strip, Label.strip] at h; simp [Action.map, Label.map, ← h]
          | tau => simp [Action.strip, Label.strip] at h
      | out n => cases n with
        | none => simp [Action.strip, Label.strip] at h
        | some m => cases a with
          | vis l' => simp [Action.strip, Label.strip] at h; simp [Action.map, Label.map, ← h]
          | tau => simp [Action.strip, Label.strip] at h
  | tau, a, h => by simp [Action.strip] at h; simp [← h, Action.map]

end Action

universe u

/-- Finitary CCS, well-scoped: `res` binds a name via `Option`. -/
inductive Process : Type u → Type (u + 1) where
  | nil {Name : Type u} : Process Name
  | pre {Name : Type u} : Action Name → Process Name → Process Name
  | sum {Name : Type u} : Process Name → Process Name → Process Name
  | par {Name : Type u} : Process Name → Process Name → Process Name
  | res {Name : Type u} : Process (Option Name) → Process Name

/-- Operational semantics of CCS. -/
inductive Step : ∀ {Name : Type*}, Process Name → Action Name → Process Name → Prop where
  | pre {Name} {α : Action Name} {P : Process Name} : Step (.pre α P) α P
  | sumL {Name} {P : Process Name} {α : Action Name} {P' Q : Process Name} :
      Step P α P' → Step (.sum P Q) α P'
  | sumR {Name} {P Q : Process Name} {α : Action Name} {Q' : Process Name} :
      Step Q α Q' → Step (.sum P Q) α Q'
  | parL {Name} {P : Process Name} {α : Action Name} {P' Q : Process Name} :
      Step P α P' → Step (.par P Q) α (.par P' Q)
  | parR {Name} {P Q : Process Name} {α : Action Name} {Q' : Process Name} :
      Step Q α Q' → Step (.par P Q) α (.par P Q')
  | parSync {Name} {P : Process Name} {a : Label Name} {P' Q Q' : Process Name} :
      Step P (.vis a) P' → Step Q (.vis a.co) Q' → Step (.par P Q) .tau (.par P' Q')
  | res {Name} {P : Process (Option Name)} {α : Action Name} {P' : Process (Option Name)} :
      Step P (Action.map some α) P' → Step (.res P) α (.res P')

end CCS
