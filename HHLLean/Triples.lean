import HHLLean.Language

abbrev hyperassertion (α : Type) := Set (State α) → Prop

def triple {α : Type} (P : hyperassertion α) (C : Stmt α) (Q : hyperassertion α) : Prop :=
  ∀S, P S → Q (sem C S)

macro "{* " P:term " *} " "(" S:term ")" " {* " Q:term " *}" : term =>
  `(triple $P $S $Q)

theorem rule_skip {α : Type} (P : hyperassertion α) :
    {* P *} (Stmt.skip) {* P *} :=
  by
    simp [triple]

theorem rule_seq {α : Type} {P R Q : hyperassertion α} {C₁ C₂ : Stmt α}
  (h1 : {* P *} (C₁) {* R *}) (h2 : {* R *} (C₂) {* Q *}) :
    {* P *} (C₁; C₂) {* Q *} :=
  by
    simp [triple] at *
    grind

theorem rule_cons {α : Type} {P P' Q Q' : hyperassertion α} {C : Stmt α}
  (htriple : {* P *} (C) {* Q *})
  (hP : ∀ S, P' S → P S) (hQ : ∀ S, Q S → Q' S) :
    {* P' *} (C) {* Q' *} :=
  by
    simp [triple] at *
    grind

theorem rule_exists {α β : Type} {P Q : β → hyperassertion α} {C : Stmt α}
  (h : ∀ x, triple (P x) C (Q x)) :
  triple (fun S => ∃x, P x S) C (fun S => ∃x, Q x S)
  := by
    simp [triple] at *
    grind

theorem rule_branch {α : Type} {P Q₁ Q₂ : hyperassertion α} {C₁ C₂ : Stmt α}
  (h1 : triple P C₁ Q₁) (h2 : triple P C₂ Q₂) :
  triple P (Stmt.branch C₁ C₂) (fun S => ∃ S₁ S₂, S = S₁ ∪ S₂ ∧ Q₁ S₁ ∧ Q₂ S₂) :=
  by
    simp [triple] at *
    grind

theorem rule_assume {α : Type} (P : hyperassertion α) (b : BExp α) :
  triple (fun S => P (S ∩ b)) (Stmt.assume b) P :=
  by
    simp [triple] at *

theorem rule_assign {α : Type} (P : hyperassertion α) (x : Var) (e : Exp α) :
  triple (fun S => P {σ' | ∃σ, S σ ∧ σ' = σ[x ↦ e σ]}) (Stmt.assign x e) P :=
  by
    simp [triple]
    grind
