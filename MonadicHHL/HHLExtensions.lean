import MonadicHHL.HHLMonads

-- with OK
-- Maybe I need a "replace element" function?

class HHLWithOk (M : Type _ → Type _) [Monad M] extends HHL M where

  -- Parameters
  isOk {α : Type _} : HHL.elemType M α → Prop
  mapElem {α β : Type _} (f : α → β) : HHL.elemType M α → HHL.elemType M β
  extractValueOk {α : Type _} (σ : HHL.elemType M α) (h : isOk σ) : α

  -- Properties
  deadNoElem {α : Type _} (σ : HHL.elemType M α) :
    ¬ isOk σ → (∀ f, σ = mapElem f σ)

  isOkMapElem {α β : Type _} (f : α → β) (σ : HHL.elemType M α) :
    isOk σ ↔ isOk (mapElem f σ)

  inactive {α β : Type _} (C : α → M β) (σ : HHL.elemType M α) (σ' : HHL.elemType M β) :
    ¬ isOk σ → (HHL.relWith C σ σ' ↔ (∃ f, σ' = mapElem f σ))

  okValueMatters {α β : Type _} (C : α → M β)
    (σ : HHL.elemType M α) (f : α → β) (h : isOk σ) :
    f (extractValueOk σ h) =
    extractValueOk (mapElem f σ) ((isOkMapElem f σ).mp h)

-- Is this the property needed from the class?
lemma simplify_if_ok_relWith
  {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  {α β : Type _} (b : α → Bool) (C₁ C₂ : α → M β)
  (σ : HHL.elemType M α) (σ' : HHL.elemType M β)
  (h : (h : HHLWithOk.isOk σ) → b (HHLWithOk.extractValueOk σ h))
  :
HHL.relWith (fun x ↦ if b x = true then C₁ x else C₂ x) σ σ'
↔ HHL.relWith C₁ σ σ'
:= by
  sorry

lemma simplify_if_ok_relWith_neg
  {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  {α β : Type _} (b : α → Bool) (C₁ C₂ : α → M β)
  (σ : HHL.elemType M α) (σ' : HHL.elemType M β)
  (h : (h : HHLWithOk.isOk σ) → ¬ b (HHLWithOk.extractValueOk σ h))
  :
HHL.relWith (fun x ↦ if b x = true then C₁ x else C₂ x) σ σ'
↔ HHL.relWith C₂ σ σ'
:= by
  sorry




def Low {α : Type _}
  {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  (b : α → Bool)
  (S : Set (HHL.elemType M α))
 : Prop :=
    ∀ σ₁ ∈ S, ∀ σ₂ ∈ S, (h1 : HHLWithOk.isOk σ₁) → (h2 : HHLWithOk.isOk σ₂) →
      (b (HHLWithOk.extractValueOk σ₁ h1) = b (HHLWithOk.extractValueOk σ₂ h2))

lemma low_elim
  {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  {α : Type _} (b : α → Bool)
  (S : Set (HHL.elemType M α))
  (h : Low b S)
  :
  (∀ σ ∈ S, (h : HHLWithOk.isOk σ) → b (HHLWithOk.extractValueOk σ h))
  ∨
  (∀ σ ∈ S, (h : HHLWithOk.isOk σ) → ¬ b (HHLWithOk.extractValueOk σ h))
  := sorry
  -- Case distinction: Empty trivial,
  -- otherwise pick an element and use its value

lemma low_semify_if
  {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  {α β : Type _} (b : α → Bool) (C₁ C₂ : α → M β)
  (S : Set (HHL.elemType M α))
  (h : Low b S)
  :
(HHL.semify (fun x ↦ if b x = true then C₁ x else C₂ x) S
= HHL.semify C₁ S)
∨
(HHL.semify (fun x ↦ if b x = true then C₁ x else C₂ x) S
= HHL.semify C₂ S)
:= by
  simp [HHL.semify]
  have h := low_elim b S h
  cases h
  {
    rename_i h_true
    apply Or.inl
    apply Set.ext
    intro x
    simp
    have h := simplify_if_ok_relWith b C₁ C₂
    aesop
  }
  {
    rename_i h_false
    apply Or.inr
    apply Set.ext
    intro x
    simp
    have h := simplify_if_ok_relWith_neg b C₁ C₂
    aesop
  }

lemma if_sync {M : Type _ → Type _} [Monad M] [HHLWithOk M]
  {α β : Type _} (b : α → Bool) (C₁ C₂ : α → M β)
  (P : HHL.hyperassertion α)
  (Q : HHL.hyperassertion β)
  (h : ∀ S, P S →
    (∀ σ₁ ∈ S, ∀ σ₂ ∈ S, (h1 : HHLWithOk.isOk σ₁) → (h2 : HHLWithOk.isOk σ₂) →
      (b (HHLWithOk.extractValueOk σ₁ h1) = b (HHLWithOk.extractValueOk σ₂ h2))))
  (h₁ : HHL.triple P C₁ Q)
  (h₂ : HHL.triple P C₂ Q) :
  HHL.triple P (fun x => if b x then C₁ x else C₂ x) Q := by
  simp [HHL.triple] at *
  intro S hP
  specialize h₁ S hP
  specialize h₂ S hP
  have hh := low_semify_if b C₁ C₂ S (h S hP)
  aesop

instance : HHLWithOk Id where
  isOk σ := True
  extractValueOk σ h := σ
  mapElem f σ := f σ
  deadNoElem σ h := by contradiction
  isOkMapElem f σ := by simp
  inactive C σ σ' h := by contradiction
  okValueMatters C σ f h := by simp

def dAnd (P : Prop) (Q : P → Prop) : Prop
  := P ∧ ((h : P) → Q h)

open Classical in
noncomputable def diteClassical {α : Sort _} (P : Prop)
    (t : P → α) (f : ¬ P → α) : α :=
  by
    classical
    by_cases h : P
    · exact t h
    · exact f h


instance (M : Type _ → Type _) [Monad M] [LawfulMonad M] [HHLWithOk M] : HHLWithOk (OptionT M) where

  isOk σ := dAnd (HHLWithOk.isOk σ) (fun h => Option.isSome (HHLWithOk.extractValueOk σ h))

  mapElem f := HHLWithOk.mapElem (Option.map f)

  extractValueOk σ h :=
    Option.get (HHLWithOk.extractValueOk σ h.left) (sorry)

  -- Properties

  deadNoElem σ h := sorry

  isOkMapElem f σ := sorry

  inactive C σ σ' h := sorry

  okValueMatters C σ f h := sorry


-- Other classes


class HHLPrecise (M : Type _ → Type _) [Monad M] extends HHLWithOk M where
  alwaysOutcome {α β : Type _} (C : α → M β) (σ : HHL.elemType M α) :
    ∃σ', HHL.relWith C σ σ'

/-
Everything satisfies this class except Set...
Because Set losing info with divergence... (empty set)
Allows framing!
-/

/-
Other class:
OkType
ErrType
NonTermType

Props that:
- OkType is the only Ok one
- The two others are dead
- We only have these 3 types
- Can quantify over those
- Hopefully, we can even connect the NonTerm type to loop divergence generically
-/
