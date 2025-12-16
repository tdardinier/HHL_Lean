import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

register_simp_attr charact_simps
register_simp_attr wp_simps

-------------------------------
------- Preliminaries ---------
-------------------------------

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | S, f => {b | ∃a, a ∈ S ∧ b ∈ f a}

instance : Monad Set where
  pure := Set.pure
  bind := Set.bind

instance : LawfulMonad Set where
  pure_bind  :=
    by
      intro α β a f
      simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
  bind_pure_comp  :=
    by
      intro α ma
      simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
      simp [Functor.map, Set.image]
      aesop
  bind_assoc :=
    by
      intro α β γ f g ma
      simp [Bind.bind, Set.bind]
      apply Set.ext
      aesop
  seqLeft_eq := sorry
  seqRight_eq := sorry
  pure_seq := sorry
  bind_map := sorry

lemma prove_prop_by_eq {α : Type} {x y : α}
  (P : α → Prop)
  (h : x = y) :
  P x ↔ P y := by
    rw [h]

def optionify {α β : Type} {m : Type → Type} [Monad m]
  (f : α → m (Option β)) : Option α → m (Option β)
  | some a => f a
  | none   => pure none

def exceptify {ε α β : Type} {m : Type → Type} [Monad m]
  (f : α → m (Except ε β)) : Except ε α → m (Except ε β)
  | Except.ok a => f a
  | Except.error e => pure (Except.error e)


--------------------------------
-------- HHL typeclass ---------
--------------------------------

class HHL (M : Type _ → Type _) [Monad M] where
  elemType (α : Type _) : Type _
  relWith : {α β : Type _} → (α → M β) → elemType α → elemType β → Prop
  bind_rel
    {α₀ α₁ α₂ : Type _}
    (C₁ : α₀ → M α₁) (C₂ : α₁ → M α₂)
    (p₀ : elemType α₀) (p₂ : elemType α₂) :
      relWith (fun v₁ ↦ bind (C₁ v₁) C₂) p₀ p₂
      ↔ ∃ p₁, relWith C₁ p₀ p₁ ∧ relWith C₂ p₁ p₂

section

namespace HHL

variable {M : Type _ → Type _} [Monad M] [HHL M]  -- pretend we live in a world with a MyClass α


def semify {α₁ α₂ : Type}
  (C : α₁ → M α₂) : Set (elemType M α₁) → Set (elemType M α₂) :=
  fun S => { p' | ∃ p ∈ S, relWith C p p'}

lemma semify_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M α₂)
  (C₂ : α₂ → M α₃)
  (S : Set (elemType M α₁))
  :
 semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := bind_rel C₁ C₂
  aesop

lemma semify_if_sync {α β : Type _}
  (C1 C2 : α → M β) (b : Bool)
  (S : Set (elemType M α)) :
  (b → semify (fun v ↦ if b then C1 v else C2 v) S = semify C1 S)
  ∧
  (¬b → semify (fun v ↦ if b then C1 v else C2 v) S = semify C2 S)
 := by
  simp [semify]
  aesop

/-
lemma relWith_equiv {α β : Type _}
  {C1 C2 : α → M β}
  (h : ∀ v, C1 v = C2 v)
  (p : elemType M α) (p' : elemType M β) :
  HHL.relWith C1 p p' ↔ HHL.relWith C2 p p'
  := by

    simp [HHL.relWith]

    intro p'
    simp [semify]
    apply Iff.intro
    {
      intro h1
      rcases h1 with ⟨p, hpS, hpRel⟩
      apply Exists.intro p

      aesop
    }
    {
      intro h1
      rcases h1 with ⟨p, hpS, hpRel⟩
      have heq : C2 p = C1 p := by rw [←h p]
      rw [heq] at hpRel
      aesop
    }
-/


/-
lemma rel_with_if_specialized {α : Type}
  (C1 C2 : Bool → M α)
  (p : elemType M Bool)
  (p' : elemType M α)
  :
relWith (fun b ↦ if b = true then C1 b else C2 b) p p'
↔ (relWith C1 p p' ∨ relWith C2 p p')
:=
sorry



lemma semify_if {α : Type}
  (C1 : Bool → M α) (C2 : Bool → M α) (S : Set (elemType M Bool)) :
  semify (fun b ↦ if b then C1 b else C2 b) S = semify C1 S ∪ semify C2 S
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := rel_with_if_specialized C1 C2
  aesop
-/

def hyperassertion (α : Type) : Type :=
  Set (elemType M α) → Prop

def W (α₁ α₂ : Type) : Type :=
  @hyperassertion M _ _ α₂ → @hyperassertion M _ _ α₁

def WP {α₁ α₂ : Type}
  (C : α₁ → M α₂) : @W M _ _ α₁ α₂ :=
  fun Q S => Q (semify C S)

lemma WP_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M α₂)
  (C₂ : α₂ → M α₃) :
  WP (C₁ >=> C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP]
    apply prove_prop_by_eq
    have h := semify_bind C₁ C₂ S
    aesop

lemma WP_if_sync {α β : Type _}
  (C1 C2 : α → M β) (b : Bool) :
  WP (fun v ↦ if b then C1 v else C2 v) =
    if b then WP C1 else WP C2
 := by
  have h := semify_if_sync C1 C2 b
  aesop

def triple {α₁ α₂ : Type}
  (P : @hyperassertion M _ _ α₁)
  (C : α₁ → M α₂)
  (Q : @hyperassertion M _ _ α₂) : Prop :=
  ∀ S, P S → Q (semify C S)

lemma triple_equiv {α β : Type}
  (P : @hyperassertion M _ _ α)
  (C : α → M β)
  (Q : @hyperassertion M _ _ β) :
  triple P C Q ↔ (∀ S, P S → WP C Q S) :=
  by
    simp [triple, WP]

lemma rule_seq {α₁ α₂ α₃ : Type}
  {C1 : α₁ → M α₂}
  {C2 : α₂ → M α₃}
  {P : @hyperassertion M _ _ α₁}
  {R : @hyperassertion M _ _ α₂}
  {Q : @hyperassertion M _ _ α₃}
  (h1 : triple P C1 R)
  (h2 : triple R C2 Q) :
  triple P (C1 >=> C2) Q
  := by
    simp [triple_equiv] at *
    have h := WP_bind C1 C2
    aesop


------------------------------------------------
---------------- Base Monads -------------------
------------------------------------------------

---------------- Id ---------------

instance : HHL Id where
  elemType := Id
  relWith f p p' := p' = f p
  bind_rel := by
    aesop

---------------- Set ---------------

instance : HHL Set where
  elemType := Id
  relWith C p p' := p' ∈ C p
  bind_rel := by
    aesop

------------------------------------------------
-------- Transformers Instantiations -----------
------------------------------------------------

------------ StateT ---------------

instance (σ : Type) (m : Type → Type) [Monad m] [HHL m] : HHL (StateT σ m) where
  elemType α := elemType m (α × σ)
  --elemType α := elemType m α × σ
  relWith {α β : Type} (C : α → StateT σ m β)
    (p : elemType m (α × σ)) (p' : elemType m (β × σ)) :=
    relWith (fun v ↦ C v.1 v.2) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i x0 HHL_M x2 HHL_m
    apply HHL_m.bind_rel (fun v₁ ↦ C₁ v₁.1 v₁.2) (fun v₂ ↦ C₂ v₂.1 v₂.2) p₀ p₂


variable (σ : Type)
-- #check (HHL.relWith (M := StateT σ Set))
#synth HHL (StateT σ Set)

lemma test_stateT_set1 (σ α : Type _) :
  elemType (StateT σ Set) α = (α × σ) := by
  rfl

lemma test_stateT_set2 {σ α : Type}
  (C : α → StateT σ Set α) (p p' : elemType (StateT σ Set) α)
  : relWith C p p' ↔ p' ∈ C p.1 p.2 := by
  rfl

------------ OptionT ---------------

instance (m : Type → Type) [Monad m] [HHL m] [LawfulMonad m] : HHL (OptionT m) where
  elemType α := elemType m (Option α)
  relWith {α β : Type}
    (f : α → m (Option β))
    (p : elemType m (Option α)) (p' : elemType m (Option β))
    := relWith (optionify f) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i Monad_M HHL_M Monad_m HHL_m Lawful_m
    have h := HHL_m.bind_rel (optionify C₁) (optionify C₂) p₀ p₂

    have heq : (fun v₁ ↦ optionify C₁ v₁ >>= optionify C₂)
      = (optionify fun v₁ ↦ @bind (OptionT m) OptionT.instMonad.toBind α₁ α₂ (C₁ v₁) C₂)
    := by
      apply funext
      simp [optionify, Bind.bind, OptionT.bind]
      intro p0
      cases p0
      {
        simp
        simp [optionify]
      }
      {
        rename_i v0
        rw [Bind.bind]
        simp
        rw [OptionT.mk]
        have heq : (optionify C₂) = (fun v ↦ match v with | some a => C₂ a | none => pure none)
        := by
          apply funext
          intro p
          simp [optionify]
        aesop
      }
    aesop


-- #check (HHL.relWith (M := StateT σ Set))
-- set_option diagnostics true
#synth HHL (OptionT Id)

lemma test_HHL_Option1 (α : Type _) :
  elemType (OptionT Id) α = Option α := by
  rfl

lemma test_HHL_Option2 {α : Type}
  (C : α → (OptionT Id) α) (p p' : elemType (OptionT Id) α)
  : relWith C p p' ↔ (match p with
    | some v => p' = C v
    | none => p' = none
  )
  := by
    simp [HHL.relWith, optionify, pure]
    aesop

/-
lemma rel_with_if_specialized_to_option {α β : Type}
  {C1 C2 : α → OptionT Id β}
  {p : elemType (OptionT Id) α}
  {p' : elemType (OptionT Id) β}
  {b : α → Bool}
  :
relWith (fun v ↦ if b v then C1 v else C2 v) p p'
↔ (relWith C1 p p' ∨ relWith C2 p p')
:= by
  simp [HHL.relWith, optionify, pure]
  cases p
  · simp
  simp
  rename_i v


  cases v
  {
    simp

  }
  -/


------------ ExceptT ---------------

instance (ε : Type) (m : Type → Type) [Monad m] [HHL m] [LawfulMonad m] : HHL (ExceptT ε m) where
  elemType α := elemType m (Except ε α)
  relWith {α β : Type}
    (f : α → m (Except ε β))
    (p : elemType m (Except ε α)) (p' : elemType m (Except ε β))
    := relWith (exceptify f) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i Monad_M HHL_M Monad_m HHL_m Lawful_m
    have h := HHL_m.bind_rel (exceptify C₁) (exceptify C₂) p₀ p₂

    have heq : (fun v₁ ↦ exceptify C₁ v₁ >>= exceptify C₂)
      = (exceptify fun v₁ ↦ @bind (ExceptT ε m) ExceptT.instMonad.toBind α₁ α₂ (C₁ v₁) C₂)
    := by
      apply funext
      intro p0
      simp [exceptify, Bind.bind, ExceptT.bind]
      cases p0
      {
        simp
        simp [exceptify]
      }
      {
        rename_i v0
        rw [Bind.bind]
        simp
        rw [ExceptT.mk]
        have heq : (exceptify C₂) =
        (fun v ↦ match v with | Except.ok a => C₂ a | Except.error e => pure (Except.error e))
        := by
          apply funext
          intro p
          simp [exceptify]
        aesop
      }
    aesop


------------ ReaderT ---------------

instance (σ : Type) (m : Type → Type) [Monad m] [HHL m] : HHL (ReaderT σ m) where
  -- elemType α := elemType m (α × σ)
  elemType α := elemType m α × σ
  relWith {α β : Type} (C : α → ReaderT σ m β)
    (p : elemType m α × σ) (p' : elemType m β × σ) :=
    relWith (fun v => C v p.2) p.1 p'.1 ∧ p.2 = p'.2
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i x0 HHL_M x2 HHL_m
    have h := HHL_m.bind_rel (fun v₁ ↦ C₁ v₁ p₀.2) (fun v₂ ↦ C₂ v₂ p₂.2) p₀.1 p₂.1
    apply Iff.intro
    {
      intro h1
      have h := h.mp (by
        rw [HHL.relWith]
        aesop
      )
      rcases h with ⟨s1, hp1_rel, hp2_rel⟩
      apply Exists.intro (s1, p₀.2)
      aesop
    }
    {
      intro h1
      rcases h1 with ⟨p1, hp1_rel, hp2_rel⟩
      have h := h.mpr (by
        rw [HHL.relWith]
        aesop
      )
      have heq : (fun v₁ ↦ do let v₂ ← C₁ v₁ p₀.2; C₂ v₂ p₂.2)
        = (fun v ↦ (fun v₁ ↦ C₁ v₁ >>= C₂) v p₀.2) := by
        aesop
      aesop
    }


------------ Logical Variables ---------------

--- The unused type parameter is the logical part of the state
def LogicT (_ : Type) (m : Type _ → Type _) : Type _ → Type _
 := m

instance (L : Type) (m : Type _ → Type _) [M : Monad m] : Monad (LogicT L m) where
  pure := M.pure
  bind := M.bind

/-
def logicify {L : Type} {m : Type _ → Type _} [Monad m]
  (f : α → LogicT L m β) (x : α × L) : m β × L :=
    (f x.1, x.2)
-/

-- Like StateT basically?
-- How does this compose with the set base monad?
instance {m : Type _ → Type _} (L : Type) [Monad m] [HHL m] : HHL (LogicT L m) where
  elemType α := elemType m α × L
  --elemType α := elemType m (α × L)
  relWith --C p p' :=
   {α β : Type} (C : α → LogicT L m β)
   --(p : elemType m (α × L)) (p' : elemType m (β × L)) :=
   (p : elemType m α × L) (p' : elemType m β × L) :=
    @relWith m _ _ _ _ C p.1 p'.1
    ∧ p.2 = p'.2
    --relWith (logicify C) p p'
    -- relWith (fun v ↦ C v v) p p'
  bind_rel := by
    intro α₀ α₁ α₂ C₁ C₂ p₀ p₂
    rename_i Monad_M HHL_M Monad_m HHL_m
    have h := HHL_m.bind_rel C₁ C₂ p₀.1 p₂.1
    aesop

abbrev LHHL_Monad (L σ α : Type) : Type :=
  LogicT L (StateT σ Set) α

lemma rel_with_LHHL_Monad (L σ α β : Type)
  (C : α → LHHL_Monad L σ β)
  (p : (α × σ) × L) (p' : (β × σ) × L) :
  HHL.relWith C p p' ↔ (p.2 = p'.2 ∧ p'.1 ∈ C p.1.1 p.1.2)
  := by
  simp [HHL.relWith]
  aesop

lemma semify_HHL (L σ α₁ α₂ : Type)
  (C : α₁ → LHHL_Monad L σ α₂)
  (S : Set ((α₁ × σ) × L)) :
  HHL.semify C S = { p' | ∃ p ∈ S, p.2 = p'.2 ∧ p'.1 ∈ C p.1.1 p.1.2 }
  := by
  simp [HHL.semify]
  --have h := rel_with_LHHL_Monad L σ α₁ α₂ C
  apply Set.ext
  intro p2
  simp [HHL.relWith]
  apply Iff.intro
  {
    intro h
    rcases h with ⟨p, hpS, hpRel⟩
    apply Exists.intro p.1.1
    apply Exists.intro p.1.2
    have heq : ((p.1.1, p.1.2), p2.2) = p := by aesop
    aesop
  }
  {
    intro h
    aesop
  }


abbrev weird_monad (L σ α : Type) : Type :=
  StateT σ (LogicT L Set) α

lemma same_monads :
  weird_monad = LHHL_Monad :=
  rfl

lemma same_elemType (L σ : Type) :
  HHL.elemType (weird_monad L σ) = HHL.elemType (LHHL_Monad L σ) :=
  rfl

lemma same_rel_with (L σ : Type) :
  @HHL.relWith (weird_monad L σ) = @HHL.relWith (LHHL_Monad L σ) :=
  rfl


end HHL


abbrev HHL_Monad (σ α : Type) : Type :=
  StateT σ Set α

lemma semify_for_HHL {σ α₁ α₂ : Type}
  (C : α₁ → HHL_Monad σ α₂) (S : Set (α₁ × σ)) :
  HHL.semify C S = { p' | ∃ p ∈ S, p' ∈ C p.1 p.2 }
:= rfl

abbrev Hypra_Monad (σ α : Type) : Type :=
  OptionT (StateT σ Set) α

variable {σ : Type}
#synth HHL (StateT σ Set)
#synth LawfulMonad (OptionT (StateT σ Set))
#synth HHL (OptionT (StateT σ Set))

lemma relWith_Hypra {σ α₁ α₂ : Type}
  (C : α₁ → Hypra_Monad σ α₂)
  (p : Option α₁ × σ)
  (p' : Option α₂ × σ) :
  HHL.relWith C p p' ↔
    (p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2) ∨
    (∃ v, p.1 = some v ∧ p' ∈ C v p.2)
:= by
  simp [HHL.relWith, optionify, pure]
  cases p.1
  {
    simp
    simp [StateT.pure, pure, Set.pure]
    grind
  }
  simp

lemma semify_for_Hypra {σ α₁ α₂ : Type}
  (C : α₁ → Hypra_Monad σ α₂) (S : Set (Option α₁ × σ)) :
  HHL.semify C S =
  { p' | ∃ p ∈ S, (p.1 = none ∧ p'.1 = none ∧ p.2 = p'.2) ∨ (∃ v, p.1 = some v ∧ p' ∈ C v p.2) }
:= by
  simp [HHL.semify]
  have h := relWith_Hypra C
  apply Set.ext
  intro x
  simp [HHL.relWith, optionify, pure]
  apply Iff.intro
  {
    intro h
    rcases h with ⟨p, hpS, hpRel⟩
    sorry
  }
  {
    sorry
  }


syntax (name := checkUnfolding) "#check " term " unfolding " ident* : command

open Lean Elab Command Meta
@[command_elab checkUnfolding]
def elacCheckUnfolding : CommandElab
  | `(#check%$tk $term unfolding $ids:ident*) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    if let `($id:ident) := term then
      try
        for c in (← realizeGlobalConstWithInfos term) do
          addCompletionInfo <| .id term id.getId (danglingDot := false) {} none
          let mut «type» ← Meta.inferType (← mkConstWithLevelParams c)
          for id in ids do
            «type» := (← Meta.unfold «type» id.getId).expr
          logInfoAt tk <| .signature c
          logInfoAt tk m!"{«type»}"
          return
      catch _ => pure ()
  | _ => throwUnsupportedSyntax


abbrev MonadT : Type _ := (Type _ → Type _) → Type _ → Type _


def asym_triple {α : Type}
  (P : Set α → Prop) (C : α → Option α) (Q : Set (Option α) → Prop) : Prop
  :=
  (∀ S, P S → Q (C '' S))

def the {α : Type} [Inhabited α] (x : Option α) : α :=
  Option.getD x (Inhabited.default)

/-
lemma hyperassertion_option {α : Type} :
  @HHL.elemType (OptionT Id) _ _ α = Option α := b
  rfl

  Maybe nice syntactic rule?
-/
lemma asym_triple_equiv {α : Type} [Inhabited α]
  (P : Set α → Prop) (C : α → OptionT Id α) (Q : Set (OptionT Id α) → Prop) :
  asym_triple P C Q
  ↔ @HHL.triple (OptionT Id) _ _ _ _ (fun S => P (the '' S) ∧ (∀ σ ∈ S, σ ≠ none)) C Q :=
  by
    simp [asym_triple, HHL.triple, HHL.elemType]
    simp [HHL.semify]
    apply Iff.intro
    {
      intro h
      intro S
      intro hP
      have hQ := h (the '' S)
      sorry
    }
    {
      intro h
      intro S
      intro hP
      sorry
    }


end
