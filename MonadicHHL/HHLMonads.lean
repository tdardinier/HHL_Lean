import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

lemma prove_prop_by_eq {α : Type} {x y : α}
  (P : α → Prop)
  (h : x = y) :
  P x ↔ P y := by
    rw [h]

class HHL (M : Type _ → Type _) [Monad M] where
  elemType : Type _ → Type _
  relWith : {α β : Type _} → (α → M β) → elemType α → elemType β → Prop
  bind_rel {σ α₁ α₂ : Type}
    (C₁ : α₀ → M α₁) (C₂ : α₁ → M α₂)
    (p₀ : elemType α₀) (p₂ : elemType α₂) :
      relWith (fun v₁ ↦ bind (C₁ v₁) C₂) p₀ p₂
      ↔ ∃ p₁, relWith C₁ p₀ p₁ ∧ relWith C₂ p₁ p₂

section
variable {M : Type _ → Type _} [HHL M]  -- pretend we live in a world with a MyClass α


def semify  {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : Set (ElemType σ α₁) → Set (ElemType σ α₂) :=
  fun S => { p' | ∃ p ∈ S, rel_with C p p'}


lemma semify_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃)
  (S : Set (ElemType σ α₁))
  :
 semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := interaction_bind_rel C₁ C₂
  aesop

def hyperassertion (σ α : Type) : Type :=
  Set (ElemType σ α) → Prop

def W (σ α₁ α₂ : Type) : Type :=
  hyperassertion σ α₂ → hyperassertion σ α₁

def WP {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : W σ α₁ α₂ :=
  fun Q S => Q (semify C S)

lemma WP_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP, Bind.bind]
    apply prove_prop_by_eq
    have h := semify_bind C₁ C₂ S
    aesop


namespace StateNonDetAlt

-- Parameters

-- Computational monad:
def M (σ α : Type) : Type :=
  σ → Set (α × σ)

def pure {σ α : Type} (x : α) : M σ α :=
  fun σ => {(x, σ)}

def bind {σ α₁ α₂ : Type}
  (C₁ : M σ α₁) (C₂ : α₁ → M σ α₂) : M σ α₂ :=
  fun σ => (⋃p' ∈ C₁ σ, C₂ p'.1 p'.2)

instance (σ : Type) : Monad (M σ) where
  pure := pure
  bind := bind

-- Abstraction in the logic
def ElemType (σ α : Type) : Type :=
  α × σ

def rel_with {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) (p : ElemType σ α₁) (p' : ElemType σ α₂)
   : Prop :=
  p' ∈ C p.1 p.2

-- Sequential composition

lemma interaction_bind_rel {σ α₁ α₂ : Type}
  (C₁ : α₀ → M σ α₁)
  (C₂ : α₁ → M σ α₂)
  (p₀ : ElemType σ α₀)
  (p₂ : ElemType σ α₂) :
  rel_with (fun v₁ ↦ bind (C₁ v₁) C₂) p₀ p₂
↔ ∃ p₁, rel_with C₁ p₀ p₁ ∧ rel_with C₂ p₁ p₂
:= by
  simp [rel_with, bind]
  aesop

-------------------------
-------- Generic --------
-------------------------

def semify {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : Set (ElemType σ α₁) → Set (ElemType σ α₂) :=
  fun S => { p' | ∃ p ∈ S, rel_with C p p'}


lemma semify_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃)
  (S : Set (ElemType σ α₁))
  :
 semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)
 := by
  simp [semify]
  apply Set.ext
  intro p'
  simp
  have h := interaction_bind_rel C₁ C₂
  aesop

def hyperassertion (σ α : Type) : Type :=
  Set (ElemType σ α) → Prop

def W (σ α₁ α₂ : Type) : Type :=
  hyperassertion σ α₂ → hyperassertion σ α₁

def WP {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : W σ α₁ α₂ :=
  fun Q S => Q (semify C S)

lemma WP_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP, Bind.bind]
    apply prove_prop_by_eq
    have h := semify_bind C₁ C₂ S
    aesop

end StateNonDetAlt




universe u v w

section SetBaseMonad

/-
def SetT (m : Type u -> Type v) (α : Type u) : Type _ :=
  Set (m α)

def SetT (m : Type u -> Type v) (α : Type u) : Type _ :=
  m (Set α)
-/

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | S, f => {b | ∃a, a ∈ S ∧ b ∈ f a}

instance : Monad Set where
  pure := Set.pure
  bind := Set.bind

instance Set.LawfulMonad : LawfulMonad Set :=
  {
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_pure_comp  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
        sorry
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Bind.bind, Set.bind]
        apply Set.ext
        aesop
    seqLeft_eq := sorry
    seqRight_eq := sorry
    pure_seq := sorry
    bind_map := sorry }


def set_bind_state {α val : Type} (S : Set (val × α)) (C : (val × α) → Set (val × α)) : Set (val × α) :=
  { y | ∃ x ∈ S, y ∈ C x }

abbrev HHL_monad (α : Type) : Type → Type :=
  StateT α Set

lemma HHL_monad_simpler (α val : Type) :
  HHL_monad α val = (α → Set (val × α)) := by
    simp [HHL_monad, StateT]

lemma HHL_monad_same_bind {α : Type} (C₁ : HHL_monad α Unit) (C₂ : Unit → HHL_monad α Unit) :
  C₁ >>= C₂ = (fun σ => set_bind_state (C₁ σ) (fun (_, σ') => C₂ () σ'))
  := by
    aesop

lemma HHL_monad_same_bind_val {α val : Type}
  (C₁ : HHL_monad α val) (C₂ : val → HHL_monad α val) :
  C₁ >>= C₂ = (fun σ => set_bind_state (C₁ σ) (fun (x, σ') => C₂ x σ'))
  := by
    aesop

-- with option for errors

abbrev Hypra_monad (α : Type) : Type → Type :=
  OptionT (StateT α Set)

lemma Hypra_monad_simpler (α val : Type) :
  Hypra_monad α val = (α → Set (Option val × α)) := by
    simp [Hypra_monad, OptionT, StateT]


def set_bind_state_hypra {α val : Type}
  (S : Set (Option val × α))
  (C : (val × α) → Set (Option val × α)) : Set (Option val × α) :=
  { y | ∃ x ∈ S,
  (
    match x with
    | (none, σ) => y = (none, σ)
    | (some v, σ) => y ∈ C (v, σ)
  )}



lemma Hypra_monad_same_bind {α : Type} (C₁ : Hypra_monad α Unit) (C₂ : Unit → Hypra_monad α Unit) :
  C₁ >>= C₂ = (fun σ => set_bind_state_hypra (C₁ σ) (fun (_, σ') => C₂ () σ'))
  := by
    simp [Hypra_monad, set_bind_state_hypra, bind, OptionT.bind, OptionT.mk]
    apply funext
    intro x
    refine Set.ext ?_
    intro y
    simp [StateT.bind]
    apply Iff.intro
    {
      intro yin
      rcases yin with ⟨a, ha, hcase⟩
      apply Exists.intro a.fst
      apply Exists.intro a.snd
      apply And.intro
      assumption
      simp
      cases a with
      | mk o σ =>
        cases o with
        | none =>
            simpa using hcase
        | some v =>
            cases v
            simpa using hcase
    }
    {
      intro h
      rcases h with ⟨a, ha, ⟨hcase, hh⟩⟩
      simp [bind, Set.bind]
      apply Exists.intro a
      apply Exists.intro ha
      apply And.intro hcase
      cases a
      simp [pure, StateT.pure, Set.pure]
      aesop
      simp
      aesop
    }

lemma Hypra_monad_same_bind_val {α val : Type}
  (C₁ : Hypra_monad α val) (C₂ : val → Hypra_monad α val) :
  C₁ >>= C₂ = (fun σ => set_bind_state_hypra (C₁ σ) (fun (x, σ') => C₂ x σ'))
  := by
    simp [Hypra_monad, set_bind_state_hypra, bind, OptionT.bind, OptionT.mk]
    apply funext
    intro x
    refine Set.ext ?_
    intro y
    simp [StateT.bind]
    apply Iff.intro
    {
      intro yin
      rcases yin with ⟨a, ha, hcase⟩
      apply Exists.intro a.fst
      apply Exists.intro a.snd
      apply And.intro
      assumption
      simp
      cases a with
      | mk o σ =>
        cases o with
        | none =>
            simpa using hcase
        | some v =>
            simpa using hcase
    }
    {
      intro h
      rcases h with ⟨a, ha, ⟨hcase, hh⟩⟩
      simp [bind, Set.bind]
      apply Exists.intro a
      apply Exists.intro ha
      apply And.intro hcase
      cases a
      simp [pure, StateT.pure, Set.pure]
      aesop
      simp
      aesop
    }

abbrev Var : Type :=
  String

def SState (α : Type) : Type :=
  Var → α

abbrev HypraM (α val : Type) : Type :=
  -- State α → Set (Option α × State α)
  OptionT (StateT (SState α) Set) val

lemma simpler_HypraM (α val : Type) :
  HypraM α val = (SState α → Set (Option val × SState α)) := by
    simp [HypraM, OptionT, StateT]

abbrev HHLMonad (α val : Type) : Type :=
  -- State α → Set (Option α × State α)
  StateT (SState α) Set val


lemma simpler_HHLMonad (α val : Type _) :
  HHLMonad α val = (SState α → Set (val × SState α)) := by
    simp [HHLMonad, StateT]

example (α L : Type _) :
  (HHLMonad α L → L) = ((SState α → Set (L × SState α)) → L)
  := by simp [HHLMonad, StateT]


example (α : Type) :
  (HypraM α (Prop × Prop) → (Prop × Prop))
  =
  ((SState α → Set (Option (Prop × Prop) × SState α)) → Prop × Prop)
:= by
  simp [HypraM, OptionT, StateT]


/-
instance : MAlgOrdered (StateM Int) (Int → Prop) where
  μ (f : Int → (Int → Prop) × Int) :=
    fun b =>
      let (post, b') := f b
      post b'
  μ_ord_pure := sorry
  μ_ord_bind := sorry
-/

example (α : Type) :
  HHLMonad α (Set (SState α) → Prop) = (SState α → Set ((Set (SState α) → Prop) × SState α)) := by
    simp [HHLMonad, StateT]

#check StateT


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


abbrev MonadT : Type _ :=
  (Type _ → Type _) → Type _ → Type _




-- Do we even need the set in the computation monad?
-- How to get non-det?
-- Do I just get a monad then?
--def HyperM (T : MonadT) (α : Type _) : Type _ :=
--  T Set α
--  T Set α

-- Computation monad:
-- OptionT (StateT (SState α) Set)
-- OptionT (StateT σ) Set)
-- with α = σ → Set (Option α × σ)

namespace Id

----- Step 1
----- Id
def M (α : Type) : Type :=
  α

def pure {α : Type} (x : α) : Id.M α :=
  x

def bind {α β : Type}
  (ma : Id.M α)
  (f : α → Id.M β) : Id.M β :=
  f ma

instance : Monad Id.M where
  pure := Id.pure
  bind := Id.bind

def hyperassertion (α : Type) : Type :=
  Set α → Prop

def W (α₁ α₂ : Type) : Type :=
  Id.hyperassertion α₂ → Id.hyperassertion α₁

def WP {α₁ α₂ : Type}
  (C : α₁ → Id.M α₂) : Id.W α₁ α₂ :=
  fun Q S => Q (C '' S)

lemma WP_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → Id.M α₂)
  (C₂ : α₂ → Id.M α₃) :
  Id.WP (fun v₁ => C₁ v₁ >>= C₂) = (Id.WP C₁) ∘ (Id.WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [Id.WP, Set.image, Bind.bind, Id.bind]

end Id

----------------------------------------
------ Adding set
----------------------------------------

namespace NonDet

def M (α : Type) : Type :=
  Set α

instance : Monad M where
  pure := Set.pure
  bind := Set.bind

def hyperassertion (α : Type) : Type :=
  Set α → Prop

def W (α₁ α₂ : Type) : Type :=
  hyperassertion α₂ → hyperassertion α₁

def WP {α₁ α₂ : Type}
  (C : α₁ → M α₂) : W α₁ α₂ :=
  fun Q S => Q (⋃σ∈S, C σ)

lemma WP_bind {α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M α₂)
  (C₂ : α₂ → M α₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP, Bind.bind, Set.bind]
    apply prove_prop_by_eq
    apply Set.ext
    intro p'
    simp
    aesop

end NonDet

namespace State

def M (σ α : Type) : Type :=
  σ → α × σ

def pure {σ α : Type} (x : α) : M σ α :=
  fun s => (x, s)

def bind {σ α₁ α₂ : Type}
  (ma : M σ α₁)
  (f : α₁ → M σ α₂) : M σ α₂ :=
  fun s =>
    let (a, s') := ma s
    f a s'

instance (σ : Type) : Monad (M σ) where
  pure := pure
  bind := bind

def hyperassertion (σ α : Type) : Type :=
  Set (α × σ) → Prop

def W (σ α₁ α₂ : Type) : Type :=
  hyperassertion σ α₂ → hyperassertion σ α₁

def WP {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : W σ α₁ α₂ :=
  fun Q S => Q { p' | ∃ v σ, (v, σ) ∈ S ∧ p' = C v σ }

lemma WP_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP, Bind.bind, bind]
    grind


end State

namespace StateNonDet

-- Parameters

def M (σ α : Type) : Type :=
  σ → Set (α × σ)

def pure {σ α : Type} (x : α) : M σ α :=
  fun σ => {(x, σ)}

def bind {σ α₁ α₂ : Type}
  (C₁ : M σ α₁) (C₂ : α₁ → M σ α₂) : M σ α₂ :=
  fun σ => (⋃p' ∈ C₁ σ, C₂ p'.1 p'.2)

instance (σ : Type) : Monad (M σ) where
  pure := pure
  bind := bind

def ElemType (σ α : Type) : Type :=
  α × σ

def semify {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : Set (ElemType σ α₁) → Set (ElemType σ α₂) :=
    fun S => (⋃p∈S, C p.1 p.2)

lemma semify_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃)
  (S : Set (ElemType σ α₁))
  :
 semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)
 := by
  simp [semify, bind]
  aesop

------------------------------
-- Generic
------------------------------

def hyperassertion (σ α : Type) : Type :=
  Set (ElemType σ α) → Prop

def W (σ α₁ α₂ : Type) : Type :=
  hyperassertion σ α₂ → hyperassertion σ α₁

def WP {σ α₁ α₂ : Type}
  (C : α₁ → M σ α₂) : W σ α₁ α₂ :=
  fun Q S => Q (semify C S)

lemma WP_bind {σ α₁ α₂ α₃ : Type}
  (C₁ : α₁ → M σ α₂)
  (C₂ : α₂ → M σ α₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = (WP C₁) ∘ (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp [WP, Bind.bind]
    apply prove_prop_by_eq
    have h := semify_bind C₁ C₂ S
    aesop

end StateNonDet


semify (fun v₁ ↦ bind (C₁ v₁) C₂) S = semify C₂ (semify C₁ S)


-------------------- Older stuff



def HyperM (σ : Type) : Type → Type :=
  OptionT (StateT σ Set)

example (α σ : Type) :
  HyperM σ α = (σ → Set (Option α × σ)) := by
    simp [HyperM, OptionT, StateT]


-- What's the morphism?

---- Instantiations

-- T = Id
-- HyperM T α = α
-- HyperW T α = (Set α → Prop) → (Set α → Prop)

-- HyperM is just the monad?

-- T = State σ
-- HyperM T α = σ → α × σ
-- HyperW T α₁ α₂ = (Set (α₂ × σ) → Prop) → (Set (α₂ × σ) → Prop)


-- T = ?
-- HyperM T α = σ → Set (α × σ)
-- HyperW T α₁ α₂ = (Set (α₂ × σ) → Prop) → (Set (α₂ × σ) → Prop)

-- T = ?
-- HyperM T α = Set α
-- HyperW T α₁ α₂ = (Set α₂ → Prop) → (Set α₁ → Prop)

-- ...
-- Computation monad := σ → Set (Option α × σ)
-- HyperW α₁ α₂ = (Set (Option α₂ × σ) → Prop) → (Set (Option α₁ × σ) → Prop)






example (α val : Type) :
  (HyperM (StateT α) val) = (α → Set (val × α)) := by
  simp [HyperM, StateT]

def HyperW (T : MonadT) (α : Type) : Type :=
  (Set (val₂ × α) → Prop) → Set (val₁ × α) → Prop

def HyperW (α val₁ val₂ : Type) : Type :=
  (Set (val₂ × α) → Prop) → Set (val₁ × α) → Prop
  -- post → pre



abbrev HyperM (α val : Type) : Type :=
  -- α → Set (val × α)
  StateT α Set val

example (α val : Type) :
  HyperM α val = (α → Set (val × α)) := by
    simp [HyperM, StateT]

def hyperassertion (α : Type) : Type :=
  Set α → Prop

def HyperW (α val₁ val₂ : Type) : Type :=
  (Set (val₂ × α) → Prop) → Set (val₁ × α) → Prop
  -- post → pre

def WP {α val₁ val₂ : Type}
  (C : val₁ → HyperM α val₂) : HyperW α val₁ val₂ :=
  fun post S =>
    post { p' | ∃ v σ, (v, σ) ∈ S ∧ p' ∈ C v σ }

def bind_like_WP {α val₁ val₂ val₃ : Type}
  (WP1 : HyperW α val₁ val₂) (WP2 : HyperW α val₂ val₃)
  : HyperW α val₁ val₃ :=
  WP1 ∘ WP2

#check WP
#print WP
#reduce WP
#reduce (types := true) WP

#check WP
#check WP unfolding HyperW HyperM StateT

-- syntax (name := elabCheckDsimp) "#check_dsimp " term : command





lemma WP_bind_works {α val₁ val₂ val₃ : Type}
  (C₁ : val₁ → HyperM α val₂)
  (C₂ : val₂ → HyperM α val₃) :
  WP (fun v₁ => C₁ v₁ >>= C₂) = bind_like_WP (WP C₁) (WP C₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    apply propext
    simp  [bind_like_WP, bind, WP, StateT.bind, Set.bind]
    apply prove_prop_by_eq
    apply Set.ext
    intro p'
    aesop


#check WP
#check WP unfolding HyperW HyperM StateT

def WP_pure {α val₁ val₂ : Type} (x : val₂) : HyperW α val₁ val₂ :=
  fun (post : Set (val₂ × α) → Prop) (S : Set (val₁ × α)) =>
    post {  p | ∃ v σ, (v, σ) ∈ S ∧ p = (x, σ) }

def pureM {α val : Type} (x : val) : HyperM α val :=
  fun σ => {(x, σ)}

-- Kinda useless?
lemma WP_pure_works {α val₁ val₂ : Type}
  (x : val₂) :
  WP (fun (_ : val₁) => pureM x)
  = (WP_pure x: HyperW α val₁ val₂)
  := by
    apply funext
    intro Q
    apply funext
    intro S
    simp [WP, pureM, WP_pure]

/-
nection is given by the morphism WPStateM : StateM σ α → StateW σ α defined as follows:  WPStateM (m : StateM σ α) ≜ λ post (s : σ). let (res, s′) = (m s) in post res s′ (3)
-/
def WP {α val : Type}
  (C : HyperM α val) : HyperW α val :=
  fun post S =>
    post { (v, σ') | ∃ σ ∈ S, (v, σ') ∈ C σ }

-- we add the return to every state in S
def WP.pure {α val : Type} (x : val) : HyperW α val :=
  fun (post : Set (val × α) → Prop) (S : Set α) =>
    post { (x, σ) | σ ∈ S }

def StateW.bind {α val₁ val₂ : Type}
  (w : HyperW α val₁)
  (f : val₁ → HyperW α val₂) : HyperW α val₂ :=
  fun
    (post : Set (val₂ × α) → Prop)
    (S : Set α)
    =>
    w
      (fun (S' : Set (val₁ × α)) => ∀ (v₁ : val₁) (σ' : α),
        (v₁, σ') ∈ S' →
        f v₁ post {σ' })
      S

-- What does bind mean in this context???
-- Specification monad doesn't work with relational reasoning?
def WP.bind {α val₁ val₂ : Type}
  (w : HyperW α val₁)
  (f : val₁ → HyperW α val₂) : HyperW α val₂ :=
  fun
    (post : Set (val₂ × α) → Prop)
    (S : Set α)
    =>
    sorry

-- WP(C1; C2, Q) = WP(C1, WP(C2, Q))

def WP.bind_unit {α val₂ : Type}
  (WP1 : HyperW α Unit)
  (WP2 : Unit → HyperW α val₂) : HyperW α val₂ :=
  --WP1 : Set (Unit × α) → Prop) → (Set α → Prop)
  fun (Q : Set (val₂ × α) → Prop) (S : Set α) =>
    have RR : Set α → Prop := WP2 () Q
    have R : Set (Unit × α) → Prop :=
      fun S' => RR (Prod.snd '' S')
    WP1 R S

/-
  (Set (val × α) → Prop) → (Set α → Prop)
      (fun (S' : Set (Unit × α)) => ∀ (σ' : α),
        ((), σ') ∈ S' →
        f () post {σ' })
      S
  -/



/-
∀x, WP (pureM x) = pureW x (4)  ∀m f , WP (bindM m f ) = bindW (WP m) (λr . WP (f r )) (5)
-/

instance (α : Type) : MAlgOrdered (HyperM α) (Set α → Prop) where
  μ (f : α → Set ((Set α → Prop) × α)) :=
    fun S: Set α =>
      -- let SS : Set (Set ((Set α → Prop) × α)) := f '' S
      let SS : Set ((Set α → Prop) × α) := (⋃σ∈S, f σ)
      -- Intuitively: I have a set of initial states S, and I create the set of reachable states from all initial states
      -- What do I do with all my postconditions?
      let posts : Set (Set α → Prop) := Prod.fst '' SS
      let S' : Set α := Prod.snd '' SS
      -- need non-emptiness for mu_ord_pure
      ∀ post ∈ posts, post S'
  μ_ord_pure := by
    simp [pure, StateT.pure, Set.pure, Set.image]
    intro P
    apply funext
    intro S
    -- if exists: ⊢ ((∃ x, x ∈ S) ∧ P S) = P S
    -- if forall: ⊢ (∀ post,  ∀ x ∈ S, post = P → post S) = P S

    refine propext ?_
    apply Iff.intro
    {
      -- cannot prove existence of postcondition
      -- aesop
      sorry
    }
    {
      -- needs non-emptiness for this case
      /-
      intro h
      rcases h with ⟨post, postIn, hpost⟩
      specialize hpost P
      exact hpost
      -/
      sorry
    }

  μ_ord_bind := by
    simp [Bind.bind, Set.image, StateT.bind, Set.bind, Pi.hasLe]
    intro α f g x1 x2 x3 x4 x5
    intro x6 x7 x8 x9 x10 x11 x12



    sorry


instance (α : Type) : MAlgOrdered (HHLMonadAbstract α) (Set α → Prop) where
  μ (f : α → Set ((Set α → Prop) × α)) :=
    fun S: Set α =>
      -- let SS : Set (Set ((Set α → Prop) × α)) := f '' S
      let SS : Set ((Set α → Prop) × α) := (⋃σ∈S, f σ)
      -- Intuitively: I have a set of initial states S, and I create the set of reachable states from all initial states
      -- What do I do with all my postconditions?
      let posts : Set (Set α → Prop) := Prod.fst '' SS
      let S' : Set α := Prod.snd '' SS
      -- need non-emptiness for mu_ord_pure
      (∃σ, σ ∈ S') ∧ (∀ post ∈ posts, post S')
  μ_ord_pure := by
    simp [pure, StateT.pure, Set.pure, Set.image]
    intro P
    apply funext
    intro S
    refine propext ?_
    apply Iff.intro
    {
      -- needs non-emptiness for this case
      aesop
      /-
      intro h
      rcases h with ⟨hex, h⟩
      rcases hex with ⟨x, xS⟩
      specialize h P x
      -/
    }
    {
      -- cannot prove existence of x
      aesop
      sorry
    }



  μ_ord_bind := by
    simp [Bind.bind, Set.bind]
    intro α f g
    sorry

-- μ : HHLMonad α (Set (State α) → Prop) → Set (State α) → Prop
instance : MAlgOrdered Set Prop where
-- instance (α : Type) : MAlgOrdered (HHLMonad α) Prop where
  μ := (fun S => (∀ x ∈ S, x) ∧ (∃x ∈ S, x))
  μ_ord_pure := by
    simp [pure, Set.pure]
    aesop
  μ_ord_bind := by
    simp [Bind.bind, Set.bind]
    intro α f g h1 S h2
    intro P x hxS hPfx hP
    simp [Pi.hasLe] at h1
    apply And.intro
    {
      intro Q y hyS Qgy
      apply h2
      exact hxS
      -- could also use x

      specialize h1 y




      sorry
    }
    {

      sorry
    }




instance (α : Type) : MAlgOrdered (HypraM α) (Set (State α) → Prop) where
  μ := (fun S => (∀ x ∈ S, x) ∧ (∃x ∈ S, x))
  μ_ord_pure := by
    simp [pure, Set.pure]
    aesop
  μ_ord_bind := by
    simp [Bind.bind, Set.bind]
    intro α f g
    sorry

instance : MAlgOrdered Set Prop where
  μ := (fun S => (∀ x ∈ S, x) ∧ (∃x ∈ S, x))
  μ_ord_pure := by
    simp [pure, Set.pure]
    aesop
  μ_ord_bind := by
    simp [Bind.bind, Set.bind]
    intro α f g
    sorry

instance (σ : Type u) : MAlgOrdered (Set σ) (Set σ → Prop) where
instance (σ : Type u) : MAlgOrdered (σ → Prop) ((σ → Prop) → Prop) where
