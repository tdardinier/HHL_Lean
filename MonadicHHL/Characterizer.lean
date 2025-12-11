import MonadicHHL.HHLMonads

--- Characterizer definition

-- For the simplest case : Set α → Set β
structure charact_path (α β : Type _) where
  pc : α → Prop -- or Bool?
  res : α → β

abbrev characterizer (α β : Type _) : Type := List (charact_path α β)

--- Characterizer soundness

def characterizer_sound {α β : Type _}
  (C : α → Id β) (charac : characterizer α β) : Prop :=
  ∀a b, b = C a ↔ (∃ cp ∈ charac, cp.pc a ∧ cp.res a = b)

lemma characterizer_soundE {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (a : α) :
   ∃ cp ∈ charac, cp.pc a ∧ cp.res a = C a :=
  by
    simp [characterizer_sound] at h
    specialize h a (C a)
    aesop

lemma characterizer_sound_altE {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (cp : charact_path α β)
  (a : α) (b : β)
  (hh : cp ∈ charac ∧ cp.pc a ∧ cp.res a = b) :
  b = C a
  :=
  by
    simp [characterizer_sound] at h
    have h := (h a b).mpr
    simp at h
    specialize h cp
    aesop

lemma characterizer_sound_set_view {α β : Type _}
  {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (S : Set α) :
  C '' S = { σ' | ∃σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ cp.res σ = σ' }
  := by
    apply Set.ext
    intro σ'
    simp [Set.image]
    apply Iff.intro
    {
      intro h
      rcases h with ⟨σ, inS, hC⟩
      have hcp := characterizer_soundE h σ
      rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
      apply Exists.intro σ
      simp [inS]
      apply Exists.intro cp
      simp [cp_in, cp_pc, cp_res, hC]
    }
    {
      intro h
      rcases h with ⟨σ, inS, ⟨cp, cp_in, cp_pc, cp_res⟩⟩
      have hC := characterizer_sound_altE h cp σ (cp.res σ)
      apply Exists.intro σ
      simp [inS]
      aesop
    }


------ Sound characterizers for pure, bind, if ------

def characterizer_pure {α β : Type _} (x : β) : characterizer α β :=
  [ {
      pc := fun _ => true,
      res := fun _ => x
  } ]

lemma characterizer_sound_id {α β : Type _} (x : β) :
  characterizer_sound (fun (_ : α) => pure x) (characterizer_pure x) := by
  simp [characterizer_sound, characterizer_pure]
  aesop

def combine_characts {α β γ : Type _}
  (cps : charact_path α β × charact_path β γ) : charact_path α γ :=
  {
    pc := fun a => cps.1.pc a ∧ cps.2.pc (cps.1.res a),
    res := fun a => cps.2.res (cps.1.res a)
  }

def bind_characterizers {α β γ : Type _}
  (charac1 : characterizer α β)
  (charac2 : characterizer β γ) : characterizer α γ :=
  List.map combine_characts (List.product charac1 charac2)

lemma bind_characterizers_sound {α β γ : Type _}
  {C1 : α → Id β} {C2 : β → Id γ}
  {charac1 : characterizer α β}
  {charac2 : characterizer β γ}
  (h1 : characterizer_sound C1 charac1)
  (h2 : characterizer_sound C2 charac2) :
  characterizer_sound (fun v => C1 v >>= C2) (bind_characterizers charac1 charac2) := by
  simp [characterizer_sound, bind_characterizers, combine_characts, Bind.bind]
  intro a b
  apply Iff.intro
  {
    intro h
    have h1 := characterizer_soundE h1 a
    have h2 := characterizer_soundE h2 (C1 a)
    aesop
  }
  {
    intro h
    rcases h with ⟨cp1, cp2, ⟨cp1_in, cp2_in⟩, hcp_comb_res, x4⟩
    have h1 := characterizer_sound_altE h1 cp1
    have h2 := characterizer_sound_altE h2 cp2
    aesop
  }

def conjoin_pc {α β : Type _}
  (b : α → Bool)
  (charac : charact_path α β)
  : charact_path α β :=
  {
    pc := fun a => charac.pc a ∧ b a,
    res := charac.res
  }


lemma concat_for_branch {α β : Type _}
  {C1 C2 : α → Id β}
  {charac1 charac2 : characterizer α β}
  {b : α → Bool}
  (h1 : characterizer_sound C1 charac1)
  (h2 : characterizer_sound C2 charac2) :
  characterizer_sound
    (fun v => if b v then C1 v else C2 v)
    (List.map (conjoin_pc b) charac1 ++ List.map (conjoin_pc (fun a => !b a)) charac2) := by
  simp [characterizer_sound, conjoin_pc]
  intro x y

  apply Iff.intro
  {
    have h1 := characterizer_soundE h1 x
    have h2 := characterizer_soundE h2 x
    aesop
  }
  {
    intro h
    rcases h with ⟨cp, hcp_in, hcp_pc, hcp_res⟩
    cases hcp_in
    {
      rename_i cp_in
      rcases cp_in with ⟨cp, cp_in_charac1, hpc_conj⟩
      have h := characterizer_sound_altE h1 cp x y
      aesop
    }
    {
      rename_i cp_in
      rcases cp_in with ⟨cp, cp_in_charac1, hpc_conj⟩
      rename_i cp'
      have h := characterizer_sound_altE h2 cp x y
      aesop
    }
  }


def generic_characterizer {α β : Type _}
  (C : α → Id β) : characterizer α β :=
  [{
    pc := fun _ => true,
    res := C
  }]

lemma generic_characterizer_sound {α β : Type _}
  (C : α → Id β) :
  characterizer_sound C (generic_characterizer C) := by
  simp [characterizer_sound, generic_characterizer]
  aesop

--------- WP from characterizers ------

def hyperassertion (α : Type _) := Set α → Prop

def triple {α β : Type _}
  (P : hyperassertion α) (C : α → Id β) (Q : hyperassertion β) : Prop :=
  ∀ S, P S → Q (C '' S)

def is_WP {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β) (P : hyperassertion α) : Prop :=
  triple P C Q ∧
  (∀ P', triple P' C Q → (∀ S, P' S → P S))

lemma is_WP_unique {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β)
  (P1 P2 : hyperassertion α)
  (h1 : is_WP C Q P1)
  (h2 : is_WP C Q P2) :
  P1 = P2 :=
  by
    apply Set.ext
    intro S
    simp [is_WP] at h1 h2
    aesop

lemma is_WP_obvious {α β : Type _}
  (C : α → Id β) (Q : hyperassertion β) :
  is_WP C Q (fun S => Q (C '' S))
  := by simp [is_WP, triple]

lemma is_WPE {α β : Type _}
  {P : hyperassertion α}
  {C : α → Id β}
  {Q : hyperassertion β}
  (h : is_WP C Q P)
: (∀ S, P S = Q (C '' S))
:= by
  have heq : P = (fun S => Q (C '' S)) := by
    apply is_WP_unique C Q _ _ h
    apply is_WP_obvious
  aesop

/-
def WP_forall_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → Prop) : hyperassertion α :=
  fun S => ∀σ ∈ S, ∀ cp ∈ charac, cp.pc σ → Q (cp.res σ)

lemma WP_forall_from_charact_is_WP {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → Prop) :
  is_WP C (fun S => ∀σ ∈ S, Q σ) (WP_forall_from_charact charac Q) :=
  by
    constructor
    {
      intro S hP
      simp [WP_forall_from_charact] at hP
      simp [Set.image]
      intro a ha
      have hcp := characterizer_soundE h a
      rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
      specialize hP a ha cp cp_in cp_pc
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_forall_from_charact]
      intro σ hσ cp cp_in cp_pc
      have hcp := characterizer_sound_altE h cp σ (cp.res σ)
      aesop
    }

def WP_exists_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → Prop) : hyperassertion α :=
  fun S => ∃σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ Q (cp.res σ)

lemma WP_exists_from_charact_is_WP {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → Prop) :
  is_WP C (fun S => ∃σ ∈ S, Q σ) (WP_exists_from_charact charac Q) :=
  by
    constructor
    {
      intro S hP
      simp [WP_exists_from_charact] at hP
      simp [Set.image]
      rcases hP with ⟨σ, inS, ⟨cp, hcp⟩⟩
      apply Exists.intro σ
      simp [inS]
      have hcp' := characterizer_sound_altE h cp σ (cp.res σ)
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_exists_from_charact]
      simp [triple] at htriple
      specialize htriple S hP
      rcases htriple with ⟨σ, inS, hh⟩
      apply Exists.intro σ
      simp [inS]
      have hcp := characterizer_soundE h σ
      aesop
    }
-/

--- "Constructors"

def H.pure {α : Type _} (P : Prop) : hyperassertion α :=
  fun _ => P

def H.forall {α : Type _} (P : α → hyperassertion α) : hyperassertion α :=
  fun S => ∀ σ ∈ S, P σ S

def H.exists {α : Type _} (P : α → hyperassertion α) : hyperassertion α :=
  fun S => ∃ σ ∈ S, P σ S

---- Example

abbrev forall_forall_post {β : Type _} (Q : β → β → Prop) : hyperassertion β :=
  H.forall (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2)))

def WP.forall {α β : Type _}
  (charac : characterizer α β) (P : β → hyperassertion α) : hyperassertion α :=
  fun S =>
    ∀ σ ∈ S, ∀ cp ∈ charac, cp.pc σ → P (cp.res σ) S

def WP.exists {α β : Type _}
  (charac : characterizer α β) (P : β → hyperassertion α) : hyperassertion α :=
  fun S =>
    ∃ σ ∈ S, ∃ cp ∈ charac, cp.pc σ ∧ P (cp.res σ) S

lemma triple_cons_post {α β : Type _}
  (P : hyperassertion α)
  (C : α → Id β)
  (Q Q' : hyperassertion β)
  (htriple : triple P C Q')
  (hcons : ∀ S, Q' S → Q S)
  : triple P C Q :=
  by
    simp [triple] at *
    aesop

@[grind .]
lemma is_WP_forall_comp {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → hyperassertion β)
  (P : β → hyperassertion α)
  (hh : ∀ σ', is_WP C (Q σ') (P σ')) :
  is_WP C (H.forall Q) (WP.forall charac P) := by
    have heq : WP.forall charac P = (fun S => H.forall Q (C '' S)) := by
    {
      apply funext
      intro S
      simp [WP.forall, H.forall]
      have hsimpler : ∀ σ ∈ S, (∀ cp ∈ charac, cp.pc σ → P (cp.res σ) S) ↔ (Q (C σ) (C '' S)) := by
      {
        intro σ hS
        apply Iff.intro
        {
          intro hcp
          have hh := is_WPE (hh (C σ)) S
          rw [hh.symm]
          have h := characterizer_soundE h σ
          rcases h with ⟨cp, cp_in, cp_pc, cp_res⟩
          specialize hcp cp cp_in cp_pc
          aesop
        }
        {
          intro hQ cp cp_in cp_pc
          have hh := is_WPE (hh (C σ)) S
          have hcp := characterizer_sound_altE h cp σ (cp.res σ)
          aesop
        }
      }
      aesop
    }
    rw [heq]
    apply is_WP_obvious

@[grind .]
lemma is_WP_exists_comp {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → hyperassertion β)
  (P : β → hyperassertion α)
  (hh : ∀ σ', is_WP C (Q σ') (P σ')) :
  is_WP C (H.exists Q) (WP.exists charac P) := by
    have heq : WP.exists charac P = (fun S => H.exists Q (C '' S)) := by
    {
      apply funext
      intro S
      simp [WP.exists, H.exists]
      have hsimpler : ∀ σ ∈ S, (∃ cp ∈ charac, cp.pc σ ∧ P (cp.res σ) S) ↔ (Q (C σ) (C '' S)) := by
        {
          intro σ hS
          apply Iff.intro
          {
            intro hcp
            rcases hcp with ⟨cp, cp_in, cp_pc, cp_res⟩
            have hh := is_WPE (hh (C σ)) S
            have h := characterizer_sound_altE h cp σ
            aesop
          }
          {
            intro hQ
            have hcp := characterizer_soundE h σ
            have hh := is_WPE (hh (C σ)) S
            aesop
          }
        }
      grind
    }
    rw [heq]
    apply is_WP_obvious


@[simp, grind .]
lemma is_WP_pure {α β : Type _} {C : α → Id β} (P : Prop)
  : is_WP C (H.pure P) (H.pure P)
  := by simp [is_WP, triple, H.pure]

lemma elim_triple {α β : Type _}
  {P : hyperassertion α}
  {C : α → Id β}
  {Q : hyperassertion β}
  (htriple : triple P C Q)
  (S : Set α)
  (hP : P S) :
  Q (C '' S) :=
  by
    simp [triple] at htriple
    specialize htriple S hP
    aesop

@[grind .]
lemma is_WP_and {α β : Type _} {C : α → Id β}
  {P1 P2 : hyperassertion α}
  {Q1 Q2 : hyperassertion β}
  (h1 : is_WP C Q1 P1)
  (h2 : is_WP C Q2 P2) :
  is_WP C (fun S => Q1 S ∧ Q2 S) (fun S => P1 S ∧ P2 S) :=
  by
    have h1 := is_WPE h1
    have h2 := is_WPE h2
    simp [is_WP, triple]
    aesop

@[grind .]
lemma is_WP_or {α β : Type _} {C : α → Id β}
  {P1 P2 : hyperassertion α}
  {Q1 Q2 : hyperassertion β}
  (h1 : is_WP C Q1 P1)
  (h2 : is_WP C Q2 P2) :
  is_WP C (fun S => Q1 S ∨ Q2 S) (fun S => P1 S ∨ P2 S) :=
  by
    have h1 := is_WPE h1
    have h2 := is_WPE h2
    simp [is_WP, triple]
    aesop

lemma is_WP_forall_normal {α β γ : Type _} {C : α → Id β}
  (Q : γ → hyperassertion β)
  (P : γ → hyperassertion α)
  (hh : ∀ x, is_WP C (Q x) (P x)) :
  is_WP C (fun S => ∀ x, Q x S) (fun S => ∀ x, P x S) := by
    constructor
    {
      intro S h x
      have hh := is_WPE (hh x) S
      aesop
    }
    {
      intro P' htriple S hP x
      have hh := is_WPE (hh x) S
      aesop
    }

lemma is_WP_exists_normal {α β γ : Type _} {C : α → Id β}
  (Q : γ → hyperassertion β)
  (P : γ → hyperassertion α)
  (hh : ∀ x, is_WP C (Q x) (P x)) :
  is_WP C (fun S => ∃ x, Q x S) (fun S => ∃ x, P x S) := by
    constructor
    {
      simp [triple]
      intro S x
      have hh := is_WPE (hh x)
      aesop
    }
    {
      intro P' htriple S hP
      have htriple := elim_triple htriple S hP
      rcases htriple with ⟨x, h'⟩
      have hh := is_WPE (hh x) S
      aesop
    }






--------------------------
-- Examples
--------------------------

-- Forall

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → Prop) :
  is_WP C
    (H.forall (fun σ => H.pure (Q σ)))
    (WP.forall charac (fun σ => H.pure (Q σ)))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.forall (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.forall charac (fun σ1 => WP.forall charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

-- Exists

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → Prop) :
  is_WP C
    (H.exists (fun σ => H.pure (Q σ)))
    (WP.exists charac (fun σ => H.pure (Q σ)))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.exists (fun σ1 => H.exists (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.exists charac (fun σ1 => WP.exists charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

-- Mixed

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.forall (fun σ1 => H.exists (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.forall charac (fun σ1 => WP.exists charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind

example {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac) (Q : β → β → Prop) :
  is_WP C
    (H.exists (fun σ1 => H.forall (fun σ2 => H.pure (Q σ1 σ2))))
    (WP.exists charac (fun σ1 => WP.forall charac (fun σ2 => H.pure (Q σ1 σ2))))
  := by grind


/-

def WP_forall_forall_from_charact {α β : Type _}
  (charac : characterizer α β) (Q : β → β → Prop) : hyperassertion α :=
  fun S =>
    ∀ a1 ∈ S, ∀cp1 ∈ charac, cp1.pc a1 →
    ∀ a2 ∈ S, ∀cp2 ∈ charac, cp2.pc a2 →
      Q (cp1.res a1) (cp2.res a2)

lemma same_hyperassertions {β : Type _} (Q : β → β → Prop) :
  (fun S => ∀σ1 ∈ S, ∀σ2 ∈ S, Q σ1 σ2) = forall_forall_post Q
  := rfl

lemma WP_forall_forall_from_charact_sound {α β : Type _} {C : α → Id β} {charac : characterizer α β}
  (h : characterizer_sound C charac)
  (Q : β → β → Prop) :
  is_WP C
    -- (forall_forall_post Q)
    (fun S => ∀σ1 ∈ S, ∀σ2 ∈ S, Q σ1 σ2)
    (WP_forall_forall_from_charact charac Q) :=
  by
    constructor
    {
      simp [triple, WP_forall_forall_from_charact, Set.image]
      intro S hP σ1 h1 σ2 h2
      have hcp1 := characterizer_soundE h σ1
      rcases hcp1 with ⟨cp1, cp1_in, cp1_pc, cp1_res⟩
      have hcp2 := characterizer_soundE h σ2
      rcases hcp2 with ⟨cp2, cp2_in, cp2_pc, cp2_res⟩
      specialize hP σ1 h1 cp1 cp1_in cp1_pc σ2 h2 cp2 cp2_in cp2_pc
      aesop
    }
    {
      intro P' htriple S hP
      simp [WP_forall_forall_from_charact]
      intro σ1 h1 cp1 cp1_in cp1_pc σ2 h2 cp2 cp2_in cp2_pc
      have hcp1 := characterizer_sound_altE h cp1 σ1 (cp1.res σ1)
      have hcp2 := characterizer_sound_altE h cp2 σ2 (cp2.res σ2)
      specialize htriple S hP
      aesop
    }

lemma WP_forall_forall_same {α β : Type _}
  (charac : characterizer α β) (Q : β → β → Prop) :
  WP_forall_forall_from_charact charac Q = WP_forall_forall_from_charact_comp charac Q
  := rfl

-/
