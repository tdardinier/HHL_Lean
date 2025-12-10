import MonadicHHL.HHLMonads

-- For the simplest case : Set α → Set β
structure charact_path (α β : Type _) where
  pc : α → Prop -- or Bool?
  res : α → β

def id_charact_path {α : Type _} : charact_path α α :=
  { pc := fun _ => true,
    res := fun y => y }

abbrev characterizer (α β : Type _) : Type := List (charact_path α β)

def characterizer_pure {α β : Type _} (x : β) : characterizer α β :=
  [ {
      pc := fun _ => true,
      res := fun _ => x
  } ]

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

lemma bind_characterizers_sound_simplified {α β γ : Type _}
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
