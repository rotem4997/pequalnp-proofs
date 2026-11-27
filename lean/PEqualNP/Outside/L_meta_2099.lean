import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2099_aux

def inc (a b : Fin 13) : Bool := [0, 1, 3, 9].contains ((a.val + 13 - b.val) % 13)

theorem inc_iff : ∀ a b : Fin 13,
    (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + d) ↔ inc a b = true := by decide

def missB (f : Fin 13 → Bool) (w : Fin 13) : Bool :=
  (List.finRange 13).all fun p => !(f p && inc p w)

def bitB (f : Fin 13 → Bool) (k : Fin 17) : Bool :=
  if k.val < 5 then f (Fin.ofNat 13 k.val)
  else if k.val < 14 then missB f (Fin.ofNat 13 (k.val - 5))
  else missB f (Fin.ofNat 13 (k.val - 4))

def enc : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (enc bs)

theorem enc_testBit : ∀ (l : List Bool) (k : ℕ), (enc l).testBit k = l.getD k false
  | [], k => by simp [enc]
  | b :: bs, 0 => by simp [enc]
  | b :: bs, k + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit bs k]

def LL : List ℕ := [31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455,
  8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590,
  29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324,
  58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040]

def h1B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).all fun v => f v || (List.finRange 13).any fun w => missB f w && inc v w

def h2B (f : Fin 13 → Bool) : Bool :=
  (List.finRange 13).any (fun w => (List.finRange 13).all fun p => !f p || inc p w) ||
  (List.finRange 13).any (fun v => (List.finRange 13).all fun w => !missB f w || inc v w)

def chkF (f : Fin 13 → Bool) : Bool :=
  !h1B f || !h2B f || LL.any (fun m => (enc ((List.finRange 17).map (bitB f)) ||| m) == m)

theorem key0 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key1 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key2 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key3 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key4 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key5 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key6 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key7 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [false, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key8 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key9 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key10 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key11 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, false, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key12 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key13 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, false, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key14 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, false, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key15 : ∀ b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [true, true, true, true, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  decide +kernel

theorem key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    chkF (fun i => [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12].getD i.val false) = true := by
  intro b0 b1 b2 b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact key0
  · exact key1
  · exact key2
  · exact key3
  · exact key4
  · exact key5
  · exact key6
  · exact key7
  · exact key8
  · exact key9
  · exact key10
  · exact key11
  · exact key12
  · exact key13
  · exact key14
  · exact key15

end PEqualNP.Outside.L_meta_2099_aux

open PEqualNP.Outside.L_meta_2099_aux in
theorem PEqualNP.Outside.L_meta_2099 : ∀ (x1 : Finset (Fin (13 : ℕ))),   have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};   have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => ∃ x5 ∈ x2, x3 = x4 + x5;   have x4 : Fin (13 : ℕ) → Prop := fun (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x1, ¬x3 x5 x4;   have x5 : Fin (17 : ℕ) → Fin (26 : ℕ) := fun (x5 : Fin (17 : ℕ)) => Fin.ofNat (26 : ℕ) (if ↑x5 < (5 : ℕ) then ↑x5 else if ↑x5 < (14 : ℕ) then ↑x5 + (8 : ℕ) else ↑x5 + (9 : ℕ));   (∀ x6 ∉ x1, ∃ (x8 : Fin (13 : ℕ)), x4 x8 ∧ x3 x6 x8) →     ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x1, x3 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x4 x8 → x3 x7 x8) →       ∃         x8 ∈           have x9 : List ℕ :=             have x9 : List ℕ :=               have x9 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];               (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x9;             have x10 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x9;             (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x10;           have x10 : List ℕ :=             have x10 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x9;             (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x10;           have x11 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x10;           (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x11,         ∀ (x9 : Fin (17 : ℕ)), ((∃ x10 ∈ x1, x5 x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x5 x9 = Fin.natAdd (13 : ℕ) x10 ∧ x4 x10) → x8.testBit ↑x9 = Bool.true := by
  intro X
  dsimp only
  intro h1 h2
  let f : Fin 13 → Bool := fun i => decide (i ∈ X)
  have hf : chkF f = true := by
    have h := key (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11) (f 12)
    have e : (fun i : Fin 13 => [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12].getD i.val false) = f := by
      funext i
      fin_cases i <;> rfl
    rwa [e] at h
  have hmiss : ∀ w, missB f w = true ↔ ∀ p ∈ X, ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d := by
    intro w
    constructor
    · intro h p hp hi
      simp only [missB, List.all_eq_true] at h
      have := h p (List.mem_finRange p)
      simp [f, hp, (inc_iff p w).1 hi] at this
    · intro h
      simp only [missB, List.all_eq_true]
      intro p _
      by_cases hp : p ∈ X
      · have : inc p w = false := by
          cases hi : inc p w
          · rfl
          · exact absurd ((inc_iff p w).2 hi) (h p hp)
        simp [f, hp, this]
      · simp [f, hp]
  have hh1 : h1B f = true := by
    simp only [h1B, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, hmiss, ← inc_iff, f, decide_eq_true_eq]
    intro v
    by_cases hv : v ∈ X
    · exact Or.inl hv
    · obtain ⟨w, a, b⟩ := h1 v hv
      exact Or.inr ⟨w, trivial, a, b⟩
  have hh2 : h2B f = true := by
    simp only [h2B, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', ← inc_iff, f, decide_eq_false_iff_not]
    rcases h2 with ⟨w, hw⟩ | ⟨v, hv⟩
    · left
      refine ⟨w, trivial, fun p => ?_⟩
      by_cases hp : p ∈ X
      · exact Or.inr (hw p hp)
      · exact Or.inl hp
    · right
      refine ⟨v, trivial, fun w => ?_⟩
      by_cases hw : ∀ p ∈ X, ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d
      · exact Or.inr (hv w hw)
      · left
        cases hc : missB f w
        · rfl
        · exact absurd ((hmiss w).1 hc) hw
  simp only [chkF, hh1, hh2, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at hf
  obtain ⟨m, hm, he⟩ := hf
  refine ⟨m, hm, fun k hk => ?_⟩
  have hb : bitB f k = true := by
    have pc : ∀ (k : Fin 17) (p : Fin 13), Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9) = Fin.castAdd 13 p → k.val < 5 ∧ p = Fin.ofNat 13 k.val := by decide
    have pn : ∀ (k : Fin 17) (w : Fin 13), Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9) = Fin.natAdd 13 w → ¬ k.val < 5 ∧ ((k.val < 14 ∧ w = Fin.ofNat 13 (k.val - 5)) ∨ (¬ k.val < 14 ∧ w = Fin.ofNat 13 (k.val - 4))) := by decide
    rcases hk with ⟨p, hp, he2⟩ | ⟨w, he2, hw⟩
    · obtain ⟨a, b⟩ := pc k p he2
      subst b
      simp only [bitB, a, ite_true, f, decide_eq_true_eq]
      exact hp
    · obtain ⟨a, b | b⟩ := pn k w he2
      · obtain ⟨b1, b2⟩ := b
        subst b2
        simp only [bitB, a, b1, ite_false, ite_true]
        exact (hmiss _).2 hw
      · obtain ⟨b1, b2⟩ := b
        subst b2
        simp only [bitB, a, b1, ite_false]
        exact (hmiss _).2 hw
  have ht := congrArg (fun n => n.testBit k.val) he
  simp only [Nat.testBit_or, enc_testBit] at ht
  rw [← ht]
  have : ((List.finRange 17).map (bitB f)).getD k.val false = bitB f k := by
    simp
  rw [this, hb, Bool.true_or]
