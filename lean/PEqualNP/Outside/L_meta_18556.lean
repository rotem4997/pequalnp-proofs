import PEqualNP.Defs
set_option maxRecDepth 7000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_18556 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool),   (∀ (x2 x3 : Fin (14 : ℕ) → Bool), (∀ (x4 : Fin (14 : ℕ)), x2 x4 = Bool.true → x3 x4 = Bool.true) → x1 x2 = Bool.true → x1 x3 = Bool.true) →     (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → (x1 fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) →       (∀           x4 ∈             have x5 : List ℕ :=               have x5 : List ℕ :=                 have x5 : List ℕ := [(595 : ℕ), (480 : ℕ), (361 : ℕ), (244 : ℕ), (127 : ℕ)];                 (2626 : ℕ) :: (2244 : ℕ) :: (2376 : ℕ) :: (2126 : ℕ) :: (720 : ℕ) :: x5;               have x6 : List ℕ := (8488 : ℕ) :: (8368 : ℕ) :: (8250 : ℕ) :: (3008 : ℕ) :: (833 : ℕ) :: x5;               (1313 : ℕ) :: (9250 : ℕ) :: (1188 : ℕ) :: (1063 : ℕ) :: x6;             have x6 : List ℕ :=               have x6 : List ℕ := (8722 : ℕ) :: (4244 : ℕ) :: (12312 : ℕ) :: (4125 : ℕ) :: (9632 : ℕ) :: x5;               (10250 : ℕ) :: (6156 : ℕ) :: (12944 : ℕ) :: (4625 : ℕ) :: x6;             have x7 : List ℕ := (7300 : ℕ) :: (5125 : ℕ) :: (3078 : ℕ) :: (14600 : ℕ) :: (4361 : ℕ) :: x6;             (16256 : ℕ) :: (5889 : ℕ) :: (11778 : ℕ) :: (1539 : ℕ) :: x7,           (x1 fun (x6 : Fin (14 : ℕ)) => x4.testBit ↑x6) = Bool.false) →         ∀ (x5 : Fin (14 : ℕ) → Bool), x1 x5 = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true := by
  intro f up pos neg x
  constructor
  · intro hit
    apply Classical.byContradiction
    intro miss
    let bs := List.ofFn (fun p : Fin 7 => x (Fin.castAdd 7 p))
    let b := BitVec.ofBoolListLE bs
    have hlen : bs.length = 7 := by simp [bs]
    have hlt : b.toNat < 128 := by
      have z := b.isLt
      change b.toNat < 2 ^ bs.length at z
      exact Nat.lt_of_lt_of_eq z (congrArg (fun t : Nat => 2^t) hlen)
    let k : Fin 128 := ⟨b.toNat,hlt⟩
    have pack (p : Fin 7) : k.val.testBit p.val = x (Fin.castAdd 7 p) := by
      change b.toNat.testBit p.val = _
      rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
      have h : p.val < bs.length := by rw [hlen]; exact p.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_ofFn h
    let tab : List Nat := [16256, 5889, 11778, 1539, 7300, 5125, 3078, 1063, 14600, 4361, 10250, 127, 6156, 4125, 2126, 127, 12944, 4625, 8722, 595, 4244, 4125, 127, 127, 12312, 4125, 8250, 127, 4125, 4125, 127, 127, 9632, 1313, 9250, 1063, 1188, 1063, 1063, 1063, 8488, 361, 8250, 127, 127, 127, 127, 127, 8368, 127, 8250, 127, 244, 127, 127, 127, 8250, 127, 8250, 127, 127, 127, 127, 127, 3008, 833, 2626, 595, 2244, 127, 2126, 127, 2376, 361, 2126, 127, 2126, 127, 2126, 127, 720, 595, 595, 595, 244, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 480, 361, 127, 127, 244, 127, 127, 127, 361, 361, 127, 127, 127, 127, 127, 127, 244, 127, 127, 127, 244, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127]
    have cert : ∀ a : Fin 128,
      let n := tab.getD a.val 0
      n ∈ ([16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127] : List Nat) ∧
      (∀ p : Fin 7, a.val.testBit p.val = true → n.testBit p.val = true) ∧
      (∀ l : Fin 7, (∀ p : Fin 7, a.val.testBit p.val = true → ¬ (p = l ∨ p = l+1 ∨ p = l+3)) →
        n.testBit (7+l.val) = true) := by decide +kernel
    obtain ⟨member,points,lines⟩ := cert k
    let n := tab.getD k.val 0
    have domination : ∀ i : Fin 14, x i = true → n.testBit i.val = true := by
      intro i
      refine Fin.addCases (m := 7) (n := 7) (motive := fun j => x j = true → n.testBit j.val = true) ?_ ?_ i
      · intro p hp
        exact points p ((pack p).trans hp)
      · intro l hl
        apply lines l
        intro p hp hi
        exact miss ⟨p,l,hi,(pack p).symm.trans hp,hl⟩
    have yes := up x (fun i => n.testBit i.val) domination hit
    have no := neg n member
    rw [no] at yes
    contradiction
  · rintro ⟨p,l,hi,hp,hl⟩
    apply up _ x _ (pos p l hi)
    intro i h
    simp only [decide_eq_true_eq] at h
    rcases h with rfl | rfl
    · exact hp
    · exact hl
