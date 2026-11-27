import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5040_732 :
(let ev := fun (grade : Bool) (p : List (Fin 32768)) (v : List ℕ) =>
    (p.foldl (fun w t =>
      let a := w.getD (t.val % 128) 0
      let b := w.getD (t.val / 128 % 128) 0
      w.concat (if t.val < 16384 then cond grade (a+b) (min a b) else max a b))
      (0 :: (cond grade 0 1) :: v)).getD (27+p.length) 0
 ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
 C.size ≤ 63 → C.output + 1 = 26 + C.size →
 ∃ p : List (Fin 32768), p.length = C.size ∧
 (∀ x : List Bool, x.length = 26 → ev false p (x.map Bool.toNat) = (C.eval x).toNat) ∧
 ∀ M : Finset ℕ, ev true p (List.ofFn (fun i : Fin 26 => if i.val ∈ M then 1 else 0)) = C.lineDeg 26 M) →
(let masks : List ℕ := [7405575,23330829,5799955,22282261,21757977,21233693,3735587,19988517,3211303,19415081,7372867,24117317,7340103,23085129,23068749,22052945,5275731,22020181,19939425,19923045,18890857,6389891,6619269,6357127,6570121,6553741,6324419,6308041,21512457,21528849,4751635,21496089,17318185,20988233,21004625,17891877]
 let D : Finset (Fin 13) := {0,1,3,9}
 ∀ Q : Finset (Fin 13), (Q.card=3 ∨ Q.card=4) →
 (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ D)).card ≤ 2) →
 ∃ k ∈ masks, ∃ t : Fin 13,
 (∀ p : Fin 13, k.testBit (p-t).val = decide (p ∈ Q)) ∧
 ∀ l : Fin 13, k.testBit (13+(l-t).val) = decide (∀ p ∈ Q, p-l ∉ D)) →
(let ev := fun (grade : Bool) (p : List (Fin 32768)) (v : List ℕ) =>
    (p.foldl (fun w t =>
      let a := w.getD (t.val % 128) 0
      let b := w.getD (t.val / 128 % 128) 0
      w.concat (if t.val < 16384 then cond grade (a+b) (min a b) else max a b))
      (0 :: (cond grade 0 1) :: v)).getD (27+p.length) 0
 let D : Finset (Fin 13) := {0,1,3,9}
 let row := fun (P L : Fin 13 → Bool) => (List.ofFn P ++ List.ofFn L).map Bool.toNat
 ∀ p : List (Fin 32768), p.length ≤ 63 →
 (∀ M ∈ ([Finset.range 13, Finset.Ico 13 26] : List (Finset ℕ)), 1 < ev true p (List.ofFn (fun i : Fin 26 => if i.val ∈ M then 1 else 0))) →
 (∀ a l : Fin 13, a-l ∈ D → ev false p (row (fun i => decide (i=a)) (fun i => decide (i=l))) = 1) →
 ∃ Q : Finset (Fin 13), (Q.card=3 ∨ Q.card=4) ∧
 (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ D)).card ≤ 2) ∧
 ev false p (row (fun i => decide (i ∈ Q)) (fun l => decide (∀ i ∈ Q, i-l ∉ D))) ≠ 0) →
(have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ x2.output + (1 : ℕ) = (26 : ℕ) + x2.size ∧ (∀ x3 ∈ x2.gates.zipIdx, ∀ x5 ∈ x3.1.inputs, x5 < (26 : ℕ) + x3.2 ∨ x5 = (89 : ℕ)) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x4 = (0 : Fin (13 : ℕ)) ∨ x4 = (1 : Fin (13 : ℕ)) ∨ x4 = (3 : Fin (13 : ℕ)) ∨ x4 = (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) (x3 + x4) ∨ x6 = Fin.natAdd (13 : ℕ) x3)) = Bool.true) ∧ ∀ x3 ∈ x1, ∀ (x5 : Fin (13 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x7 : Fin (13 : ℕ)), x3.testBit ↑(x7 - x5) = Bool.true ∧ x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x3.testBit ((13 : ℕ) + ↑(x7 - x5)) = Bool.true ∧ x6 = Fin.natAdd (13 : ℕ) x7)) = Bool.false) := by
  intro compile locate exclude rows
  rintro ⟨C, mono, size, last, _, right, left, yes, no⟩
  obtain ⟨p, len, sim, grad⟩ := compile C mono size last
  have hsplit : ∀ f : Fin 26 → Bool, List.ofFn f =
      List.ofFn (fun i : Fin 13 => f (Fin.castAdd 13 i)) ++ List.ofFn (fun i : Fin 13 => f (Fin.natAdd 13 i)) :=
    fun f => List.ofFn_add (m := 13) (n := 13) (f := f)
  have hcn : ∀ i j : Fin 13, Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
    intro i j h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  have hcc : ∀ i j : Fin 13, ((Fin.castAdd 13 i : Fin 26) = Fin.castAdd 13 j) = (i = j) := by
    intro i j
    simp only [Fin.ext_iff, Fin.val_castAdd]
  have hnn : ∀ i j : Fin 13, ((Fin.natAdd 13 i : Fin 26) = Fin.natAdd 13 j) = (i = j) := by
    intro i j
    simp only [Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]
  have hcn' : ∀ i j : Fin 13, ((Fin.castAdd 13 i : Fin 26) = Fin.natAdd 13 j) = False := by
    intro i j
    exact eq_false (hcn i j)
  have hnc' : ∀ i j : Fin 13, ((Fin.natAdd 13 i : Fin 26) = Fin.castAdd 13 j) = False := by
    intro i j
    exact eq_false (fun h => hcn j i h.symm)
  obtain ⟨Q, card, arc, fails⟩ := exclude p (len.trans_le size) (by
    intro M hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [grad]
    rcases hm with rfl | rfl
    · exact Nat.lt_of_not_ge left
    · exact Nat.lt_of_not_ge right) (by
    intro a l edge
    rw [sim _ (by simp)]
    have h := yes l (a-l) (by simpa using edge)
    rw [add_sub_cancel] at h
    unfold PEqualNP.MetaComplexity.circuitFun at h
    rw [hsplit] at h
    simp only [hcc, hnn, hcn', hnc', or_false, false_or] at h
    exact congrArg Bool.toNat h)
  obtain ⟨k, hk, t, hp, hl⟩ := locate Q card arc
  have h := no k (show k ∈ rows from hk) t
  unfold PEqualNP.MetaComplexity.circuitFun at h
  rw [hsplit] at h
  simp only [hcc, hnn, hcn', hnc', and_false, exists_false, or_false, false_or, exists_eq_right', Bool.decide_eq_true, hp, hl] at h
  apply fails
  rw [sim _ (by simp), h]
  rfl
