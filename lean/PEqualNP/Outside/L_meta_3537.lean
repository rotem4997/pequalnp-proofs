import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3537

def rows : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]

def heawood (x : Fin 14 → Bool) : Bool :=
  decide (∃ (u v : Fin 14), (rows.getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true)

def nbrs (u : Fin 14) : Fin 14 × Fin 14 × Fin 14 :=
  match u.val with
  | 0 => (7, 8, 10)
  | 1 => (7, 9, 13)
  | 2 => (8, 12, 13)
  | 3 => (7, 11, 12)
  | 4 => (10, 11, 13)
  | 5 => (9, 10, 12)
  | 6 => (8, 9, 11)
  | 7 => (0, 1, 3)
  | 8 => (0, 2, 6)
  | 9 => (1, 5, 6)
  | 10 => (0, 4, 5)
  | 11 => (3, 4, 6)
  | 12 => (2, 3, 5)
  | _ => (1, 2, 4)

def adj (u v : Fin 14) : Bool :=
  let (a, b, c) := nbrs u
  v == a || v == b || v == c

lemma heawood_pair : ∀ u v : Fin 14,
    heawood (fun k : Fin 14 => decide (k = u ∨ k = v)) = adj u v := by
  decide +kernel

lemma perm_adj (σ : Equiv.Perm (Fin 14))
    (h : ∀ y : Fin 14 → Bool, heawood (y ∘ σ) = heawood y) (u v : Fin 14) :
    adj (σ u) (σ v) = adj u v := by
  have hy := h (fun k : Fin 14 => decide (k = σ u ∨ k = σ v))
  have hcomp : (fun k : Fin 14 => decide (k = σ u ∨ k = σ v)) ∘ σ =
      (fun k : Fin 14 => decide (k = u ∨ k = v)) := by
    funext k
    simp only [Function.comp_apply]
    have e1 : (σ k = σ u) ↔ (k = u) := σ.injective.eq_iff
    have e2 : (σ k = σ v) ↔ (k = v) := σ.injective.eq_iff
    simp [e1, e2]
  rw [hcomp, heawood_pair, heawood_pair] at hy
  exact hy.symm

def thirdNbr (u a b : Fin 14) : Fin 14 :=
  let (x, y, z) := nbrs u
  if x != a && x != b then x
  else if y != a && y != b then y
  else z

def commonNbr (a b : Fin 14) : Fin 14 :=
  let (x, y, z) := nbrs a
  if adj b x then x
  else if adj b y then y
  else z

lemma adj_mem_nbrs (u v : Fin 14) (h : adj u v = true) :
    v = (nbrs u).1 ∨ v = (nbrs u).2.1 ∨ v = (nbrs u).2.2 := by
  unfold adj at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma nbrs_distinct : ∀ u : Fin 14,
    (nbrs u).1 ≠ (nbrs u).2.1 ∧ (nbrs u).1 ≠ (nbrs u).2.2 ∧ (nbrs u).2.1 ≠ (nbrs u).2.2 := by
  decide +kernel

lemma eq_thirdNbr (u a b c : Fin 14)
    (ha : adj u a = true) (hb : adj u b = true) (hc : adj u c = true)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : c = thirdNbr u a b := by
  have ha' := adj_mem_nbrs u a ha
  have hb' := adj_mem_nbrs u b hb
  have hc' := adj_mem_nbrs u c hc
  obtain ⟨h12, h13, h23⟩ := nbrs_distinct u
  unfold thirdNbr
  rcases hc' with rfl | rfl | rfl <;> rcases ha' with h1 | h1 | h1 <;> rcases hb' with h2 | h2 | h2
  all_goals first | contradiction | (subst h1; contradiction) | (subst h2; contradiction) | (subst h1; subst h2; simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23])

lemma eq_commonNbr : ∀ a b c : Fin 14,
    a ≠ b → adj a c = true → adj b c = true → c = commonNbr a b := by
  decide +kernel

def perm3 (p : Fin 6) (u : Fin 14) : Fin 14 × Fin 14 × Fin 14 :=
  let (x, y, z) := nbrs u
  match p.val with
  | 0 => (x, y, z)
  | 1 => (x, z, y)
  | 2 => (y, x, z)
  | 3 => (y, z, x)
  | 4 => (z, x, y)
  | _ => (z, y, x)

lemma exists_perm3 (u a b c : Fin 14)
    (ha : adj u a = true) (hb : adj u b = true) (hc : adj u c = true)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ∃ p : Fin 6, perm3 p u = (a, b, c) := by
  have ha' := adj_mem_nbrs u a ha
  have hb' := adj_mem_nbrs u b hb
  have hc' := adj_mem_nbrs u c hc
  rcases ha' with rfl | rfl | rfl <;> rcases hb' with h2 | h2 | h2 <;> rcases hc' with h3 | h3 | h3
  all_goals first | contradiction | (subst h2; contradiction) | (subst h3; contradiction) |
    (subst h2; subst h3; first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩)

def otherNbr (u a : Fin 14) (pick : Bool) : Fin 14 :=
  let (x, y, z) := nbrs u
  if x == a then (if pick then y else z)
  else if y == a then (if pick then x else z)
  else (if pick then x else y)

lemma exists_otherNbr : ∀ u a b : Fin 14,
    adj u a = true → adj u b = true → b ≠ a →
    ∃ pick : Bool, otherNbr u a pick = b := by
  decide +kernel

def buildAut (a0 : Fin 14) (p : Fin 6) (b1 b2 : Bool) : Fin 14 → Fin 14 :=
  let t := perm3 p a0
  let a7 := t.1
  let a8 := t.2.1
  let a10 := t.2.2
  let a1 := otherNbr a7 a0 b1
  let a2 := otherNbr a8 a0 b2
  let a3 := thirdNbr a7 a0 a1
  let a6 := thirdNbr a8 a0 a2
  let a13 := commonNbr a1 a2
  let a9 := commonNbr a1 a6
  let a11 := commonNbr a3 a6
  let a12 := commonNbr a2 a3
  let a4 := thirdNbr a13 a1 a2
  let a5 := thirdNbr a12 a2 a3
  fun i => match i.val with
    | 0 => a0
    | 1 => a1
    | 2 => a2
    | 3 => a3
    | 4 => a4
    | 5 => a5
    | 6 => a6
    | 7 => a7
    | 8 => a8
    | 9 => a9
    | 10 => a10
    | 11 => a11
    | 12 => a12
    | _ => a13

lemma aut_determined (σ : Equiv.Perm (Fin 14))
    (hadj : ∀ u v : Fin 14, adj (σ u) (σ v) = adj u v) :
    ∃ (a0 : Fin 14) (p : Fin 6) (b1 b2 : Bool), ∀ i : Fin 14, σ i = buildAut a0 p b1 b2 i := by
  have hne : ∀ u v : Fin 14, u ≠ v → σ u ≠ σ v := fun u v huv h => huv (σ.injective h)
  have e07 : adj (σ 0) (σ 7) = true := (hadj 0 7).trans (by decide)
  have e08 : adj (σ 0) (σ 8) = true := (hadj 0 8).trans (by decide)
  have e010 : adj (σ 0) (σ 10) = true := (hadj 0 10).trans (by decide)
  obtain ⟨p, hp⟩ := exists_perm3 (σ 0) (σ 7) (σ 8) (σ 10) e07 e08 e010
    (hne 7 8 (by decide)) (hne 7 10 (by decide)) (hne 8 10 (by decide))
  have e70 : adj (σ 7) (σ 0) = true := (hadj 7 0).trans (by decide)
  have e71 : adj (σ 7) (σ 1) = true := (hadj 7 1).trans (by decide)
  have e73 : adj (σ 7) (σ 3) = true := (hadj 7 3).trans (by decide)
  obtain ⟨b1, hb1⟩ := exists_otherNbr (σ 7) (σ 0) (σ 1) e70 e71 (hne 1 0 (by decide))
  have e80 : adj (σ 8) (σ 0) = true := (hadj 8 0).trans (by decide)
  have e82 : adj (σ 8) (σ 2) = true := (hadj 8 2).trans (by decide)
  have e86 : adj (σ 8) (σ 6) = true := (hadj 8 6).trans (by decide)
  obtain ⟨b2, hb2⟩ := exists_otherNbr (σ 8) (σ 0) (σ 2) e80 e82 (hne 2 0 (by decide))
  have h3 : σ 3 = thirdNbr (σ 7) (σ 0) (σ 1) :=
    eq_thirdNbr _ _ _ _ e70 e71 e73 (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 1 3 (by decide))
  have h6 : σ 6 = thirdNbr (σ 8) (σ 0) (σ 2) :=
    eq_thirdNbr _ _ _ _ e80 e82 e86 (hne 0 2 (by decide)) (hne 0 6 (by decide)) (hne 2 6 (by decide))
  have h13 : σ 13 = commonNbr (σ 1) (σ 2) :=
    eq_commonNbr _ _ _ (hne 1 2 (by decide)) ((hadj 1 13).trans (by decide)) ((hadj 2 13).trans (by decide))
  have h9 : σ 9 = commonNbr (σ 1) (σ 6) :=
    eq_commonNbr _ _ _ (hne 1 6 (by decide)) ((hadj 1 9).trans (by decide)) ((hadj 6 9).trans (by decide))
  have h11 : σ 11 = commonNbr (σ 3) (σ 6) :=
    eq_commonNbr _ _ _ (hne 3 6 (by decide)) ((hadj 3 11).trans (by decide)) ((hadj 6 11).trans (by decide))
  have h12 : σ 12 = commonNbr (σ 2) (σ 3) :=
    eq_commonNbr _ _ _ (hne 2 3 (by decide)) ((hadj 2 12).trans (by decide)) ((hadj 3 12).trans (by decide))
  have h4 : σ 4 = thirdNbr (σ 13) (σ 1) (σ 2) :=
    eq_thirdNbr _ _ _ _ ((hadj 13 1).trans (by decide)) ((hadj 13 2).trans (by decide))
      ((hadj 13 4).trans (by decide)) (hne 1 2 (by decide)) (hne 1 4 (by decide)) (hne 2 4 (by decide))
  have h5 : σ 5 = thirdNbr (σ 12) (σ 2) (σ 3) :=
    eq_thirdNbr _ _ _ _ ((hadj 12 2).trans (by decide)) ((hadj 12 3).trans (by decide))
      ((hadj 12 5).trans (by decide)) (hne 2 3 (by decide)) (hne 2 5 (by decide)) (hne 3 5 (by decide))
  refine ⟨σ 0, p, b1, b2, fun i => ?_⟩
  have h7 : (perm3 p (σ 0)).1 = σ 7 := by rw [hp]
  have h8 : (perm3 p (σ 0)).2.1 = σ 8 := by rw [hp]
  have h10 : (perm3 p (σ 0)).2.2 = σ 10 := by rw [hp]
  have h1 : otherNbr (σ 7) (σ 0) b1 = σ 1 := hb1
  have h2 : otherNbr (σ 8) (σ 0) b2 = σ 2 := hb2
  fin_cases i <;> simp only [buildAut, h7, h8, h10, h1, h2]
  all_goals try first | rfl | exact h3 | exact h6 | exact h13
  · rw [← h13]; exact h4
  · rw [← h3, ← h12]; exact h5
  · rw [← h6]; exact h9
  · rw [← h3, ← h6]; exact h11
  · rw [← h3]; exact h12

def tbl : List (List ℕ) :=
  [[226, 227, 228, 232, 233, 234, 236, 239, 258, 259, 260, 262, 263],
   [264, 266, 267, 269, 277, 278, 281, 284, 338, 341, 344, 354, 355],
   [356, 359, 402, 404, 1576, 1577, 1582, 1583, 1584, 1589, 1592, 1593, 1598],
   [1599, 1601, 1604, 1609, 1611, 1614, 1617, 1619, 2026, 2027, 2032, 2034, 2036],
   [2039, 2042, 2043, 2045, 2047, 2048, 2051, 2053, 2054, 2058, 2066, 2067, 2069]]

def score (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + 15 * min c d + max c d

def liftF (f : Fin 14 → Fin 14) (i : Fin 15) : ℕ :=
  if i.val < 14 then (f (Fin.ofNat 14 i.val)).val else 14

def entry (k : Fin 65) : ℕ :=
  (tbl.getD (k.val / 13) []).getD (k.val % 13) 0

lemma order_ok : ∀ k : Fin 65,
    (0 : Fin 14) < Fin.ofNat 14 (entry k / 225) ∧
    Fin.ofNat 15 (entry k % 225 / 15) < Fin.ofNat 15 (entry k % 15) := by
  decide +kernel

def checkOne (f : Fin 14 → Fin 14) (v : ℕ) : Bool :=
  let x6 := Fin.ofNat 14 (v / 225)
  let x7 := Fin.ofNat 15 (v % 225 / 15)
  let x8 := Fin.ofNat 15 (v % 15)
  decide (score 0 x6.val x7.val x8.val ≤ score (f 0).val (f x6).val (liftF f x7) (liftF f x8))

def checkAut (a0 : Fin 14) (p : Fin 6) (b1 b2 : Bool) : Bool :=
  let f := buildAut a0 p b1 b2
  tbl.all (fun row => row.all (checkOne f))

lemma checkAut_all : ∀ (a0 : Fin 14) (p : Fin 6) (b1 b2 : Bool),
    checkAut a0 p b1 b2 = true := by
  decide +kernel

lemma entry_mem_tbl (k : Fin 65) : ∃ row ∈ tbl, entry k ∈ row := by
  have hk1 : k.val / 13 < tbl.length := by
    change k.val / 13 < 5
    omega
  refine ⟨tbl[k.val / 13], List.getElem_mem hk1, ?_⟩
  have hk2 : k.val % 13 < tbl[k.val / 13].length := by
    have hlen : ∀ i : Fin 5, tbl[i.val].length = 13 := by decide
    have h : tbl[k.val / 13].length = 13 := hlen ⟨k.val / 13, hk1⟩
    rw [h]
    omega
  have heq : entry k = tbl[k.val / 13][k.val % 13] := by
    unfold entry
    rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2]
  rw [heq]
  exact List.getElem_mem hk2

lemma min_ok (k : Fin 65) (a0 : Fin 14) (p : Fin 6) (b1 b2 : Bool) :
    let v := entry k
    let x6 := Fin.ofNat 14 (v / 225)
    let x7 := Fin.ofNat 15 (v % 225 / 15)
    let x8 := Fin.ofNat 15 (v % 15)
    let f := buildAut a0 p b1 b2
    score 0 x6.val x7.val x8.val ≤ score (f 0).val (f x6).val (liftF f x7) (liftF f x8) := by
  have hall := checkAut_all a0 p b1 b2
  unfold checkAut at hall
  rw [List.all_eq_true] at hall
  obtain ⟨row, hrow, hent⟩ := entry_mem_tbl k
  have hr := hall row hrow
  rw [List.all_eq_true] at hr
  have hv := hr (entry k) hent
  unfold checkOne at hv
  exact of_decide_eq_true hv

end PEqualNP.Outside.L_meta_3537

theorem PEqualNP.Outside.L_meta_3537 : have x1 : (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true); have x2 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x2 x3 x4 x5 : ℕ) => ((15 : ℕ) * Min.min x2 x3 + Max.max x2 x3) * (225 : ℕ) + (15 : ℕ) * Min.min x4 x5 + Max.max x4 x5; have x3 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x3 : Equiv.Perm (Fin (14 : ℕ))) (x4 : Fin (15 : ℕ)) => if ↑x4 < (14 : ℕ) then ↑(x3 (Fin.ofNat (14 : ℕ) ↑x4)) else (14 : ℕ); ∀ (x4 : Fin (65 : ℕ)),   have x5 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);   have x6 : Fin (14 : ℕ) := Fin.ofNat (14 : ℕ) (x5 / (225 : ℕ));   have x7 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (225 : ℕ) / (15 : ℕ));   have x8 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (15 : ℕ));   (0 : Fin (14 : ℕ)) < x6 ∧ x7 < x8 ∧ ∀ (x9 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x10 : Fin (14 : ℕ) → Bool), x1 (x10 ∘ ⇑x9) = x1 x10) → x2 (0 : ℕ) ↑x6 ↑x7 ↑x8 ≤ x2 (↑(x9 (0 : Fin (14 : ℕ)))) (↑(x9 x6)) (x3 x9 x7) (x3 x9 x8) := by
  dsimp only
  intro x4
  refine ⟨(PEqualNP.Outside.L_meta_3537.order_ok x4).1, (PEqualNP.Outside.L_meta_3537.order_ok x4).2, ?_⟩
  intro σ hσ
  have hadj := PEqualNP.Outside.L_meta_3537.perm_adj σ hσ
  obtain ⟨a0, p, b1, b2, hdet⟩ := PEqualNP.Outside.L_meta_3537.aut_determined σ hadj
  have hlift : ∀ z : Fin 15, (if z.val < 14 then (σ (Fin.ofNat 14 z.val)).val else 14) =
      PEqualNP.Outside.L_meta_3537.liftF (PEqualNP.Outside.L_meta_3537.buildAut a0 p b1 b2) z := by
    intro z
    unfold PEqualNP.Outside.L_meta_3537.liftF
    split_ifs
    · rw [hdet]
    · rfl
  have hmin := PEqualNP.Outside.L_meta_3537.min_ok x4 a0 p b1 b2
  dsimp only at hmin ⊢
  rw [hdet 0, hdet _, hlift _, hlift _]
  exact hmin
