import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2615

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

def inc (p l : Fin 13) : Prop :=
  p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9

def incB (p l : Fin 13) : Bool :=
  decide (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9)

def sElem : Fin 4 → Fin 13
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 9

def adjB (u v : Fin 26) : Bool :=
  if hu : u.val < 13 then
    if hv : 13 ≤ v.val then incB ⟨u.val, hu⟩ ⟨v.val - 13, by omega⟩ else false
  else
    if hv : v.val < 13 then incB ⟨v.val, hv⟩ ⟨u.val - 13, by omega⟩ else false

def nbr (u : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => adjB u v = true)

def pgEdges : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun pl => incB pl.1 pl.2 = true)

def incEdges (c : Fin 26) : Finset (Fin 13 × Fin 13) :=
  pgEdges.filter (fun pl => Fin.castAdd 13 pl.1 = c ∨ Fin.natAdd 13 pl.2 = c)

def otherEnd (c : Fin 26) (pl : Fin 13 × Fin 13) : Fin 26 :=
  if Fin.castAdd 13 pl.1 = c then Fin.natAdd 13 pl.2 else Fin.castAdd 13 pl.1

lemma incB_eq_true (p l : Fin 13) : incB p l = true ↔ inc p l := by
  simp [incB, inc]

lemma inc_iff_sElem (p l : Fin 13) : inc p l ↔ ∃ i : Fin 4, p - l = sElem i := by
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

lemma singer_unique :
    ∀ i1 j1 i2 j2 : Fin 4,
      i1 ≠ j1 → sElem i1 - sElem j1 = sElem i2 - sElem j2 → i1 = i2 := by
  decide

lemma adjB_symm : ∀ u v : Fin 26, adjB u v = adjB v u := by decide

lemma adjB_irrefl : ∀ u : Fin 26, adjB u u = false := by decide

lemma adjB_cast_nat : ∀ p l : Fin 13, adjB (Fin.castAdd 13 p) (Fin.natAdd 13 l) = incB p l := by
  decide

lemma pgEdges_card : pgEdges.card = 52 := by decide

lemma nbr_card : ∀ u : Fin 26, (nbr u).card = 4 := by decide

lemma incEdges_card : ∀ c : Fin 26, (incEdges c).card = 4 := by decide

lemma adjB_iff_exists (u v : Fin 26) :
    adjB u v = true ↔
      ∃ p l : Fin 13, inc p l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p)) := by
  constructor
  · intro h
    by_cases hu : u.val < 13
    · by_cases hv : 13 ≤ v.val
      · have hinc : incB ⟨u.val, hu⟩ ⟨v.val - 13, by omega⟩ = true := by
          simpa [adjB, hu, hv] using h
        refine ⟨⟨u.val, hu⟩, ⟨v.val - 13, by omega⟩, (incB_eq_true _ _).mp hinc, Or.inl ⟨?_, ?_⟩⟩
        · ext; rfl
        · ext; simp; omega
      · exfalso
        have hf : adjB u v = false := by simp [adjB, hu, hv]
        rw [hf] at h
        exact Bool.false_ne_true h
    · by_cases hv : v.val < 13
      · have hinc : incB ⟨v.val, hv⟩ ⟨u.val - 13, by omega⟩ = true := by
          simpa [adjB, hu, hv] using h
        refine ⟨⟨v.val, hv⟩, ⟨u.val - 13, by omega⟩, (incB_eq_true _ _).mp hinc, Or.inr ⟨?_, ?_⟩⟩
        · ext; simp; omega
        · ext; rfl
      · exfalso
        have hf : adjB u v = false := by simp [adjB, hu, hv]
        rw [hf] at h
        exact Bool.false_ne_true h
  · rintro ⟨p, l, hinc, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · rw [adjB_cast_nat, incB_eq_true]; exact hinc
    · rw [adjB_symm, adjB_cast_nat, incB_eq_true]; exact hinc

lemma c4_points {p1 p2 l1 l2 : Fin 13} (hp : p1 ≠ p2)
    (h11 : inc p1 l1) (h21 : inc p2 l1) (h12 : inc p1 l2) (h22 : inc p2 l2) : l1 = l2 := by
  obtain ⟨i1, hi1⟩ := (inc_iff_sElem p1 l1).mp h11
  obtain ⟨j1, hj1⟩ := (inc_iff_sElem p2 l1).mp h21
  obtain ⟨i2, hi2⟩ := (inc_iff_sElem p1 l2).mp h12
  obtain ⟨j2, hj2⟩ := (inc_iff_sElem p2 l2).mp h22
  have hne : i1 ≠ j1 := by
    intro h
    rw [h] at hi1
    have hsub : p1 - l1 = p2 - l1 := hi1.trans hj1.symm
    exact hp (sub_left_inj.mp hsub)
  have hdiff : sElem i1 - sElem j1 = sElem i2 - sElem j2 := by
    rw [← hi1, ← hj1, ← hi2, ← hj2]
    abel
  have hi : i1 = i2 := singer_unique i1 j1 i2 j2 hne hdiff
  rw [hi] at hi1
  have hsub : p1 - l1 = p1 - l2 := hi1.trans hi2.symm
  exact sub_right_inj.mp hsub

lemma c4_lines {p1 p2 l1 l2 : Fin 13} (hl : l1 ≠ l2)
    (h11 : inc p1 l1) (h12 : inc p1 l2) (h21 : inc p2 l1) (h22 : inc p2 l2) : p1 = p2 := by
  obtain ⟨i1, hi1⟩ := (inc_iff_sElem p1 l1).mp h11
  obtain ⟨j1, hj1⟩ := (inc_iff_sElem p1 l2).mp h12
  obtain ⟨i2, hi2⟩ := (inc_iff_sElem p2 l1).mp h21
  obtain ⟨j2, hj2⟩ := (inc_iff_sElem p2 l2).mp h22
  have hne : i1 ≠ j1 := by
    intro h
    rw [h] at hi1
    have hsub : p1 - l1 = p1 - l2 := hi1.trans hj1.symm
    exact hl (sub_right_inj.mp hsub)
  have hdiff : sElem i1 - sElem j1 = sElem i2 - sElem j2 := by
    rw [← hi1, ← hj1, ← hi2, ← hj2]
    abel
  have hi : i1 = i2 := singer_unique i1 j1 i2 j2 hne hdiff
  rw [hi] at hi1
  have hsub : p1 - l1 = p2 - l1 := hi1.trans hi2.symm
  exact sub_left_inj.mp hsub

lemma adjB_bipartite (u v : Fin 26) (h : adjB u v = true) : u.val < 13 ↔ 13 ≤ v.val := by
  obtain ⟨p, l, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := (adjB_iff_exists u v).mp h <;> simp

lemma c4_free (u v : Fin 26) (huv : u ≠ v) : (nbr u ∩ nbr v).card ≤ 1 := by
  by_contra h
  have h2 : 1 < (nbr u ∩ nbr v).card := by omega
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp h2
  simp only [Finset.mem_inter, nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  by_cases hu : u.val < 13
  · have hw1_ge : 13 ≤ w1.val := (adjB_bipartite u w1 hw1.1).mp hu
    have hw2_ge : 13 ≤ w2.val := (adjB_bipartite u w2 hw2.1).mp hu
    have hv : v.val < 13 := (adjB_bipartite v w1 hw1.2).mpr hw1_ge
    let p1 : Fin 13 := ⟨u.val, hu⟩
    let p2 : Fin 13 := ⟨v.val, hv⟩
    let l1 : Fin 13 := ⟨w1.val - 13, by omega⟩
    let l2 : Fin 13 := ⟨w2.val - 13, by omega⟩
    have hu_eq : u = Fin.castAdd 13 p1 := by ext; rfl
    have hv_eq : v = Fin.castAdd 13 p2 := by ext; rfl
    have hw1_eq : w1 = Fin.natAdd 13 l1 := by ext; simp [l1]; omega
    have hw2_eq : w2 = Fin.natAdd 13 l2 := by ext; simp [l2]; omega
    have h11 : inc p1 l1 := by
      have := hw1.1; rw [hu_eq, hw1_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h21 : inc p2 l1 := by
      have := hw1.2; rw [hv_eq, hw1_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h12 : inc p1 l2 := by
      have := hw2.1; rw [hu_eq, hw2_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h22 : inc p2 l2 := by
      have := hw2.2; rw [hv_eq, hw2_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have hpne : p1 ≠ p2 := fun heq => huv (by rw [hu_eq, hv_eq, heq])
    have hl : l1 = l2 := c4_points hpne h11 h21 h12 h22
    exact hne (by rw [hw1_eq, hw2_eq, hl])
  · have hw1_lt : w1.val < 13 := by
      have := (adjB_bipartite u w1 hw1.1).not.mp hu; omega
    have hw2_lt : w2.val < 13 := by
      have := (adjB_bipartite u w2 hw2.1).not.mp hu; omega
    have hv : ¬ v.val < 13 := fun hlt =>
      (by omega : ¬ 13 ≤ w1.val) ((adjB_bipartite v w1 hw1.2).mp hlt)
    let l1 : Fin 13 := ⟨u.val - 13, by omega⟩
    let l2 : Fin 13 := ⟨v.val - 13, by omega⟩
    let p1 : Fin 13 := ⟨w1.val, hw1_lt⟩
    let p2 : Fin 13 := ⟨w2.val, hw2_lt⟩
    have hu_eq : u = Fin.natAdd 13 l1 := by ext; simp [l1]; omega
    have hv_eq : v = Fin.natAdd 13 l2 := by ext; simp [l2]; omega
    have hw1_eq : w1 = Fin.castAdd 13 p1 := by ext; rfl
    have hw2_eq : w2 = Fin.castAdd 13 p2 := by ext; rfl
    have h11 : inc p1 l1 := by
      have := hw1.1; rw [adjB_symm, hw1_eq, hu_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h12 : inc p1 l2 := by
      have := hw1.2; rw [adjB_symm, hw1_eq, hv_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h21 : inc p2 l1 := by
      have := hw2.1; rw [adjB_symm, hw2_eq, hu_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have h22 : inc p2 l2 := by
      have := hw2.2; rw [adjB_symm, hw2_eq, hv_eq, adjB_cast_nat, incB_eq_true] at this; exact this
    have hlne : l1 ≠ l2 := fun heq => huv (by rw [hu_eq, hv_eq, heq])
    have hp : p1 = p2 := c4_lines hlne h11 h12 h21 h22
    exact hne (by rw [hw1_eq, hw2_eq, hp])

lemma mem_pgEdges (pl : Fin 13 × Fin 13) : pl ∈ pgEdges ↔ inc pl.1 pl.2 := by
  simp [pgEdges, incB_eq_true]

lemma mem_nbr (u v : Fin 26) : v ∈ nbr u ↔ adjB u v = true := by
  simp [nbr]

lemma mem_incEdges (c : Fin 26) (pl : Fin 13 × Fin 13) :
    pl ∈ incEdges c ↔ inc pl.1 pl.2 ∧ (Fin.castAdd 13 pl.1 = c ∨ Fin.natAdd 13 pl.2 = c) := by
  simp [incEdges, mem_pgEdges]

lemma incEdges_inter_nonempty_of_adj (c1 c2 : Fin 26) (h : adjB c1 c2 = true) :
    (incEdges c1 ∩ incEdges c2).Nonempty := by
  obtain ⟨p, l, hinc, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := (adjB_iff_exists c1 c2).mp h
  · exact ⟨(p, l), Finset.mem_inter.mpr ⟨(mem_incEdges _ _).mpr ⟨hinc, Or.inl rfl⟩,
      (mem_incEdges _ _).mpr ⟨hinc, Or.inr rfl⟩⟩⟩
  · exact ⟨(p, l), Finset.mem_inter.mpr ⟨(mem_incEdges _ _).mpr ⟨hinc, Or.inr rfl⟩,
      (mem_incEdges _ _).mpr ⟨hinc, Or.inl rfl⟩⟩⟩

lemma otherEnd_injOn (c : Fin 26) :
    Set.InjOn (otherEnd c) (incEdges c : Set (Fin 13 × Fin 13)) := by
  intro pl1 h1 pl2 h2 heq
  rw [Finset.mem_coe, mem_incEdges] at h1 h2
  rcases h1.2 with h1p | h1l <;> rcases h2.2 with h2p | h2l
  · have hother : Fin.natAdd 13 pl1.2 = Fin.natAdd 13 pl2.2 := by
      simpa [otherEnd, h1p, h2p] using heq
    apply Prod.ext
    · exact Fin.castAdd_injective 13 13 (h1p.trans h2p.symm)
    · exact Fin.natAdd_injective 13 13 hother
  · have : (Fin.castAdd 13 pl1.1).val = (Fin.natAdd 13 pl2.2).val := by rw [h1p, h2l]
    simp at this; omega
  · have : (Fin.natAdd 13 pl1.2).val = (Fin.castAdd 13 pl2.1).val := by rw [h1l, h2p]
    simp at this; omega
  · have hne1 : Fin.castAdd 13 pl1.1 ≠ c := by
      intro hc; have := congrArg Fin.val (hc.trans h1l.symm); simp at this; omega
    have hne2 : Fin.castAdd 13 pl2.1 ≠ c := by
      intro hc; have := congrArg Fin.val (hc.trans h2l.symm); simp at this; omega
    have hother : Fin.castAdd 13 pl1.1 = Fin.castAdd 13 pl2.1 := by
      simpa [otherEnd, hne1, hne2] using heq
    apply Prod.ext
    · exact Fin.castAdd_injective 13 13 hother
    · exact Fin.natAdd_injective 13 13 (h1l.trans h2l.symm)

lemma disjoint_of_card_biUnion_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β)
    (heq : (s.biUnion f).card = ∑ a ∈ s, (f a).card) :
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (f a) (f b) := by
  intro a ha b hb hab
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have h1 : s = insert a (insert b ((s.erase a).erase b)) := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hya : y = a
    · subst hya; simp [ha]
    · by_cases hyb : y = b
      · subst hyb; simp [hb]
      · simp [hya, hyb]
  set R := (s.erase a).erase b
  have haR : a ∉ insert b R := by simp [R, hab]
  have hbR : b ∉ R := by simp [R]
  have hsum : ∑ y ∈ s, (f y).card = (f a).card + (f b).card + ∑ y ∈ R, (f y).card := by
    conv_lhs => rw [h1]
    rw [Finset.sum_insert haR, Finset.sum_insert hbR]
    omega
  have hbi : s.biUnion f = (f a ∪ f b) ∪ R.biUnion f := by
    conv_lhs => rw [h1]
    rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
  have hlt : (f a ∪ f b).card < (f a).card + (f b).card := by
    have hpos : 0 < (f a ∩ f b).card := Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxa, hxb⟩⟩
    have hun := Finset.card_union_add_card_inter (f a) (f b)
    omega
  have hle1 : ((f a ∪ f b) ∪ R.biUnion f).card ≤ (f a ∪ f b).card + (R.biUnion f).card :=
    Finset.card_union_le _ _
  have hle2 : (R.biUnion f).card ≤ ∑ y ∈ R, (f y).card := Finset.card_biUnion_le
  rw [hbi] at heq
  omega

lemma eq_of_sum_eq_of_le {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → ℕ)
    (hle : ∀ a ∈ s, f a ≤ g a) (heq : ∑ a ∈ s, f a = ∑ a ∈ s, g a) :
    ∀ a ∈ s, f a = g a := by
  intro a ha
  by_contra hne
  have hlt : f a < g a := lt_of_le_of_ne (hle a ha) hne
  have h1 := Finset.add_sum_erase s f ha
  have h2 := Finset.add_sum_erase s g ha
  have h3 : ∑ x ∈ s.erase a, f x ≤ ∑ x ∈ s.erase a, g x :=
    Finset.sum_le_sum (fun x hx => hle x (Finset.mem_of_mem_erase hx))
  omega

def val (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def one (v : Fin 26) : Fin 26 → Bool :=
  fun u => decide (u = v)

def pair (u v : Fin 26) : Fin 26 → Bool :=
  fun w => decide (w = u ∨ w = v)

def F (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def isOr (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def w0 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 0 0

def w1 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 1 0

def CleanHyp (C : Circuit) : Prop :=
  C.size ≤ 64 ∧
  IsAO2 26 C ∧
  (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.inputs.Nodup) ∧
  (∀ x : Fin 26 → Bool, val C x C.output = true ↔ F x) ∧
  (∀ j : ℕ, (gateAt C j).op = GateOp.and → ∀ x : Fin 26 → Bool,
    val C x (26 + j) = true → val C x C.output = true)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  cases g with | mk op ins => cases op <;> simp [isAnd]

lemma isOr_iff (g : Gate) : isOr g = true ↔ g.op = GateOp.or := by
  cases g with | mk op ins => cases op <;> simp [isOr]

lemma isAnd_and_isOr_false (g : Gate) : ¬ (isAnd g = true ∧ isOr g = true) := by
  cases g with | mk op ins => cases op <;> simp [isAnd, isOr]

lemma foldl_stepWire_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWire acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl stepWire acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hlt : i < (stepWire acc g).length := by
      simp [stepWire]; omega
    rw [List.foldl_cons, ih (stepWire acc g) hlt]
    simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_stepWire_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hrb : ∀ w ∈ g.inputs, w < acc.length + j) :
    (gs.foldl stepWire acc).getD (acc.length + j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stepWire acc).getD i false) := by
  induction gs generalizing acc j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp at hj
      subst hj
      have hlen : acc.length < (stepWire acc g0).length := by simp [stepWire]
      rw [Nat.add_zero, List.foldl_cons, foldl_stepWire_getD_lt gs (stepWire acc g0) acc.length hlen]
      have h0 : (stepWire acc g0).getD acc.length false =
          g0.op.eval (g0.inputs.map fun i => acc.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h0]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < acc.length := by simpa using hrb i hi
      have hilt' : i < (stepWire acc g0).length := by simp [stepWire]; omega
      rw [foldl_stepWire_getD_lt gs (stepWire acc g0) i hilt']
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (stepWire acc g0).length = acc.length + 1 := by simp [stepWire]
      have hrb' : ∀ w ∈ g.inputs, w < (stepWire acc g0).length + j := by
        intro w hw; rw [hlen]; have := hrb w hw; omega
      have hidx : acc.length + (j + 1) = (stepWire acc g0).length + j := by rw [hlen]; omega
      rw [List.foldl_cons, hidx]
      exact ih (stepWire acc g0) j hj hrb'

lemma gates_getElem?_eq_some_gateAt (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gateAt_mem_gates (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates :=
  List.mem_of_getElem? (gates_getElem?_eq_some_gateAt C hj)

lemma gate_inputs_eq {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [w0 C j, w1 C j] := by
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.1.2.2 _ (gateAt_mem_gates C hj)
  rcases h : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp [w0, w1, h]
  · simp [h] at hlen

lemma gate_op_cases {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j < C.gates.length) :
    isAnd (gateAt C j) = true ∨ isOr (gateAt C j) = true := by
  rcases hC.2.1.1 _ (gateAt_mem_gates C hj) with h | h
  · exact Or.inl ((isAnd_iff _).mpr h)
  · exact Or.inr ((isOr_iff _).mpr h)

lemma w0_ne_w1 {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j < C.gates.length) :
    w0 C j ≠ w1 C j := by
  have hnd := hC.2.2.1 j (gateAt C j) (gates_getElem?_eq_some_gateAt C hj)
  rw [gate_inputs_eq hC hj] at hnd
  simpa using hnd

lemma w0_lt {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j < C.gates.length) :
    w0 C j < 26 + j := by
  apply hC.2.1.2.1 j hj
  rw [gate_inputs_eq hC hj]
  simp

lemma w1_lt {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j < C.gates.length) :
    w1 C j < 26 + j := by
  apply hC.2.1.2.1 j hj
  rw [gate_inputs_eq hC hj]
  simp

lemma val_input (C : Circuit) (x : Fin 26 → Bool) (v : Fin 26) :
    val C x v.val = x v := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD v.val false = x v
  have hv : v.val < (List.ofFn x).length := by simp
  rw [foldl_stepWire_getD_lt C.gates (List.ofFn x) v.val hv]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some, List.getElem_ofFn]

lemma val_ge_len (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : 26 + C.gates.length ≤ w) :
    val C x w = false := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD w false = false
  have hlen : (C.gates.foldl stepWire (List.ofFn x)).length = 26 + C.gates.length := by
    rw [foldl_stepWire_length]; simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_and {C : Circuit} (hC : CleanHyp C) (x : Fin 26 → Bool) {j : ℕ}
    (hj : j < C.gates.length) (hand : isAnd (gateAt C j) = true) :
    val C x (26 + j) = (val C x (w0 C j) && val C x (w1 C j)) := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD (26 + j) false =
    ((C.gates.foldl stepWire (List.ofFn x)).getD (w0 C j) false &&
     (C.gates.foldl stepWire (List.ofFn x)).getD (w1 C j) false)
  have hlen : (List.ofFn x).length = 26 := by simp
  have hrb : ∀ w ∈ (gateAt C j).inputs, w < (List.ofFn x).length + j := by
    rw [hlen]; exact hC.2.1.2.1 j hj
  have hstep := foldl_stepWire_getD_gate C.gates (List.ofFn x) j (gateAt C j)
    (gates_getElem?_eq_some_gateAt C hj) hrb
  rw [hlen] at hstep
  rw [hstep, (isAnd_iff _).mp hand, gate_inputs_eq hC hj]
  simp [GateOp.eval]

lemma val_or {C : Circuit} (hC : CleanHyp C) (x : Fin 26 → Bool) {j : ℕ}
    (hj : j < C.gates.length) (hor : isOr (gateAt C j) = true) :
    val C x (26 + j) = (val C x (w0 C j) || val C x (w1 C j)) := by
  change (C.gates.foldl stepWire (List.ofFn x)).getD (26 + j) false =
    ((C.gates.foldl stepWire (List.ofFn x)).getD (w0 C j) false ||
     (C.gates.foldl stepWire (List.ofFn x)).getD (w1 C j) false)
  have hlen : (List.ofFn x).length = 26 := by simp
  have hrb : ∀ w ∈ (gateAt C j).inputs, w < (List.ofFn x).length + j := by
    rw [hlen]; exact hC.2.1.2.1 j hj
  have hstep := foldl_stepWire_getD_gate C.gates (List.ofFn x) j (gateAt C j)
    (gates_getElem?_eq_some_gateAt C hj) hrb
  rw [hlen] at hstep
  rw [hstep, (isOr_iff _).mp hor, gate_inputs_eq hC hj]
  simp [GateOp.eval]

lemma val_mono {C : Circuit} (hC : CleanHyp C) {x y : Fin 26 → Bool}
    (hxy : ∀ v : Fin 26, x v = true → y v = true) :
    ∀ w : ℕ, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hw : w < 26
    · have h1 := val_input C x ⟨w, hw⟩
      have h2 := val_input C y ⟨w, hw⟩
      exact h2.trans (hxy ⟨w, hw⟩ (h1.symm.trans hx))
    · by_cases hlen : w < 26 + C.gates.length
      · set j := w - 26
        have hj : j < C.gates.length := by omega
        have hwj : w = 26 + j := by omega
        rw [hwj] at hx ⊢
        rcases gate_op_cases hC hj with hand | hor
        · rw [val_and hC x hj hand] at hx
          rw [val_and hC y hj hand]
          simp only [Bool.and_eq_true] at hx ⊢
          exact ⟨ih (w0 C j) (by have := w0_lt hC hj; omega) hx.1,
                 ih (w1 C j) (by have := w1_lt hC hj; omega) hx.2⟩
        · rw [val_or hC x hj hor] at hx
          rw [val_or hC y hj hor]
          simp only [Bool.or_eq_true] at hx ⊢
          rcases hx with h0 | h1
          · exact Or.inl (ih (w0 C j) (by have := w0_lt hC hj; omega) h0)
          · exact Or.inr (ih (w1 C j) (by have := w1_lt hC hj; omega) h1)
      · rw [val_ge_len C x w (by omega)] at hx
        exact absurd hx Bool.false_ne_true

lemma F_iff_adj (x : Fin 26 → Bool) :
    F x ↔ ∃ u v : Fin 26, adjB u v = true ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨p, l, hinc, hp, hl⟩
    exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, (adjB_iff_exists _ _).mpr ⟨p, l, hinc, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
  · rintro ⟨u, v, hadj, hu, hv⟩
    obtain ⟨p, l, hinc, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := (adjB_iff_exists u v).mp hadj
    · exact ⟨p, l, hinc, hu, hv⟩
    · exact ⟨p, l, hinc, hv, hu⟩

lemma not_F_one (v : Fin 26) : ¬ F (one v) := by
  rw [F_iff_adj]
  rintro ⟨u1, u2, hadj, h1, h2⟩
  simp only [one, decide_eq_true_eq] at h1 h2
  subst h1; subst h2
  rw [adjB_irrefl] at hadj
  exact Bool.false_ne_true hadj

lemma F_pair_iff (u v : Fin 26) : F (pair u v) ↔ adjB u v = true := by
  rw [F_iff_adj]
  constructor
  · rintro ⟨u1, u2, hadj, h1, h2⟩
    simp only [pair, decide_eq_true_eq] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · rw [adjB_irrefl] at hadj; exact absurd hadj Bool.false_ne_true
    · exact hadj
    · rw [adjB_symm] at hadj; exact hadj
    · rw [adjB_irrefl] at hadj; exact absurd hadj Bool.false_ne_true
  · intro hadj
    exact ⟨u, v, hadj, by simp [pair], by simp [pair]⟩

lemma output_bounds {C : Circuit} (hC : CleanHyp C) :
    26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
  constructor
  · by_contra hlt
    have hlt' : C.output < 26 := by omega
    let v : Fin 26 := ⟨C.output, hlt'⟩
    have hv : val C (one v) C.output = true := by
      have := val_input C (one v) v
      simpa [v, one] using this
    exact not_F_one v ((hC.2.2.2.1 (one v)).mp hv)
  · by_contra hge
    have hF : F (fun _ => true) := ⟨0, 0, Or.inl (by simp), rfl, rfl⟩
    have hv := (hC.2.2.2.1 (fun _ => true)).mpr hF
    rw [val_ge_len C _ C.output (by omega)] at hv
    exact Bool.false_ne_true hv

def supp (C : Circuit) (w : ℕ) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => val C (one v) w = true)

lemma mem_supp (C : Circuit) (w : ℕ) (v : Fin 26) :
    v ∈ supp C w ↔ val C (one v) w = true := by
  simp [supp]

lemma supp_input (C : Circuit) (v : Fin 26) : supp C v.val = {v} := by
  ext u
  simp [supp, val_input, one, eq_comm]

lemma supp_empty_imp_ge26 (C : Circuit) (w : ℕ) (h : supp C w = ∅) : 26 ≤ w := by
  by_contra hlt
  have hlt' : w < 26 := by omega
  let v : Fin 26 := ⟨w, hlt'⟩
  have hv : v ∈ supp C w := by
    change v ∈ supp C v.val
    rw [supp_input]
    exact Finset.mem_singleton_self v
  rw [h] at hv
  exact Finset.notMem_empty v hv

lemma supp_ge_len (C : Circuit) (w : ℕ) (hw : 26 + C.gates.length ≤ w) : supp C w = ∅ := by
  ext v
  simp [supp, val_ge_len C (one v) w hw]

lemma supp_output {C : Circuit} (hC : CleanHyp C) : supp C C.output = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false]
  intro hv
  exact not_F_one v ((hC.2.2.2.1 (one v)).mp hv)

lemma supp_and {C : Circuit} (hC : CleanHyp C) {j : ℕ}
    (hand : isAnd (gateAt C j) = true) : supp C (26 + j) = ∅ := by
  ext v
  simp only [mem_supp, Finset.notMem_empty, iff_false]
  intro hv
  have hout := hC.2.2.2.2 j ((isAnd_iff _).mp hand) (one v) hv
  exact not_F_one v ((hC.2.2.2.1 (one v)).mp hout)

lemma supp_or {C : Circuit} (hC : CleanHyp C) {j : ℕ}
    (hj : j < C.gates.length) (hor : isOr (gateAt C j) = true) :
    supp C (26 + j) = supp C (w0 C j) ∪ supp C (w1 C j) := by
  ext v
  simp only [mem_supp, Finset.mem_union, val_or hC (one v) hj hor, Bool.or_eq_true]

lemma val_of_mem_supp {C : Circuit} (hC : CleanHyp C) (x : Fin 26 → Bool) (w : ℕ) (v : Fin 26)
    (hv : v ∈ supp C w) (hx : x v = true) : val C x w = true := by
  apply val_mono hC _ w ((mem_supp C w v).mp hv)
  intro u hu
  simp only [one, decide_eq_true_eq] at hu
  subst hu
  exact hx

lemma and_supp_adj {C : Circuit} (hC : CleanHyp C) {j : ℕ}
    (hj : j < C.gates.length) (hand : isAnd (gateAt C j) = true)
    {u v : Fin 26} (hu : u ∈ supp C (w0 C j)) (hv : v ∈ supp C (w1 C j)) :
    adjB u v = true := by
  have h0 : val C (pair u v) (w0 C j) = true :=
    val_of_mem_supp hC (pair u v) (w0 C j) u hu (by simp [pair])
  have h1 : val C (pair u v) (w1 C j) = true :=
    val_of_mem_supp hC (pair u v) (w1 C j) v hv (by simp [pair])
  have hjv : val C (pair u v) (26 + j) = true := by
    rw [val_and hC (pair u v) hj hand, h0, h1]; rfl
  have hout := hC.2.2.2.2 j ((isAnd_iff _).mp hand) (pair u v) hjv
  exact (F_pair_iff u v).mp ((hC.2.2.2.1 (pair u v)).mp hout)

lemma and_supp_card_one {C : Circuit} (hC : CleanHyp C) {j : ℕ}
    (hj : j < C.gates.length) (hand : isAnd (gateAt C j) = true)
    (h0 : (supp C (w0 C j)).Nonempty) (h1 : (supp C (w1 C j)).Nonempty) :
    (supp C (w0 C j)).card = 1 ∨ (supp C (w1 C j)).card = 1 := by
  by_contra h
  push Not at h
  have hc0 : 1 < (supp C (w0 C j)).card := by
    have := Finset.card_pos.mpr h0; omega
  have hc1 : 1 < (supp C (w1 C j)).card := by
    have := Finset.card_pos.mpr h1; omega
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hc0
  have hsub : supp C (w1 C j) ⊆ nbr u1 ∩ nbr u2 := by
    intro v hv
    rw [Finset.mem_inter, mem_nbr, mem_nbr]
    exact ⟨and_supp_adj hC hj hand hu1 hv, and_supp_adj hC hj hand hu2 hv⟩
  have hle1 := Finset.card_le_card hsub
  have hle2 := c4_free u1 u2 hune
  omega

def coneOf (C : Circuit) : ℕ → Finset ℕ
  | j =>
    if j < C.gates.length then
      (gateAt C j).inputs.toFinset.biUnion (fun w =>
        if h : 26 ≤ w ∧ w < 26 + j then insert (w - 26) (coneOf C (w - 26)) else ∅)
    else ∅
decreasing_by omega

lemma coneOf_lt (C : Circuit) (j k : ℕ) (hk : k ∈ coneOf C j) : k < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [coneOf] at hk
    split_ifs at hk with hj
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨w, _, hw⟩ := hk
      split_ifs at hw with h
      · rw [Finset.mem_insert] at hw
        rcases hw with rfl | hmem
        · omega
        · have := ih (w - 26) (by omega) hmem; omega
      · exact absurd hw (Finset.notMem_empty _)
    · exact absurd hk (Finset.notMem_empty _)

lemma coneOf_mem_of_input (C : Circuit) {j w : ℕ} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) (h1 : 26 ≤ w) (h2 : w < 26 + j) :
    w - 26 ∈ coneOf C j := by
  rw [coneOf]
  simp only [hj, ite_true, Finset.mem_biUnion]
  refine ⟨w, List.mem_toFinset.mpr hw, ?_⟩
  simp only [h1, h2, and_self, dite_true]
  exact Finset.mem_insert_self _ _

lemma coneOf_trans (C : Circuit) {i j k : ℕ} (hki : k ∈ coneOf C i) (hij : i ∈ coneOf C j) :
    k ∈ coneOf C j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [coneOf] at hij
    split_ifs at hij with hj
    · rw [Finset.mem_biUnion] at hij
      obtain ⟨w, hw, hmem⟩ := hij
      split_ifs at hmem with h
      · rw [coneOf]
        simp only [hj, ite_true, Finset.mem_biUnion]
        refine ⟨w, hw, ?_⟩
        simp only [h, and_self, dite_true, Finset.mem_insert]
        rw [Finset.mem_insert] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inr hki
        · exact Or.inr (ih (w - 26) (by omega) hmem)
      · exact absurd hmem (Finset.notMem_empty _)
    · exact absurd hij (Finset.notMem_empty _)

lemma coneOf_has_reader (C : Circuit) (j k : ℕ) (hk : k ∈ coneOf C j) :
    ∃ q ∈ insert j (coneOf C j), 26 + k ∈ (gateAt C q).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [coneOf] at hk
    split_ifs at hk with hj
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨w, hw, hmem⟩ := hk
      split_ifs at hmem with h
      · rw [Finset.mem_insert] at hmem
        rcases hmem with rfl | hmem
        · refine ⟨j, Finset.mem_insert_self _ _, ?_⟩
          have heq : 26 + (w - 26) = w := by omega
          rw [heq]; exact List.mem_toFinset.mp hw
        · obtain ⟨q, hq, hread⟩ := ih (w - 26) (by omega) hmem
          refine ⟨q, Finset.mem_insert_of_mem ?_, hread⟩
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact coneOf_mem_of_input C hj (List.mem_toFinset.mp hw) h.1 h.2
          · exact coneOf_trans C hq (coneOf_mem_of_input C hj (List.mem_toFinset.mp hw) h.1 h.2)
      · exact absurd hmem (Finset.notMem_empty _)
    · exact absurd hk (Finset.notMem_empty _)

def outIdx (C : Circuit) : ℕ := C.output - 26

def used (C : Circuit) : Finset ℕ :=
  insert (outIdx C) (coneOf C (outIdx C))

lemma outIdx_lt {C : Circuit} (hC : CleanHyp C) : outIdx C < C.gates.length := by
  have := output_bounds hC; unfold outIdx; omega

lemma outIdx_add {C : Circuit} (hC : CleanHyp C) : 26 + outIdx C = C.output := by
  have := output_bounds hC; unfold outIdx; omega

lemma used_le_out (C : Circuit) {k : ℕ} (hk : k ∈ used C) : k ≤ outIdx C := by
  rw [used, Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · exact le_rfl
  · exact le_of_lt (coneOf_lt C (outIdx C) k hk)

lemma used_sub {C : Circuit} (hC : CleanHyp C) : used C ⊆ Finset.range C.gates.length := by
  intro k hk
  rw [Finset.mem_range]
  have h1 := used_le_out C hk
  have h2 := outIdx_lt hC
  omega

lemma used_closed {C : Circuit} (hC : CleanHyp C) {j w : ℕ}
    (hj : j ∈ used C) (hw : w ∈ (gateAt C j).inputs) (h26 : 26 ≤ w) :
    w - 26 ∈ used C := by
  have hjlt : j < C.gates.length := Finset.mem_range.mp (used_sub hC hj)
  have hwlt : w < 26 + j := hC.2.1.2.1 j hjlt w hw
  have hmem : w - 26 ∈ coneOf C j := coneOf_mem_of_input C hjlt hw h26 hwlt
  rw [used, Finset.mem_insert] at hj ⊢
  rcases hj with rfl | hj
  · exact Or.inr hmem
  · exact Or.inr (coneOf_trans C hmem hj)

lemma used_has_reader (C : Circuit) {k : ℕ} (hk : k ∈ (used C).erase (outIdx C)) :
    ∃ q ∈ used C, 26 + k ∈ (gateAt C q).inputs := by
  rw [Finset.mem_erase, used, Finset.mem_insert] at hk
  rcases hk.2 with hEq | hcone
  · exact absurd hEq hk.1
  · exact coneOf_has_reader C (outIdx C) k hcone

def Mset (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isAnd (gateAt C k) = true ∧ (supp C (w0 C k)).Nonempty ∧ (supp C (w1 C k)).Nonempty)

def Aless (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isAnd (gateAt C k) = true ∧ (supp C (w0 C k) = ∅ ∨ supp C (w1 C k) = ∅))

def Oclean (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k) = true ∧ supp C (w0 C k) = ∅ ∧ supp C (w1 C k) = ∅)

def Omix (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k) = true ∧
      ((supp C (w0 C k) = ∅ ∧ (supp C (w1 C k)).Nonempty) ∨
       ((supp C (w0 C k)).Nonempty ∧ supp C (w1 C k) = ∅)))

def Opure (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k =>
    isOr (gateAt C k) = true ∧ (supp C (w0 C k)).Nonempty ∧ (supp C (w1 C k)).Nonempty)

def cleanGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => supp C (26 + k) = ∅)

lemma cleanGates_eq_union {C : Circuit} (hC : CleanHyp C) :
    cleanGates C = Mset C ∪ Aless C ∪ Oclean C := by
  ext k
  simp only [cleanGates, Mset, Aless, Oclean, Finset.mem_union, Finset.mem_filter,
    Finset.mem_range, Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨hk, hs⟩
    rcases gate_op_cases hC hk with hand | hor
    · by_cases h0 : supp C (w0 C k) = ∅
      · exact Or.inl (Or.inr ⟨hk, hand, Or.inl h0⟩)
      · by_cases h1 : supp C (w1 C k) = ∅
        · exact Or.inl (Or.inr ⟨hk, hand, Or.inr h1⟩)
        · exact Or.inl (Or.inl ⟨hk, hand, h0, h1⟩)
    · rw [supp_or hC hk hor, Finset.union_eq_empty] at hs
      exact Or.inr ⟨hk, hor, hs.1, hs.2⟩
  · rintro ((⟨hk, hand, _, _⟩ | ⟨hk, hand, _⟩) | ⟨hk, hor, h0, h1⟩)
    · exact ⟨hk, supp_and hC hand⟩
    · exact ⟨hk, supp_and hC hand⟩
    · exact ⟨hk, by rw [supp_or hC hk hor, h0, h1, Finset.empty_union]⟩

lemma sum_partition {C : Circuit} (hC : CleanHyp C) (U : Finset ℕ)
    (hU : U ⊆ Finset.range C.gates.length) (f : ℕ → ℕ) :
    ∑ q ∈ U, f q = (∑ q ∈ Mset C ∩ U, f q) + (∑ q ∈ Aless C ∩ U, f q) +
      (∑ q ∈ Oclean C ∩ U, f q) + (∑ q ∈ Omix C ∩ U, f q) + (∑ q ∈ Opure C ∩ U, f q) := by
  have hunion : U = (Mset C ∩ U) ∪ (Aless C ∩ U) ∪ (Oclean C ∩ U) ∪ (Omix C ∩ U) ∪ (Opure C ∩ U) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_inter, Mset, Aless, Oclean, Omix, Opure,
      Finset.mem_filter, Finset.mem_range, Finset.nonempty_iff_ne_empty]
    constructor
    · intro hkU
      have hk : k < C.gates.length := Finset.mem_range.mp (hU hkU)
      rcases gate_op_cases hC hk with hand | hor
      · by_cases h0 : supp C (w0 C k) = ∅
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hk, hand, Or.inl h0⟩, hkU⟩)))
        · by_cases h1 : supp C (w1 C k) = ∅
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hk, hand, Or.inr h1⟩, hkU⟩)))
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hk, hand, h0, h1⟩, hkU⟩)))
      · by_cases h0 : supp C (w0 C k) = ∅
        · by_cases h1 : supp C (w1 C k) = ∅
          · exact Or.inl (Or.inl (Or.inr ⟨⟨hk, hor, h0, h1⟩, hkU⟩))
          · exact Or.inl (Or.inr ⟨⟨hk, hor, Or.inl ⟨h0, h1⟩⟩, hkU⟩)
        · by_cases h1 : supp C (w1 C k) = ∅
          · exact Or.inl (Or.inr ⟨⟨hk, hor, Or.inr ⟨h0, h1⟩⟩, hkU⟩)
          · exact Or.inr ⟨⟨hk, hor, h0, h1⟩, hkU⟩
    · rintro ((((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩) <;> exact h
  have hd1 : Disjoint (Mset C ∩ U) (Aless C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_inter, Mset, Aless, Finset.mem_filter, Finset.nonempty_iff_ne_empty] at h1 h2
    rcases h2.1.2.2 with h0 | h1'
    · exact h1.1.2.2.1 h0
    · exact h1.1.2.2.2 h1'
  have hd2 : Disjoint ((Mset C ∩ U) ∪ (Aless C ∩ U)) (Oclean C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, Mset, Aless, Oclean, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
  have hd3 : Disjoint ((Mset C ∩ U) ∪ (Aless C ∩ U) ∪ (Oclean C ∩ U)) (Omix C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, Mset, Aless, Oclean, Omix,
      Finset.mem_filter, Finset.nonempty_iff_ne_empty] at h1 h2
    rcases h1 with (h1 | h1) | h1
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · rcases h2.1.2.2 with ⟨_, h1'⟩ | ⟨h0', _⟩
      · exact h1' h1.1.2.2.2
      · exact h0' h1.1.2.2.1
  have hd4 : Disjoint ((Mset C ∩ U) ∪ (Aless C ∩ U) ∪ (Oclean C ∩ U) ∪ (Omix C ∩ U)) (Opure C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, Mset, Aless, Oclean, Omix, Opure,
      Finset.mem_filter, Finset.nonempty_iff_ne_empty] at h1 h2
    rcases h1 with ((h1 | h1) | h1) | h1
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · exact h2.1.2.2.1 h1.1.2.2.1
    · rcases h1.1.2.2 with ⟨h0, _⟩ | ⟨_, h1'⟩
      · exact h2.1.2.2.1 h0
      · exact h2.1.2.2.2 h1'
  conv_lhs => rw [hunion]
  rw [Finset.sum_union hd4, Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1]

lemma card_partition {C : Circuit} (hC : CleanHyp C) (U : Finset ℕ)
    (hU : U ⊆ Finset.range C.gates.length) :
    U.card = (Mset C ∩ U).card + (Aless C ∩ U).card + (Oclean C ∩ U).card +
      (Omix C ∩ U).card + (Opure C ∩ U).card := by
  simpa using sum_partition hC U hU (fun _ => 1)

lemma clean_card_partition {C : Circuit} (hC : CleanHyp C) (U : Finset ℕ) :
    (cleanGates C ∩ U).card =
      (Mset C ∩ U).card + (Aless C ∩ U).card + (Oclean C ∩ U).card := by
  have hun : cleanGates C ∩ U = (Mset C ∩ U) ∪ (Aless C ∩ U) ∪ (Oclean C ∩ U) := by
    rw [cleanGates_eq_union hC, Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
  have hd1 : Disjoint (Mset C ∩ U) (Aless C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_inter, Mset, Aless, Finset.mem_filter, Finset.nonempty_iff_ne_empty] at h1 h2
    rcases h2.1.2.2 with h0 | h1'
    · exact h1.1.2.2.1 h0
    · exact h1.1.2.2.2 h1'
  have hd2 : Disjoint ((Mset C ∩ U) ∪ (Aless C ∩ U)) (Oclean C ∩ U) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, Mset, Aless, Oclean, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
    · exact isAnd_and_isOr_false _ ⟨h1.1.2.1, h2.1.2.1⟩
  rw [hun, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

def cross (C : Circuit) (j : ℕ) : Finset (Fin 13 × Fin 13) :=
  pgEdges.filter (fun pl =>
    (Fin.castAdd 13 pl.1 ∈ supp C (w0 C j) ∧ Fin.natAdd 13 pl.2 ∈ supp C (w1 C j)) ∨
    (Fin.natAdd 13 pl.2 ∈ supp C (w0 C j) ∧ Fin.castAdd 13 pl.1 ∈ supp C (w1 C j)))

def ctrWire (C : Circuit) (j : ℕ) : ℕ :=
  if (supp C (w0 C j)).card = 1 then w0 C j else w1 C j

def leafWire (C : Circuit) (j : ℕ) : ℕ :=
  if (supp C (w0 C j)).card = 1 then w1 C j else w0 C j

def ctr (C : Circuit) (j : ℕ) : Fin 26 :=
  if h : (supp C (ctrWire C j)).Nonempty then (supp C (ctrWire C j)).min' h else 0

lemma supp_ctrWire_eq {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C) :
    supp C (ctrWire C j) = {ctr C j} := by
  simp only [Mset, Finset.mem_filter, Finset.mem_range] at hj
  have hc := and_supp_card_one hC hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
  have hcard : (supp C (ctrWire C j)).card = 1 := by
    unfold ctrWire
    split_ifs with h0
    · exact h0
    · exact hc.resolve_left h0
  have hne : (supp C (ctrWire C j)).Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ctr C j ∈ supp C (ctrWire C j) := by
    unfold ctr; simp only [hne, dite_true]; exact Finset.min'_mem _ hne
  exact (Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun x hx => by
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
    rw [hy, Finset.mem_singleton] at hmem hx
    exact hx.trans hmem.symm⟩)

lemma supp_leafWire_sub_nbr {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C) :
    supp C (leafWire C j) ⊆ nbr (ctr C j) := by
  have hctr : ctr C j ∈ supp C (ctrWire C j) := by
    rw [supp_ctrWire_eq hC hj]; exact Finset.mem_singleton_self _
  simp only [Mset, Finset.mem_filter, Finset.mem_range] at hj
  intro v hv
  rw [mem_nbr]
  unfold ctrWire at hctr
  unfold leafWire at hv
  split_ifs at hctr hv
  · exact and_supp_adj hC hj.1 hj.2.1 hctr hv
  · rw [adjB_symm]; exact and_supp_adj hC hj.1 hj.2.1 hv hctr

lemma cross_sub_incEdges {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C) :
    cross C j ⊆ incEdges (ctr C j) := by
  have hctr := supp_ctrWire_eq hC hj
  intro pl hpl
  simp only [cross, Finset.mem_filter] at hpl
  rw [mem_incEdges]
  refine ⟨(mem_pgEdges pl).mp hpl.1, ?_⟩
  unfold ctrWire at hctr
  split_ifs at hctr
  · rcases hpl.2 with ⟨h0, _⟩ | ⟨h0, _⟩
    · rw [hctr, Finset.mem_singleton] at h0; exact Or.inl h0
    · rw [hctr, Finset.mem_singleton] at h0; exact Or.inr h0
  · rcases hpl.2 with ⟨_, h1⟩ | ⟨_, h1⟩
    · rw [hctr, Finset.mem_singleton] at h1; exact Or.inr h1
    · rw [hctr, Finset.mem_singleton] at h1; exact Or.inl h1

lemma otherEnd_mem_leaf {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C)
    {pl : Fin 13 × Fin 13} (hpl : pl ∈ cross C j) :
    otherEnd (ctr C j) pl ∈ supp C (leafWire C j) := by
  have hctr := supp_ctrWire_eq hC hj
  simp only [cross, Finset.mem_filter] at hpl
  have hne : Fin.castAdd 13 pl.1 ≠ Fin.natAdd 13 pl.2 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  unfold ctrWire at hctr
  unfold leafWire
  split_ifs at hctr ⊢
  · rcases hpl.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hctr, Finset.mem_singleton] at h0
      simp only [otherEnd, h0, ite_true]; exact h1
    · rw [hctr, Finset.mem_singleton] at h0
      have hne' : Fin.castAdd 13 pl.1 ≠ ctr C j := by rw [← h0]; exact hne
      simp only [otherEnd, hne', ite_false]; exact h1
  · rcases hpl.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hctr, Finset.mem_singleton] at h1
      have hne' : Fin.castAdd 13 pl.1 ≠ ctr C j := by rw [← h1]; exact hne
      simp only [otherEnd, hne', ite_false]; exact h0
    · rw [hctr, Finset.mem_singleton] at h1
      simp only [otherEnd, h1, ite_true]; exact h0

lemma cross_card_le_leaf {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C) :
    (cross C j).card ≤ (supp C (leafWire C j)).card := by
  apply Finset.card_le_card_of_injOn (otherEnd (ctr C j))
  · intro pl hpl
    exact otherEnd_mem_leaf hC hj hpl
  · exact (otherEnd_injOn (ctr C j)).mono (Finset.coe_subset.mpr (cross_sub_incEdges hC hj))

lemma cross_card_le_four {C : Circuit} (hC : CleanHyp C) {j : ℕ} (hj : j ∈ Mset C) :
    (cross C j).card ≤ 4 := by
  calc (cross C j).card
      ≤ (supp C (leafWire C j)).card := cross_card_le_leaf hC hj
    _ ≤ (nbr (ctr C j)).card := Finset.card_le_card (supp_leafWire_sub_nbr hC hj)
    _ = 4 := nbr_card (ctr C j)

lemma val_imp_supp_before {C : Circuit} (hC : CleanHyp C) (x : Fin 26 → Bool) (m : ℕ)
    (hno : ∀ i ∈ used C, i < m → isAnd (gateAt C i) = true → val C x (26 + i) = false) :
    ∀ w : ℕ, w < 26 + m → (w < 26 ∨ w - 26 ∈ used C) →
      val C x w = true → ∃ t ∈ supp C w, x t = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwm hwu hx
    by_cases hw26 : w < 26
    · refine ⟨⟨w, hw26⟩, ?_, ?_⟩
      · change (⟨w, hw26⟩ : Fin 26) ∈ supp C (⟨w, hw26⟩ : Fin 26).val
        rw [supp_input]; exact Finset.mem_singleton_self _
      · exact (val_input C x ⟨w, hw26⟩).symm.trans hx
    · have hkU : w - 26 ∈ used C := hwu.resolve_left hw26
      set k := w - 26
      have hwk : w = 26 + k := by omega
      have hkm : k < m := by omega
      have hklt : k < C.gates.length := Finset.mem_range.mp (used_sub hC hkU)
      rw [hwk] at hx ⊢
      rcases gate_op_cases hC hklt with hand | hor
      · rw [hno k hkU hkm hand] at hx
        exact absurd hx Bool.false_ne_true
      · rw [val_or hC x hklt hor, Bool.or_eq_true] at hx
        have h0u : w0 C k < 26 ∨ w0 C k - 26 ∈ used C := by
          by_cases hlt : w0 C k < 26
          · exact Or.inl hlt
          · refine Or.inr (used_closed hC hkU ?_ (by omega))
            rw [gate_inputs_eq hC hklt]; simp
        have h1u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C := by
          by_cases hlt : w1 C k < 26
          · exact Or.inl hlt
          · refine Or.inr (used_closed hC hkU ?_ (by omega))
            rw [gate_inputs_eq hC hklt]; simp
        rcases hx with h0 | h1
        · obtain ⟨t, ht, hxt⟩ := ih (w0 C k) (by have := w0_lt hC hklt; omega)
            (by have := w0_lt hC hklt; omega) h0u h0
          exact ⟨t, by rw [supp_or hC hklt hor]; exact Finset.mem_union_left _ ht, hxt⟩
        · obtain ⟨t, ht, hxt⟩ := ih (w1 C k) (by have := w1_lt hC hklt; omega)
            (by have := w1_lt hC hklt; omega) h1u h1
          exact ⟨t, by rw [supp_or hC hklt hor]; exact Finset.mem_union_right _ ht, hxt⟩

lemma pgEdges_covered {C : Circuit} (hC : CleanHyp C) :
    pgEdges ⊆ (Mset C ∩ used C).biUnion (cross C) := by
  intro pl hpl
  have hinc : inc pl.1 pl.2 := (mem_pgEdges pl).mp hpl
  set u := Fin.castAdd 13 pl.1
  set v := Fin.natAdd 13 pl.2
  set x := pair u v
  have hout : val C x (26 + outIdx C) = true := by
    rw [outIdx_add hC, hC.2.2.2.1 x, F_pair_iff, adjB_cast_nat, incB_eq_true]
    exact hinc
  set afire := (used C).filter (fun j => isAnd (gateAt C j) = true ∧ val C x (26 + j) = true)
  have hne : afire.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hno : ∀ i ∈ used C, i < C.gates.length → isAnd (gateAt C i) = true →
        val C x (26 + i) = false := by
      intro i hi _ hand
      cases hv : val C x (26 + i)
      · rfl
      · have : i ∈ afire := Finset.mem_filter.mpr ⟨hi, hand, hv⟩
        rw [hemp] at this; exact absurd this (Finset.notMem_empty _)
    have hmemU : 26 + outIdx C < 26 ∨ (26 + outIdx C) - 26 ∈ used C := by
      right; simp [used]
    obtain ⟨t, ht, _⟩ := val_imp_supp_before hC x C.gates.length hno (26 + outIdx C)
      (by have := outIdx_lt hC; omega) hmemU hout
    rw [outIdx_add hC, supp_output hC] at ht
    exact Finset.notMem_empty t ht
  set j := afire.min' hne
  have hjmem : j ∈ afire := Finset.min'_mem afire hne
  simp only [afire, Finset.mem_filter] at hjmem
  have hjU : j ∈ used C := hjmem.1
  have hjlt : j < C.gates.length := Finset.mem_range.mp (used_sub hC hjU)
  have hjand : isAnd (gateAt C j) = true := hjmem.2.1
  have hjval : val C x (26 + j) = true := hjmem.2.2
  have hno : ∀ i ∈ used C, i < j → isAnd (gateAt C i) = true → val C x (26 + i) = false := by
    intro i hi hij hand
    cases hv : val C x (26 + i)
    · rfl
    · have : i ∈ afire := Finset.mem_filter.mpr ⟨hi, hand, hv⟩
      have := Finset.min'_le afire i this
      omega
  rw [val_and hC x hjlt hjand, Bool.and_eq_true] at hjval
  have h0u : w0 C j < 26 ∨ w0 C j - 26 ∈ used C := by
    by_cases hlt : w0 C j < 26
    · exact Or.inl hlt
    · refine Or.inr (used_closed hC hjU ?_ (by omega))
      rw [gate_inputs_eq hC hjlt]; simp
  have h1u : w1 C j < 26 ∨ w1 C j - 26 ∈ used C := by
    by_cases hlt : w1 C j < 26
    · exact Or.inl hlt
    · refine Or.inr (used_closed hC hjU ?_ (by omega))
      rw [gate_inputs_eq hC hjlt]; simp
  obtain ⟨t0, ht0, hxt0⟩ := val_imp_supp_before hC x j hno (w0 C j) (w0_lt hC hjlt) h0u hjval.1
  obtain ⟨t1, ht1, hxt1⟩ := val_imp_supp_before hC x j hno (w1 C j) (w1_lt hC hjlt) h1u hjval.2
  have hadj : adjB t0 t1 = true := and_supp_adj hC hjlt hjand ht0 ht1
  have htne : t0 ≠ t1 := by
    intro heq; subst heq; rw [adjB_irrefl] at hadj; exact Bool.false_ne_true hadj
  simp only [x, pair, decide_eq_true_eq] at hxt0 hxt1
  have hjM : j ∈ Mset C := by
    simp only [Mset, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjlt, hjand, ⟨t0, ht0⟩, ⟨t1, ht1⟩⟩
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_inter.mpr ⟨hjM, hjU⟩, ?_⟩
  simp only [cross, Finset.mem_filter]
  refine ⟨hpl, ?_⟩
  rcases hxt0 with rfl | rfl <;> rcases hxt1 with rfl | rfl
  · exact absurd rfl htne
  · exact Or.inl ⟨ht0, ht1⟩
  · exact Or.inr ⟨ht0, ht1⟩
  · exact absurd rfl htne

lemma thirteen_le_M_used {C : Circuit} (hC : CleanHyp C) : 13 ≤ (Mset C ∩ used C).card := by
  have h52 : 52 ≤ ∑ j ∈ Mset C ∩ used C, (cross C j).card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ ((Mset C ∩ used C).biUnion (cross C)).card := Finset.card_le_card (pgEdges_covered hC)
      _ ≤ ∑ j ∈ Mset C ∩ used C, (cross C j).card := Finset.card_biUnion_le
  have h4 : ∑ j ∈ Mset C ∩ used C, (cross C j).card ≤ 4 * (Mset C ∩ used C).card := by
    calc ∑ j ∈ Mset C ∩ used C, (cross C j).card
        ≤ ∑ _j ∈ Mset C ∩ used C, 4 := Finset.sum_le_sum (fun j hj =>
          cross_card_le_four hC (Finset.mem_inter.mp hj).1)
      _ = 4 * (Mset C ∩ used C).card := by simp [mul_comm]
  omega

def Hc (C : Circuit) (c : Fin 26) : Finset ℕ :=
  (Opure C).filter (fun k => supp C (26 + k) ⊆ nbr c ∧ 2 ≤ (supp C (26 + k)).card)

lemma Hc_disjoint (C : Circuit) {c1 c2 : Fin 26} (hne : c1 ≠ c2) :
    Disjoint (Hc C c1) (Hc C c2) := by
  rw [Finset.disjoint_left]
  intro k h1 h2
  simp only [Hc, Finset.mem_filter] at h1 h2
  have hsub : supp C (26 + k) ⊆ nbr c1 ∩ nbr c2 := Finset.subset_inter h1.2.1 h2.2.1
  have hle1 := Finset.card_le_card hsub
  have hle2 := c4_free c1 c2 hne
  omega

lemma biUnion_supp_le {C : Circuit} (hC : CleanHyp C) (c : Fin 26) :
    ∀ m : ℕ, ∀ W : Finset ℕ,
      (∀ w ∈ W, w < 26 + m) → (∀ w ∈ W, supp C w ⊆ nbr c) →
      (W.biUnion (supp C)).card ≤ W.card + ((Hc C c).filter (· < m)).card := by
  intro m
  induction m with
  | zero =>
    intro W hW _
    have h1 : ∀ w ∈ W, (supp C w).card ≤ 1 := by
      intro w hw
      have hlt : w < 26 := by have := hW w hw; omega
      have heq : supp C w = {⟨w, hlt⟩} := by
        change supp C (⟨w, hlt⟩ : Fin 26).val = _; exact supp_input C ⟨w, hlt⟩
      rw [heq]; simp
    calc (W.biUnion (supp C)).card
        ≤ ∑ w ∈ W, (supp C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum h1
      _ = W.card := by simp
      _ ≤ W.card + ((Hc C c).filter (· < 0)).card := Nat.le_add_right _ _
  | succ m ih =>
    intro W hW hsub
    by_cases hmem : 26 + m ∈ W
    · set W' := W.erase (26 + m)
      have hW'lt : ∀ w ∈ W', w < 26 + m := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2; omega
      have hW'sub : ∀ w ∈ W', supp C w ⊆ nbr c :=
        fun w hw => hsub w (Finset.mem_of_mem_erase hw)
      have hWcard : W'.card + 1 = W.card := Finset.card_erase_add_one hmem
      have hfilt_sub : (Hc C c).filter (· < m) ⊆ (Hc C c).filter (· < m + 1) := by
        intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, by omega⟩
      by_cases hmlt : m < C.gates.length
      · rcases gate_op_cases hC hmlt with hand | hor
        · have heq : W.biUnion (supp C) = W'.biUnion (supp C) := by
            rw [← Finset.insert_erase hmem, Finset.biUnion_insert, supp_and hC hand,
              Finset.empty_union]
          rw [heq]
          have hih := ih W' hW'lt hW'sub
          have hfl := Finset.card_le_card hfilt_sub
          omega
        · have hsupp_m : supp C (26 + m) = supp C (w0 C m) ∪ supp C (w1 C m) :=
            supp_or hC hmlt hor
          have hsub0 : supp C (w0 C m) ⊆ nbr c :=
            Finset.Subset.trans (by rw [hsupp_m]; exact Finset.subset_union_left) (hsub _ hmem)
          have hsub1 : supp C (w1 C m) ⊆ nbr c :=
            Finset.Subset.trans (by rw [hsupp_m]; exact Finset.subset_union_right) (hsub _ hmem)
          by_cases h0 : supp C (w0 C m) = ∅
          · have heq : W.biUnion (supp C) = (insert (w1 C m) W').biUnion (supp C) := by
              rw [← Finset.insert_erase hmem, Finset.biUnion_insert, Finset.biUnion_insert,
                hsupp_m, h0, Finset.empty_union]
            rw [heq]
            have hih := ih (insert (w1 C m) W')
              (fun w hw => by
                rw [Finset.mem_insert] at hw
                rcases hw with rfl | hw; exact w1_lt hC hmlt; exact hW'lt w hw)
              (fun w hw => by
                rw [Finset.mem_insert] at hw
                rcases hw with rfl | hw; exact hsub1; exact hW'sub w hw)
            have hc1 : (insert (w1 C m) W').card ≤ W'.card + 1 := Finset.card_insert_le _ _
            have hfl := Finset.card_le_card hfilt_sub
            omega
          · by_cases h1 : supp C (w1 C m) = ∅
            · have heq : W.biUnion (supp C) = (insert (w0 C m) W').biUnion (supp C) := by
                rw [← Finset.insert_erase hmem, Finset.biUnion_insert, Finset.biUnion_insert,
                  hsupp_m, h1, Finset.union_empty]
              rw [heq]
              have hih := ih (insert (w0 C m) W')
                (fun w hw => by
                  rw [Finset.mem_insert] at hw
                  rcases hw with rfl | hw; exact w0_lt hC hmlt; exact hW'lt w hw)
                (fun w hw => by
                  rw [Finset.mem_insert] at hw
                  rcases hw with rfl | hw; exact hsub0; exact hW'sub w hw)
              have hc1 : (insert (w0 C m) W').card ≤ W'.card + 1 := Finset.card_insert_le _ _
              have hfl := Finset.card_le_card hfilt_sub
              omega
            · by_cases hcard2 : 2 ≤ (supp C (26 + m)).card
              · have hmHc : m ∈ Hc C c := by
                  simp only [Hc, Opure, Finset.mem_filter, Finset.mem_range,
                    Finset.nonempty_iff_ne_empty]
                  exact ⟨⟨hmlt, hor, h0, h1⟩, hsub _ hmem, hcard2⟩
                have hfilt_eq : (Hc C c).filter (· < m + 1) =
                    insert m ((Hc C c).filter (· < m)) := by
                  ext k; simp only [Finset.mem_filter, Finset.mem_insert]
                  constructor
                  · rintro ⟨hk, hlt⟩
                    by_cases hkm : k = m
                    · exact Or.inl hkm
                    · exact Or.inr ⟨hk, by omega⟩
                  · rintro (rfl | ⟨hk, hlt⟩)
                    · exact ⟨hmHc, by omega⟩
                    · exact ⟨hk, by omega⟩
                have hm_notin : m ∉ (Hc C c).filter (· < m) := by simp
                have hfc : ((Hc C c).filter (· < m + 1)).card =
                    ((Hc C c).filter (· < m)).card + 1 := by
                  rw [hfilt_eq, Finset.card_insert_of_notMem hm_notin]
                have heq : W.biUnion (supp C) =
                    (insert (w0 C m) (insert (w1 C m) W')).biUnion (supp C) := by
                  rw [← Finset.insert_erase hmem, Finset.biUnion_insert, Finset.biUnion_insert,
                    Finset.biUnion_insert, hsupp_m, Finset.union_assoc]
                rw [heq]
                have hih := ih (insert (w0 C m) (insert (w1 C m) W'))
                  (fun w hw => by
                    simp only [Finset.mem_insert] at hw
                    rcases hw with rfl | rfl | hw
                    · exact w0_lt hC hmlt
                    · exact w1_lt hC hmlt
                    · exact hW'lt w hw)
                  (fun w hw => by
                    simp only [Finset.mem_insert] at hw
                    rcases hw with rfl | rfl | hw
                    · exact hsub0
                    · exact hsub1
                    · exact hW'sub w hw)
                have hc1 : (insert (w0 C m) (insert (w1 C m) W')).card ≤ W'.card + 2 := by
                  have := Finset.card_insert_le (w0 C m) (insert (w1 C m) W')
                  have := Finset.card_insert_le (w1 C m) W'
                  omega
                omega
              · have hne0 : (supp C (w0 C m)).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
                have hsub0m : supp C (w0 C m) ⊆ supp C (26 + m) := by
                  rw [hsupp_m]; exact Finset.subset_union_left
                have heq0 : supp C (w0 C m) = supp C (26 + m) := by
                  apply Finset.eq_of_subset_of_card_le hsub0m
                  have := Finset.card_pos.mpr hne0
                  omega
                have heq : W.biUnion (supp C) = (insert (w0 C m) W').biUnion (supp C) := by
                  rw [← Finset.insert_erase hmem, Finset.biUnion_insert, Finset.biUnion_insert,
                    heq0]
                rw [heq]
                have hih := ih (insert (w0 C m) W')
                  (fun w hw => by
                    rw [Finset.mem_insert] at hw
                    rcases hw with rfl | hw; exact w0_lt hC hmlt; exact hW'lt w hw)
                  (fun w hw => by
                    rw [Finset.mem_insert] at hw
                    rcases hw with rfl | hw; exact hsub0; exact hW'sub w hw)
                have hc1 : (insert (w0 C m) W').card ≤ W'.card + 1 := Finset.card_insert_le _ _
                have hfl := Finset.card_le_card hfilt_sub
                omega
      · have heq : W.biUnion (supp C) = W'.biUnion (supp C) := by
          rw [← Finset.insert_erase hmem, Finset.biUnion_insert, supp_ge_len C (26 + m) (by omega),
            Finset.empty_union]
        rw [heq]
        have hih := ih W' hW'lt hW'sub
        have hfl := Finset.card_le_card hfilt_sub
        omega
    · have hWlt : ∀ w ∈ W, w < 26 + m := by
        intro w hw
        have := hW w hw
        have hne : w ≠ 26 + m := fun h => hmem (h ▸ hw)
        omega
      have hih := ih W hWlt hsub
      have hfilt_sub : (Hc C c).filter (· < m) ⊆ (Hc C c).filter (· < m + 1) := by
        intro k hk; simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, by omega⟩
      have hfl := Finset.card_le_card hfilt_sub
      omega

lemma bound1_edges {C : Circuit} (hC : CleanHyp C) :
    52 ≤ (Mset C ∩ used C).card + (Opure C).card := by
  set MU := Mset C ∩ used C
  let Mc : Fin 26 → Finset ℕ := fun c => MU.filter (fun j => ctr C j = c)
  have hcov : pgEdges ⊆ Finset.univ.biUnion (fun c : Fin 26 => (Mc c).biUnion (cross C)) := by
    intro pl hpl
    have hmem := pgEdges_covered hC hpl
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨j, hj, hplj⟩ := hmem
    rw [Finset.mem_biUnion]
    refine ⟨ctr C j, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, ?_, hplj⟩⟩
    exact Finset.mem_filter.mpr ⟨hj, rfl⟩
  have hper : ∀ c : Fin 26, ((Mc c).biUnion (cross C)).card ≤ (Mc c).card + (Hc C c).card := by
    intro c
    set Lc := (Mc c).image (leafWire C)
    have hcard_le : ((Mc c).biUnion (cross C)).card ≤ (Lc.biUnion (supp C)).card := by
      apply Finset.card_le_card_of_injOn (otherEnd c)
      · intro pl hpl
        rw [Finset.mem_coe, Finset.mem_biUnion] at hpl
        obtain ⟨j, hj, hplj⟩ := hpl
        have hjM : j ∈ Mset C := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
        have hjc : ctr C j = c := (Finset.mem_filter.mp hj).2
        rw [Finset.mem_coe, Finset.mem_biUnion]
        refine ⟨leafWire C j, Finset.mem_image_of_mem _ hj, ?_⟩
        rw [← hjc]; exact otherEnd_mem_leaf hC hjM hplj
      · apply (otherEnd_injOn c).mono
        intro pl hpl
        rw [Finset.mem_coe] at hpl ⊢
        rw [Finset.mem_biUnion] at hpl
        obtain ⟨j, hj, hplj⟩ := hpl
        have hjM : j ∈ Mset C := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
        have hjc : ctr C j = c := (Finset.mem_filter.mp hj).2
        rw [← hjc]; exact cross_sub_incEdges hC hjM hplj
    have hLlt : ∀ w ∈ Lc, w < 26 + C.gates.length := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      have hjM : j ∈ Mset C := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
      have hjlt : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hjM).1
      unfold leafWire
      split_ifs
      · have := w1_lt hC hjlt; omega
      · have := w0_lt hC hjlt; omega
    have hLsub : ∀ w ∈ Lc, supp C w ⊆ nbr c := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      have hjM : j ∈ Mset C := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
      have hjc : ctr C j = c := (Finset.mem_filter.mp hj).2
      rw [← hjc]; exact supp_leafWire_sub_nbr hC hjM
    have hbi := biUnion_supp_le hC c C.gates.length Lc hLlt hLsub
    have hHfilt : (Hc C c).filter (· < C.gates.length) = Hc C c := by
      ext k; simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hk
      simp only [Hc, Opure, Finset.mem_filter, Finset.mem_range] at hk
      exact hk.1.1
    rw [hHfilt] at hbi
    have hLcard : Lc.card ≤ (Mc c).card := Finset.card_image_le
    omega
  have hsumMc : ∑ c : Fin 26, (Mc c).card = MU.card := by
    have hun : Finset.univ.biUnion Mc = MU := by
      ext j; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Mc, Finset.mem_filter]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨ctr C j, h, rfl⟩⟩
    have hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Mc := by
      intro c1 _ c2 _ hne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Mc, Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    rw [← hun, Finset.card_biUnion (fun c1 _ c2 _ hne => hdisj (Set.mem_univ c1) (Set.mem_univ c2) hne)]
  have hsumHc : ∑ c : Fin 26, (Hc C c).card ≤ (Opure C).card := by
    have hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) (Hc C) :=
      fun c1 _ c2 _ hne => Hc_disjoint C hne
    rw [← Finset.card_biUnion (fun c1 _ c2 _ hne => hdisj (Set.mem_univ c1) (Set.mem_univ c2) hne)]
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_biUnion] at hk
    obtain ⟨c, _, hkc⟩ := hk
    exact (Finset.mem_filter.mp hkc).1
  calc 52 = pgEdges.card := pgEdges_card.symm
    _ ≤ (Finset.univ.biUnion (fun c : Fin 26 => (Mc c).biUnion (cross C))).card :=
        Finset.card_le_card hcov
    _ ≤ ∑ c : Fin 26, ((Mc c).biUnion (cross C)).card := Finset.card_biUnion_le
    _ ≤ ∑ c : Fin 26, ((Mc c).card + (Hc C c).card) := Finset.sum_le_sum (fun c _ => hper c)
    _ = (∑ c : Fin 26, (Mc c).card) + (∑ c : Fin 26, (Hc C c).card) := Finset.sum_add_distrib
    _ ≤ MU.card + (Opure C).card := by omega

def cleanIn (C : Circuit) (q : ℕ) : Finset ℕ :=
  ((gateAt C q).inputs.toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)).image (· - 26)

lemma mem_cleanIn (C : Circuit) (q k : ℕ) :
    k ∈ cleanIn C q ↔ 26 + k ∈ (gateAt C q).inputs ∧ supp C (26 + k) = ∅ := by
  simp only [cleanIn, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨w, ⟨hw, h26, hs⟩, rfl⟩
    have heq : 26 + (w - 26) = w := by omega
    rw [heq]; exact ⟨hw, hs⟩
  · rintro ⟨hw, hs⟩
    exact ⟨26 + k, ⟨hw, by omega, hs⟩, by omega⟩

lemma cleanIn_card_eq (C : Circuit) (q : ℕ) :
    (cleanIn C q).card =
      ((gateAt C q).inputs.toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)).card := by
  unfold cleanIn
  apply Finset.card_image_of_injOn
  intro w1 hw1 w2 hw2 heq
  rw [Finset.mem_coe, Finset.mem_filter] at hw1 hw2
  dsimp only at heq
  omega

lemma cleanIn_card_M {C : Circuit} (hC : CleanHyp C) {q : ℕ} (hq : q ∈ Mset C) :
    (cleanIn C q).card = 0 := by
  simp only [Mset, Finset.mem_filter, Finset.mem_range, Finset.nonempty_iff_ne_empty] at hq
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq.1]
  simp [hq.2.2.1, hq.2.2.2]

lemma cleanIn_card_Opure {C : Circuit} (hC : CleanHyp C) {q : ℕ} (hq : q ∈ Opure C) :
    (cleanIn C q).card = 0 := by
  simp only [Opure, Finset.mem_filter, Finset.mem_range, Finset.nonempty_iff_ne_empty] at hq
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq.1]
  simp [hq.2.2.1, hq.2.2.2]

lemma cleanIn_card_Omix {C : Circuit} (hC : CleanHyp C) {q : ℕ} (hq : q ∈ Omix C) :
    (cleanIn C q).card = 1 := by
  simp only [Omix, Finset.mem_filter, Finset.mem_range, Finset.nonempty_iff_ne_empty] at hq
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq.1]
  rcases hq.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h26 := supp_empty_imp_ge26 C (w0 C q) h0
    have heq : ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) = {w0 C q} := by
      ext w
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, _, hs⟩
        · rfl
        · exact absurd hs h1
      · rintro rfl
        exact ⟨Or.inl rfl, h26, h0⟩
    rw [heq]; simp
  · have h26 := supp_empty_imp_ge26 C (w1 C q) h1
    have heq : ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) = {w1 C q} := by
      ext w
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, _, hs⟩
        · exact absurd hs h0
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h26, h1⟩
    rw [heq]; simp

lemma cleanIn_card_Oclean {C : Circuit} (hC : CleanHyp C) {q : ℕ} (hq : q ∈ Oclean C) :
    (cleanIn C q).card = 2 := by
  simp only [Oclean, Finset.mem_filter, Finset.mem_range] at hq
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq.1]
  have h260 := supp_empty_imp_ge26 C (w0 C q) hq.2.2.1
  have h261 := supp_empty_imp_ge26 C (w1 C q) hq.2.2.2
  have hne := w0_ne_w1 hC hq.1
  have heq : ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) =
      {w0 C q, w1 C q} := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, _⟩; exact hw
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, h260, hq.2.2.1⟩
      · exact ⟨Or.inr rfl, h261, hq.2.2.2⟩
  rw [heq, Finset.card_pair hne]

lemma cleanIn_card_Aless_le {C : Circuit} (hC : CleanHyp C) {q : ℕ} (hq : q ∈ Aless C) :
    (cleanIn C q).card ≤ 2 := by
  simp only [Aless, Finset.mem_filter, Finset.mem_range] at hq
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq.1]
  calc ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)).card
      ≤ [w0 C q, w1 C q].toFinset.card := Finset.card_filter_le _ _
    _ ≤ 2 := by simpa using Finset.card_insert_le (w0 C q) {w1 C q}

lemma cleanIn_card_eq_two_imp {C : Circuit} (hC : CleanHyp C) {q : ℕ}
    (hq : q < C.gates.length) (h2 : (cleanIn C q).card = 2) :
    supp C (w0 C q) = ∅ ∧ supp C (w1 C q) = ∅ := by
  rw [cleanIn_card_eq C q, gate_inputs_eq hC hq] at h2
  have hsub : ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) ⊆
      {w0 C q, w1 C q} := by
    intro w hw; simp at hw ⊢; exact hw.1
  have hpair : ({w0 C q, w1 C q} : Finset ℕ).card = 2 := Finset.card_pair (w0_ne_w1 hC hq)
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have h0 : w0 C q ∈ ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) := by
    rw [heq]; simp
  have h1 : w1 C q ∈ ([w0 C q, w1 C q].toFinset.filter (fun w => 26 ≤ w ∧ supp C w = ∅)) := by
    rw [heq]; simp
  exact ⟨(Finset.mem_filter.mp h0).2.2, (Finset.mem_filter.mp h1).2.2⟩

lemma cleanUsed_erase_sub_biUnion (C : Circuit) :
    (cleanGates C ∩ used C).erase (outIdx C) ⊆ (used C).biUnion (cleanIn C) := by
  intro k hk
  rw [Finset.mem_erase, Finset.mem_inter] at hk
  have hke : k ∈ (used C).erase (outIdx C) := Finset.mem_erase.mpr ⟨hk.1, hk.2.2⟩
  obtain ⟨q, hqU, hread⟩ := used_has_reader C hke
  rw [Finset.mem_biUnion]
  exact ⟨q, hqU, (mem_cleanIn C q k).mpr ⟨hread, (Finset.mem_filter.mp hk.2.1).2⟩⟩

lemma outIdx_mem_cleanUsed {C : Circuit} (hC : CleanHyp C) :
    outIdx C ∈ cleanGates C ∩ used C := by
  rw [Finset.mem_inter, cleanGates, Finset.mem_filter, Finset.mem_range]
  refine ⟨⟨outIdx_lt hC, ?_⟩, Finset.mem_insert_self _ _⟩
  rw [outIdx_add hC]
  exact supp_output hC

lemma equality_bundle {C : Circuit} (hC : CleanHyp C) :
    Mset C ∩ used C = Mset C ∧
    (Mset C).card = 13 ∧
    Aless C ∩ used C = Aless C ∧
    Oclean C ∩ used C = Oclean C ∧
    Omix C ∩ used C = Omix C ∧
    (∀ q1 ∈ used C, ∀ q2 ∈ used C, q1 ≠ q2 → Disjoint (cleanIn C q1) (cleanIn C q2)) ∧
    (∀ q ∈ Aless C, supp C (w0 C q) = ∅ ∧ supp C (w1 C q) = ∅) ∧
    (∀ j ∈ Mset C, cross C j = incEdges (ctr C j) ∧ supp C (leafWire C j) = nbr (ctr C j)) ∧
    (∀ j1 ∈ Mset C, ∀ j2 ∈ Mset C, j1 ≠ j2 → ctr C j1 ≠ ctr C j2 ∧ adjB (ctr C j1) (ctr C j2) = false) := by
  have hUsub := used_sub hC
  have hsum_slots :
      ∑ q ∈ used C, (cleanIn C q).card =
        2 * (Oclean C ∩ used C).card + (Omix C ∩ used C).card +
        ∑ q ∈ Aless C ∩ used C, (cleanIn C q).card := by
    rw [sum_partition hC (used C) hUsub (fun q => (cleanIn C q).card)]
    have hM0 : ∑ q ∈ Mset C ∩ used C, (cleanIn C q).card = 0 :=
      Finset.sum_eq_zero (fun q hq => cleanIn_card_M hC (Finset.mem_inter.mp hq).1)
    have hP0 : ∑ q ∈ Opure C ∩ used C, (cleanIn C q).card = 0 :=
      Finset.sum_eq_zero (fun q hq => cleanIn_card_Opure hC (Finset.mem_inter.mp hq).1)
    have hOC : ∑ q ∈ Oclean C ∩ used C, (cleanIn C q).card = 2 * (Oclean C ∩ used C).card := by
      calc ∑ q ∈ Oclean C ∩ used C, (cleanIn C q).card
          = ∑ _q ∈ Oclean C ∩ used C, 2 := Finset.sum_congr rfl (fun q hq =>
            cleanIn_card_Oclean hC (Finset.mem_inter.mp hq).1)
        _ = 2 * (Oclean C ∩ used C).card := by simp [mul_comm]
    have hOM : ∑ q ∈ Omix C ∩ used C, (cleanIn C q).card = (Omix C ∩ used C).card := by
      calc ∑ q ∈ Omix C ∩ used C, (cleanIn C q).card
          = ∑ _q ∈ Omix C ∩ used C, 1 := Finset.sum_congr rfl (fun q hq =>
            cleanIn_card_Omix hC (Finset.mem_inter.mp hq).1)
        _ = (Omix C ∩ used C).card := by simp
    omega
  have hAless_sum_le : ∑ q ∈ Aless C ∩ used C, (cleanIn C q).card ≤ 2 * (Aless C ∩ used C).card := by
    calc ∑ q ∈ Aless C ∩ used C, (cleanIn C q).card
        ≤ ∑ _q ∈ Aless C ∩ used C, 2 := Finset.sum_le_sum (fun q hq =>
          cleanIn_card_Aless_le hC (Finset.mem_inter.mp hq).1)
      _ = 2 * (Aless C ∩ used C).card := by simp [mul_comm]
  have hclean_erase_le_bi :
      ((cleanGates C ∩ used C).erase (outIdx C)).card ≤ ((used C).biUnion (cleanIn C)).card :=
    Finset.card_le_card (cleanUsed_erase_sub_biUnion C)
  have hbi_le_sum : ((used C).biUnion (cleanIn C)).card ≤ ∑ q ∈ used C, (cleanIn C q).card :=
    Finset.card_biUnion_le
  have herase_card : ((cleanGates C ∩ used C).erase (outIdx C)).card + 1 =
      (cleanGates C ∩ used C).card :=
    Finset.card_erase_add_one (outIdx_mem_cleanUsed hC)
  have hclean_part := clean_card_partition hC (used C)
  have hall_part : C.gates.length =
      (Mset C).card + (Aless C).card + (Oclean C).card + (Omix C).card + (Opure C).card := by
    have h := card_partition hC (Finset.range C.gates.length) Finset.Subset.rfl
    have hM : Mset C ∩ Finset.range C.gates.length = Mset C :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    have hA : Aless C ∩ Finset.range C.gates.length = Aless C :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    have hOC : Oclean C ∩ Finset.range C.gates.length = Oclean C :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    have hOM : Omix C ∩ Finset.range C.gates.length = Omix C :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    have hOP : Opure C ∩ Finset.range C.gates.length = Opure C :=
      Finset.inter_eq_left.mpr (Finset.filter_subset _ _)
    rw [Finset.card_range, hM, hA, hOC, hOM, hOP] at h
    exact h
  have hle_M : (Mset C ∩ used C).card ≤ (Mset C).card := Finset.card_le_card Finset.inter_subset_left
  have hle_A : (Aless C ∩ used C).card ≤ (Aless C).card := Finset.card_le_card Finset.inter_subset_left
  have hle_OC : (Oclean C ∩ used C).card ≤ (Oclean C).card := Finset.card_le_card Finset.inter_subset_left
  have hle_OM : (Omix C ∩ used C).card ≤ (Omix C).card := Finset.card_le_card Finset.inter_subset_left
  have h13 := thirteen_le_M_used hC
  have h52 := bound1_edges hC
  have hsize : C.gates.length ≤ 64 := hC.1
  have hM_eq_card : (Mset C ∩ used C).card = (Mset C).card := by omega
  have hM13 : (Mset C).card = 13 := by omega
  have hA_eq_card : (Aless C ∩ used C).card = (Aless C).card := by omega
  have hOC_eq_card : (Oclean C ∩ used C).card = (Oclean C).card := by omega
  have hOM_eq_card : (Omix C ∩ used C).card = (Omix C).card := by omega
  have hbi_eq_sum : ((used C).biUnion (cleanIn C)).card = ∑ q ∈ used C, (cleanIn C q).card := by omega
  have hAless_sum_eq : ∑ q ∈ Aless C ∩ used C, (cleanIn C q).card = 2 * (Aless C ∩ used C).card := by omega
  have hM_eq : Mset C ∩ used C = Mset C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hA_eq : Aless C ∩ used C = Aless C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hOC_eq : Oclean C ∩ used C = Oclean C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hOM_eq : Omix C ∩ used C = Omix C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hdisj_clean : ∀ q1 ∈ used C, ∀ q2 ∈ used C, q1 ≠ q2 →
      Disjoint (cleanIn C q1) (cleanIn C q2) :=
    disjoint_of_card_biUnion_eq_sum (used C) (cleanIn C) hbi_eq_sum
  have hAless_two : ∀ q ∈ Aless C, supp C (w0 C q) = ∅ ∧ supp C (w1 C q) = ∅ := by
    intro q hq
    have hsum2 : ∑ r ∈ Aless C, (cleanIn C r).card = ∑ _r ∈ Aless C, 2 := by
      rw [← hA_eq, hAless_sum_eq]; simp [mul_comm]
    have hq2 := eq_of_sum_eq_of_le (Aless C) (fun r => (cleanIn C r).card) (fun _ => 2)
      (fun r hr => cleanIn_card_Aless_le hC hr) hsum2 q hq
    exact cleanIn_card_eq_two_imp hC (Finset.mem_range.mp (Finset.mem_filter.mp hq).1) hq2
  have hcross_cov : pgEdges ⊆ (Mset C).biUnion (cross C) := by
    rw [← hM_eq]; exact pgEdges_covered hC
  have hcross_bi_le : ((Mset C).biUnion (cross C)).card ≤ ∑ j ∈ Mset C, (cross C j).card :=
    Finset.card_biUnion_le
  have hcross_sum_le : ∑ j ∈ Mset C, (cross C j).card ≤ ∑ _j ∈ Mset C, 4 :=
    Finset.sum_le_sum (fun j hj => cross_card_le_four hC hj)
  have hcross_sum4 : ∑ _j ∈ Mset C, 4 = 52 := by simp [hM13]
  have h52_le_bi : 52 ≤ ((Mset C).biUnion (cross C)).card := by
    rw [← pgEdges_card]; exact Finset.card_le_card hcross_cov
  have hcross_bi_eq : ((Mset C).biUnion (cross C)).card = ∑ j ∈ Mset C, (cross C j).card := by omega
  have hcross_sum_eq : ∑ j ∈ Mset C, (cross C j).card = ∑ _j ∈ Mset C, 4 := by omega
  have hcross_four : ∀ j ∈ Mset C, (cross C j).card = 4 :=
    eq_of_sum_eq_of_le (Mset C) (fun j => (cross C j).card) (fun _ => 4)
      (fun j hj => cross_card_le_four hC hj) hcross_sum_eq
  have hcross_disj : ∀ j1 ∈ Mset C, ∀ j2 ∈ Mset C, j1 ≠ j2 →
      Disjoint (cross C j1) (cross C j2) :=
    disjoint_of_card_biUnion_eq_sum (Mset C) (cross C) hcross_bi_eq
  have hM_star : ∀ j ∈ Mset C, cross C j = incEdges (ctr C j) ∧
      supp C (leafWire C j) = nbr (ctr C j) := by
    intro j hj
    have hc4 := hcross_four j hj
    have hce : cross C j = incEdges (ctr C j) :=
      Finset.eq_of_subset_of_card_le (cross_sub_incEdges hC hj)
        (by rw [incEdges_card, hc4])
    have hle := cross_card_le_leaf hC hj
    have hlf : supp C (leafWire C j) = nbr (ctr C j) :=
      Finset.eq_of_subset_of_card_le (supp_leafWire_sub_nbr hC hj)
        (by rw [nbr_card]; omega)
    exact ⟨hce, hlf⟩
  have hM_indep : ∀ j1 ∈ Mset C, ∀ j2 ∈ Mset C, j1 ≠ j2 →
      ctr C j1 ≠ ctr C j2 ∧ adjB (ctr C j1) (ctr C j2) = false := by
    intro j1 hj1 j2 hj2 hne
    have hdisj := hcross_disj j1 hj1 j2 hj2 hne
    rw [(hM_star j1 hj1).1, (hM_star j2 hj2).1] at hdisj
    constructor
    · intro heq
      rw [heq] at hdisj
      have hpos : (incEdges (ctr C j2)).Nonempty :=
        Finset.card_pos.mp (by rw [incEdges_card]; omega)
      obtain ⟨pl, hpl⟩ := hpos
      exact Finset.disjoint_left.mp hdisj hpl hpl
    · cases hadj : adjB (ctr C j1) (ctr C j2)
      · rfl
      · obtain ⟨pl, hpl⟩ := incEdges_inter_nonempty_of_adj _ _ hadj
        rw [Finset.mem_inter] at hpl
        exact absurd hpl.2 (Finset.disjoint_left.mp hdisj hpl.1)
  exact ⟨hM_eq, hM13, hA_eq, hOC_eq, hOM_eq, hdisj_clean, hAless_two, hM_star, hM_indep⟩

def cleanSub (C : Circuit) : ℕ → Finset ℕ
  | k =>
    if k < C.gates.length ∧ supp C (26 + k) = ∅ then
      insert k ((gateAt C k).inputs.toFinset.biUnion (fun w =>
        if h : 26 ≤ w ∧ w < 26 + k ∧ supp C w = ∅ then cleanSub C (w - 26) else ∅))
    else ∅
decreasing_by omega

lemma mem_cleanSub_self (C : Circuit) {k : ℕ} (hk : k ∈ cleanGates C) :
    k ∈ cleanSub C k := by
  simp only [cleanGates, Finset.mem_filter, Finset.mem_range] at hk
  rw [cleanSub]
  simp only [hk, and_self, ite_true]
  exact Finset.mem_insert_self _ _

lemma cleanSub_le (C : Circuit) (k i : ℕ) (hi : i ∈ cleanSub C k) : i ≤ k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [cleanSub] at hi
    split_ifs at hi with hk
    · rw [Finset.mem_insert] at hi
      rcases hi with rfl | hmem
      · exact le_rfl
      · rw [Finset.mem_biUnion] at hmem
        obtain ⟨w, _, hw⟩ := hmem
        split_ifs at hw with h
        · have := ih (w - 26) (by omega) hw; omega
        · exact absurd hw (Finset.notMem_empty _)
    · exact absurd hi (Finset.notMem_empty _)

lemma cleanSub_sub_clean (C : Circuit) (k i : ℕ) (hi : i ∈ cleanSub C k) :
    i ∈ cleanGates C := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [cleanSub] at hi
    split_ifs at hi with hk
    · rw [Finset.mem_insert] at hi
      rcases hi with rfl | hmem
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.1, hk.2⟩
      · rw [Finset.mem_biUnion] at hmem
        obtain ⟨w, _, hw⟩ := hmem
        split_ifs at hw with h
        · exact ih (w - 26) (by omega) hw
        · exact absurd hw (Finset.notMem_empty _)
    · exact absurd hi (Finset.notMem_empty _)

lemma cleanSub_has_M {C : Circuit} (hC : CleanHyp C)
    (hAless_two : ∀ q ∈ Aless C, supp C (w0 C q) = ∅ ∧ supp C (w1 C q) = ∅)
    (k : ℕ) (hk : k ∈ cleanGates C) :
    ∃ g ∈ Mset C, g ∈ cleanSub C k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hku := hk
    rw [cleanGates_eq_union hC, Finset.mem_union, Finset.mem_union] at hku
    rcases hku with (hM | hA) | hOC
    · exact ⟨k, hM, mem_cleanSub_self C hk⟩
    · have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hks : supp C (26 + k) = ∅ := (Finset.mem_filter.mp hk).2
      have h0s : supp C (w0 C k) = ∅ := (hAless_two k hA).1
      have h26 := supp_empty_imp_ge26 C (w0 C k) h0s
      have hlt := w0_lt hC hklt
      have hsub_cl : w0 C k - 26 ∈ cleanGates C := by
        simp only [cleanGates, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 26 + (w0 C k - 26) = w0 C k := by omega
        rw [this]; exact h0s
      obtain ⟨g, hgM, hgsub⟩ := ih (w0 C k - 26) (by omega) hsub_cl
      refine ⟨g, hgM, ?_⟩
      rw [cleanSub]
      simp only [hklt, hks, and_self, ite_true, Finset.mem_insert]
      right
      rw [Finset.mem_biUnion]
      refine ⟨w0 C k, List.mem_toFinset.mpr (by rw [gate_inputs_eq hC hklt]; simp), ?_⟩
      simp only [h26, hlt, h0s, and_self, dite_true]
      exact hgsub
    · have hklt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hks : supp C (26 + k) = ∅ := (Finset.mem_filter.mp hk).2
      have h0s : supp C (w0 C k) = ∅ := (Finset.mem_filter.mp hOC).2.2.1
      have h26 := supp_empty_imp_ge26 C (w0 C k) h0s
      have hlt := w0_lt hC hklt
      have hsub_cl : w0 C k - 26 ∈ cleanGates C := by
        simp only [cleanGates, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : 26 + (w0 C k - 26) = w0 C k := by omega
        rw [this]; exact h0s
      obtain ⟨g, hgM, hgsub⟩ := ih (w0 C k - 26) (by omega) hsub_cl
      refine ⟨g, hgM, ?_⟩
      rw [cleanSub]
      simp only [hklt, hks, and_self, ite_true, Finset.mem_insert]
      right
      rw [Finset.mem_biUnion]
      refine ⟨w0 C k, List.mem_toFinset.mpr (by rw [gate_inputs_eq hC hklt]; simp), ?_⟩
      simp only [h26, hlt, h0s, and_self, dite_true]
      exact hgsub

lemma cleanSub_has_internal_reader (C : Circuit) (a i : ℕ)
    (hi : i ∈ cleanSub C a) (hne : i ≠ a) :
    ∃ p ∈ cleanSub C a, 26 + i ∈ (gateAt C p).inputs := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    rw [cleanSub] at hi
    split_ifs at hi with ha
    · rw [Finset.mem_insert] at hi
      rcases hi with rfl | hmem
      · exact absurd rfl hne
      · rw [Finset.mem_biUnion] at hmem
        obtain ⟨w, hw, hsub⟩ := hmem
        split_ifs at hsub with h
        · by_cases hiw : i = w - 26
          · refine ⟨a, ?_, ?_⟩
            · rw [cleanSub]; simp only [ha, and_self, ite_true]; exact Finset.mem_insert_self _ _
            · have heq : 26 + i = w := by omega
              rw [heq]; exact List.mem_toFinset.mp hw
          · obtain ⟨p, hp, hread⟩ := ih (w - 26) (by omega) hsub hiw
            refine ⟨p, ?_, hread⟩
            rw [cleanSub]
            simp only [ha, and_self, ite_true, Finset.mem_insert]
            right
            rw [Finset.mem_biUnion]
            refine ⟨w, hw, ?_⟩
            simp only [h, and_self, dite_true]; exact hp
        · exact absurd hsub (Finset.notMem_empty _)
    · exact absurd hi (Finset.notMem_empty _)

lemma cleanGates_sub_used {C : Circuit} (hC : CleanHyp C) : cleanGates C ⊆ used C := by
  have ⟨hM, _, hA, hOC, _, _, _, _, _⟩ := equality_bundle hC
  intro k hk
  rw [cleanGates_eq_union hC, Finset.mem_union, Finset.mem_union] at hk
  rcases hk with (h | h) | h
  · rw [← hM] at h; exact (Finset.mem_inter.mp h).2
  · rw [← hA] at h; exact (Finset.mem_inter.mp h).2
  · rw [← hOC] at h; exact (Finset.mem_inter.mp h).2

lemma cleanSub_boundary {C : Circuit} (hC : CleanHyp C) {a q0 : ℕ}
    (hq0U : q0 ∈ used C) (ha_read : 26 + a ∈ (gateAt C q0).inputs)
    (ha_clean : a ∈ cleanGates C) :
    ∀ i ∈ cleanSub C a, ∀ q ∈ used C, 26 + i ∈ (gateAt C q).inputs →
      q ∈ cleanSub C a ∨ (i = a ∧ q = q0) := by
  have ⟨_, _, _, _, _, hdisj_clean, _, _, _⟩ := equality_bundle hC
  intro i hi q hqU hread
  have hi_cl : i ∈ cleanGates C := cleanSub_sub_clean C a i hi
  have hi_s : supp C (26 + i) = ∅ := (Finset.mem_filter.mp hi_cl).2
  have hi_in_q : i ∈ cleanIn C q := (mem_cleanIn C q i).mpr ⟨hread, hi_s⟩
  by_cases hia : i = a
  · right
    refine ⟨hia, ?_⟩
    subst hia
    have ha_in_q0 : i ∈ cleanIn C q0 := (mem_cleanIn C q0 i).mpr ⟨ha_read, hi_s⟩
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj_clean q hqU q0 hq0U hne) hi_in_q ha_in_q0
  · left
    obtain ⟨p, hp, hpread⟩ := cleanSub_has_internal_reader C a i hi hia
    have hpU : p ∈ used C := cleanGates_sub_used hC (cleanSub_sub_clean C a p hp)
    have hi_in_p : i ∈ cleanIn C p := (mem_cleanIn C p i).mpr ⟨hpread, hi_s⟩
    have hqp : q = p := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj_clean q hqU p hpU hne) hi_in_q hi_in_p
    rw [hqp]; exact hp

lemma Aless_empty {C : Circuit} (hC : CleanHyp C) : Aless C = ∅ := by
  by_contra hne
  obtain ⟨j, hjA⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have ⟨hM_eq, _, hA_eq, _, _, _, hAless_two, hM_star, hM_indep⟩ := equality_bundle hC
  have hjU : j ∈ used C := by rw [← hA_eq] at hjA; exact (Finset.mem_inter.mp hjA).2
  have hjlt : j < C.gates.length := Finset.mem_range.mp (used_sub hC hjU)
  have hjand : isAnd (gateAt C j) = true := (Finset.mem_filter.mp hjA).2.1
  have ⟨h0s, h1s⟩ := hAless_two j hjA
  have h260 := supp_empty_imp_ge26 C (w0 C j) h0s
  have h261 := supp_empty_imp_ge26 C (w1 C j) h1s
  have h0lt := w0_lt hC hjlt
  have h1lt := w1_lt hC hjlt
  set a := w0 C j - 26
  set b := w1 C j - 26
  have ha_eq : 26 + a = w0 C j := by omega
  have hb_eq : 26 + b = w1 C j := by omega
  have hab : a ≠ b := by have := w0_ne_w1 hC hjlt; omega
  have ha_cl : a ∈ cleanGates C := by
    simp only [cleanGates, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [ha_eq]; exact h0s⟩
  have hb_cl : b ∈ cleanGates C := by
    simp only [cleanGates, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [hb_eq]; exact h1s⟩
  have ha_read : 26 + a ∈ (gateAt C j).inputs := by
    rw [gate_inputs_eq hC hjlt, ha_eq]; simp
  have hb_read : 26 + b ∈ (gateAt C j).inputs := by
    rw [gate_inputs_eq hC hjlt, hb_eq]; simp
  have hbd := cleanSub_boundary hC hjU ha_read ha_cl
  obtain ⟨g1, hg1M, hg1sub⟩ := cleanSub_has_M hC hAless_two a ha_cl
  set c1 := ctr C g1
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by rw [nbr_card c1]; omega : 0 < (nbr c1).card)
  rw [mem_nbr] at hl
  set x := pair c1 l
  have hind : ∀ w : ℕ, (w < 26 ∨ w - 26 ∈ used C) →
      ((supp C w).Nonempty → val C x w = true → c1 ∈ supp C w ∨ l ∈ supp C w) ∧
      (∀ k : ℕ, w = 26 + k → k ∈ cleanGates C → k ∉ cleanSub C a → val C x w = false) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwu
      constructor
      · intro hsupp hval
        by_cases hw26 : w < 26
        · have heq : supp C w = {⟨w, hw26⟩} := by
            change supp C (⟨w, hw26⟩ : Fin 26).val = _; exact supp_input C ⟨w, hw26⟩
          have hxw : x ⟨w, hw26⟩ = true := (val_input C x ⟨w, hw26⟩).symm.trans hval
          simp only [x, pair, decide_eq_true_eq] at hxw
          rw [heq]
          rcases hxw with h1 | h2
          · exact Or.inl (by rw [h1]; exact Finset.mem_singleton_self _)
          · exact Or.inr (by rw [h2]; exact Finset.mem_singleton_self _)
        · have hkU : w - 26 ∈ used C := hwu.resolve_left hw26
          set k := w - 26
          have hwk : w = 26 + k := by omega
          have hklt : k < C.gates.length := Finset.mem_range.mp (used_sub hC hkU)
          rw [hwk] at hsupp hval ⊢
          rcases gate_op_cases hC hklt with hand | hor
          · rw [supp_and hC hand] at hsupp
            exact absurd hsupp Finset.not_nonempty_empty
          · rw [val_or hC x hklt hor, Bool.or_eq_true] at hval
            rw [supp_or hC hklt hor]
            have h0u : w0 C k < 26 ∨ w0 C k - 26 ∈ used C := by
              by_cases hlt : w0 C k < 26
              · exact Or.inl hlt
              · exact Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) (by omega))
            have h1u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C := by
              by_cases hlt : w1 C k < 26
              · exact Or.inl hlt
              · exact Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) (by omega))
            have hnot_sub : k ∉ cleanSub C a := by
              intro hmem
              have := (Finset.mem_filter.mp (cleanSub_sub_clean C a k hmem)).2
              rw [this] at hsupp; exact Finset.not_nonempty_empty hsupp
            have hkj : k ≠ j := by
              intro heq; subst heq; exact isAnd_and_isOr_false _ ⟨hjand, hor⟩
            rcases hval with hv0 | hv1
            · by_cases hs0 : supp C (w0 C k) = ∅
              · have h26 := supp_empty_imp_ge26 C (w0 C k) hs0
                have hlt := w0_lt hC hklt
                set i0 := w0 C k - 26
                have hi0_eq : 26 + i0 = w0 C k := by omega
                have hi0_cl : i0 ∈ cleanGates C :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi0_eq]; exact hs0⟩
                have hi0_not : i0 ∉ cleanSub C a := by
                  intro hmem
                  have hread : 26 + i0 ∈ (gateAt C k).inputs := by
                    rw [gate_inputs_eq hC hklt, hi0_eq]; simp
                  rcases hbd i0 hmem k hkU hread with hksub | ⟨_, hEq⟩
                  · exact hnot_sub hksub
                  · exact hkj hEq
                have hf := (ih (w0 C k) (by omega) h0u).2 i0 hi0_eq.symm hi0_cl hi0_not
                rw [hf] at hv0; exact absurd hv0 Bool.false_ne_true
              · have hrec := (ih (w0 C k) (by have := w0_lt hC hklt; omega) h0u).1
                  (Finset.nonempty_iff_ne_empty.mpr hs0) hv0
                rcases hrec with hc | hl'
                · exact Or.inl (Finset.mem_union_left _ hc)
                · exact Or.inr (Finset.mem_union_left _ hl')
            · by_cases hs1 : supp C (w1 C k) = ∅
              · have h26 := supp_empty_imp_ge26 C (w1 C k) hs1
                have hlt := w1_lt hC hklt
                set i1 := w1 C k - 26
                have hi1_eq : 26 + i1 = w1 C k := by omega
                have hi1_cl : i1 ∈ cleanGates C :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi1_eq]; exact hs1⟩
                have hi1_not : i1 ∉ cleanSub C a := by
                  intro hmem
                  have hread : 26 + i1 ∈ (gateAt C k).inputs := by
                    rw [gate_inputs_eq hC hklt, hi1_eq]; simp
                  rcases hbd i1 hmem k hkU hread with hksub | ⟨_, hEq⟩
                  · exact hnot_sub hksub
                  · exact hkj hEq
                have hf := (ih (w1 C k) (by omega) h1u).2 i1 hi1_eq.symm hi1_cl hi1_not
                rw [hf] at hv1; exact absurd hv1 Bool.false_ne_true
              · have hrec := (ih (w1 C k) (by have := w1_lt hC hklt; omega) h1u).1
                  (Finset.nonempty_iff_ne_empty.mpr hs1) hv1
                rcases hrec with hc | hl'
                · exact Or.inl (Finset.mem_union_right _ hc)
                · exact Or.inr (Finset.mem_union_right _ hl')
      · intro k hwk hk_cl hk_not
        subst hwk
        have hkU : k ∈ used C := cleanGates_sub_used hC hk_cl
        have hklt : k < C.gates.length := Finset.mem_range.mp (used_sub hC hkU)
        have hku := hk_cl
        rw [cleanGates_eq_union hC, Finset.mem_union, Finset.mem_union] at hku
        rcases hku with (hkM | hkA) | hkOC
        · have hkg1 : k ≠ g1 := fun heq => hk_not (heq ▸ hg1sub)
          have hck_ne_c1 : ctr C k ≠ c1 := (hM_indep k hkM g1 hg1M hkg1).1
          have hck_ne_l : ctr C k ≠ l := by
            intro heq
            have hadj := (hM_indep g1 hg1M k hkM hkg1.symm).2
            rw [heq] at hadj
            rw [hadj] at hl
            exact Bool.false_ne_true hl
          have hcw_lt : ctrWire C k < 26 + k := by
            unfold ctrWire; split_ifs; exact w0_lt hC hklt; exact w1_lt hC hklt
          have hcw_in : ctrWire C k ∈ (gateAt C k).inputs := by
            rw [gate_inputs_eq hC hklt]; unfold ctrWire; split_ifs <;> simp
          have hcw_u : ctrWire C k < 26 ∨ ctrWire C k - 26 ∈ used C := by
            by_cases hlt : ctrWire C k < 26
            · exact Or.inl hlt
            · exact Or.inr (used_closed hC hkU hcw_in (by omega))
          have hcw_s : supp C (ctrWire C k) = {ctr C k} := supp_ctrWire_eq hC hkM
          have hcw_false : val C x (ctrWire C k) = false := by
            cases hcv : val C x (ctrWire C k)
            · rfl
            · have hrec := (ih (ctrWire C k) hcw_lt hcw_u).1
                (by rw [hcw_s]; exact Finset.singleton_nonempty _) hcv
              rw [hcw_s, Finset.mem_singleton, Finset.mem_singleton] at hrec
              rcases hrec with h1 | h2
              · exact absurd h1.symm hck_ne_c1
              · exact absurd h2.symm hck_ne_l
          have hkand : isAnd (gateAt C k) = true := (Finset.mem_filter.mp hkM).2.1
          rw [val_and hC x hklt hkand]
          unfold ctrWire at hcw_false
          split_ifs at hcw_false
          · rw [hcw_false]; rfl
          · rw [hcw_false]; simp
        · have hkand : isAnd (gateAt C k) = true := (Finset.mem_filter.mp hkA).2.1
          have ⟨h0sk, h1sk⟩ := hAless_two k hkA
          have h261k := supp_empty_imp_ge26 C (w1 C k) h1sk
          have h1ltk := w1_lt hC hklt
          set i1 := w1 C k - 26
          have hi1_eq : 26 + i1 = w1 C k := by omega
          have hi1_cl : i1 ∈ cleanGates C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi1_eq]; exact h1sk⟩
          have hi1_read : 26 + i1 ∈ (gateAt C k).inputs := by
            rw [gate_inputs_eq hC hklt, hi1_eq]; simp
          have hi1_u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C :=
            Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) h261k)
          have hi1_not : i1 ∉ cleanSub C a := by
            intro hmem
            rcases hbd i1 hmem k hkU hi1_read with hksub | ⟨hEqA, hEqJ⟩
            · exact hk_not hksub
            · subst hEqJ
              exact hab hEqA.symm
          have hf1 := (ih (w1 C k) h1ltk hi1_u).2 i1 hi1_eq.symm hi1_cl hi1_not
          rw [val_and hC x hklt hkand, hf1]; simp
        · have hkor : isOr (gateAt C k) = true := (Finset.mem_filter.mp hkOC).2.1
          have h0sk : supp C (w0 C k) = ∅ := (Finset.mem_filter.mp hkOC).2.2.1
          have h1sk : supp C (w1 C k) = ∅ := (Finset.mem_filter.mp hkOC).2.2.2
          have hkj : k ≠ j := fun heq => isAnd_and_isOr_false _ ⟨hjand, heq ▸ hkor⟩
          have h260k := supp_empty_imp_ge26 C (w0 C k) h0sk
          have h261k := supp_empty_imp_ge26 C (w1 C k) h1sk
          have h0ltk := w0_lt hC hklt
          have h1ltk := w1_lt hC hklt
          set i0 := w0 C k - 26
          set i1 := w1 C k - 26
          have hi0_eq : 26 + i0 = w0 C k := by omega
          have hi1_eq : 26 + i1 = w1 C k := by omega
          have hi0_cl : i0 ∈ cleanGates C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi0_eq]; exact h0sk⟩
          have hi1_cl : i1 ∈ cleanGates C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi1_eq]; exact h1sk⟩
          have hi0_not : i0 ∉ cleanSub C a := by
            intro hmem
            have hread : 26 + i0 ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt, hi0_eq]; simp
            rcases hbd i0 hmem k hkU hread with hksub | ⟨_, hEqJ⟩
            · exact hk_not hksub
            · exact hkj hEqJ
          have hi1_not : i1 ∉ cleanSub C a := by
            intro hmem
            have hread : 26 + i1 ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt, hi1_eq]; simp
            rcases hbd i1 hmem k hkU hread with hksub | ⟨_, hEqJ⟩
            · exact hk_not hksub
            · exact hkj hEqJ
          have hi0_u : w0 C k < 26 ∨ w0 C k - 26 ∈ used C :=
            Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) h260k)
          have hi1_u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C :=
            Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) h261k)
          have hf0 := (ih (w0 C k) h0ltk hi0_u).2 i0 hi0_eq.symm hi0_cl hi0_not
          have hf1 := (ih (w1 C k) h1ltk hi1_u).2 i1 hi1_eq.symm hi1_cl hi1_not
          rw [val_or hC x hklt hkor, hf0, hf1]; rfl
  have hout_not : outIdx C ∉ cleanSub C a := by
    intro hmem
    have h1 := cleanSub_le C a (outIdx C) hmem
    have h2 := used_le_out C hjU
    omega
  have hout_u : 26 + outIdx C < 26 ∨ (26 + outIdx C) - 26 ∈ used C := by
    right; simp [used]
  have hout_cl : outIdx C ∈ cleanGates C := (Finset.mem_inter.mp (outIdx_mem_cleanUsed hC)).1
  have hf := (hind (26 + outIdx C) hout_u).2 (outIdx C) rfl hout_cl hout_not
  rw [outIdx_add hC] at hf
  have ht : val C x C.output = true := (hC.2.2.2.1 x).mpr ((F_pair_iff c1 l).mpr hl)
  rw [hf] at ht
  exact Bool.false_ne_true ht

lemma Omix_empty {C : Circuit} (hC : CleanHyp C) : Omix C = ∅ := by
  by_contra hne
  obtain ⟨m, hmO⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hAless0 := Aless_empty hC
  have ⟨hM_eq, _, _, _, hOM_eq, _, hAless_two, hM_star, hM_indep⟩ := equality_bundle hC
  have hmU : m ∈ used C := by rw [← hOM_eq] at hmO; exact (Finset.mem_inter.mp hmO).2
  have hmlt : m < C.gates.length := Finset.mem_range.mp (used_sub hC hmU)
  have hmor : isOr (gateAt C m) = true := (Finset.mem_filter.mp hmO).2.1
  have ha_ex : ∃ a : ℕ, a < m ∧ a ∈ cleanGates C ∧ 26 + a ∈ (gateAt C m).inputs ∧
      (supp C (26 + m)).Nonempty := by
    have hmix := (Finset.mem_filter.mp hmO).2.2
    rcases hmix with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have h26 := supp_empty_imp_ge26 C (w0 C m) h0
      have hlt := w0_lt hC hmlt
      have heq0 : 26 + (w0 C m - 26) = w0 C m := by omega
      refine ⟨w0 C m - 26, by omega,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [heq0]; exact h0⟩,
        by rw [gate_inputs_eq hC hmlt, heq0]; simp,
        by rw [supp_or hC hmlt hmor, h0, Finset.empty_union]; exact h1⟩
    · have h26 := supp_empty_imp_ge26 C (w1 C m) h1
      have hlt := w1_lt hC hmlt
      have heq1 : 26 + (w1 C m - 26) = w1 C m := by omega
      refine ⟨w1 C m - 26, by omega,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [heq1]; exact h1⟩,
        by rw [gate_inputs_eq hC hmlt, heq1]; simp,
        by rw [supp_or hC hmlt hmor, h1, Finset.union_empty]; exact h0⟩
  obtain ⟨a, ham, ha_cl, ha_read, hsm_ne⟩ := ha_ex
  have hbd := cleanSub_boundary hC hmU ha_read ha_cl
  obtain ⟨g1, hg1M, hg1sub⟩ := cleanSub_has_M hC hAless_two a ha_cl
  set c1 := ctr C g1
  have hl_ex : ∃ l : Fin 26, adjB c1 l = true ∧
      ∀ k ∈ Mset C, k ≠ g1 → supp C (26 + m) = {ctr C k} → adjB (ctr C k) l = false := by
    by_cases hcase : ∃ k ∈ Mset C, k ≠ g1 ∧ supp C (26 + m) = {ctr C k}
    · obtain ⟨k0, hk0M, hk0ne, hsm0⟩ := hcase
      have hc2ne : ctr C k0 ≠ c1 := (hM_indep k0 hk0M g1 hg1M hk0ne).1
      have hpos : 0 < (nbr c1 \ nbr (ctr C k0)).card := by
        have h1 := nbr_card c1
        have h2 := c4_free c1 (ctr C k0) hc2ne.symm
        have h3 := Finset.card_sdiff_add_card_inter (nbr c1) (nbr (ctr C k0))
        omega
      obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_sdiff, mem_nbr, mem_nbr] at hl
      refine ⟨l, hl.1, ?_⟩
      intro k _ _ hsmk
      have hce : ctr C k = ctr C k0 := by
        have hmem : ctr C k ∈ ({ctr C k0} : Finset (Fin 26)) := by
          rw [← hsm0, hsmk]; exact Finset.mem_singleton_self _
        exact Finset.mem_singleton.mp hmem
      rw [hce]
      cases hadj : adjB (ctr C k0) l
      · rfl
      · exact absurd hadj hl.2
    · obtain ⟨l, hl⟩ := Finset.card_pos.mp (by rw [nbr_card c1]; omega : 0 < (nbr c1).card)
      rw [mem_nbr] at hl
      refine ⟨l, hl, ?_⟩
      intro k hkM hkne hsmk
      exact absurd ⟨k, hkM, hkne, hsmk⟩ hcase
  obtain ⟨l, hl, hl_avoid⟩ := hl_ex
  set x := pair c1 l
  have hind : ∀ w : ℕ, (w < 26 ∨ w - 26 ∈ used C) →
      ((supp C w).Nonempty → val C x w = true →
        c1 ∈ supp C w ∨ l ∈ supp C w ∨ supp C (26 + m) ⊆ supp C w) ∧
      (∀ k : ℕ, w = 26 + k → k ∈ cleanGates C → k ∉ cleanSub C a → val C x w = false) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwu
      constructor
      · intro hsupp hval
        by_cases hw26 : w < 26
        · have heq : supp C w = {⟨w, hw26⟩} := by
            change supp C (⟨w, hw26⟩ : Fin 26).val = _; exact supp_input C ⟨w, hw26⟩
          have hxw : x ⟨w, hw26⟩ = true := (val_input C x ⟨w, hw26⟩).symm.trans hval
          simp only [x, pair, decide_eq_true_eq] at hxw
          rw [heq]
          rcases hxw with h1 | h2
          · exact Or.inl (by rw [h1]; exact Finset.mem_singleton_self _)
          · exact Or.inr (Or.inl (by rw [h2]; exact Finset.mem_singleton_self _))
        · have hkU : w - 26 ∈ used C := hwu.resolve_left hw26
          set k := w - 26
          have hwk : w = 26 + k := by omega
          have hklt : k < C.gates.length := Finset.mem_range.mp (used_sub hC hkU)
          rw [hwk] at hsupp hval ⊢
          by_cases hkm : k = m
          · subst hkm; exact Or.inr (Or.inr Finset.Subset.rfl)
          · rcases gate_op_cases hC hklt with hand | hor
            · rw [supp_and hC hand] at hsupp
              exact absurd hsupp Finset.not_nonempty_empty
            · rw [val_or hC x hklt hor, Bool.or_eq_true] at hval
              rw [supp_or hC hklt hor]
              have h0u : w0 C k < 26 ∨ w0 C k - 26 ∈ used C := by
                by_cases hlt : w0 C k < 26
                · exact Or.inl hlt
                · exact Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) (by omega))
              have h1u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C := by
                by_cases hlt : w1 C k < 26
                · exact Or.inl hlt
                · exact Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) (by omega))
              have hnot_sub : k ∉ cleanSub C a := by
                intro hmem
                have := (Finset.mem_filter.mp (cleanSub_sub_clean C a k hmem)).2
                rw [this] at hsupp; exact Finset.not_nonempty_empty hsupp
              rcases hval with hv0 | hv1
              · by_cases hs0 : supp C (w0 C k) = ∅
                · have h26 := supp_empty_imp_ge26 C (w0 C k) hs0
                  have hlt := w0_lt hC hklt
                  set i0 := w0 C k - 26
                  have hi0_eq : 26 + i0 = w0 C k := by omega
                  have hi0_cl : i0 ∈ cleanGates C :=
                    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi0_eq]; exact hs0⟩
                  have hi0_not : i0 ∉ cleanSub C a := by
                    intro hmem
                    have hread : 26 + i0 ∈ (gateAt C k).inputs := by
                      rw [gate_inputs_eq hC hklt, hi0_eq]; simp
                    rcases hbd i0 hmem k hkU hread with hksub | ⟨_, hEq⟩
                    · exact hnot_sub hksub
                    · exact hkm hEq
                  have hf := (ih (w0 C k) (by omega) h0u).2 i0 hi0_eq.symm hi0_cl hi0_not
                  rw [hf] at hv0; exact absurd hv0 Bool.false_ne_true
                · have hrec := (ih (w0 C k) (by have := w0_lt hC hklt; omega) h0u).1
                    (Finset.nonempty_iff_ne_empty.mpr hs0) hv0
                  rcases hrec with hc | hl' | hsubm
                  · exact Or.inl (Finset.mem_union_left _ hc)
                  · exact Or.inr (Or.inl (Finset.mem_union_left _ hl'))
                  · exact Or.inr (Or.inr (Finset.Subset.trans hsubm Finset.subset_union_left))
              · by_cases hs1 : supp C (w1 C k) = ∅
                · have h26 := supp_empty_imp_ge26 C (w1 C k) hs1
                  have hlt := w1_lt hC hklt
                  set i1 := w1 C k - 26
                  have hi1_eq : 26 + i1 = w1 C k := by omega
                  have hi1_cl : i1 ∈ cleanGates C :=
                    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi1_eq]; exact hs1⟩
                  have hi1_not : i1 ∉ cleanSub C a := by
                    intro hmem
                    have hread : 26 + i1 ∈ (gateAt C k).inputs := by
                      rw [gate_inputs_eq hC hklt, hi1_eq]; simp
                    rcases hbd i1 hmem k hkU hread with hksub | ⟨_, hEq⟩
                    · exact hnot_sub hksub
                    · exact hkm hEq
                  have hf := (ih (w1 C k) (by omega) h1u).2 i1 hi1_eq.symm hi1_cl hi1_not
                  rw [hf] at hv1; exact absurd hv1 Bool.false_ne_true
                · have hrec := (ih (w1 C k) (by have := w1_lt hC hklt; omega) h1u).1
                    (Finset.nonempty_iff_ne_empty.mpr hs1) hv1
                  rcases hrec with hc | hl' | hsubm
                  · exact Or.inl (Finset.mem_union_right _ hc)
                  · exact Or.inr (Or.inl (Finset.mem_union_right _ hl'))
                  · exact Or.inr (Or.inr (Finset.Subset.trans hsubm Finset.subset_union_right))
      · intro k hwk hk_cl hk_not
        subst hwk
        have hkU : k ∈ used C := cleanGates_sub_used hC hk_cl
        have hklt : k < C.gates.length := Finset.mem_range.mp (used_sub hC hkU)
        have hku := hk_cl
        rw [cleanGates_eq_union hC, Finset.mem_union, Finset.mem_union] at hku
        rcases hku with (hkM | hkA) | hkOC
        · have hkg1 : k ≠ g1 := fun heq => hk_not (heq ▸ hg1sub)
          have hck_ne_c1 : ctr C k ≠ c1 := (hM_indep k hkM g1 hg1M hkg1).1
          have hck_ne_l : ctr C k ≠ l := by
            intro heq
            have hadj := (hM_indep g1 hg1M k hkM hkg1.symm).2
            rw [heq] at hadj
            rw [hadj] at hl
            exact Bool.false_ne_true hl
          have hkand : isAnd (gateAt C k) = true := (Finset.mem_filter.mp hkM).2.1
          cases hkv : val C x (26 + k)
          · rfl
          · exfalso
            rw [val_and hC x hklt hkand, Bool.and_eq_true] at hkv
            have hcw_v : val C x (ctrWire C k) = true := by
              unfold ctrWire; split_ifs; exact hkv.1; exact hkv.2
            have hlw_v : val C x (leafWire C k) = true := by
              unfold leafWire; split_ifs; exact hkv.2; exact hkv.1
            have hcw_lt : ctrWire C k < 26 + k := by
              unfold ctrWire; split_ifs; exact w0_lt hC hklt; exact w1_lt hC hklt
            have hlw_lt : leafWire C k < 26 + k := by
              unfold leafWire; split_ifs; exact w1_lt hC hklt; exact w0_lt hC hklt
            have hcw_in : ctrWire C k ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt]; unfold ctrWire; split_ifs <;> simp
            have hlw_in : leafWire C k ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt]; unfold leafWire; split_ifs <;> simp
            have hcw_u : ctrWire C k < 26 ∨ ctrWire C k - 26 ∈ used C := by
              by_cases hlt : ctrWire C k < 26
              · exact Or.inl hlt
              · exact Or.inr (used_closed hC hkU hcw_in (by omega))
            have hlw_u : leafWire C k < 26 ∨ leafWire C k - 26 ∈ used C := by
              by_cases hlt : leafWire C k < 26
              · exact Or.inl hlt
              · exact Or.inr (used_closed hC hkU hlw_in (by omega))
            have hcw_s : supp C (ctrWire C k) = {ctr C k} := supp_ctrWire_eq hC hkM
            have hlw_s : supp C (leafWire C k) = nbr (ctr C k) := (hM_star k hkM).2
            have hrec_c := (ih (ctrWire C k) hcw_lt hcw_u).1
              (by rw [hcw_s]; exact Finset.singleton_nonempty _) hcw_v
            rw [hcw_s, Finset.mem_singleton, Finset.mem_singleton] at hrec_c
            have hsub_ck : supp C (26 + m) ⊆ {ctr C k} := by
              rcases hrec_c with h1 | h2 | h3
              · exact absurd h1.symm hck_ne_c1
              · exact absurd h2.symm hck_ne_l
              · exact h3
            have hsm_eq : supp C (26 + m) = {ctr C k} :=
              Finset.eq_of_subset_of_card_le hsub_ck
                (by have := Finset.card_pos.mpr hsm_ne; simp; omega)
            have hl_not : adjB (ctr C k) l = false := hl_avoid k hkM hkg1 hsm_eq
            have hlw_ne : (supp C (leafWire C k)).Nonempty := by
              rw [hlw_s]; exact Finset.card_pos.mp (by rw [nbr_card]; omega)
            have hrec_l := (ih (leafWire C k) hlw_lt hlw_u).1 hlw_ne hlw_v
            rw [hlw_s, mem_nbr, mem_nbr] at hrec_l
            rcases hrec_l with hc1n | hln | hsmn
            · have := (hM_indep k hkM g1 hg1M hkg1).2
              rw [this] at hc1n; exact Bool.false_ne_true hc1n
            · rw [hl_not] at hln; exact Bool.false_ne_true hln
            · have hself : ctr C k ∈ nbr (ctr C k) :=
                hsmn (by rw [hsm_eq]; exact Finset.mem_singleton_self _)
              rw [mem_nbr, adjB_irrefl] at hself
              exact Bool.false_ne_true hself
        · rw [hAless0] at hkA; exact absurd hkA (Finset.notMem_empty _)
        · have hkor : isOr (gateAt C k) = true := (Finset.mem_filter.mp hkOC).2.1
          have h0sk : supp C (w0 C k) = ∅ := (Finset.mem_filter.mp hkOC).2.2.1
          have h1sk : supp C (w1 C k) = ∅ := (Finset.mem_filter.mp hkOC).2.2.2
          have hkm : k ≠ m := by
            intro heq; subst heq
            have : supp C (26 + k) = ∅ := (Finset.mem_filter.mp hk_cl).2
            rw [this] at hsm_ne; exact Finset.not_nonempty_empty hsm_ne
          have h260k := supp_empty_imp_ge26 C (w0 C k) h0sk
          have h261k := supp_empty_imp_ge26 C (w1 C k) h1sk
          have h0ltk := w0_lt hC hklt
          have h1ltk := w1_lt hC hklt
          set i0 := w0 C k - 26
          set i1 := w1 C k - 26
          have hi0_eq : 26 + i0 = w0 C k := by omega
          have hi1_eq : 26 + i1 = w1 C k := by omega
          have hi0_cl : i0 ∈ cleanGates C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi0_eq]; exact h0sk⟩
          have hi1_cl : i1 ∈ cleanGates C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hi1_eq]; exact h1sk⟩
          have hi0_not : i0 ∉ cleanSub C a := by
            intro hmem
            have hread : 26 + i0 ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt, hi0_eq]; simp
            rcases hbd i0 hmem k hkU hread with hksub | ⟨_, hEqM⟩
            · exact hk_not hksub
            · exact hkm hEqM
          have hi1_not : i1 ∉ cleanSub C a := by
            intro hmem
            have hread : 26 + i1 ∈ (gateAt C k).inputs := by
              rw [gate_inputs_eq hC hklt, hi1_eq]; simp
            rcases hbd i1 hmem k hkU hread with hksub | ⟨_, hEqM⟩
            · exact hk_not hksub
            · exact hkm hEqM
          have hi0_u : w0 C k < 26 ∨ w0 C k - 26 ∈ used C :=
            Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) h260k)
          have hi1_u : w1 C k < 26 ∨ w1 C k - 26 ∈ used C :=
            Or.inr (used_closed hC hkU (by rw [gate_inputs_eq hC hklt]; simp) h261k)
          have hf0 := (ih (w0 C k) h0ltk hi0_u).2 i0 hi0_eq.symm hi0_cl hi0_not
          have hf1 := (ih (w1 C k) h1ltk hi1_u).2 i1 hi1_eq.symm hi1_cl hi1_not
          rw [val_or hC x hklt hkor, hf0, hf1]; rfl
  have hout_not : outIdx C ∉ cleanSub C a := by
    intro hmem
    have h1 := cleanSub_le C a (outIdx C) hmem
    have h2 := used_le_out C hmU
    omega
  have hout_u : 26 + outIdx C < 26 ∨ (26 + outIdx C) - 26 ∈ used C := by
    right; simp [used]
  have hout_cl : outIdx C ∈ cleanGates C := (Finset.mem_inter.mp (outIdx_mem_cleanUsed hC)).1
  have hf := (hind (26 + outIdx C) hout_u).2 (outIdx C) rfl hout_cl hout_not
  rw [outIdx_add hC] at hf
  have ht : val C x C.output = true := (hC.2.2.2.1 x).mpr ((F_pair_iff c1 l).mpr hl)
  rw [hf] at ht
  exact Bool.false_ne_true ht

lemma val_unclean_imp_supp {C : Circuit} (hC : CleanHyp C) (x : Fin 26 → Bool) :
    ∀ w : ℕ, (supp C w).Nonempty → val C x w = true → ∃ v ∈ supp C w, x v = true := by
  have hOmix0 := Omix_empty hC
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hne hval
    by_cases hw26 : w < 26
    · refine ⟨⟨w, hw26⟩, ?_, (val_input C x ⟨w, hw26⟩).symm.trans hval⟩
      change (⟨w, hw26⟩ : Fin 26) ∈ supp C (⟨w, hw26⟩ : Fin 26).val
      rw [supp_input]; exact Finset.mem_singleton_self _
    · by_cases hlen : w < 26 + C.gates.length
      · set k := w - 26
        have hklt : k < C.gates.length := by omega
        have hwk : w = 26 + k := by omega
        rw [hwk] at hne hval ⊢
        rcases gate_op_cases hC hklt with hand | hor
        · rw [supp_and hC hand] at hne
          exact absurd hne Finset.not_nonempty_empty
        · have hs0_ne : (supp C (w0 C k)).Nonempty := by
            by_contra h0
            rw [Finset.not_nonempty_iff_eq_empty] at h0
            have h1 : (supp C (w1 C k)).Nonempty := by
              rw [supp_or hC hklt hor, h0, Finset.empty_union] at hne; exact hne
            have hkOmix : k ∈ Omix C :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, hor, Or.inl ⟨h0, h1⟩⟩
            rw [hOmix0] at hkOmix; exact Finset.notMem_empty k hkOmix
          have hs1_ne : (supp C (w1 C k)).Nonempty := by
            by_contra h1
            rw [Finset.not_nonempty_iff_eq_empty] at h1
            have hkOmix : k ∈ Omix C :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, hor, Or.inr ⟨hs0_ne, h1⟩⟩
            rw [hOmix0] at hkOmix; exact Finset.notMem_empty k hkOmix
          rw [val_or hC x hklt hor, Bool.or_eq_true] at hval
          rw [supp_or hC hklt hor]
          rcases hval with h0 | h1
          · obtain ⟨v, hv, hxv⟩ := ih (w0 C k) (by have := w0_lt hC hklt; omega) hs0_ne h0
            exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
          · obtain ⟨v, hv, hxv⟩ := ih (w1 C k) (by have := w1_lt hC hklt; omega) hs1_ne h1
            exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
      · rw [supp_ge_len C w (by omega)] at hne
        exact absurd hne Finset.not_nonempty_empty

lemma main_contradiction {C : Circuit} (hC : CleanHyp C)
    (u v : Fin 26) (j a b : ℕ)
    (hj : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩)
    (hfire : val C (pair u v) (26 + j) = true)
    (hnotv : ¬ ((val C (one v) a || val C (one v) b) = true)) : False := by
  have hjlt : j < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hj
    exact absurd hj (by simp)
  have hgate : gateAt C j = ⟨GateOp.and, [a, b]⟩ := by
    have h1 := gates_getElem?_eq_some_gateAt C hjlt
    rw [hj] at h1
    exact Option.some.inj h1.symm
  have hjand : isAnd (gateAt C j) = true := by rw [hgate]; rfl
  have ha_eq : w0 C j = a := by simp [w0, hgate]
  have hb_eq : w1 C j = b := by simp [w1, hgate]
  have hAless0 := Aless_empty hC
  have ha_ne : (supp C a).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have hjA : j ∈ Aless C :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjand, Or.inl (by rw [ha_eq]; exact h0)⟩
    rw [hAless0] at hjA; exact Finset.notMem_empty j hjA
  have hb_ne : (supp C b).Nonempty := by
    by_contra h1
    rw [Finset.not_nonempty_iff_eq_empty] at h1
    have hjA : j ∈ Aless C :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hjand, Or.inr (by rw [hb_eq]; exact h1)⟩
    rw [hAless0] at hjA; exact Finset.notMem_empty j hjA
  rw [val_and hC (pair u v) hjlt hjand, ha_eq, hb_eq, Bool.and_eq_true] at hfire
  obtain ⟨t1, ht1, hxt1⟩ := val_unclean_imp_supp hC (pair u v) a ha_ne hfire.1
  obtain ⟨t2, ht2, hxt2⟩ := val_unclean_imp_supp hC (pair u v) b hb_ne hfire.2
  simp only [pair, decide_eq_true_eq] at hxt1 hxt2
  have hv_notin_a : v ∉ supp C a := by
    intro hv
    apply hnotv
    rw [Bool.or_eq_true]
    exact Or.inl ((mem_supp C a v).mp hv)
  have hv_notin_b : v ∉ supp C b := by
    intro hv
    apply hnotv
    rw [Bool.or_eq_true]
    exact Or.inr ((mem_supp C b v).mp hv)
  have ht1u : t1 = u := by
    rcases hxt1 with h | h
    · exact h
    · subst h; exact absurd ht1 hv_notin_a
  have ht2u : t2 = u := by
    rcases hxt2 with h | h
    · exact h
    · subst h; exact absurd ht2 hv_notin_b
  subst ht1u; subst ht2u
  have hadj := and_supp_adj hC hjlt hjand (by rw [ha_eq]; exact ht1) (by rw [hb_eq]; exact ht2)
  rw [adjB_irrefl] at hadj
  exact Bool.false_ne_true hadj

end PEqualNP.Outside.L_meta_2615

theorem PEqualNP.Outside.L_meta_2615 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → x5.inputs.Nodup) →         have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ));         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x1.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x5 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin (26 : ℕ) → Bool), x6 x10 ((26 : ℕ) + x8) = Bool.true → x6 x10 x1.output = Bool.true) →             ∀ (x9 x10 : Fin (13 : ℕ)),               x5 x9 x10 →                 have x12 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.castAdd (13 : ℕ) x9;                 have x13 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.natAdd (13 : ℕ) x10;                 have x14 : ℕ → ℕ → ℕ → Prop := fun (x14 x15 x16 : ℕ) => x1.gates[x14]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x15, x16] : PEqualNP.CircuitLowerBounds.Gate } ∧ x6 (fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x12 ∨ x17 = x13)) ((26 : ℕ) + x14) = Bool.true;                 have x15 : Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x15 : Fin (26 : ℕ)) (x16 x17 : ℕ) => (x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x16 || x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x17) = Bool.true;                 ∀ (x16 x17 x18 x19 x20 x21 : ℕ), x14 x16 x17 x18 → x14 x19 x20 x21 → x15 x12 x17 x18 → ¬x15 x13 x17 x18 → x15 x13 x20 x21 → x15 x12 x20 x21 := by
  intro x1 hsize hao2 hnodup x5 x6 hcomp hclean x9 x10 _ x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 h14a _ _ hnot _
  have hC : PEqualNP.Outside.L_meta_2615.CleanHyp x1 :=
    ⟨hsize, hao2, hnodup, hcomp, hclean⟩
  exact False.elim (PEqualNP.Outside.L_meta_2615.main_contradiction hC
    (Fin.castAdd 13 x9) (Fin.natAdd 13 x10) x16 x17 x18 h14a.1 h14a.2 hnot)
