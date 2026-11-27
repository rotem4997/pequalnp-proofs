import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5801


open PEqualNP.CircuitLowerBounds

def gm (g : Gate) (w : List (BitVec 58)) : BitVec 58 :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => w.getD i 0).foldr (fun a b => a &&& b) (-1)
  | GateOp.or => (g.inputs.map fun i => w.getD i 0).foldr (fun a b => a ||| b) 0
  | _ => 0

def mw (gs : List Gate) (W : List (BitVec 58)) : List (BitVec 58) :=
  gs.foldl (fun w g => w ++ [gm g w]) W

def Ok (L : List (BitVec 58)) (m : BitVec 58) : Prop := m = 0 ∨ m = -1 ∨ m ∈ L

def P (base x10 : List (BitVec 58)) : Prop :=
  ∀ (i : ℕ) (h : i < x10.length), x10[i] ∉ base ++ x10.take i ∧ x10[i] ≠ 0 ∧ x10[i] ≠ -1 ∧
    ∃ x13 ∈ base ++ x10.take i, ∃ x14 ∈ base ++ x10.take i,
      x10[i] = x13 &&& x14 ∨ x10[i] = x13 ||| x14

theorem neg1 : (-1 : BitVec 58) = BitVec.allOnes 58 := by decide

theorem n_and (b : BitVec 58) : (-1 : BitVec 58) &&& b = b := by
  rw [neg1, BitVec.allOnes_and]

theorem and_n (b : BitVec 58) : b &&& (-1 : BitVec 58) = b := by
  rw [neg1, BitVec.and_allOnes]

theorem n_or (b : BitVec 58) : (-1 : BitVec 58) ||| b = -1 := by
  rw [neg1, BitVec.allOnes_or]

theorem or_n (b : BitVec 58) : b ||| (-1 : BitVec 58) = -1 := by
  rw [neg1, BitVec.or_allOnes]

theorem bit_all (k : ℕ) (hk : k < 58) (l : List (BitVec 58)) :
    (l.map fun v => v.getLsbD k).all id = (l.foldr (fun a b => a &&& b) (-1)).getLsbD k := by
  induction l with
  | nil => rw [List.foldr_nil, neg1, BitVec.getLsbD_allOnes]; simp [hk]
  | cons a l ih => simp_all

theorem bit_any (k : ℕ) (l : List (BitVec 58)) :
    (l.map fun v => v.getLsbD k).any id = (l.foldr (fun a b => a ||| b) 0).getLsbD k := by
  induction l with
  | nil => simp
  | cons a l ih => simp_all

theorem bit_getD (W : List (BitVec 58)) (k i : ℕ) :
    (W.map fun v => v.getLsbD k).getD i false = (W.getD i 0).getLsbD k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

theorem bit_gate (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (k : ℕ)
    (hk : k < 58) (W : List (BitVec 58)) :
    g.op.eval (g.inputs.map fun i => (W.map fun v => v.getLsbD k).getD i false)
      = (gm g W).getLsbD k := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, gm, bit_getD]
    rw [← bit_all k hk, List.map_map]
    rfl
  · simp only [GateOp.eval, gm, bit_getD]
    rw [← bit_any k, List.map_map]
    rfl

theorem bit_fold (k : ℕ) (hk : k < 58) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) → ∀ W : List (BitVec 58),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun v => v.getLsbD k) = (mw gs W).map fun v => v.getLsbD k := by
  intro gs
  induction gs with
  | nil => intro _ W; rfl
  | cons g gs ih =>
    intro hm W
    rw [List.foldl_cons, bit_gate g (hm g (by simp)) k hk W]
    have e : (W.map fun v => v.getLsbD k) ++ [(gm g W).getLsbD k]
        = (W ++ [gm g W]).map fun v => v.getLsbD k := by simp
    rw [e, ih (fun g1 hg1 => hm g1 (by simp [hg1])) (W ++ [gm g W])]
    rfl

theorem mw_prefix : ∀ (gs : List Gate) (W : List (BitVec 58)), ∃ t, mw gs W = W ++ t := by
  intro gs
  induction gs with
  | nil => intro W; exact ⟨[], by simp [mw]⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (W ++ [gm g W])
    exact ⟨[gm g W] ++ t, by rw [← List.append_assoc, ← ht]; rfl⟩

theorem getD_mem (W : List (BitVec 58)) (i : ℕ) (h : W.getD i 0 ≠ 0) : W.getD i 0 ∈ W := by
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp
  · exfalso
    apply h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem gclass (L : List (BitVec 58)) (g : Gate) (W : List (BitVec 58))
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hW : ∀ m ∈ W, Ok L m) :
    Ok L (gm g W) ∨ ∃ a b, Ok L a ∧ Ok L b ∧ (gm g W = a &&& b ∨ gm g W = a ||| b) := by
  have hget : ∀ i, Ok L (W.getD i 0) := by
    intro i
    by_cases h : W.getD i 0 = 0
    · exact Or.inl h
    · exact hW _ (getD_mem W i h)
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  match ins, hlen with
  | [], _ =>
    left
    rcases hop with rfl | rfl
    · right; left; simp [gm]
    · left; simp [gm]
  | [a], _ =>
    right
    refine ⟨W.getD a 0, W.getD a 0, hget a, hget a, ?_⟩
    rcases hop with rfl | rfl
    · left; simp only [gm, List.map, List.foldr, and_n, BitVec.and_self]
    · right; simp [gm]
  | [a, b], _ =>
    right
    refine ⟨W.getD a 0, W.getD b 0, hget a, hget b, ?_⟩
    rcases hop with rfl | rfl
    · left; simp only [gm, List.map, List.foldr, and_n]
    · right; simp [gm]
  | _ :: _ :: _ :: _, h => simp at h

theorem step (L : List (BitVec 58)) (a b m : BitVec 58) (hab : m = a &&& b ∨ m = a ||| b)
    (ha : Ok L a) (hb : Ok L b) : Ok L m ∨ (a ∈ L ∧ b ∈ L) := by
  unfold Ok at *
  rcases ha with rfl | rfl | ha
  · left; rcases hab with rfl | rfl
    · simp
    · simpa using hb
  · left; rcases hab with rfl | rfl
    · rw [n_and]; exact hb
    · rw [n_or]; exact Or.inr (Or.inl rfl)
  · rcases hb with rfl | rfl | hb
    · left; rcases hab with rfl | rfl
      · simp
      · simp [ha]
    · left; rcases hab with rfl | rfl
      · rw [and_n]; exact Or.inr (Or.inr ha)
      · rw [or_n]; exact Or.inr (Or.inl rfl)
    · exact Or.inr ⟨ha, hb⟩

theorem P_append (base x10 : List (BitVec 58)) (m : BitVec 58) (hP : P base x10)
    (h1 : m ∉ base ++ x10) (h2 : m ≠ 0) (h3 : m ≠ -1)
    (h4 : ∃ x13 ∈ base ++ x10, ∃ x14 ∈ base ++ x10, m = x13 &&& x14 ∨ m = x13 ||| x14) :
    P base (x10 ++ [m]) := by
  intro i hi
  by_cases h : i < x10.length
  · rw [List.getElem_append_left h, List.take_append_of_le_length (by omega)]
    exact hP i h
  · have hi2 : i = x10.length := by simp at hi; omega
    subst hi2
    have e : (x10 ++ [m])[x10.length] = m := by simp
    have e2 : (x10 ++ [m]).take x10.length = x10 := by simp
    rw [e, e2]
    exact ⟨h1, h2, h3, h4⟩

theorem main (base : List (BitVec 58)) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ (W x10 : List (BitVec 58)), P base x10 → (∀ m ∈ W, Ok (base ++ x10) m) →
    ∃ y, P base y ∧ y.length ≤ x10.length + gs.length ∧
      ∀ m ∈ mw gs W, Ok (base ++ y) m := by
  intro gs
  induction gs with
  | nil => intro _ W x10 hP hW; exact ⟨x10, hP, by simp, by simpa [mw] using hW⟩
  | cons g gs ih =>
    intro hm W x10 hP hW
    have hg := hm g (by simp)
    have hm2 : ∀ g1 ∈ gs, g1.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g1.inputs.length ≤ 2 :=
      fun g1 hg1 => hm g1 (by simp [hg1])
    have hcl := gclass (base ++ x10) g W hg.1 hg.2 hW
    have hmw : mw (g :: gs) W = mw gs (W ++ [gm g W]) := rfl
    rw [hmw]
    by_cases hok : Ok (base ++ x10) (gm g W)
    · obtain ⟨y, h1, h2, h3⟩ := ih hm2 (W ++ [gm g W]) x10 hP (by
        intro m hmm
        rw [List.mem_append] at hmm
        rcases hmm with h | h
        · exact hW m h
        · simp at h; subst h; exact hok)
      exact ⟨y, h1, by simp; omega, h3⟩
    · rcases hcl with h | ⟨a, b, ha, hb, hab⟩
      · exact absurd h hok
      · rcases step (base ++ x10) a b _ hab ha hb with h | ⟨ha2, hb2⟩
        · exact absurd h hok
        · have hn : gm g W ≠ 0 ∧ gm g W ≠ -1 ∧ gm g W ∉ base ++ x10 := by
            unfold Ok at hok
            push Not at hok
            exact hok
          have hP2 := P_append base x10 (gm g W) hP hn.2.2 hn.1 hn.2.1 ⟨a, ha2, b, hb2, hab⟩
          obtain ⟨y, h1, h2, h3⟩ := ih hm2 (W ++ [gm g W]) (x10 ++ [gm g W]) hP2 (by
            intro m hmm
            rw [List.mem_append] at hmm
            rcases hmm with h | h
            · rcases hW m h with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · right; right
                rw [← List.append_assoc]
                exact List.mem_append_left _ h
            · simp at h; subst h; right; right; simp)
          exact ⟨y, h1, by simp at h2 ⊢; omega, h3⟩

end PEqualNP.Outside.L_meta_5801

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_5801 in
theorem PEqualNP.Outside.L_meta_5801 : ∀ (x1 : Fin (14 : ℕ) → BitVec (58 : ℕ)) (x2 x3 : BitVec (58 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 →     x2 ≠ (0 : BitVec (58 : ℕ)) →       x2 ≠ (-1 : BitVec (58 : ℕ)) →         x3 ≠ (0 : BitVec (58 : ℕ)) →           x3 ≠ (-1 : BitVec (58 : ℕ)) →             (∀ (x12 : Fin (58 : ℕ)),                 have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (14 : ℕ)) => (x1 x13).getLsbD ↑x12);                 x13.getD x5 Bool.false = x2.getLsbD ↑x12 ∧ x13.getD x6 Bool.false = x3.getLsbD ↑x12) →               have x13 : List (BitVec (58 : ℕ)) := List.ofFn x1;               ∃ (x14 : List (BitVec (58 : ℕ))),                 x14.length ≤ x4.size ∧                   x2 ∈ x13 ++ x14 ∧                     x3 ∈ x13 ++ x14 ∧                       ∀ (x15 : Fin x14.length),                         have x16 : List (BitVec (58 : ℕ)) := x13 ++ List.take (↑x15) x14;                         x14.get x15 ∉ x16 ∧ x14.get x15 ≠ (0 : BitVec (58 : ℕ)) ∧ x14.get x15 ≠ (-1 : BitVec (58 : ℕ)) ∧ ∃ x17 ∈ x16, ∃ x18 ∈ x16, x14.get x15 = x17 &&& x18 ∨ x14.get x15 = x17 ||| x18 := by
  intro x1 x2 x3 x4 x5 x6 hmono h20 h21 h30 h31 hbits
  have hb : ∀ k : Fin 58,
      ((mw x4.gates (List.ofFn x1)).getD x5 0).getLsbD k = x2.getLsbD k ∧
      ((mw x4.gates (List.ofFn x1)).getD x6 0).getLsbD k = x3.getLsbD k := by
    intro k
    have h := hbits k
    simp only [Circuit.wires] at h
    have e : List.ofFn (fun i => (x1 i).getLsbD k) = (List.ofFn x1).map (fun v => v.getLsbD k) := by
      simp
    rw [e, bit_fold k k.2 _ (fun g hg => (hmono g hg).1), bit_getD, bit_getD] at h
    exact h
  have hx2 : (mw x4.gates (List.ofFn x1)).getD x5 0 = x2 :=
    BitVec.eq_of_getLsbD_eq (fun i hi => (hb ⟨i, hi⟩).1)
  have hx3 : (mw x4.gates (List.ofFn x1)).getD x6 0 = x3 :=
    BitVec.eq_of_getLsbD_eq (fun i hi => (hb ⟨i, hi⟩).2)
  obtain ⟨x14, hP, hlen, hall⟩ := main (List.ofFn x1) x4.gates
    (fun g1 hg1 => hmono g1 hg1) (List.ofFn x1) [] (fun i hi => by simp at hi)
    (fun m hm => Or.inr (Or.inr (by simpa using hm)))
  have hmem2 := getD_mem (mw x4.gates (List.ofFn x1)) x5 (by rw [hx2]; exact h20)
  have hmem3 := getD_mem (mw x4.gates (List.ofFn x1)) x6 (by rw [hx3]; exact h30)
  rw [hx2] at hmem2
  rw [hx3] at hmem3
  refine ⟨x14, by simpa [Circuit.size] using hlen, ?_, ?_, ?_⟩
  · rcases hall x2 hmem2 with h | h | h
    · exact absurd h h20
    · exact absurd h h21
    · exact h
  · rcases hall x3 hmem3 with h | h | h
    · exact absurd h h30
    · exact absurd h h31
    · exact h
  · intro x15
    exact hP x15.1 x15.2
