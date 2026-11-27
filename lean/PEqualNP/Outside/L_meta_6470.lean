import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6470

def Legal (base xs : List Nat) : Prop :=
  ∀ i : Fin xs.length, ∃ a ∈ base ++ xs.take i.val, ∃ b ∈ base ++ xs.take i.val,
    xs.get i = a &&& b ∨ xs.get i = a ||| b

def Step (available : List Nat) (v : Nat) : Prop :=
  ∃ a ∈ available, ∃ b ∈ available, v = a &&& b ∨ v = a ||| b

theorem legal_snoc (base xs : List Nat) (x : Nat) :
    Legal base (xs ++ [x]) ↔ Legal base xs ∧ Step (base ++ xs) x := by
  constructor
  · intro h
    constructor
    · intro i
      have hi : i.val < (xs ++ [x]).length := by simp
      have h' := h ⟨i.val, hi⟩
      change Step (base ++ (xs ++ [x]).take i.val) (xs ++ [x])[i.val] at h'
      rwa [List.take_append_of_le_length i.isLt.le, List.getElem_append_left i.isLt] at h'
    · have hi : xs.length < (xs ++ [x]).length := by simp
      have h' := h ⟨xs.length, hi⟩
      change Step (base ++ (xs ++ [x]).take xs.length) (xs ++ [x])[xs.length] at h'
      simpa using h'
  · rintro ⟨h, hs⟩ i
    change Step (base ++ (xs ++ [x]).take i.val) (xs ++ [x])[i.val]
    by_cases hi : i.val < xs.length
    · rw [List.take_append_of_le_length hi.le, List.getElem_append_left hi]
      exact h ⟨i.val, hi⟩
    · have eq : i.val = xs.length := by have := i.isLt; simp at this; omega
      simp [eq, hs]

theorem legal_nil (base : List Nat) : Legal base [] := fun i => Fin.elim0 i

theorem legal_mono (B C : List Nat) (hBC : ∀ b ∈ B, b ∈ C) (V : List Nat) (h : Legal B V) :
    Legal C V := by
  induction V using List.reverseRecOn with
  | nil => exact legal_nil C
  | append_singleton V x ih =>
    obtain ⟨hV, a, ha, b, hb, hop⟩ := (legal_snoc _ _ _).mp h
    refine (legal_snoc _ _ _).mpr ⟨ih hV, a, ?_, b, ?_, hop⟩
    · rcases List.mem_append.mp ha with h1 | h1
      · exact List.mem_append_left _ (hBC a h1)
      · exact List.mem_append_right _ h1
    · rcases List.mem_append.mp hb with h1 | h1
      · exact List.mem_append_left _ (hBC b h1)
      · exact List.mem_append_right _ h1

theorem legal_append (A U : List Nat) (hU : Legal A U) (V : List Nat) (hV : Legal (A ++ U) V) :
    Legal A (U ++ V) := by
  induction V using List.reverseRecOn with
  | nil => simpa using hU
  | append_singleton V x ih =>
    obtain ⟨hV', hs⟩ := (legal_snoc _ _ _).mp hV
    rw [← List.append_assoc]
    refine (legal_snoc _ _ _).mpr ⟨ih hV', ?_⟩
    simpa [List.append_assoc] using hs

def natStep (xs : List Nat) (g : Bool × Nat × Nat) : List Nat :=
  xs ++ [if g.1 = true then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

def bvStep (xs : List (BitVec 59)) (g : Bool × Fin 40 × Fin 40) : List (BitVec 59) :=
  xs ++ [if g.1 = true then xs.getD g.2.1.val 0 ||| xs.getD g.2.2.val 0
    else xs.getD g.2.1.val 0 &&& xs.getD g.2.2.val 0]

def gcast (g : Bool × Fin 40 × Fin 40) : Bool × Nat × Nat := (g.1, g.2.1.val, g.2.2.val)

theorem fold_transfer (xs : List (BitVec 59)) (ops : List (Bool × Fin 40 × Fin 40)) :
    List.foldl natStep (List.map BitVec.toNat xs) (List.map gcast ops)
      = List.map BitVec.toNat (List.foldl bvStep xs ops) := by
  induction ops generalizing xs with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    rcases op with ⟨b, a, c⟩
    cases b <;> simp [bvStep, natStep, gcast] <;>
      cases xs[a.val]? <;> cases xs[c.val]? <;> rfl

theorem fold_prefix (gs : List (Bool × Nat × Nat)) (L : List Nat) (i : Nat) (hi : i < L.length) :
    (List.foldl natStep L gs).getD i 0 = L.getD i 0 := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (natStep L g).length := by simp [natStep]; omega
    rw [ih _ hlen]
    simp only [natStep]
    rw [List.getD_append _ _ _ _ hi]

theorem build (A : List Nat) (P : List Nat) (hP : Legal A P) (hlen : A.length + P.length ≤ 39) :
    ∃ gs : List (Bool × Fin 40 × Fin 40), gs.length = P.length ∧
      List.foldl natStep A (List.map gcast gs) = A ++ P := by
  induction P using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp⟩
  | append_singleton P x ih =>
    obtain ⟨hP', a, ha, b, hb, hop⟩ := (legal_snoc _ _ _).mp hP
    have hlen' : A.length + P.length ≤ 39 := by simp at hlen; omega
    obtain ⟨gs, hgl, hgf⟩ := ih hP' hlen'
    have hLl : (A ++ P).length ≤ 38 := by simp at hlen ⊢; omega
    have hia : (A ++ P).idxOf a < (A ++ P).length := List.idxOf_lt_length_of_mem ha
    have hib : (A ++ P).idxOf b < (A ++ P).length := List.idxOf_lt_length_of_mem hb
    have hga : (A ++ P).getD ((A ++ P).idxOf a) 0 = a := by
      rw [List.getD_eq_getElem _ _ hia, List.getElem_idxOf]
    have hgb : (A ++ P).getD ((A ++ P).idxOf b) 0 = b := by
      rw [List.getD_eq_getElem _ _ hib, List.getElem_idxOf]
    let ia : Fin 40 := ⟨(A ++ P).idxOf a, by omega⟩
    let ib : Fin 40 := ⟨(A ++ P).idxOf b, by omega⟩
    rcases hop with hx | hx
    · refine ⟨gs ++ [(false, ia, ib)], by simp [hgl], ?_⟩
      rw [List.map_append, List.foldl_append, hgf]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, natStep, gcast]
      simp only [Bool.false_eq_true, if_false, ia, ib, hga, hgb, hx, List.append_assoc]
    · refine ⟨gs ++ [(true, ia, ib)], by simp [hgl], ?_⟩
      rw [List.map_append, List.foldl_append, hgf]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, natStep, gcast]
      simp only [if_true, ia, ib, hga, hgb, hx, List.append_assoc]

theorem toNat_getD (W : List (BitVec 59)) (i : Nat) :
    (W.getD i 0).toNat = (List.map BitVec.toNat W).getD i 0 := by
  rw [← List.getD_map (f := BitVec.toNat)]
  simp

theorem main (init : List (BitVec 59)) (F K V : List Nat) (a b : Nat)
    (hinit : init.length = 14) (hlen : F.length + V.length ≤ 25)
    (hF : Legal (init.map BitVec.toNat) F) (hK : ∀ k ∈ K, k ∈ init.map BitVec.toNat ++ F)
    (hV : Legal K V) (ha : a ∈ K ++ V) (hb : b ∈ K ++ V)
    (ha' : a ∉ init.map BitVec.toNat) (hb' : b ∉ init.map BitVec.toNat) (hab : a ≠ b) :
    ∃ (gs : List (Bool × Fin 40 × Fin 40)) (l r : Fin 39),
      gs.length = 25 ∧ 14 ≤ l.val ∧ l < r ∧
      (((List.foldl bvStep init gs).getD l.val 0).toNat = a ∧
        ((List.foldl bvStep init gs).getD r.val 0).toNat = b ∨
       ((List.foldl bvStep init gs).getD l.val 0).toNat = b ∧
        ((List.foldl bvStep init gs).getD r.val 0).toNat = a) := by
  set A := init.map BitVec.toNat with hA
  have hAl : A.length = 14 := by simp [hA, hinit]
  have hP : Legal A (F ++ V) := legal_append A F hF V (legal_mono K (A ++ F) hK V hV)
  have hPl : (F ++ V).length ≤ 25 := by simp; omega
  obtain ⟨gs, hgl, hgf⟩ := build A (F ++ V) hP (by omega)
  have memP : ∀ c, c ∈ K ++ V → c ∉ A → c ∈ F ++ V := by
    intro c hc hc'
    rcases List.mem_append.mp hc with h1 | h1
    · rcases List.mem_append.mp (hK c h1) with h2 | h2
      · exact absurd h2 hc'
      · exact List.mem_append_left _ h2
    · exact List.mem_append_right _ h1
  have haP := memP a ha ha'
  have hbP := memP b hb hb'
  set P := F ++ V with hPdef
  have hja : P.idxOf a < P.length := List.idxOf_lt_length_of_mem haP
  have hjb : P.idxOf b < P.length := List.idxOf_lt_length_of_mem hbP
  have hne : P.idxOf a ≠ P.idxOf b := by
    intro h
    apply hab
    have e1 := List.getElem_idxOf hja
    have e2 := List.getElem_idxOf hjb
    simp only [h] at e1
    exact e1.symm.trans e2
  let pad : List (Bool × Fin 40 × Fin 40) := List.replicate (25 - P.length) (false, 0, 0)
  have key : ∀ j (hj : j < P.length),
      ((List.foldl bvStep init (gs ++ pad)).getD (14 + j) 0).toNat = P[j] := by
    intro j hj
    rw [toNat_getD, ← fold_transfer, List.map_append, List.foldl_append, hgf]
    rw [fold_prefix _ _ _ (by simp; omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega
  have ka := key _ hja
  have kb := key _ hjb
  rw [List.getElem_idxOf] at ka kb
  have hgsl : (gs ++ pad).length = 25 := by simp [pad, hgl]; omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · refine ⟨gs ++ pad, ⟨14 + P.idxOf a, by omega⟩, ⟨14 + P.idxOf b, by omega⟩, hgsl,
      by simp, by simp [Fin.lt_def]; omega, Or.inl ⟨ka, kb⟩⟩
  · refine ⟨gs ++ pad, ⟨14 + P.idxOf b, by omega⟩, ⟨14 + P.idxOf a, by omega⟩, hgsl,
      by simp, by simp [Fin.lt_def]; omega, Or.inr ⟨kb, ka⟩⟩

end PEqualNP.Outside.L_meta_6470

theorem PEqualNP.Outside.L_meta_6470 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List (BitVec (59 : ℕ)) → Bool × Fin (40 : ℕ) × Fin (40 : ℕ) → List (BitVec (59 : ℕ)) := fun (x2 : List (BitVec (59 : ℕ))) (x3 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x2 ++ [if x3.1 = Bool.true then x2.getD ↑x3.2.1 (0 : BitVec (59 : ℕ)) ||| x2.getD ↑x3.2.2 (0 : BitVec (59 : ℕ)) else x2.getD ↑x3.2.1 (0 : BitVec (59 : ℕ)) &&& x2.getD ↑x3.2.2 (0 : BitVec (59 : ℕ))]; ∀ (x3 : List (BitVec (59 : ℕ))) (x4 x5 x6 : List ℕ) (x7 x8 : ℕ),   x3.length = (14 : ℕ) →     x4.length + x6.length ≤ (25 : ℕ) →       x1 (List.map BitVec.toNat x3) x4 →         (∀ x12 ∈ x5, x12 ∈ List.map BitVec.toNat x3 ++ x4) →           x1 x5 x6 →             x7 ∈ x5 ++ x6 →               x8 ∈ x5 ++ x6 →                 x7 ∉ List.map BitVec.toNat x3 →                   x8 ∉ List.map BitVec.toNat x3 →                     x7 ≠ x8 →                       ∃ (x19 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))) (x20 : Fin (39 : ℕ)) (x21 : Fin (39 : ℕ)),                         x19.length = (25 : ℕ) ∧                           (14 : ℕ) ≤ ↑x20 ∧                             x20 < x21 ∧                               have x22 : List (BitVec (59 : ℕ)) := List.foldl x2 x3 x19;                               (x22.getD ↑x20 (0 : BitVec (59 : ℕ))).toNat = x7 ∧ (x22.getD ↑x21 (0 : BitVec (59 : ℕ))).toNat = x8 ∨ (x22.getD ↑x20 (0 : BitVec (59 : ℕ))).toNat = x8 ∧ (x22.getD ↑x21 (0 : BitVec (59 : ℕ))).toNat = x7 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact PEqualNP.Outside.L_meta_6470.main x3 x4 x5 x6 x7 x8 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
