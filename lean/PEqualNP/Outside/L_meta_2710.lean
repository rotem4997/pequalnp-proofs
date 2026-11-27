import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2710

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def P : List Gate := [⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [19, 23]⟩, ⟨GateOp.or, [26, 27]⟩]

def E : List Gate := [⟨GateOp.and, [6, 28]⟩,
  ⟨GateOp.or, [18, 17]⟩,
  ⟨GateOp.or, [30, 15]⟩,
  ⟨GateOp.or, [31, 22]⟩,
  ⟨GateOp.and, [5, 32]⟩,
  ⟨GateOp.or, [29, 33]⟩,
  ⟨GateOp.or, [20, 19]⟩,
  ⟨GateOp.or, [35, 17]⟩,
  ⟨GateOp.or, [36, 24]⟩,
  ⟨GateOp.and, [7, 37]⟩,
  ⟨GateOp.or, [34, 38]⟩,
  ⟨GateOp.or, [21, 20]⟩,
  ⟨GateOp.or, [40, 18]⟩,
  ⟨GateOp.or, [41, 25]⟩,
  ⟨GateOp.and, [8, 42]⟩,
  ⟨GateOp.or, [39, 43]⟩,
  ⟨GateOp.or, [22, 21]⟩,
  ⟨GateOp.or, [45, 19]⟩,
  ⟨GateOp.or, [46, 13]⟩,
  ⟨GateOp.and, [9, 47]⟩,
  ⟨GateOp.or, [44, 48]⟩,
  ⟨GateOp.or, [23, 22]⟩,
  ⟨GateOp.or, [50, 20]⟩,
  ⟨GateOp.or, [51, 14]⟩,
  ⟨GateOp.and, [10, 52]⟩,
  ⟨GateOp.or, [49, 53]⟩,
  ⟨GateOp.or, [24, 23]⟩,
  ⟨GateOp.or, [55, 21]⟩,
  ⟨GateOp.or, [56, 15]⟩,
  ⟨GateOp.and, [11, 57]⟩,
  ⟨GateOp.or, [54, 58]⟩,
  ⟨GateOp.or, [25, 24]⟩,
  ⟨GateOp.or, [60, 22]⟩,
  ⟨GateOp.or, [61, 16]⟩,
  ⟨GateOp.and, [12, 62]⟩,
  ⟨GateOp.or, [59, 63]⟩]

def L32 : List (Fin 13 × Fin 13) := [(6, 3), (6, 5), (6, 6), (6, 10), (5, 5), (5, 4), (5, 2), (5, 9), (7, 7), (7, 6), (7, 4), (7, 11), (8, 8), (8, 7), (8, 5), (8, 12), (9, 9), (9, 8), (9, 6), (9, 0), (10, 10), (10, 9), (10, 7), (10, 1), (11, 11), (11, 10), (11, 8), (11, 2), (12, 12), (12, 11), (12, 9), (12, 3)]

def M32 : List (Fin 26 × Fin 26) := [(6, 16), (6, 18), (6, 19), (6, 23), (5, 18), (5, 17), (5, 15), (5, 22), (7, 20), (7, 19), (7, 17), (7, 24), (8, 21), (8, 20), (8, 18), (8, 25), (9, 22), (9, 21), (9, 19), (9, 13), (10, 23), (10, 22), (10, 20), (10, 14), (11, 24), (11, 23), (11, 21), (11, 15), (12, 25), (12, 24), (12, 22), (12, 16)]

abbrev inc (p l : Fin 13) : Prop := ∃ d ∈ [(0 : Fin 13), 1, 3, 9], p = l + d

def phi : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ)))

def pi (j : ℕ) : ℕ := if j < 5 then j else if j < 14 then j + 8 else j + 9

def r (w : ℕ) : ℕ := if w < 20 then pi w else w + 45

def remap (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

lemma ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

lemma ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

lemma getD_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default]; simp; omega

lemma foldl_F_length (L : List Gate) : ∀ w : List Bool,
    (L.foldl F w).length = w.length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons g L ih => intro w; simp [ih, F]; omega

lemma foldl_getD_lt (L : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (L.foldl F w).getD i false = w.getD i false := by
  induction L with
  | nil => intro w i _; rfl
  | cons g L ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih (F w g) i (by simp [F]; omega)]
    simp only [F]
    rw [getD_snoc, ite_t hi]

lemma sim (L : List Gate) : ∀ (Dw Cw : List Bool), Dw.length = Cw.length + 45 →
    20 ≤ Cw.length → (∀ w, Dw.getD (r w) false = Cw.getD w false) →
    ((L.map remap).foldl F Dw).length = (L.foldl F Cw).length + 45 ∧
      ∀ w, ((L.map remap).foldl F Dw).getD (r w) false = (L.foldl F Cw).getD w false := by
  induction L with
  | nil => intro Dw Cw hl _ hw; exact ⟨hl, hw⟩
  | cons g L ih =>
    intro Dw Cw hl h20 hw
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [F, remap, hl]
    · simp [F]; omega
    · have hv : (remap g).op.eval ((remap g).inputs.map fun i => Dw.getD i false) =
          g.op.eval (g.inputs.map fun i => Cw.getD i false) := by
        simp only [remap, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hw i
      intro w
      simp only [F]
      rw [hv]
      by_cases hwm : w < 20
      · have hr : r w < Dw.length := by
          have : r w ≤ 28 := by
            simp only [r, pi, hwm, ↓reduceIte]
            split_ifs <;> omega
          omega
        rw [getD_snoc, ite_t hr, getD_snoc, ite_t (by omega)]
        exact hw w
      · have hr : r w = w + 45 := by simp [r, hwm]
        rw [hr, getD_snoc, getD_snoc]
        by_cases h1 : w < Cw.length
        · rw [ite_t (by omega), ite_t h1, ← hr]
          exact hw w
        · rw [ite_f (by omega), ite_f h1]
          by_cases h2 : w = Cw.length
          · rw [ite_t (by omega), ite_t h2]
          · rw [ite_f (by omega), ite_f h2]

lemma key2 : ∀ p l : Fin 13, (5 ≤ (p : ℕ) ∧ inc p l) → (Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ M32 := by
  unfold inc M32
  decide

lemma back : ∀ q ∈ M32, ∃ p l : Fin 13, q = (Fin.castAdd 13 p, Fin.natAdd 13 l) ∧
    5 ≤ (p : ℕ) ∧ inc p l := by
  unfold inc M32
  decide

lemma exists_iff (x : Fin 26 → Bool) :
    (∃ p l : Fin 13, 5 ≤ (p : ℕ) ∧ inc p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) ↔ ∃ q ∈ M32, x q.1 = true ∧ x q.2 = true := by
  constructor
  · rintro ⟨p, l, h5, hi, hx, hy⟩
    exact ⟨_, key2 p l ⟨h5, hi⟩, hx, hy⟩
  · rintro ⟨q, hq, hx, hy⟩
    obtain ⟨p, l, rfl, h5, hi⟩ := back q hq
    exact ⟨p, l, h5, hi, hx, hy⟩

lemma epart (x : Fin 26 → Bool) : ((P ++ E).foldl F (List.ofFn x)).getD 64 false =
    decide (∃ p l : Fin 13, 5 ≤ (p : ℕ) ∧ inc p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, exists_iff]
  simp only [M32]
  simp [P, E, F, List.ofFn_succ, GateOp.eval, and_or_left, or_assoc]

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma PE_mono : ∀ g ∈ P ++ E, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    g.inputs.length ≤ 2 := by
  simp [P, E]

lemma PE_length : (P ++ E).length = 39 := rfl

lemma inputs (x : Fin 26 → Bool) : ∀ w, ((P ++ E).foldl F (List.ofFn x)).getD (r w) false =
    (List.ofFn (phi x)).getD w false := by
  intro w
  by_cases hw : w < 20
  · have hlen0 : (P.foldl F (List.ofFn x)).length = 29 := by rw [foldl_F_length]; simp [P]
    have h29 : r w < 29 := by
      simp only [r, pi, hw, ↓reduceIte]; split_ifs <;> omega
    rw [List.foldl_append, foldl_getD_lt E _ _ (by omega), getD_ofFn _ _ hw]
    by_cases h17 : w < 17
    · have h26 : r w < 26 := by simp only [r, pi, hw, ↓reduceIte]; split_ifs <;> omega
      rw [foldl_getD_lt P _ _ (by simpa using h26), getD_ofFn _ _ h26]
      simp only [phi, h17, ↓reduceIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_ofNat, r, pi, hw, ↓reduceIte]
      split_ifs <;> omega
    · have : w = 17 ∨ w = 18 ∨ w = 19 := by omega
      rcases this with rfl | rfl | rfl <;> simp [r, pi, P, F, List.ofFn_succ, GateOp.eval, phi]
  · have hr : r w = w + 45 := by simp [r, hw]
    rw [hr, List.getD_eq_default _ _ (by rw [foldl_F_length]; simp [P, E]; omega),
      List.getD_eq_default _ _ (by simp; omega)]

def fin (C : Circuit) : Gate := ⟨GateOp.or, [64, r C.output]⟩

def D (C : Circuit) : Circuit := ⟨P ++ E ++ C.gates.map remap ++ [fin C], 65 + C.gates.length⟩

end PEqualNP.Outside.L_meta_2710

theorem PEqualNP.Outside.L_meta_2710 : have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x7 ∧ x2 x7 x8 ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) || PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 x6)) := by
  intro x1 x2 C hC
  refine ⟨L_meta_2710.D C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [L_meta_2710.D, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | hg) | rfl
    · exact L_meta_2710.PE_mono g (List.mem_append_left _ hg)
    · exact L_meta_2710.PE_mono g (List.mem_append_right _ hg)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      obtain ⟨h1, h2⟩ := hC g' hg'
      exact ⟨h1, by simpa [L_meta_2710.remap] using h2⟩
    · simp [L_meta_2710.fin]
  · show (L_meta_2710.P ++ L_meta_2710.E ++ C.gates.map L_meta_2710.remap ++
      [L_meta_2710.fin C]).length ≤ C.gates.length + 40
    rw [List.length_append, List.length_append, L_meta_2710.PE_length, List.length_map,
      List.length_singleton]
    omega
  · intro x
    have hW1len : ((L_meta_2710.P ++ L_meta_2710.E).foldl L_meta_2710.F (List.ofFn x)).length
        = 65 := by
      rw [L_meta_2710.foldl_F_length, L_meta_2710.PE_length]; simp
    obtain ⟨_, hv2⟩ := L_meta_2710.sim C.gates
      ((L_meta_2710.P ++ L_meta_2710.E).foldl L_meta_2710.F (List.ofFn x))
      (List.ofFn (L_meta_2710.phi x)) (by rw [hW1len]; simp) (by simp) (L_meta_2710.inputs x)
    have hl2 : ((C.gates.map L_meta_2710.remap).foldl L_meta_2710.F
        ((L_meta_2710.P ++ L_meta_2710.E).foldl L_meta_2710.F (List.ofFn x))).length =
          65 + C.gates.length := by
      rw [L_meta_2710.foldl_F_length, hW1len, List.length_map]
    show (List.foldl L_meta_2710.F (List.ofFn x) (L_meta_2710.P ++ L_meta_2710.E ++
      C.gates.map L_meta_2710.remap ++ [L_meta_2710.fin C])).getD
        (65 + C.gates.length) false = _
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, L_meta_2710.F, L_meta_2710.fin]
    rw [L_meta_2710.getD_snoc, L_meta_2710.ite_f (by omega), L_meta_2710.ite_t (by omega)]
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id, Bool.or_false]
    rw [L_meta_2710.foldl_getD_lt _ _ _ (by omega), hv2, L_meta_2710.epart]
    rfl
