import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6860

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem foldl_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [List.foldl_cons, ih, stepF]; omega

theorem foldl_pre (gs : List Gate) : ∀ w : List Bool, ∃ R, gs.foldl stepF w = w ++ R := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨R, hR⟩ := ih (stepF w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ R, by rw [List.foldl_cons, hR, stepF, List.append_assoc]⟩

def F (a : ℕ → Bool) : Bool := (((((((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))) || (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31))) || (a 14 && ((((a 35 || a 40) || a 21) || a 31) || a 34))) || (a 17 && ((((a 38 || a 22) || a 24) || a 34) || a 37))) || (a 20 && ((((a 41 || a 25) || a 27) || a 37) || a 40)))

def T (B o : ℕ) : List Gate := [
  ⟨.or, [23, 28]⟩,
  ⟨.or, [B + 0, 30]⟩,
  ⟨.or, [B + 1, 40]⟩,
  ⟨.or, [B + 2, 22]⟩,
  ⟨.and, [2, B + 3]⟩,
  ⟨.or, [26, 31]⟩,
  ⟨.or, [B + 5, 33]⟩,
  ⟨.or, [B + 6, 22]⟩,
  ⟨.or, [B + 7, 25]⟩,
  ⟨.and, [5, B + 8]⟩,
  ⟨.or, [29, 34]⟩,
  ⟨.or, [B + 10, 36]⟩,
  ⟨.or, [B + 11, 25]⟩,
  ⟨.or, [B + 12, 28]⟩,
  ⟨.and, [8, B + 13]⟩,
  ⟨.or, [32, 37]⟩,
  ⟨.or, [B + 15, 39]⟩,
  ⟨.or, [B + 16, 28]⟩,
  ⟨.or, [B + 17, 31]⟩,
  ⟨.and, [11, B + 18]⟩,
  ⟨.or, [35, 40]⟩,
  ⟨.or, [B + 20, 21]⟩,
  ⟨.or, [B + 21, 31]⟩,
  ⟨.or, [B + 22, 34]⟩,
  ⟨.and, [14, B + 23]⟩,
  ⟨.or, [38, 22]⟩,
  ⟨.or, [B + 25, 24]⟩,
  ⟨.or, [B + 26, 34]⟩,
  ⟨.or, [B + 27, 37]⟩,
  ⟨.and, [17, B + 28]⟩,
  ⟨.or, [41, 25]⟩,
  ⟨.or, [B + 30, 27]⟩,
  ⟨.or, [B + 31, 37]⟩,
  ⟨.or, [B + 32, 40]⟩,
  ⟨.and, [20, B + 33]⟩,
  ⟨.or, [B + 4, B + 9]⟩,
  ⟨.or, [B + 35, B + 14]⟩,
  ⟨.or, [B + 36, B + 19]⟩,
  ⟨.or, [B + 37, B + 24]⟩,
  ⟨.or, [B + 38, B + 29]⟩,
  ⟨.or, [B + 39, B + 34]⟩,
  ⟨.or, [o, B + 40]⟩]

def L (a : ℕ → Bool) (E : Bool) : List Bool := [
  (a 23 || a 28),
  ((a 23 || a 28) || a 30),
  (((a 23 || a 28) || a 30) || a 40),
  ((((a 23 || a 28) || a 30) || a 40) || a 22),
  (a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)),
  (a 26 || a 31),
  ((a 26 || a 31) || a 33),
  (((a 26 || a 31) || a 33) || a 22),
  ((((a 26 || a 31) || a 33) || a 22) || a 25),
  (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25)),
  (a 29 || a 34),
  ((a 29 || a 34) || a 36),
  (((a 29 || a 34) || a 36) || a 25),
  ((((a 29 || a 34) || a 36) || a 25) || a 28),
  (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28)),
  (a 32 || a 37),
  ((a 32 || a 37) || a 39),
  (((a 32 || a 37) || a 39) || a 28),
  ((((a 32 || a 37) || a 39) || a 28) || a 31),
  (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31)),
  (a 35 || a 40),
  ((a 35 || a 40) || a 21),
  (((a 35 || a 40) || a 21) || a 31),
  ((((a 35 || a 40) || a 21) || a 31) || a 34),
  (a 14 && ((((a 35 || a 40) || a 21) || a 31) || a 34)),
  (a 38 || a 22),
  ((a 38 || a 22) || a 24),
  (((a 38 || a 22) || a 24) || a 34),
  ((((a 38 || a 22) || a 24) || a 34) || a 37),
  (a 17 && ((((a 38 || a 22) || a 24) || a 34) || a 37)),
  (a 41 || a 25),
  ((a 41 || a 25) || a 27),
  (((a 41 || a 25) || a 27) || a 37),
  ((((a 41 || a 25) || a 27) || a 37) || a 40),
  (a 20 && ((((a 41 || a 25) || a 27) || a 37) || a 40)),
  ((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))),
  (((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))),
  ((((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))) || (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31))),
  (((((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))) || (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31))) || (a 14 && ((((a 35 || a 40) || a 21) || a 31) || a 34))),
  ((((((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))) || (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31))) || (a 14 && ((((a 35 || a 40) || a 21) || a 31) || a 34))) || (a 17 && ((((a 38 || a 22) || a 24) || a 34) || a 37))),
  (((((((a 2 && ((((a 23 || a 28) || a 30) || a 40) || a 22)) || (a 5 && ((((a 26 || a 31) || a 33) || a 22) || a 25))) || (a 8 && ((((a 29 || a 34) || a 36) || a 25) || a 28))) || (a 11 && ((((a 32 || a 37) || a 39) || a 28) || a 31))) || (a 14 && ((((a 35 || a 40) || a 21) || a 31) || a 34))) || (a 17 && ((((a 38 || a 22) || a 24) || a 34) || a 37))) || (a 20 && ((((a 41 || a 25) || a 27) || a 37) || a 40))),
  (E || F a)]

def rd (W L : List Bool) (j i : ℕ) : Bool :=
  if i < W.length then W.getD i false else if i - W.length < j then L.getD (i - W.length) false else false

theorem rd_eq (W L : List Bool) (j i : ℕ) (hj : j ≤ L.length) :
    (W ++ L.take j).getD i false = rd W L j i := by
  unfold rd
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega), List.getElem?_take]
    simp [h2]
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none]
    · rfl
    · simp; omega

def Good (W Lf : List Bool) : List Gate → ℕ → Prop
  | [], _ => True
  | g :: gs, j => g.op.eval (g.inputs.map (rd W Lf j)) = Lf.getD j false ∧ Good W Lf gs (j + 1)

theorem foldl_spec (W Lf : List Bool) (gs : List Gate) : ∀ j : ℕ, gs.length + j = Lf.length →
    Good W Lf gs j → gs.foldl stepF (W ++ Lf.take j) = W ++ Lf := by
  induction gs with
  | nil =>
    intro j hl _
    simp only [List.length_nil, Nat.zero_add] at hl
    subst hl
    simp
  | cons g gs ih =>
    intro j hl h
    simp only [Good] at h
    obtain ⟨h0, h1⟩ := h
    simp only [List.length_cons] at hl
    have hj : j < Lf.length := by omega
    rw [List.foldl_cons]
    have e1 : stepF (W ++ Lf.take j) g = W ++ Lf.take (j + 1) := by
      unfold stepF
      have hm : (g.inputs.map fun i => (W ++ Lf.take j).getD i false) = g.inputs.map (rd W Lf j) := by
        apply List.map_congr_left
        intro i _
        exact rd_eq W Lf j i (by omega)
      rw [hm, h0, List.take_add_one, List.append_assoc]
      congr 2
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [e1]
    exact ih (j + 1) (by omega) h1

theorem core (W : List Bool) (hW : 42 ≤ W.length) (o : ℕ) (E : Bool)
    (hE : rd W (L (fun i => W.getD i false) E) 41 o = E) :
    ((T W.length o).foldl stepF W).getD (W.length + 41) false = (E || F (fun i => W.getD i false)) := by
  have hlt : ∀ i, i < 42 → i < W.length := fun i hi => by omega
  have key := foldl_spec W (L (fun i => W.getD i false) E) (T W.length o) 0 rfl (by
    simp only [T, Good, List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd, hE]
    simp [rd, L, F, GateOp.eval, hlt])
  simp only [List.take_zero, List.append_nil] at key
  rw [key, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [L]

def oo (C : Circuit) : ℕ := if C.output < 56 + C.gates.length then C.output else 56 + C.gates.length + 100

def pairs : List (ℕ × ℕ) := [(2, 23), (2, 28), (2, 30), (2, 40), (2, 22), (5, 26), (5, 31), (5, 33), (5, 22), (5, 25), (8, 29), (8, 34), (8, 36), (8, 25), (8, 28), (11, 32), (11, 37), (11, 39), (11, 28), (11, 31), (14, 35), (14, 40), (14, 21), (14, 31), (14, 34), (17, 38), (17, 22), (17, 24), (17, 34), (17, 37), (20, 41), (20, 25), (20, 27), (20, 37), (20, 40)]

theorem hpairs : ∀ x6 x7 : Fin 42, (↑x6 < (21 : ℕ) ∧ ↑x6 % (3 : ℕ) = (2 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧
    (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ↔
    ((x6 : ℕ), (x7 : ℕ)) ∈ pairs := by
  decide +kernel

theorem pairs_lt : ∀ pr ∈ pairs, pr.1 < 42 ∧ pr.2 < 42 := by decide +kernel

theorem F_any (a : ℕ → Bool) : F a = pairs.any (fun pr => a pr.1 && a pr.2) := by
  simp [F, pairs, Bool.and_or_distrib_left, Bool.or_assoc]

theorem F_iff (a : ℕ → Bool) : F a = true ↔ ∃ (x6 x7 : Fin 42), (↑x6 < (21 : ℕ) ∧ ↑x6 % (3 : ℕ) = (2 : ℕ) ∧
    (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
    a x6 = true ∧ a x7 = true := by
  rw [F_any, List.any_eq_true]
  constructor
  · rintro ⟨pr, hpr, h⟩
    obtain ⟨h1, h2⟩ := pairs_lt pr hpr
    refine ⟨⟨pr.1, h1⟩, ⟨pr.2, h2⟩, (hpairs _ _).2 hpr, ?_⟩
    simpa using h
  · rintro ⟨x6, x7, hc, h1, h2⟩
    exact ⟨((x6 : ℕ), (x7 : ℕ)), (hpairs _ _).1 hc, by simp [h1, h2]⟩

theorem T_mono (B o : ℕ) : ∀ g ∈ T B o, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem main (C : Circuit) (hm : Monotone2 C) : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 42 ∧
    ∀ x : List Bool, x.length = 56 → (D.eval x = true ↔ C.eval x = true ∨
      ∃ (x6 x7 : Fin 42), (↑x6 < (21 : ℕ) ∧ ↑x6 % (3 : ℕ) = (2 : ℕ) ∧
      (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
      x.getD (↑x6) false = true ∧ x.getD (↑x7) false = true) := by
  refine ⟨⟨C.gates ++ T (56 + C.gates.length) (oo C), 56 + C.gates.length + 41⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hm g h
    · exact T_mono _ _ g h
  · simp [Circuit.size, T]
  · intro x hx
    have hlen : (C.wires x).length = 56 + C.gates.length := by rw [wires_eq, foldl_len, hx]
    have hpre : ∀ i : Fin 42, (C.wires x).getD (i : ℕ) false = x.getD (i : ℕ) false := by
      intro i
      obtain ⟨R, hR⟩ := foldl_pre C.gates x
      rw [wires_eq, hR, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    have hE : rd (C.wires x) (L (fun i => (C.wires x).getD i false) (C.eval x)) 41 (oo C) = C.eval x := by
      unfold oo rd
      by_cases ho : C.output < 56 + C.gates.length
      · rw [if_pos ho, if_pos (show C.output < (C.wires x).length by omega)]
        rfl
      · rw [if_neg ho, if_neg (show ¬ (56 + C.gates.length + 100 < (C.wires x).length) by omega),
          if_neg (show ¬ (56 + C.gates.length + 100 - (C.wires x).length < 41) by omega)]
        unfold Circuit.eval
        rw [List.getD_eq_default _ _ (by omega)]
    show ((C.gates ++ T (56 + C.gates.length) (oo C)).foldl stepF x).getD (56 + C.gates.length + 41) false = true ↔ _
    rw [List.foldl_append, ← wires_eq, show 56 + C.gates.length = (C.wires x).length from hlen.symm]
    rw [core (C.wires x) (by omega) (oo C) (C.eval x) hE, Bool.or_eq_true, F_iff]
    simp only [hpre]

end PEqualNP.Outside.L_meta_6860

theorem PEqualNP.Outside.L_meta_6860 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ x1.size + (42 : ℕ) ∧ ∀ (x4 : List Bool), x4.length = (56 : ℕ) → (x3.eval x4 = Bool.true ↔ x1.eval x4 = Bool.true ∨ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ ↑x6 % (3 : ℕ) = (2 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4.getD (↑x6) Bool.false = Bool.true ∧ x4.getD (↑x7) Bool.false = Bool.true) := by
  exact PEqualNP.Outside.L_meta_6860.main
