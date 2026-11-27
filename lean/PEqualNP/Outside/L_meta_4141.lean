import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4141

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def tbl : List ℕ := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def rl (i : ℕ) : ℕ := if i < 21 then tbl.getD i 0 else i + 24

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rg (g : Gate) : Gate := ⟨g.op, g.inputs.map rl⟩

lemma tbl_lt (i : ℕ) (hi : i < 21) : tbl.getD i 0 < 26 := by
  interval_cases i <;> decide

lemma rl_lt (i k : ℕ) (hk : 21 ≤ k) (hi : i < k) : rl i < k + 24 := by
  unfold rl
  split_ifs with h
  · have := tbl_lt i h
    omega
  · omega

def Rel (w w' : List Bool) : Prop :=
  21 ≤ w.length ∧ w'.length = w.length + 24 ∧ ∀ i, w'.getD (rl i) false = w.getD i false

lemma rel_step (w w' : List Bool) (g : Gate) (h : Rel w w') :
    Rel (step w g) (step w' (rg g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (rg g).op.eval ((rg g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [rg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [step]; omega, by simp [step, h2], ?_⟩
  intro i
  simp only [step]
  rw [hv]
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by rw [h2]; exact rl_lt i _ h1 hi)]
    exact h3 i
  · subst hi
    have : rl w.length = w'.length := by
      unfold rl
      split_ifs <;> omega
    rw [this, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
    simp
  · have hr : rl i = i + 24 := by
      unfold rl
      rw [if_neg (by omega)]
    rw [hr, List.getD_eq_default, List.getD_eq_default] <;> simp <;> omega

lemma rel_foldl (gs : List Gate) :
    ∀ w w', Rel w w' → Rel (gs.foldl step w) ((gs.map rg).foldl step w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih => intro w w' h; exact ih _ _ (rel_step w w' g h)

lemma foldl_len (gs : List Gate) : ∀ w, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [ih, step]; omega

lemma foldl_pre (gs : List Gate) : ∀ w, ∃ L, gs.foldl step w = w ++ L := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨L, hL⟩ := ih (step w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: L, by rw [List.foldl_cons, hL]; simp [step]⟩

def og (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩
def ag (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩

def pre : List Gate :=
  [og 13 17, og 23 25, og 26 27, ag 0 28, og 13 14, og 18 24, og 30 31, ag 1 32,
   og 13 15, og 16 20, og 34 35, ag 3 36, og 13 19, og 21 22, og 38 39, ag 9 40,
   og 29 33, og 37 41, og 42 43]

lemma ofFn26 (x : Fin 26 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8,
    x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23,
    x 24, x 25] := by
  simp [List.ofFn_succ]

def o (a b : Bool) : Bool := a || (b || false)
def n (a b : Bool) : Bool := a && (b && true)

lemma pre44 (x : Fin 26 → Bool) : (pre.foldl step (List.ofFn x)).getD 44 false =
    o (o (n (x 0) (o (o (x 13) (x 17)) (o (x 23) (x 25)))) (n (x 1) (o (o (x 13) (x 14)) (o (x 18) (x 24)))))
      (o (n (x 3) (o (o (x 13) (x 15)) (o (x 16) (x 20)))) (n (x 9) (o (o (x 13) (x 19)) (o (x 21) (x 22))))) := by
  rw [ofFn26]
  simp [pre, step, og, ag, GateOp.eval, o, n]

lemma ca0 : Fin.castAdd 13 (0 : Fin 13) = (0 : Fin 26) := rfl
lemma ca1 : Fin.castAdd 13 (1 : Fin 13) = (1 : Fin 26) := rfl
lemma ca3 : Fin.castAdd 13 (3 : Fin 13) = (3 : Fin 26) := rfl
lemma ca9 : Fin.castAdd 13 (9 : Fin 13) = (9 : Fin 26) := rfl
lemma na0 : Fin.natAdd 13 (0 : Fin 13) = (13 : Fin 26) := rfl
lemma na1 : Fin.natAdd 13 (1 : Fin 13) = (14 : Fin 26) := rfl
lemma na2 : Fin.natAdd 13 (2 : Fin 13) = (15 : Fin 26) := rfl
lemma na3 : Fin.natAdd 13 (3 : Fin 13) = (16 : Fin 26) := rfl
lemma na4 : Fin.natAdd 13 (4 : Fin 13) = (17 : Fin 26) := rfl
lemma na5 : Fin.natAdd 13 (5 : Fin 13) = (18 : Fin 26) := rfl
lemma na6 : Fin.natAdd 13 (6 : Fin 13) = (19 : Fin 26) := rfl
lemma na7 : Fin.natAdd 13 (7 : Fin 13) = (20 : Fin 26) := rfl
lemma na8 : Fin.natAdd 13 (8 : Fin 13) = (21 : Fin 26) := rfl
lemma na9 : Fin.natAdd 13 (9 : Fin 13) = (22 : Fin 26) := rfl
lemma na10 : Fin.natAdd 13 (10 : Fin 13) = (23 : Fin 26) := rfl
lemma na11 : Fin.natAdd 13 (11 : Fin 13) = (24 : Fin 26) := rfl
lemma na12 : Fin.natAdd 13 (12 : Fin 13) = (25 : Fin 26) := rfl
lemma ex13 (P : Fin 13 → Prop) : (∃ b : Fin 13, P b) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 ∨ P 8 ∨ P 9 ∨ P 10 ∨ P 11 ∨ P 12 := by
  constructor
  · rintro ⟨b, h⟩
    fin_cases b <;> simp_all
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h) <;> exact ⟨_, h⟩

lemma x3_eq (x : Fin 26 → Bool) :
  (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
   Decidable.decide (∃ x4 ∈ x1, ∃ (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x5) = Bool.true))
  = o (o (n (x 0) (o (o (x 13) (x 17)) (o (x 23) (x 25)))) (n (x 1) (o (o (x 13) (x 14)) (o (x 18) (x 24)))))
      (o (n (x 3) (o (o (x 13) (x 15)) (o (x 16) (x 20)))) (n (x 9) (o (o (x 13) (x 19)) (o (x 21) (x 22))))) := by
  dsimp only
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  simp only [ex13]
  simp (config := {decide := true}) [and_or_left, or_assoc, ca0, ca1, ca3, ca9, na0, na1, na2, na3, na4, na5, na6, na7, na8, na9, na10, na11, na12, o, n]

lemma base (x : Fin 26 → Bool) (L : List Bool) (hL : L.length = 19) :
    Rel ((List.filter (fun (x2 : Fin (26 : ℕ)) => Decidable.decide (↑x2 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ))).map x) (List.ofFn x ++ L) := by
  have hx2 : List.filter (fun (x2 : Fin (26 : ℕ)) => Decidable.decide (↑x2 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)) = [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] := by
    decide
  rw [hx2]
  refine ⟨by simp, by simp [hL], ?_⟩
  intro i
  by_cases hi : i < 21
  · have hlt : rl i < (List.ofFn x).length := by
      have := tbl_lt i hi
      simp only [rl, hi, if_true, List.length_ofFn]
      omega
    rw [List.getD_append _ _ _ _ hlt, ofFn26]
    interval_cases i <;> rfl
  · have hr : rl i = i + 24 := by
      unfold rl
      split_ifs <;> omega
    rw [hr, List.getD_eq_default, List.getD_eq_default] <;> simp [hL] <;> omega

lemma wires_eq (D : Circuit) (y : List Bool) : D.wires y = D.gates.foldl step y := rfl

end PEqualNP.Outside.L_meta_4141

open PEqualNP.Outside.L_meta_4141

theorem PEqualNP.Outside.L_meta_4141 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (Fin (26 : ℕ)) := List.filter (fun (x2 : Fin (26 : ℕ)) => Decidable.decide (↑x2 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)); have x3 : (Fin (26 : ℕ) → Bool) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) => Decidable.decide (∃ x4 ∈ x1, ∃ (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < (21 : ℕ) + x4.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x4.size + (20 : ℕ) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 x8 = (x4.eval (List.map x8 x2) || x3 x8) := by
  dsimp only
  intro C hM _
  refine ⟨⟨pre ++ C.gates.map rg ++ [og (rl C.output) 44], 45 + C.size⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst h <;> simp [og, ag]
    · obtain ⟨h1, h2⟩ := hM g0 hg0
      exact ⟨h1, by simpa [rg] using h2⟩
    · simp [og]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, pre]
  · intro x8
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, wires_eq, List.foldl_append]
    obtain ⟨L, hL⟩ := foldl_pre pre (List.ofFn x8)
    have hylen : (pre.foldl step (List.ofFn x8)).length = 45 := by
      rw [foldl_len]
      simp [pre]
    have hLlen : L.length = 19 := by
      rw [hL] at hylen
      simp at hylen
      omega
    have hR := rel_foldl C.gates _ _ (base x8 L hLlen)
    rw [← hL] at hR
    obtain ⟨_, _, hval⟩ := hR
    have hWlen : ((C.gates.map rg).foldl step (pre.foldl step (List.ofFn x8))).length = 45 + C.size := by
      rw [foldl_len, hylen]
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    have hW44 : ((C.gates.map rg).foldl step (pre.foldl step (List.ofFn x8))).getD 44 false
        = (pre.foldl step (List.ofFn x8)).getD 44 false := by
      obtain ⟨M, hM'⟩ := foldl_pre (C.gates.map rg) (pre.foldl step (List.ofFn x8))
      rw [hM', List.getD_append _ _ _ _ (by rw [hylen]; norm_num)]
    have hx3 := x3_eq x8
    dsimp only at hx3
    rw [List.foldl_cons, List.foldl_nil]
    simp only [step]
    rw [List.getD_append_right _ _ _ _ (by rw [hWlen])]
    simp only [hWlen, Nat.sub_self, og, List.map_cons, List.map_nil, hval, hW44, pre44, hx3]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
