import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2428

open PEqualNP.CircuitLowerBounds

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma tsnoc_lt (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i [] = T.getD i [] := by
  simp [List.getD, List.getElem?_append_left h]

lemma tsnoc_eq (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i = T.length) :
    (T ++ [a]).getD i [] = a := by
  subst h
  simp [List.getD]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

def evalD (v : ℕ → Bool) (D : List (List ℕ)) : Bool := D.any fun c => c.all v

def prodD (D1 D2 : List (List ℕ)) : List (List ℕ) :=
  D1.flatMap fun c1 => D2.map fun c2 => c1 ++ c2

lemma evalD_append (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (D1 ++ D2) = (evalD v D1 || evalD v D2) := by
  unfold evalD
  rw [List.any_append]

lemma evalD_prod (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (prodD D1 D2) = (evalD v D1 && evalD v D2) := by
  rw [Bool.eq_iff_iff]
  simp only [evalD, prodD, List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨c, ⟨c1, h1, c2, h2, rfl⟩, hc⟩
    exact ⟨⟨c1, h1, fun i hi => hc i (List.mem_append_left _ hi)⟩,
      ⟨c2, h2, fun i hi => hc i (List.mem_append_right _ hi)⟩⟩
  · rintro ⟨⟨c1, h1, a1⟩, ⟨c2, h2, a2⟩⟩
    refine ⟨c1 ++ c2, ⟨c1, h1, c2, h2, rfl⟩, fun i hi => ?_⟩
    rcases List.mem_append.mp hi with h | h
    · exact a1 i h
    · exact a2 i h

def gD (T : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => T.getD i []).foldr prodD [[]]
  | _ => (g.inputs.map fun i => T.getD i []).foldr (fun a b => a ++ b) []

def okb (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length ≤ 2)
  | GateOp.or => decide (g.inputs.length ≤ 2)
  | _ => false

def tstep (T : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) := T ++ [gD T g]

lemma all_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).all id
      = evalD v ((l.map fun i => T.getD i []).foldr prodD [[]]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) && (l.map fun i => w.getD i false).all id)
      = evalD v (prodD (T.getD a []) ((l.map fun i => T.getD i []).foldr prodD [[]]))
    rw [evalD_prod, ← ih, h a]
    rfl

lemma any_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).any id
      = evalD v ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) || (l.map fun i => w.getD i false).any id)
      = evalD v (T.getD a [] ++ ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []))
    rw [evalD_append, ← ih, h a]
    rfl

lemma gD_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (g : Gate) (hg : okb g = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = evalD v (gD T g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact all_spec v w T h ins
  | or => exact any_spec v w T h ins
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

lemma okb_spec (g : Gate) (hg : okb g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact ⟨Or.inl rfl, of_decide_eq_true hg⟩
  | or => exact ⟨Or.inr rfl, of_decide_eq_true hg⟩
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

def Good (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) : Prop :=
  w.length = T.length ∧ ∀ i, w.getD i false = evalD v (T.getD i [])

lemma good_step (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) (g : Gate)
    (hg : okb g = true) (h : Good v w T) : Good v (wstep w g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · show (wstep w g).length = (T ++ [gD T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl]
  · show (wstep w g).getD i false = evalD v ((T ++ [gD T g]).getD i [])
    by_cases hlt : i < T.length
    · rw [tsnoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl]; exact hlt)]
      exact hv i
    · by_cases heq : i = T.length
      · rw [tsnoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl]; exact heq)]
        exact gD_spec v w T hv g hg
      · have h1 : (T ++ [gD T g]).getD i [] = [] :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        have h2 : (wstep w g).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wstep_len, hl]; omega)
        rw [h1, h2]
        rfl

lemma good_fold (v : ℕ → Bool) (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : List Bool) (T : List (List (List ℕ))), Good v w T →
      Good v (gs.foldl wstep w) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step v w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

def T0 : List (List (List ℕ)) := (List.range 26).map fun i => [[i]]

lemma T0_len : T0.length = 26 := by decide +kernel

lemma T0_get : ∀ i < 26, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 26 → Bool) :
    Good (fun i => x (Fin.ofNat 26 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 26
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 26 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl

lemma sing (v : ℕ → Bool) (D : List (List ℕ)) (S : List ℕ)
    (h1 : ∀ c ∈ D, ∃ j ∈ S, c = [j]) (h2 : ∀ j ∈ S, [j] ∈ D) : evalD v D = S.any v := by
  rw [Bool.eq_iff_iff]
  unfold evalD
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, ha⟩
    obtain ⟨j, hj, rfl⟩ := h1 c hc
    refine ⟨j, hj, ?_⟩
    have hb : (v j && true) = true := ha
    rw [Bool.and_true] at hb
    exact hb
  · rintro ⟨j, hj, hv⟩
    refine ⟨[j], h2 j hj, ?_⟩
    show (v j && true) = true
    rw [Bool.and_true]
    exact hv

lemma vp (p : Fin 13) : (Fin.ofNat 26 p.val : Fin 26) = Fin.castAdd 13 p :=
  Fin.ext (Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (by decide)))

lemma vl (w : Fin 13) : (Fin.ofNat 26 (13 + w.val) : Fin 26) = Fin.natAdd 13 w :=
  Fin.ext (Nat.mod_eq_of_lt (by have := w.isLt; omega))

def GS : List Gate := [⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [28, 18]⟩, ⟨GateOp.or, [19, 23]⟩, ⟨GateOp.or, [18, 30]⟩, ⟨GateOp.or, [17, 24]⟩, ⟨GateOp.or, [32, 19]⟩, ⟨GateOp.or, [18, 25]⟩, ⟨GateOp.or, [13, 19]⟩, ⟨GateOp.or, [14, 23]⟩, ⟨GateOp.or, [15, 23]⟩, ⟨GateOp.or, [37, 24]⟩, ⟨GateOp.or, [24, 25]⟩, ⟨GateOp.or, [26, 16]⟩, ⟨GateOp.or, [40, 20]⟩, ⟨GateOp.or, [27, 16]⟩, ⟨GateOp.or, [42, 21]⟩, ⟨GateOp.or, [29, 22]⟩, ⟨GateOp.or, [31, 16]⟩, ⟨GateOp.or, [33, 20]⟩, ⟨GateOp.or, [34, 20]⟩, ⟨GateOp.or, [47, 21]⟩, ⟨GateOp.or, [35, 21]⟩, ⟨GateOp.or, [49, 22]⟩, ⟨GateOp.or, [36, 20]⟩, ⟨GateOp.or, [51, 22]⟩, ⟨GateOp.or, [38, 21]⟩, ⟨GateOp.or, [39, 16]⟩, ⟨GateOp.or, [54, 22]⟩, ⟨GateOp.and, [3, 41]⟩, ⟨GateOp.and, [4, 43]⟩, ⟨GateOp.and, [5, 44]⟩, ⟨GateOp.and, [6, 45]⟩, ⟨GateOp.and, [7, 46]⟩, ⟨GateOp.and, [8, 48]⟩, ⟨GateOp.and, [9, 50]⟩, ⟨GateOp.and, [10, 52]⟩, ⟨GateOp.and, [11, 53]⟩, ⟨GateOp.and, [12, 55]⟩, ⟨GateOp.or, [56, 57]⟩, ⟨GateOp.or, [66, 58]⟩, ⟨GateOp.or, [67, 59]⟩, ⟨GateOp.or, [68, 60]⟩, ⟨GateOp.or, [69, 61]⟩, ⟨GateOp.or, [70, 62]⟩, ⟨GateOp.or, [71, 63]⟩, ⟨GateOp.or, [72, 64]⟩, ⟨GateOp.or, [73, 65]⟩]

def Cw : Circuit := ⟨GS, 74⟩

def IDX : List ℕ := [0, 1, 2, 13, 14, 15, 17, 18, 19, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]

def X2L : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]

def TF : List (List (List ℕ)) := GS.foldl tstep T0

lemma gs_ok : ∀ g ∈ GS, okb g = true := by decide +kernel

lemma mono : PEqualNP.MetaComplexity.Monotone2 Cw := fun g hg => okb_spec g (gs_ok g hg)

lemma sz : Cw.size ≤ 49 := by decide +kernel

lemma outlt : Cw.output < 26 + Cw.size := by decide +kernel

lemma idx_lt : ∀ i : Fin 26, IDX.getD i.val 0 < 26 + Cw.size := by decide +kernel

def x4w : Fin 26 → Fin (26 + Cw.size) := fun i => ⟨IDX.getD i.val 0, idx_lt i⟩

lemma good_all (x : Fin 26 → Bool) :
    Good (fun i => x (Fin.ofNat 26 i)) (Cw.wires (List.ofFn x)) TF :=
  good_fold _ GS gs_ok _ _ (good_init x)

lemma f1 : ∀ i : Fin 26, (∀ c ∈ TF.getD (IDX.getD i.val 0) [], ∃ j ∈ X2L.getD i.val [], c = [j])
    ∧ (∀ j ∈ X2L.getD i.val [], [j] ∈ TF.getD (IDX.getD i.val 0) []) := by decide +kernel

lemma f2 : ∀ c ∈ TF.getD 74 [], ∃ p : Fin 13, ∃ w : Fin 13, c = [p.val, 13 + w.val] ∧ 3 ≤ p.val
    ∧ ∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = w + d := by
  decide +kernel

lemma f3 : ∀ p w : Fin 13, 3 ≤ p.val →
    (∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = w + d) →
    [p.val, 13 + w.val] ∈ TF.getD 74 [] := by
  decide +kernel

lemma c4 (x : Fin 26 → Bool) : PEqualNP.MetaComplexity.circuitFun 26 Cw x
    = decide (∃ (x6 : Fin 13) (x7 : Fin 13), 3 ≤ x6.val
      ∧ (∃ x8 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), x6 = x7 + x8)
      ∧ x (Fin.castAdd 13 x6) = true ∧ x (Fin.natAdd 13 x7) = true) := by
  have hv : PEqualNP.MetaComplexity.circuitFun 26 Cw x
      = evalD (fun i => x (Fin.ofNat 26 i)) (TF.getD 74 []) := (good_all x).2 74
  rw [hv, Bool.eq_iff_iff, decide_eq_true_iff]
  unfold evalD
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, ha⟩
    obtain ⟨p, w, rfl, h3, hinc⟩ := f2 c hc
    have hb : (x (Fin.ofNat 26 p.val) && (x (Fin.ofNat 26 (13 + w.val)) && true)) = true := ha
    rw [Bool.and_true, Bool.and_eq_true] at hb
    exact ⟨p, w, h3, hinc, (congrArg x (vp p)).symm.trans hb.1,
      (congrArg x (vl w)).symm.trans hb.2⟩
  · rintro ⟨p, w, h3, hinc, hp, hw⟩
    refine ⟨[p.val, 13 + w.val], f3 p w h3 hinc, ?_⟩
    show (x (Fin.ofNat 26 p.val) && (x (Fin.ofNat 26 (13 + w.val)) && true)) = true
    rw [Bool.and_true, Bool.and_eq_true]
    exact ⟨(congrArg x (vp p)).trans hp, (congrArg x (vl w)).trans hw⟩

lemma c5 (x : Fin 26 → Bool) (i : Fin 26) :
    (Cw.wires (List.ofFn x)).getD (x4w i).val false
      = (X2L.getD i.val []).any fun j => x (Fin.ofNat 26 j) :=
  ((good_all x).2 (IDX.getD i.val 0)).trans (sing _ _ _ (f1 i).1 (f1 i).2)

lemma main : ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (26 : ℕ) → Fin ((26 : ℕ) + x3.size)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (49 : ℕ) ∧ x3.output < (26 : ℕ) + x3.size ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 x5 = Decidable.decide (∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (3 : ℕ) ≤ ↑x6 ∧ (∃ x8 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), x6 = x7 + x8) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : Fin (26 : ℕ)), (x3.wires (List.ofFn x5)).getD (↑(x4 x6)) Bool.false = (([[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]] : List (List ℕ)).getD ↑x6 []).any fun (x7 : ℕ) => x5 (Fin.ofNat (26 : ℕ) x7) :=
  ⟨Cw, x4w, mono, sz, outlt, c4, c5⟩

end PEqualNP.Outside.L_meta_2428

theorem PEqualNP.Outside.L_meta_2428 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (26 : ℕ) → Fin ((26 : ℕ) + x3.size)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (49 : ℕ) ∧ x3.output < (26 : ℕ) + x3.size ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 x5 = Decidable.decide (∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (3 : ℕ) ≤ ↑x6 ∧ (∃ x8 ∈ x1, x6 = x7 + x8) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : Fin (26 : ℕ)), (x3.wires (List.ofFn x5)).getD (↑(x4 x6)) Bool.false = (x2.getD ↑x6 []).any fun (x7 : ℕ) => x5 (Fin.ofNat (26 : ℕ) x7) := by
  exact PEqualNP.Outside.L_meta_2428.main
