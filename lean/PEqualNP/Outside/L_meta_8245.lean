import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8245

def fX (x1 : Fin (9 : ℕ) → Bool) : Bool := [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2

lemma fX_a : fX (fun k => decide (k = 4)) = false := by decide
lemma fX_b : fX (fun k => decide (k = 3 ∨ k = 4)) = true := by decide
lemma fX_c : fX (fun k => decide (k = 3)) = false := by decide
lemma fX_d : ∀ k : Fin 9, k ≠ 4 → decide (k = 3 ∨ k = 4) = decide (k = 3) := by decide

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (z : List Bool) : C.wires z = C.gates.foldl F z := rfl

lemma getD_snoc (w : List Bool) (v : Bool) (k : ℕ) :
    (w ++ [v]).getD k false =
      if k < w.length then w.getD k false else if k = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (a : ℕ) :
    (List.ofFn x).getD a false = if h : a < n then x ⟨a, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [F]
    omega

lemma fold_pre (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl F w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [F]; omega)]
    unfold F
    rw [getD_snoc, if_pos hk]

lemma fold_sim (Inv : List Bool → List Bool → Prop) (G : Gate → Gate) :
    ∀ (gs : List Gate) (w' w : List Bool), Inv w' w →
    (∀ g ∈ gs, ∀ w' w, Inv w' w → Inv (F w' (G g)) (F w g)) →
    Inv ((gs.map G).foldl F w') (gs.foldl F w) := by
  intro gs
  induction gs with
  | nil => intro w' w h _; exact h
  | cons g gs ih =>
    intro w' w h hs
    exact ih _ _ (hs g (List.mem_cons_self ..) w' w h)
      (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg'))

def rg (m : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map m⟩

lemma step_map (m : ℕ → ℕ) (g : Gate) (w' w : List Bool)
    (h : ∀ k, w'.getD (m k) false = w.getD k false) :
    (rg m g).op.eval ((rg m g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [rg, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

def muA (k : ℕ) : ℕ := if k < 9 then k else k + 1

def sig (p k : ℕ) : ℕ := if k < 9 then k else if k < 9 + p then k + 1 else if k = 9 + p then 9 else k

def InvA (w' w : List Bool) : Prop :=
  w'.length = w.length + 1 ∧ 9 ≤ w.length ∧ ∀ k, w'.getD (muA k) false = w.getD k false

def InvB (p : ℕ) (w' w : List Bool) : Prop :=
  w'.length = w.length ∧ 10 + p ≤ w.length ∧ ∀ k, w'.getD (sig p k) false = w.getD k false

lemma stepA (g : Gate) (w' w : List Bool) (h : InvA w' w) : InvA (F w' (rg muA g)) (F w g) := by
  obtain ⟨hl, h9, hk⟩ := h
  have hv := step_map muA g w' w hk
  refine ⟨by simp [F]; omega, by simp [F]; omega, ?_⟩
  intro k
  have e1 : muA k < w'.length ↔ k < w.length := by unfold muA; split_ifs <;> omega
  have e2 : muA k = w'.length ↔ k = w.length := by unfold muA; split_ifs <;> omega
  unfold F
  rw [getD_snoc, getD_snoc, hv]
  by_cases c1 : k < w.length
  · rw [if_pos c1, if_pos (e1.mpr c1)]
    exact hk k
  · rw [if_neg c1, if_neg (fun h => c1 (e1.mp h))]
    by_cases c2 : k = w.length
    · rw [if_pos c2, if_pos (e2.mpr c2)]
    · rw [if_neg c2, if_neg (fun h => c2 (e2.mp h))]

lemma stepB (p : ℕ) (g : Gate) (w' w : List Bool) (h : InvB p w' w) :
    InvB p (F w' (rg (sig p) g)) (F w g) := by
  obtain ⟨hl, h9, hk⟩ := h
  have hv := step_map (sig p) g w' w hk
  refine ⟨by simp [F]; omega, by simp [F]; omega, ?_⟩
  intro k
  have e1 : sig p k < w'.length ↔ k < w.length := by unfold sig; split_ifs <;> omega
  have e2 : sig p k = w'.length ↔ k = w.length := by unfold sig; split_ifs <;> omega
  unfold F
  rw [getD_snoc, getD_snoc, hv]
  by_cases c1 : k < w.length
  · rw [if_pos c1, if_pos (e1.mpr c1)]
    exact hk k
  · rw [if_neg c1, if_neg (fun h => c1 (e1.mp h))]
    by_cases c2 : k = w.length
    · rw [if_pos c2, if_pos (e2.mpr c2)]
    · rw [if_neg c2, if_neg (fun h => c2 (e2.mp h))]

def good (g : Gate) : Prop :=
  ∀ w1 w2 : List Bool, (∀ k, k ≠ 4 → w1.getD k false = w2.getD k false) →
    g.op.eval (g.inputs.map fun i => w1.getD i false) = g.op.eval (g.inputs.map fun i => w2.getD i false)

lemma good_of_not_mem (g : Gate) (h : 4 ∉ g.inputs) : good g := by
  intro w1 w2 hw
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hw i (fun e => h (e ▸ hi))

lemma good_of_not (g : Gate) (hop : g.op = GateOp.not) (hh : g.inputs.head? ≠ some 4) : good g := by
  intro w1 w2 hw
  rw [hop]
  rcases hin : g.inputs with _ | ⟨a, t⟩
  · simp [GateOp.eval]
  · rw [hin] at hh
    have ha : a ≠ 4 := fun e => hh (by simp [e])
    simp only [GateOp.eval, List.map_cons, List.headD_cons, hw a ha]

def InvI (w1 w2 : List Bool) : Prop :=
  w1.length = w2.length ∧ ∀ k, k ≠ 4 → w1.getD k false = w2.getD k false

lemma indep (gs : List Gate) (hg : ∀ g ∈ gs, good g) :
    ∀ w1 w2 : List Bool, InvI w1 w2 → InvI (gs.foldl F w1) (gs.foldl F w2) := by
  induction gs with
  | nil => intro w1 w2 h; exact h
  | cons g gs ih =>
    intro w1 w2 h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hk⟩ := h
    have hv := hg g (List.mem_cons_self ..) w1 w2 hk
    refine ⟨by simp [F, hl], ?_⟩
    intro k hk4
    unfold F
    rw [getD_snoc, getD_snoc, hv, hl]
    split_ifs
    · exact hk k hk4
    · rfl
    · rfl

theorem main : ∀ (C : Circuit) (x3 : Fin C.size), PEqualNP.MetaComplexity.FanInTwo C →
    (C.gates.get x3).op = GateOp.not →
    (∀ x6 : Fin C.size, (4 : ℕ) ∈ (C.gates.get x6).inputs → x6 = x3) →
    PEqualNP.MetaComplexity.circuitFun 9 C = fX →
    ∃ x8 : Circuit, PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = C.size ∧
      (∀ x9 : Fin 9 → Bool, (x8.wires (List.ofFn x9)).getD 9 false = !x9 4) ∧
      PEqualNP.MetaComplexity.circuitFun 9 x8 = fX := by
  intro C x3 hF hNot h4 hfun
  have hf : ∀ x, C.eval (List.ofFn x) = fX x := fun x => congrFun hfun x
  set gs := C.gates with hgs
  set p : ℕ := x3.1 with hpdef
  have hp : p < gs.length := x3.2
  set g := gs[p] with hgdef
  have hgget : C.gates.get x3 = g := by first | rfl | simp [hgdef, hpdef, hgs, List.get_eq_getElem]
  rw [hgget] at hNot
  set A := gs.take p with hA
  set B := gs.drop (p + 1) with hB
  have hsplit : gs = A ++ g :: B := by
    rw [hA, hB, hgdef, ← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have hAl : A.length = p := by simp [hA]; omega
  by_cases hh : g.inputs.head? = some 4
  · -- the NOT gate reads input 4: move it to the front
    obtain ⟨rest, hin⟩ : ∃ rest, g.inputs = 4 :: rest := by
      rcases hi : g.inputs with _ | ⟨a, t⟩
      · rw [hi] at hh; simp at hh
      · rw [hi] at hh; simp at hh; exact ⟨t, by rw [hh]⟩
    let ng : Gate := ⟨GateOp.not, [4]⟩
    refine ⟨⟨ng :: (A.map (rg muA) ++ B.map (rg (sig p))), sig p C.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · exact ⟨by simp [ng], by simp [ng]⟩
      · rcases List.mem_append.mp hg' with h | h
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
          have := hF a (List.mem_of_mem_take ha)
          exact ⟨this.1, by simpa [rg] using this.2⟩
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
          have := hF a (List.mem_of_mem_drop ha)
          exact ⟨this.1, by simpa [rg] using this.2⟩
    · simp only [Circuit.size, List.length_cons, List.length_append, List.length_map, hAl, hB,
        List.length_drop]
      rw [← hgs]
      omega
    -- the simulation, for every input
    have key : ∀ x : Fin 9 → Bool,
        ((⟨ng :: (A.map (rg muA) ++ B.map (rg (sig p))), sig p C.output⟩ : Circuit).wires
          (List.ofFn x)).getD 9 false = !x 4 ∧
        ((⟨ng :: (A.map (rg muA) ++ B.map (rg (sig p))), sig p C.output⟩ : Circuit).eval
          (List.ofFn x)) = C.eval (List.ofFn x) := by
      intro x
      set x' := List.ofFn x with hx'
      have hl' : x'.length = 9 := by simp [hx']
      set w0 := F x' ng with hw0
      have hw0l : w0.length = 10 := by simp [hw0, F, hl']
      have hw09 : w0.getD 9 false = !x 4 := by
        rw [hw0]; unfold F; rw [getD_snoc, if_neg (by omega), if_pos hl'.symm]
        simp [ng, GateOp.eval, hx', getD_ofFn]
      have hI0 : InvA w0 x' := by
        refine ⟨by omega, by omega, ?_⟩
        intro k
        rw [hw0]; unfold F muA
        by_cases hk : k < 9
        · rw [if_pos hk, getD_snoc, if_pos (by omega)]
        · rw [if_neg hk, getD_snoc, if_neg (by omega), if_neg (by omega),
            List.getD_eq_default _ _ (by omega)]
      have hIA := fold_sim InvA (rg muA) A w0 x' hI0 (fun g _ w' w h => stepA g w' w h)
      set wA' := (A.map (rg muA)).foldl F w0 with hwA'
      set wA := A.foldl F x' with hwA
      have hwAl : wA.length = 9 + p := by rw [hwA, fold_len, hl', hAl]
      have hwA4 : wA.getD 4 false = x 4 := by
        rw [hwA, fold_pre _ _ _ (by omega), hx', getD_ofFn, dif_pos (by norm_num)]
        rfl
      have hwA'9 : wA'.getD 9 false = !x 4 := by
        rw [hwA', fold_pre _ _ _ (by omega), hw09]
      have hv : F wA g = wA ++ [!x 4] := by
        unfold F; rw [hNot, hin]; simp only [List.map_cons, GateOp.eval, List.headD_cons, hwA4]
      obtain ⟨hAl1, hA9, hAk⟩ := hIA
      have hIB0 : InvB p wA' (F wA g) := by
        rw [hv]
        refine ⟨by simp; omega, by simp; omega, ?_⟩
        intro k
        rw [getD_snoc]
        by_cases c1 : k < wA.length
        · rw [if_pos c1, ← hAk k]
          congr 1
          unfold sig muA
          split_ifs <;> omega
        · rw [if_neg c1]
          by_cases c2 : k = wA.length
          · rw [if_pos c2]
            have : sig p k = 9 := by unfold sig; split_ifs <;> omega
            rw [this, hwA'9]
          · rw [if_neg c2]
            have : sig p k = k := by unfold sig; split_ifs <;> omega
            rw [this, List.getD_eq_default _ _ (by omega)]
      have hIB := fold_sim (InvB p) (rg (sig p)) B wA' (F wA g) hIB0
        (fun g _ w' w h => stepB p g w' w h)
      obtain ⟨_, _, hBk⟩ := hIB
      have hW : (⟨ng :: (A.map (rg muA) ++ B.map (rg (sig p))), sig p C.output⟩ : Circuit).wires x'
          = (B.map (rg (sig p))).foldl F wA' := by
        rw [wires_eq]; simp only [List.foldl_cons, List.foldl_append]; rfl
      have hC : C.wires x' = B.foldl F (F wA g) := by
        rw [wires_eq, ← hgs, hsplit, List.foldl_append, List.foldl_cons]
      refine ⟨?_, ?_⟩
      · rw [hW, fold_pre _ _ _ (by omega), hwA'9]
      · unfold Circuit.eval
        rw [hW, hC]
        exact hBk C.output
    refine ⟨fun x => (key x).1, ?_⟩
    funext x
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [(key x).2, hf]
  · -- otherwise input 4 is never read: impossible
    exfalso
    have hgood : ∀ g' ∈ gs, good g' := by
      intro g' hg'
      obtain ⟨i, rfl⟩ := List.get_of_mem hg'
      by_cases hi : i = x3
      · subst hi
        rw [hgget]
        exact good_of_not g hNot hh
      · exact good_of_not_mem _ (fun hm => hi (h4 i hm))
    have hind : ∀ x y : Fin 9 → Bool, (∀ k, k ≠ 4 → x k = y k) →
        InvI (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
      intro x y hxy
      rw [wires_eq, wires_eq]
      apply indep gs hgood
      refine ⟨by simp, ?_⟩
      intro k hk
      rw [getD_ofFn, getD_ofFn]
      split_ifs with h
      · exact hxy _ (fun e => hk (by have e' := congrArg Fin.val e; simpa using e'))
      · rfl
    by_cases ho : C.output = 4
    · have e := hf (fun k => decide (k = 4))
      rw [fX_a] at e
      unfold Circuit.eval at e
      rw [ho, wires_eq, fold_pre _ _ _ (by simp), getD_ofFn, dif_pos (by norm_num)] at e
      simp at e
    · have e1 := hf (fun k => decide (k = 3 ∨ k = 4))
      have e2 := hf (fun k => decide (k = 3))
      rw [fX_b] at e1
      rw [fX_c] at e2
      have := (hind _ _ fX_d).2 C.output ho
      unfold Circuit.eval at e1 e2
      rw [this, e2] at e1
      exact Bool.false_ne_true e1

end PEqualNP.Outside.L_meta_8245

theorem PEqualNP.Outside.L_meta_8245 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.size), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x6 : Fin x2.size), (4 : ℕ) ∈ (x2.gates.get x6).inputs → x6 = x3) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = x2.size ∧ (∀ (x9 : Fin (9 : ℕ) → Bool), (x8.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = !x9 (4 : Fin (9 : ℕ))) ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 = x1 := by
  exact PEqualNP.Outside.L_meta_8245.main
