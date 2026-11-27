import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8065

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : Bool) (f g : ℕ → Bool) (l : List ℕ) (h : ∀ i, f i = b → g i = b) :
    op.eval (l.map f) = b → op.eval (l.map g) = b := by
  rcases hop with rfl | rfl
  · cases b <;> simp only [GateOp.eval, List.all_map, List.all_eq_true,
      List.all_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩
    · exact fun H x hx => h x (H x hx)
  · cases b <;> simp only [GateOp.eval, List.any_map, List.any_eq_true,
      List.any_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun H x hx => h x (H x hx)
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩

theorem main_fold (n m p : ℕ) (b : Bool) (B : List Gate)
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hp : p < n + m ∨ w'.length + B.length ≤ p)
    (hI : ∀ i, w.getD i false = b → w'.getD (eraseRedirect n m p i) false = b) :
    ∀ i, (B.foldl step w).getD i false = b →
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false = b := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    simp only [List.length_cons] at hp
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      simp only [step, getD_snoc, List.map_map]
      have hx := op_mono g.op hg b (fun i => w.getD i false)
        (fun i => w'.getD (eraseRedirect n m p i) false) g.inputs hI
      have hIi := hI i
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      by_cases h1 : i < w.length
      · rw [if_pos h1]
        intro hb
        have h3 := hIi hb
        by_cases hr1 : r < w'.length
        · rw [if_pos hr1]; exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg hr1, if_neg (by omega)]
          rw [getD_big _ _ (by omega)] at h3
          exact h3
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · rw [if_pos h2]
          intro hb
          have h3 := hx hb
          have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_neg (by omega), if_pos h4]
          exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
          exact id

theorem erase_keep : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       x4 < x1 + x3 ∨ x4 = x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;         PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size + (1 : ℕ) = x2.size ∧ ∀ (x9 : List Bool), x9.length = x1 → ∀ (x11 : Bool), (PEqualNP.LowMerge.wireVal x2 x9 (x1 + x3) = x11 → PEqualNP.LowMerge.wireVal x2 x9 x4 = x11) → ∀ (x13 : ℕ), PEqualNP.LowMerge.wireVal x2 x9 x13 = x11 → PEqualNP.LowMerge.wireVal x8 x9 (PEqualNP.CircuitMoves.eraseRedirect x1 x3 x4 x13) = x11 := by
  intro n C m p hM hm hp
  have hm' : m < C.gates.length := hm
  have hsize : C.size = C.gates.length := rfl
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM g' (List.mem_of_mem_drop hg')
      exact ⟨this.1, by simpa using this.2⟩
  · simp only [eraseGate, if_pos hm', Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  · intro x hx b hyp i
    simp only [PEqualNP.LowMerge.wireVal, wires_eq] at hyp ⊢
    have key : C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
        (step ((C.gates.take m).foldl step x) C.gates[m]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    rw [key] at hyp ⊢
    simp only [eraseGate, if_pos hm']
    rw [List.foldl_append]
    have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
      rw [fold_len, hx, List.length_take]; omega
    have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := by simp
    apply main_fold n m p b _ (fun g hg => (hM g (List.mem_of_mem_drop hg)).1)
    · simp [step]
    · omega
    · rw [hWA, hdl]; rcases hp with hp | hp
      · left; exact hp
      · right; rw [hp, hsize]; omega
    · intro j
      generalize hWAd : List.foldl step x (List.take m C.gates) = WA at *
      rw [fold_stab _ _ _ (by simp [step]; omega)] at hyp
      unfold eraseRedirect
      by_cases h1 : j = n + m
      · subst h1; rw [if_pos rfl]
        intro hb
        have h2 := hyp hb
        rcases hp with hp | hp
        · rw [fold_stab _ _ _ (by simp [step]; omega)] at h2
          simp only [step, getD_snoc, hWA, if_pos hp] at h2; exact h2
        · rw [getD_big _ _ (by rw [fold_len]; simp [step]; omega)] at h2
          rw [getD_big _ _ (by omega)]; exact h2
      · rw [if_neg h1]
        simp only [step, getD_snoc, hWA]
        by_cases h3 : j < n + m
        · rw [if_pos h3, if_neg (by omega)]; exact id
        · rw [if_neg h3, if_neg h1, if_pos (by omega), getD_big _ _ (by omega)]; exact id

theorem gate_val (n m : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hm : m < C.gates.length) (hrb : ∀ i ∈ C.gates[m].inputs, i < n + m) :
    (C.wires x).getD (n + m) false =
      C.gates[m].op.eval (C.gates[m].inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  have key : C.wires x = (C.gates.drop (m + 1)).foldl step
      (step ((C.gates.take m).foldl step x) C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  generalize hW : (C.gates.take m).foldl step x = W at key
  have hWA : W.length = n + m := by
    rw [← hW, fold_len, hx, List.length_take]; omega
  have hstab : ∀ i < n + m + 1, (C.wires x).getD i false = (step W C.gates[m]).getD i false := by
    intro i hi
    rw [key, fold_stab _ _ _ (by simp [step]; omega)]
  have hlow : ∀ i < n + m, (C.wires x).getD i false = W.getD i false := by
    intro i hi
    rw [hstab i (by omega)]
    simp only [step, getD_snoc, hWA, if_pos hi]
  rw [hstab _ (by omega)]
  simp only [step, getD_snoc, hWA, lt_irrefl, if_false, if_true]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hlow i (hrb i hi)]

end PEqualNP.Outside.L_meta_8065

open PEqualNP.Outside.L_meta_8065 PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves in
theorem PEqualNP.Outside.L_meta_8065 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and →       have x6 : Fin (2 : ℕ) → (Fin x1 → Bool) → Bool := fun (x6 : Fin (2 : ℕ)) => PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x2 x3 (PEqualNP.TopForm.opnd x2 x3 x6));       PEqualNP.MetaComplexity.circuitFun x1 x2 = fun (x7 : Fin x1 → Bool) => x6 (0 : Fin (2 : ℕ)) x7 && x6 (1 : Fin (2 : ℕ)) x7 := by
  intro n C m hAO hop
  show PEqualNP.MetaComplexity.circuitFun n C = fun x =>
    PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m (PEqualNP.TopForm.opnd C m 0)) x &&
    PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m (PEqualNP.TopForm.opnd C m 1)) x
  have hm : m < C.gates.length := by
    by_contra h
    have : PEqualNP.MetaComplexity.NestedCover.gateAt C m = ⟨GateOp.or, []⟩ := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_eq_none (by omega : C.gates.length ≤ m)]
    rw [this] at hop
    cases hop
  have hge : PEqualNP.MetaComplexity.NestedCover.gateAt C m = C.gates[m] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hm]
  have hM : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, by rw [hAO.2.2 g hg]⟩
    rcases hAO.1 g hg with h | h <;> simp [h]
  have hl : C.gates[m].inputs.length = 2 := hAO.2.2 _ (List.getElem_mem hm)
  have hrb : ∀ i ∈ C.gates[m].inputs, i < n + m := by
    intro i hi
    exact hAO.2.1 m hm i (by rw [hge]; exact hi)
  obtain ⟨u, v, huv⟩ : ∃ u v, C.gates[m].inputs = [u, v] := by
    rcases hI : C.gates[m].inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩ <;> rw [hI] at hl <;>
      simp at hl
    exact ⟨u, v, rfl⟩
  have ho0 : PEqualNP.TopForm.opnd C m 0 = u := by
    simp [PEqualNP.TopForm.opnd, hge, huv]
  have ho1 : PEqualNP.TopForm.opnd C m 1 = v := by
    simp [PEqualNP.TopForm.opnd, hge, huv]
  rw [ho0, ho1]
  have hu : u < n + m := hrb u (by simp [huv])
  have hv : v < n + m := hrb v (by simp [huv])
  have hop' : C.gates[m].op = GateOp.and := by rw [← hge]; exact hop
  funext x
  have hx : (List.ofFn x).length = n := List.length_ofFn
  have hval : PEqualNP.LowMerge.wireVal C (List.ofFn x) (n + m) =
      (PEqualNP.LowMerge.wireVal C (List.ofFn x) u && PEqualNP.LowMerge.wireVal C (List.ofFn x) v) := by
    unfold PEqualNP.LowMerge.wireVal
    rw [gate_val n m C (List.ofFn x) hx hm hrb, huv, hop']
    simp [GateOp.eval]
  have key : ∀ p : ℕ, p < n + m → ∀ b : Bool,
      (PEqualNP.LowMerge.wireVal C (List.ofFn x) (n + m) = b →
        PEqualNP.LowMerge.wireVal C (List.ofFn x) p = b) →
      PEqualNP.LowMerge.wireVal C (List.ofFn x) C.output = b →
      PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m p) x = b := by
    intro p hp b hyp hF
    obtain ⟨_, _, H⟩ := erase_keep n C m p hM hm (Or.inl hp)
    have h1 := H (List.ofFn x) hx b hyp C.output hF
    have hout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
      simp [eraseGate, hm]
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, hout]
    exact h1
  have hF : PEqualNP.MetaComplexity.circuitFun n C x =
      PEqualNP.LowMerge.wireVal C (List.ofFn x) C.output := rfl
  rw [hF]
  cases hFv : PEqualNP.LowMerge.wireVal C (List.ofFn x) C.output
  · cases hA : PEqualNP.LowMerge.wireVal C (List.ofFn x) u
    · rw [key u hu false (fun _ => hA) hFv]; rfl
    · cases hB : PEqualNP.LowMerge.wireVal C (List.ofFn x) v
      · rw [key v hv false (fun _ => hB) hFv]; simp
      · have hG : PEqualNP.LowMerge.wireVal C (List.ofFn x) (n + m) = true := by
          rw [hval, hA, hB]; rfl
        rw [key u hu false (fun h => by rw [hG] at h; cases h) hFv]; rfl
  · have h1 := key u hu true (fun h => by
      rw [hval] at h; exact (Bool.and_eq_true_iff.1 h).1) hFv
    have h2 := key v hv true (fun h => by
      rw [hval] at h; exact (Bool.and_eq_true_iff.1 h).2) hFv
    rw [h1, h2]; rfl
