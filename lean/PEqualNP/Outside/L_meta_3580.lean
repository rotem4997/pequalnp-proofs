import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3580

open PEqualNP.CircuitLowerBounds

def rd (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

def OkGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem ok_of_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
    OkGate g := by
  obtain ⟨h1, h2⟩ := h g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, h2⟩

theorem evalRd (g : Gate) (hg : OkGate g) (f f' : ℕ → Bool) (h : ∀ i ∈ rd g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨hop, hl⟩ := hg
  rcases hop with hop | hop | hop
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · rw [hop]
    simp only [rd, hop, GateOp.eval] at h
    cases hin : g.inputs with
    | nil => simp
    | cons a t =>
      rw [hin] at h
      simp only [List.map_cons]
      rw [h a (by simp)]
      simp [GateOp.eval]

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

def dl (w i : ℕ) : ℕ := if i < w then i else i - 1

def rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

theorem F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate) (hg : OkGate g)
    (h : ∀ i ∈ rd g, Q'.getD (dl w i) false = Q.getD i false) :
    (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
      = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
  simp only [rg, List.map_map]
  exact evalRd g hg _ _ h

theorem stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, OkGate g ∧ w ∉ rd g) :
    ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
  induction A with
  | nil => intro Q _; rfl
  | cons g A ih =>
    intro Q hQ
    simp only [List.map_cons, List.foldl_cons]
    have hg := hA g (by simp)
    have hF : F Q (rg w g) = F Q g := by
      unfold F
      rw [F_rg Q Q w g hg.1]
      intro i hi
      have hne : i ≠ w := fun h => hg.2 (h ▸ hi)
      simp only [List.length_cons] at hQ
      by_cases hiw : i < w
      · simp [dl, hiw]
      · simp only [dl, hiw, ite_false]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hF]
    apply ih (fun g' hg' => hA g' (by simp [hg']))
    simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
    omega

theorem key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
    (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
  by_cases hiw : i < w
  · simp only [dl, hiw, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [dl, hiw, ite_false]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
    obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
    rw [hk, List.getD_cons_succ]
    congr 1
    omega

theorem stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
    (hB : ∀ g ∈ B, OkGate g ∧ w ∉ rd g) :
    ∀ M : List Bool, ∀ i, i ≠ w →
      ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
  induction B with
  | nil => intro M i hi; exact key P M v w hP i hi
  | cons g B ih =>
    intro M i hi
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      rw [F_rg (P ++ v :: M) (P ++ M) w g hg.1, List.append_assoc]
      intro i hi
      exact key P M v w hP i (fun h => hg.2 (h ▸ hi))
    have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      simp
    rw [h1, h2]
    exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

theorem del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hok : ∀ g ∈ gs, OkGate g) (hw : ∀ g ∈ gs, n + j ∉ rd g) (x : List Bool) (hx : x.length = n)
    (i : ℕ) (hi : i ≠ n + j) :
    (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
      = (gs.foldl F x).getD i false := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
  have hAll : ∀ g ∈ gs, OkGate g ∧ n + j ∉ rd g := fun g hg => ⟨hok g hg, hw g hg⟩
  rw [herase, List.map_append, List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [stageA (n + j) (gs.take j) (fun g hg => hAll g (List.mem_of_mem_take hg)) x
    (by rw [hx, List.length_take]; omega)]
  have hP : (List.foldl F x (gs.take j)).length = n + j := by
    rw [fold_len, hx, List.length_take]; omega
  have := stageB (n + j) (List.foldl F x (gs.take j))
    (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
    (gs.drop (j + 1)) (fun g hg => hAll g (List.mem_of_mem_drop hg)) [] i hi
  simpa [F] using this

theorem indep (k : ℕ) (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) (hk : ∀ g ∈ gs, k ∉ rd g) :
    ∀ Q Q' : List Bool, Q.length = Q'.length → (∀ i, i ≠ k → Q.getD i false = Q'.getD i false) →
      ∀ i, i ≠ k → (gs.foldl F Q).getD i false = (gs.foldl F Q').getD i false := by
  induction gs with
  | nil => intro Q Q' _ h i hi; exact h i hi
  | cons g gs ih =>
    intro Q Q' hl h i hi
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hok g' (by simp [hg'])) (fun g' hg' => hk g' (by simp [hg']))
    · simp [F, hl]
    · intro i' hi'
      have hv : g.op.eval (g.inputs.map fun i => Q.getD i false)
          = g.op.eval (g.inputs.map fun i => Q'.getD i false) := by
        apply evalRd g (hok g (by simp))
        intro j hj
        exact h j (fun e => hk g (by simp) (e ▸ hj))
      unfold F
      rw [hv]
      by_cases hlt : i' < Q.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact h i' hi'
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    · exact hi

theorem count (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) :
    (gs.flatMap rd).length + (gs.filter fun g => g.op.eval [false]).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ih' := ih (fun g' hg' => hok g' (by simp [hg']))
    have hg : (rd g).length + (if g.op.eval [false] = true then 1 else 0) ≤ 2 := by
      rcases (hok g (by simp)).1 with h | h | h <;> simp [rd, h, GateOp.eval]
    rw [List.flatMap_cons, List.filter_cons, List.length_append]
    split_ifs at hg ⊢ with hc
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

theorem main (n : ℕ) : ∀ s (C : Circuit), C.gates.length = s → PEqualNP.MetaComplexity.FanInTwo C →
    (∀ x5 : Fin n, ∃ (x6 x7 : Fin n → Bool), (∀ x8, x8 ≠ x5 → x6 x8 = x7 x8) ∧
      PEqualNP.MetaComplexity.circuitFun n C x6 ≠ PEqualNP.MetaComplexity.circuitFun n C x7) →
    ∃ D : Circuit, D.size ≤ C.size ∧ PEqualNP.MetaComplexity.FanInTwo D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      ∀ k < n + D.size, k ≠ D.output → k ∈ D.gates.flatMap rd := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs hfan hrel
    have hok : ∀ g ∈ C.gates, OkGate g := ok_of_fan C hfan
    by_cases hdel : ∃ j < C.gates.length, n + j ≠ C.output ∧ ∀ g ∈ C.gates, n + j ∉ rd g
    · obtain ⟨j, hj, ho, hw⟩ := hdel
      let C' : Circuit := ⟨(C.gates.eraseIdx j).map (rg (n + j)), dl (n + j) C.output⟩
      have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
        funext x
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, wires_eq]
        exact del_getD n j C.gates hj hok hw (List.ofFn x) (by simp) C.output (fun e => ho e.symm)
      have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
        intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        have := hfan g0 (List.mem_of_mem_eraseIdx hg0)
        simpa [rg] using this
      have hlen : C'.gates.length = s - 1 := by
        simp only [C', List.length_map, List.length_eraseIdx_of_lt hj, hs]
      obtain ⟨D, h1, h2, h3, h4⟩ := ih (s - 1) (by omega) C' hlen hfan' (by
        intro x5
        obtain ⟨x6, x7, h, hne⟩ := hrel x5
        exact ⟨x6, x7, h, by rw [hfun]; exact hne⟩)
      refine ⟨D, ?_, h2, by rw [h3, hfun], h4⟩
      have : C'.size = s - 1 := hlen
      unfold Circuit.size at this h1 ⊢
      omega
    · refine ⟨C, le_refl _, hfan, rfl, ?_⟩
      intro k hk hko
      by_contra hnot
      have hk' : ∀ g ∈ C.gates, k ∉ rd g := fun g hg hkg => hnot (List.mem_flatMap.2 ⟨g, hg, hkg⟩)
      by_cases hkn : k < n
      · obtain ⟨x6, x7, h, hne⟩ := hrel ⟨k, hkn⟩
        apply hne
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, wires_eq]
        apply indep k C.gates hok hk' _ _ (by simp) _ C.output (Ne.symm hko)
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getD_eq_getElem _ _ (by simpa using hin),
            List.getElem_ofFn, List.getElem_ofFn]
          exact h ⟨i, hin⟩ (fun e => hi (congrArg Fin.val e))
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · apply hdel
        refine ⟨k - n, ?_, ?_, ?_⟩
        · unfold Circuit.size at hk
          omega
        · rw [show n + (k - n) = k by omega]
          exact hko
        · rw [show n + (k - n) = k by omega]
          exact hk'

end PEqualNP.Outside.L_meta_3580

theorem PEqualNP.Outside.L_meta_3580 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin x1), ∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), (∀ (x8 : Fin x1), x8 ≠ x5 → x6 x8 = x7 x8) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x6 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x7) →         ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),           x6.size ≤ x2.size ∧             PEqualNP.MetaComplexity.FanInTwo x6 ∧               PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧                 have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs) x6.gates;                 (∀ x8 < x1 + x6.size, x8 ≠ x6.output → x8 ∈ x7) ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x6.gates).length + (x7.length - x7.toFinset.card) ≤ x6.size + (1 : ℕ) - x1 := by
  intro n C _ hfan hrel
  obtain ⟨D, hs, hf, hfun, hread⟩ :=
    PEqualNP.Outside.L_meta_3580.main n C.gates.length C rfl hfan hrel
  refine ⟨D, hs, hf, hfun, ?_⟩
  show (∀ k < n + D.size, k ≠ D.output → k ∈ D.gates.flatMap PEqualNP.Outside.L_meta_3580.rd) ∧
    (D.gates.filter fun g => g.op.eval [false]).length +
      ((D.gates.flatMap PEqualNP.Outside.L_meta_3580.rd).length -
        (D.gates.flatMap PEqualNP.Outside.L_meta_3580.rd).toFinset.card) ≤ D.size + 1 - n
  refine ⟨hread, ?_⟩
  have hc := PEqualNP.Outside.L_meta_3580.count D.gates (PEqualNP.Outside.L_meta_3580.ok_of_fan D hf)
  have hsub : (Finset.range (n + D.size)).erase D.output ⊆
      (D.gates.flatMap PEqualNP.Outside.L_meta_3580.rd).toFinset := by
    intro k hk
    rw [Finset.mem_erase, Finset.mem_range] at hk
    rw [List.mem_toFinset]
    exact hread k hk.2 hk.1
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := Finset.range (n + D.size)) (a := D.output)
  rw [Finset.card_range] at h2
  have h3 := List.toFinset_card_le (D.gates.flatMap PEqualNP.Outside.L_meta_3580.rd)
  unfold PEqualNP.CircuitLowerBounds.Circuit.size at h1 h2 ⊢
  omega
