import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5114_419
    (monotone : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (C : Circuit),
      Even m → H.Colorable 2 →
      (∀ v, (H.neighborSet v).ncard = 3) →
      (∀ (v : Fin m) (w : H.Walk v v), w.IsCycle → 8 ≤ w.length) →
      (∃ u v, H.Adj u v) →
      IsMinimalCircuit m C →
      Monotone2 C →
      (∀ x, circuitFun m C x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      2 * m ≤ C.size + 1)
    (nonMonoAnd : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (C : Circuit),
      Even m → H.Colorable 2 →
      (∀ v, (H.neighborSet v).ncard = 3) →
      (∀ (v : Fin m) (w : H.Walk v v), w.IsCycle → 8 ≤ w.length) →
      (∃ u v, H.Adj u v) →
      IsMinimalCircuit m C →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      (∃ v : Fin m, (C.output :: C.gates.flatMap fun g =>
          List.take (bif g.op.eval [false] then 1 else 2) g.inputs).count v.val = 1 ∧
        ∃ g ∈ C.gates, g.op = GateOp.and ∧ g.inputs.length = 2 ∧ v.val ∈ g.inputs) →
      (∀ x, circuitFun m C x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      2 * m ≤ C.size + 1)
    (nonMonoOr : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (C : Circuit),
      Even m → H.Colorable 2 →
      (∀ v, (H.neighborSet v).ncard = 3) →
      (∀ (v : Fin m) (w : H.Walk v v), w.IsCycle → 8 ≤ w.length) →
      (∃ u v, H.Adj u v) →
      IsMinimalCircuit m C →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      (∃ v : Fin m, (C.output :: C.gates.flatMap fun g =>
          List.take (bif g.op.eval [false] then 1 else 2) g.inputs).count v.val = 1 ∧
        ∃ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length = 2 ∧ v.val ∈ g.inputs) →
      (∀ x, circuitFun m C x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      2 * m ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → x3.card + x2.edgeSet.ncard + (Finset.univ \ x3).card / (2 : ℕ) ≤ x11 + (1 : ℕ) := by
  classical
  intro n G A f hcol hdeg hgirth hiso hedge hspec s hs
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let eff : Gate → List ℕ := fun g =>
    List.take (bif g.op.eval [false] then 1 else 2) g.inputs
  have hev_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hev_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hev_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have heff_and : ∀ g : Gate, g.op = GateOp.and → eff g = List.take 2 g.inputs := by
    intro g h; dsimp only [eff]; rw [h]; rfl
  have heff_or : ∀ g : Gate, g.op = GateOp.or → eff g = List.take 2 g.inputs := by
    intro g h; dsimp only [eff]; rw [h]; rfl
  have heff_not : ∀ g : Gate, g.op = GateOp.not → eff g = List.take 1 g.inputs := by
    intro g h; dsimp only [eff]; rw [h]; rfl
  have hceval : ∀ (C : Circuit) (x : List Bool),
      C.eval x = (C.gates.foldl step x).getD C.output false := fun _ _ => rfl
  have hcfun_eq : ∀ (k : ℕ) (C : Circuit) (x : Fin k → Bool),
      circuitFun k C x = (C.gates.foldl step (List.ofFn x)).getD C.output false := fun _ _ _ => rfl
  have hop_cases : ∀ {op : GateOp},
      op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
    intro op hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h))
  have heff_eval : ∀ (g : Gate) (w : List Bool),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g.inputs.length ≤ 2 →
      g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval ((eff g).map fun i => w.getD i false) := by
    intro g w hop hlen
    rcases hop_cases hop with hop | hop | hop
    · rw [heff_and g hop, List.take_of_length_le hlen]
    · rw [heff_or g hop, List.take_of_length_le hlen]
    · rw [heff_not g hop, hop, hev_not, hev_not]
      cases h : g.inputs with
      | nil => simp
      | cons a rest => simp
  have heff_len : ∀ (g : Gate),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g.inputs.length ≤ 2 →
      (eff g).length ≤ 2 := by
    intro g hop hlen
    rcases hop_cases hop with hop | hop | hop
    · rw [heff_and g hop, List.take_of_length_le hlen]; exact hlen
    · rw [heff_or g hop, List.take_of_length_le hlen]; exact hlen
    · rw [heff_not g hop, List.length_take]; omega
  have hfold_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have hfold_stable : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hgetD_snoc_eq : ∀ {α : Type} (l : List α) (a d : α),
      (l ++ [a]).getD l.length d = a := by
    intro α l a d
    simp [List.getD_eq_getElem?_getD]
  have hgetD_snoc_lt : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ),
      i < l.length → (l ++ [a]).getD i d = l.getD i d := by
    intro α l a d i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hgetD_of_le : ∀ {α : Type} (l : List α) (d : α) (i : ℕ),
      l.length ≤ i → l.getD i d = d := by
    intro α l d i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have hwires_agree : ∀ (gs : List Gate) (b : ℕ) (w1 w2 : List Bool),
      w1.length = w2.length → b < w1.length →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i, i ≠ b → w1.getD i false = w2.getD i false) →
      (∀ g ∈ gs, b ∉ eff g) →
      (gs.foldl step w1).length = (gs.foldl step w2).length ∧
      ∀ i, i ≠ b → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro b w1 w2 hl _ _ ha _; exact ⟨hl, ha⟩
    | cons g gs ih =>
      intro b w1 w2 hl hb hfan ha hno
      rw [List.foldl_cons, List.foldl_cons]
      have hgfan := hfan g List.mem_cons_self
      have hmap : ((eff g).map fun i => w1.getD i false) =
          ((eff g).map fun i => w2.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact ha i (fun he => hno g List.mem_cons_self (he ▸ hi))
      have hev : g.op.eval (g.inputs.map fun i => w1.getD i false) =
          g.op.eval (g.inputs.map fun i => w2.getD i false) := by
        rw [heff_eval g w1 hgfan.1 hgfan.2, heff_eval g w2 hgfan.1 hgfan.2, hmap]
      apply ih b (step w1 g) (step w2 g)
      · simp [step, hl]
      · simp [step]; omega
      · intro g' hg'; exact hfan g' (List.mem_cons_of_mem g hg')
      · intro i hib
        dsimp only [step]
        rw [hev]
        by_cases hlt : i < w1.length
        · rw [hgetD_snoc_lt w1 _ _ i hlt, hgetD_snoc_lt w2 _ _ i (by omega)]
          exact ha i hib
        · by_cases heq : i = w1.length
          · subst heq
            rw [hgetD_snoc_eq w1, hl, hgetD_snoc_eq w2]
          · rw [hgetD_of_le _ _ _ (by simp; omega), hgetD_of_le _ _ _ (by simp; omega)]
      · intro g' hg'; exact hno g' (List.mem_cons_of_mem g hg')
  have elim : ∀ (k : ℕ) (h : (Fin k → Bool) → Bool) (p : Fin k) (r : ℕ),
      (∃ x, h (Function.update x p (!x p)) ≠ h x) →
      (∃ x y, h (Function.update x p false) ≠ h (Function.update y p false)) →
      HasCircuitSize k h r →
      ∃ t, t + 1 ≤ r ∧ HasCircuitSize k (fun x => h (Function.update x p false)) t := by
    intro k h p r hdep hnc hcirc
    rcases hcirc with ⟨C, hfanC, hsizeC, hevalC⟩
    have hex_read : ∃ g ∈ C.gates, p.val ∈ eff g := by
      by_contra hnone
      push Not at hnone
      by_cases hout : C.output = p.val
      · obtain ⟨x, y, hxy⟩ := hnc
        have hfx : h (Function.update x p false) = false := by
          rw [← hevalC, hceval, hout, hfold_stable C.gates _ p.val (by simp)]
          simp [List.getD_eq_getElem?_getD, p.isLt]
        have hfy : h (Function.update y p false) = false := by
          rw [← hevalC, hceval, hout, hfold_stable C.gates _ p.val (by simp)]
          simp [List.getD_eq_getElem?_getD, p.isLt]
        exact hxy (hfx.trans hfy.symm)
      · obtain ⟨x, hx⟩ := hdep
        have hagr := (hwires_agree C.gates p.val
          (List.ofFn (Function.update x p (!x p))) (List.ofFn x)
          (by simp) (by simp) hfanC (by
            intro i hip
            by_cases hi : i < k
            · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte]
              have hne : (⟨i, hi⟩ : Fin k) ≠ p := fun he => hip (congrArg Fin.val he)
              simp [Function.update_of_ne hne]
            · rw [hgetD_of_le _ _ _ (by simp; omega), hgetD_of_le _ _ _ (by simp; omega)])
          hnone).2 C.output hout
        have h1 : h (Function.update x p (!x p)) = h x := by
          rw [← hevalC, ← hevalC, hceval, hceval]
          exact hagr
        exact hx h1
    let evalVal : List Bool → Sum Bool ℕ → Bool := fun w v =>
      Sum.casesOn v (fun b => b) (fun j => w.getD j false)
    let stepC : (List Gate × List (Sum Bool ℕ)) → Gate → (List Gate × List (Sum Bool ℕ)) :=
      fun st g =>
        let gs := st.1
        let env := st.2
        let lu := fun i => env.getD i (Sum.inl false)
        let nw := k + gs.length
        if g.op = GateOp.not then
          List.casesOn g.inputs
            (gs, env ++ [Sum.inl true])
            (fun a _ =>
              Sum.casesOn (lu a)
                (fun b => (gs, env ++ [Sum.inl (!b)]))
                (fun j => (gs ++ [Gate.mk GateOp.not [j]], env ++ [Sum.inr nw])))
        else if g.op = GateOp.and then
          List.casesOn g.inputs
            (gs, env ++ [Sum.inl true])
            (fun a rest =>
              List.casesOn rest
                (gs, env ++ [lu a])
                (fun b rest2 =>
                  List.casesOn rest2
                    (Sum.casesOn (lu a)
                      (fun ba => if ba then
                        Sum.casesOn (lu b)
                          (fun bb => (gs, env ++ [Sum.inl bb]))
                          (fun jb => (gs, env ++ [Sum.inr jb]))
                        else (gs, env ++ [Sum.inl false]))
                      (fun ja =>
                        Sum.casesOn (lu b)
                          (fun bb => if bb then (gs, env ++ [Sum.inr ja])
                            else (gs, env ++ [Sum.inl false]))
                          (fun jb => (gs ++ [Gate.mk GateOp.and [ja, jb]], env ++ [Sum.inr nw]))))
                    (fun _ _ => (gs, env ++ [Sum.inl false]))))
        else if g.op = GateOp.or then
          List.casesOn g.inputs
            (gs, env ++ [Sum.inl false])
            (fun a rest =>
              List.casesOn rest
                (gs, env ++ [lu a])
                (fun b rest2 =>
                  List.casesOn rest2
                    (Sum.casesOn (lu a)
                      (fun ba => if ba then (gs, env ++ [Sum.inl true])
                        else Sum.casesOn (lu b)
                          (fun bb => (gs, env ++ [Sum.inl bb]))
                          (fun jb => (gs, env ++ [Sum.inr jb])))
                      (fun ja =>
                        Sum.casesOn (lu b)
                          (fun bb => if bb then (gs, env ++ [Sum.inl true])
                            else (gs, env ++ [Sum.inr ja]))
                          (fun jb => (gs ++ [Gate.mk GateOp.or [ja, jb]], env ++ [Sum.inr nw]))))
                    (fun _ _ => (gs, env ++ [Sum.inl false]))))
        else (gs, env ++ [Sum.inl false])
    have hstepC_props : ∀ (st : List Gate × List (Sum Bool ℕ)) (g : Gate)
        (orig : List Gate),
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
        g.inputs.length ≤ 2 →
        st.2.length = k + orig.length →
        st.2.getD p.val (Sum.inl false) = Sum.inl false →
        (∀ g' ∈ st.1, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g'.inputs.length ≤ 2) →
        (∀ v ∈ st.2, ∀ j, v = Sum.inr j → j < k + st.1.length) →
        (∀ (x : Fin k → Bool) (i : ℕ),
          evalVal (st.1.foldl step (List.ofFn x)) (st.2.getD i (Sum.inl false)) =
          (orig.foldl step (List.ofFn (Function.update x p false))).getD i false) →
        let st' := stepC st g
        st'.2.length = k + (orig ++ [g]).length ∧
        st'.2.getD p.val (Sum.inl false) = Sum.inl false ∧
        (∀ g' ∈ st'.1, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g'.inputs.length ≤ 2) ∧
        (∀ v ∈ st'.2, ∀ j, v = Sum.inr j → j < k + st'.1.length) ∧
        (∀ (x : Fin k → Bool) (i : ℕ),
          evalVal (st'.1.foldl step (List.ofFn x)) (st'.2.getD i (Sum.inl false)) =
          ((orig ++ [g]).foldl step (List.ofFn (Function.update x p false))).getD i false) ∧
        st'.1.length ≤ st.1.length + 1 ∧
        (p.val ∈ eff g → st'.1.length = st.1.length) := by
      intro st g orig hgop hglen henvlen hpval hgsfan hbound heval
      rcases st with ⟨gs, env⟩
      dsimp only at henvlen hpval hgsfan hbound heval ⊢
      have hp_lt : p.val < env.length := by have := p.isLt; omega
      have hstable_eval : ∀ (extra : List Gate) (x : Fin k → Bool) (i : ℕ),
          evalVal ((gs ++ extra).foldl step (List.ofFn x)) (env.getD i (Sum.inl false)) =
          evalVal (gs.foldl step (List.ofFn x)) (env.getD i (Sum.inl false)) := by
        intro extra x i
        by_cases hi : i < env.length
        · have hmem : env.getD i (Sum.inl false) ∈ env := by
            rw [List.getD_eq_getElem _ _ hi]
            exact List.getElem_mem hi
          cases hv : env.getD i (Sum.inl false) with
          | inl b => rfl
          | inr j =>
            have hj : j < k + gs.length := hbound _ hmem j hv
            dsimp only [evalVal]
            rw [List.foldl_append, hfold_stable extra _ j (by rw [hfold_len]; simp; omega)]
        · rw [hgetD_of_le _ _ _ (by omega)]
      have hnew_eval : ∀ (op : GateOp) (inps : List ℕ) (x : Fin k → Bool),
          ((gs ++ [Gate.mk op inps]).foldl step (List.ofFn x)).getD (k + gs.length) false =
          op.eval (inps.map fun j => (gs.foldl step (List.ofFn x)).getD j false) := by
        intro op inps x
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [step]
        have hlenw : (gs.foldl step (List.ofFn x)).length = k + gs.length := by
          rw [hfold_len]; simp
        rw [← hlenw, hgetD_snoc_eq]
      have horig_step : ∀ (x : Fin k → Bool) (i : ℕ),
          ((orig ++ [g]).foldl step (List.ofFn (Function.update x p false))).getD i false =
          if i < k + orig.length then
            (orig.foldl step (List.ofFn (Function.update x p false))).getD i false
          else if i = k + orig.length then
            g.op.eval (g.inputs.map fun idx =>
              (orig.foldl step (List.ofFn (Function.update x p false))).getD idx false)
          else false := by
        intro x i
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [step]
        have hleno : (orig.foldl step (List.ofFn (Function.update x p false))).length =
            k + orig.length := by rw [hfold_len]; simp
        by_cases hlt : i < k + orig.length
        · simp only [hlt, ↓reduceIte]
          exact hgetD_snoc_lt _ _ _ i (by rw [hleno]; exact hlt)
        · simp only [hlt, ↓reduceIte]
          by_cases heq : i = k + orig.length
          · simp only [heq, ↓reduceIte]
            rw [← hleno, hgetD_snoc_eq]
          · simp only [heq, ↓reduceIte]
            exact hgetD_of_le _ _ _ (by
              simp only [List.length_append, List.length_cons, List.length_nil]
              change (orig.foldl step (List.ofFn (Function.update x p false))).length + 1 ≤ i
              rw [hleno]
              omega)
      have hpack_same : ∀ (v : Sum Bool ℕ),
          (∀ j, v = Sum.inr j → j < k + gs.length) →
          (∀ x, evalVal (gs.foldl step (List.ofFn x)) v =
            g.op.eval (g.inputs.map fun idx =>
              (orig.foldl step (List.ofFn (Function.update x p false))).getD idx false)) →
          (env ++ [v]).length = k + (orig ++ [g]).length ∧
          (env ++ [v]).getD p.val (Sum.inl false) = Sum.inl false ∧
          (∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g'.inputs.length ≤ 2) ∧
          (∀ u ∈ env ++ [v], ∀ j, u = Sum.inr j → j < k + gs.length) ∧
          (∀ (x : Fin k → Bool) (i : ℕ),
            evalVal (gs.foldl step (List.ofFn x)) ((env ++ [v]).getD i (Sum.inl false)) =
            ((orig ++ [g]).foldl step (List.ofFn (Function.update x p false))).getD i false) ∧
          gs.length ≤ gs.length + 1 ∧
          (p.val ∈ eff g → gs.length = gs.length) := by
        intro v hv_bd hv_ev
        refine ⟨by simp [henvlen]; omega,
          by rw [hgetD_snoc_lt env v _ p.val hp_lt, hpval],
          hgsfan, ?_, ?_, by omega, fun _ => rfl⟩
        · intro u hu j huj
          rcases List.mem_append.mp hu with hu1 | hu2
          · exact hbound u hu1 j huj
          · simp only [List.mem_singleton] at hu2
            exact hv_bd j (hu2 ▸ huj)
        · intro x i
          rw [horig_step x i]
          by_cases hlt : i < k + orig.length
          · simp only [hlt, ↓reduceIte]
            rw [hgetD_snoc_lt env v _ i (by omega), heval x i]
          · simp only [hlt, ↓reduceIte]
            by_cases heq : i = k + orig.length
            · simp only [heq, ↓reduceIte]
              rw [← henvlen, hgetD_snoc_eq, hv_ev x]
            · simp only [heq, ↓reduceIte]
              rw [hgetD_of_le _ _ _ (by simp [henvlen]; omega)]
      have hpack_add : ∀ (op : GateOp) (inps : List ℕ),
          op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
          inps.length ≤ 2 →
          (∀ x, op.eval (inps.map fun j => (gs.foldl step (List.ofFn x)).getD j false) =
            g.op.eval (g.inputs.map fun idx =>
              (orig.foldl step (List.ofFn (Function.update x p false))).getD idx false)) →
          (p.val ∉ eff g) →
          let gs' := gs ++ [Gate.mk op inps]
          let env' := env ++ [Sum.inr (k + gs.length)]
          env'.length = k + (orig ++ [g]).length ∧
          env'.getD p.val (Sum.inl false) = Sum.inl false ∧
          (∀ g' ∈ gs', g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g'.inputs.length ≤ 2) ∧
          (∀ u ∈ env', ∀ j, u = Sum.inr j → j < k + gs'.length) ∧
          (∀ (x : Fin k → Bool) (i : ℕ),
            evalVal (gs'.foldl step (List.ofFn x)) (env'.getD i (Sum.inl false)) =
            ((orig ++ [g]).foldl step (List.ofFn (Function.update x p false))).getD i false) ∧
          gs'.length ≤ gs.length + 1 ∧
          (p.val ∈ eff g → gs'.length = gs.length) := by
        intro op inps hop hinps hev_add hnotp
        refine ⟨by simp [henvlen]; omega,
          by rw [hgetD_snoc_lt env _ _ p.val hp_lt, hpval],
          ?_, ?_, ?_, by simp, fun hp => absurd hp hnotp⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with hg1 | hg2
          · exact hgsfan g' hg1
          · simp only [List.mem_singleton] at hg2
            subst hg2; exact ⟨hop, hinps⟩
        · intro u hu j huj
          rcases List.mem_append.mp hu with hu1 | hu2
          · have := hbound u hu1 j huj; simp; omega
          · simp only [List.mem_singleton] at hu2
            have hj : k + gs.length = j := Sum.inr.inj (hu2.symm.trans huj)
            simp; omega
        · intro x i
          rw [horig_step x i]
          by_cases hlt : i < k + orig.length
          · simp only [hlt, ↓reduceIte]
            rw [hgetD_snoc_lt env _ _ i (by omega), hstable_eval, heval x i]
          · simp only [hlt, ↓reduceIte]
            by_cases heq : i = k + orig.length
            · simp only [heq, ↓reduceIte]
              rw [← henvlen, hgetD_snoc_eq]
              dsimp only [evalVal]
              rw [hnew_eval, hev_add x]
            · simp only [heq, ↓reduceIte]
              rw [hgetD_of_le _ _ _ (by simp [henvlen]; omega)]
      have hlu_bd : ∀ (a j : ℕ), env.getD a (Sum.inl false) = Sum.inr j → j < k + gs.length := by
        intro a j haj
        by_cases ha : a < env.length
        · exact hbound _ (by rw [List.getD_eq_getElem _ _ ha]; exact List.getElem_mem ha) j haj
        · rw [hgetD_of_le _ _ _ (by omega)] at haj; exact absurd haj (by simp)
      have hne_an : GateOp.and ≠ GateOp.not := by intro h; exact GateOp.noConfusion h
      have hne_on : GateOp.or ≠ GateOp.not := by intro h; exact GateOp.noConfusion h
      have hne_oa : GateOp.or ≠ GateOp.and := by intro h; exact GateOp.noConfusion h
      rcases hop_cases hgop with hgop | hgop | hgop
      · cases hgi : g.inputs with
        | nil =>
          have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
            simp only [stepC, hgop, hgi, hne_an, ↓reduceIte]
          rw [hst]
          exact hpack_same (Sum.inl true) (by simp) (fun x => by
            rw [hgop, hgi, hev_and]; rfl)
        | cons a rest =>
          cases rest with
          | nil =>
            have hst : stepC (gs, env) g = (gs, env ++ [env.getD a (Sum.inl false)]) := by
              simp only [stepC, hgop, hgi, hne_an, ↓reduceIte]
            rw [hst]
            exact hpack_same (env.getD a (Sum.inl false)) (hlu_bd a) (fun x => by
              rw [hgop, hgi, hev_and]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, heval x a])
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              cases ha : env.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | false =>
                  have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl false]) := by
                    simp only [stepC, hgop, hgi, hne_an, ha, ↓reduceIte, Bool.false_eq_true]
                  rw [hst]
                  exact hpack_same (Sum.inl false) (by simp) (fun x => by
                    have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                    rw [hgop, hgi, hev_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                      Bool.and_true, ← h1, Bool.false_and])
                | true =>
                  cases hb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    cases bb with
                    | false =>
                      have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl false]) := by
                        simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte]
                      rw [hst]
                      exact hpack_same (Sum.inl false) (by simp) (fun x => by
                        have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2 ⊢
                        rw [hgop, hgi, hev_and]
                        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                          Bool.and_true, ← h2, Bool.and_false])
                    | true =>
                      have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
                        simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte]
                      rw [hst]
                      exact hpack_same (Sum.inl true) (by simp) (fun x => by
                        have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                        have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                        rw [hgop, hgi, hev_and]
                        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                          Bool.and_true, ← h1, ← h2])
                  | inr jb =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inr jb]) := by
                      simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte]
                    rw [hst]
                    exact hpack_same (Sum.inr jb) (fun j hj => hlu_bd b j (hb.trans hj)) (fun x => by
                      have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                      rw [hgop, hgi, hev_and]
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                        Bool.and_true, ← h1, ← h2, Bool.true_and])
              | inr ja =>
                cases hb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | false =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl false]) := by
                      simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte, Bool.false_eq_true]
                    rw [hst]
                    exact hpack_same (Sum.inl false) (by simp) (fun x => by
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2 ⊢
                      rw [hgop, hgi, hev_and]
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                        Bool.and_true, ← h2, Bool.and_false])
                  | true =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inr ja]) := by
                      simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte]
                    rw [hst]
                    exact hpack_same (Sum.inr ja) (fun j hj => hlu_bd a j (ha.trans hj)) (fun x => by
                      have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                      rw [hgop, hgi, hev_and]
                      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                        Bool.and_true, ← h1, ← h2])
                | inr jb =>
                  have hst : stepC (gs, env) g =
                      (gs ++ [Gate.mk GateOp.and [ja, jb]], env ++ [Sum.inr (k + gs.length)]) := by
                    simp only [stepC, hgop, hgi, hne_an, ha, hb, ↓reduceIte]
                  rw [hst]
                  apply hpack_add GateOp.and [ja, jb] (Or.inl rfl) (by simp)
                  · intro x
                    have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1
                    have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                    rw [hgop, hgi, hev_and, hev_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                      Bool.and_true, ← h1, ← h2]
                  · intro hp
                    rw [heff_and g hgop, hgi] at hp
                    simp only [List.take_succ_cons, List.take_zero, List.mem_cons,
                      List.not_mem_nil, or_false] at hp
                    rcases hp with rfl | rfl
                    · rw [hpval] at ha; exact absurd ha (by simp)
                    · rw [hpval] at hb; exact absurd hb (by simp)
            | cons c rest3 =>
              rw [hgi] at hglen; simp at hglen
      · cases hgi : g.inputs with
        | nil =>
          have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl false]) := by
            simp only [stepC, hgop, hgi, hne_on, hne_oa, ↓reduceIte]
          rw [hst]
          exact hpack_same (Sum.inl false) (by simp) (fun x => by
            rw [hgop, hgi, hev_or]; rfl)
        | cons a rest =>
          cases rest with
          | nil =>
            have hst : stepC (gs, env) g = (gs, env ++ [env.getD a (Sum.inl false)]) := by
              simp only [stepC, hgop, hgi, hne_on, hne_oa, ↓reduceIte]
            rw [hst]
            exact hpack_same (env.getD a (Sum.inl false)) (hlu_bd a) (fun x => by
              rw [hgop, hgi, hev_or]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, heval x a])
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              cases ha : env.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | true =>
                  have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
                    simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, ↓reduceIte]
                  rw [hst]
                  exact hpack_same (Sum.inl true) (by simp) (fun x => by
                    have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                    rw [hgop, hgi, hev_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                      Bool.or_false, ← h1, Bool.true_or])
                | false =>
                  cases hb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    cases bb with
                    | true =>
                      have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
                        simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte,
                          Bool.false_eq_true]
                      rw [hst]
                      exact hpack_same (Sum.inl true) (by simp) (fun x => by
                        have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2 ⊢
                        rw [hgop, hgi, hev_or]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                          Bool.or_false, ← h2, Bool.or_true])
                    | false =>
                      have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl false]) := by
                        simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte,
                          Bool.false_eq_true]
                      rw [hst]
                      exact hpack_same (Sum.inl false) (by simp) (fun x => by
                        have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                        have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                        rw [hgop, hgi, hev_or]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                          Bool.or_false, ← h1, ← h2])
                  | inr jb =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inr jb]) := by
                      simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte,
                        Bool.false_eq_true]
                    rw [hst]
                    exact hpack_same (Sum.inr jb) (fun j hj => hlu_bd b j (hb.trans hj)) (fun x => by
                      have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                      rw [hgop, hgi, hev_or]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                        Bool.or_false, ← h1, ← h2, Bool.false_or])
              | inr ja =>
                cases hb : env.getD b (Sum.inl false) with
                | inl bb =>
                  cases bb with
                  | true =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
                      simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte]
                    rw [hst]
                    exact hpack_same (Sum.inl true) (by simp) (fun x => by
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2 ⊢
                      rw [hgop, hgi, hev_or]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                        Bool.or_false, ← h2, Bool.or_true])
                  | false =>
                    have hst : stepC (gs, env) g = (gs, env ++ [Sum.inr ja]) := by
                      simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte,
                        Bool.false_eq_true]
                    rw [hst]
                    exact hpack_same (Sum.inr ja) (fun j hj => hlu_bd a j (ha.trans hj)) (fun x => by
                      have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
                      have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                      rw [hgop, hgi, hev_or]
                      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                        Bool.or_false, ← h1, ← h2])
                | inr jb =>
                  have hst : stepC (gs, env) g =
                      (gs ++ [Gate.mk GateOp.or [ja, jb]], env ++ [Sum.inr (k + gs.length)]) := by
                    simp only [stepC, hgop, hgi, hne_on, hne_oa, ha, hb, ↓reduceIte]
                  rw [hst]
                  apply hpack_add GateOp.or [ja, jb] (Or.inr (Or.inl rfl)) (by simp)
                  · intro x
                    have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1
                    have h2 := heval x b; rw [hb] at h2; dsimp only [evalVal] at h2
                    rw [hgop, hgi, hev_or, hev_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                      Bool.or_false, ← h1, ← h2]
                  · intro hp
                    rw [heff_or g hgop, hgi] at hp
                    simp only [List.take_succ_cons, List.take_zero, List.mem_cons,
                      List.not_mem_nil, or_false] at hp
                    rcases hp with rfl | rfl
                    · rw [hpval] at ha; exact absurd ha (by simp)
                    · rw [hpval] at hb; exact absurd hb (by simp)
            | cons c rest3 =>
              rw [hgi] at hglen; simp at hglen
      · cases hgi : g.inputs with
        | nil =>
          have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl true]) := by
            simp only [stepC, hgop, hgi, ↓reduceIte]
          rw [hst]
          exact hpack_same (Sum.inl true) (by simp) (fun x => by
            rw [hgop, hgi, hev_not]; rfl)
        | cons a rest =>
          cases ha : env.getD a (Sum.inl false) with
          | inl ba =>
            have hst : stepC (gs, env) g = (gs, env ++ [Sum.inl (!ba)]) := by
              simp only [stepC, hgop, hgi, ha, ↓reduceIte]
            rw [hst]
            exact hpack_same (Sum.inl (!ba)) (by simp) (fun x => by
              have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1 ⊢
              rw [hgop, hgi, hev_not]
              simp only [List.map_cons, List.headD_cons, ← h1])
          | inr ja =>
            have hst : stepC (gs, env) g =
                (gs ++ [Gate.mk GateOp.not [ja]], env ++ [Sum.inr (k + gs.length)]) := by
              simp only [stepC, hgop, hgi, ha, ↓reduceIte]
            rw [hst]
            apply hpack_add GateOp.not [ja] (Or.inr (Or.inr rfl)) (by simp)
            · intro x
              have h1 := heval x a; rw [ha] at h1; dsimp only [evalVal] at h1
              rw [hgop, hgi, hev_not, hev_not]
              simp only [List.map_cons, List.headD_cons, ← h1]
            · intro hp
              rw [heff_not g hgop, hgi] at hp
              simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hp
              subst hp
              rw [hpval] at ha; exact absurd ha (by simp)
    let initEnv : List (Sum Bool ℕ) :=
      List.ofFn (fun i : Fin k => if i = p then Sum.inl false else Sum.inr i.val)
    have hfoldC : ∀ (rem orig : List Gate) (st : List Gate × List (Sum Bool ℕ)),
        (∀ g ∈ rem, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) →
        st.2.length = k + orig.length →
        st.2.getD p.val (Sum.inl false) = Sum.inl false →
        (∀ g' ∈ st.1, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g'.inputs.length ≤ 2) →
        (∀ v ∈ st.2, ∀ j, v = Sum.inr j → j < k + st.1.length) →
        (∀ (x : Fin k → Bool) (i : ℕ),
          evalVal (st.1.foldl step (List.ofFn x)) (st.2.getD i (Sum.inl false)) =
          (orig.foldl step (List.ofFn (Function.update x p false))).getD i false) →
        let st' := rem.foldl stepC st
        (∀ g' ∈ st'.1, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g'.inputs.length ≤ 2) ∧
        (∀ (x : Fin k → Bool) (i : ℕ),
          evalVal (st'.1.foldl step (List.ofFn x)) (st'.2.getD i (Sum.inl false)) =
          ((orig ++ rem).foldl step (List.ofFn (Function.update x p false))).getD i false) ∧
        st'.1.length ≤ st.1.length + rem.length ∧
        ((∃ g ∈ rem, p.val ∈ eff g) → st'.1.length + 1 ≤ st.1.length + rem.length) := by
      intro rem
      induction rem with
      | nil =>
        intro orig st _ _ _ hgsfan _ heval
        refine ⟨hgsfan, ?_, by simp, by simp⟩
        intro x i; simpa using heval x i
      | cons g rem ih =>
        intro orig st hremfan henvlen hpval hgsfan hbound heval
        have hgfan := hremfan g List.mem_cons_self
        have hstep := hstepC_props st g orig hgfan.1 hgfan.2 henvlen hpval hgsfan hbound heval
        rcases hstep with ⟨hl', hp', hfan', hbd', hev', hsz', hhit'⟩
        have hrec := ih (orig ++ [g]) (stepC st g)
          (fun g' hg' => hremfan g' (List.mem_cons_of_mem g hg'))
          hl' hp' hfan' hbd' hev'
        rcases hrec with ⟨hfanf, hevf, hszf, hhitf⟩
        refine ⟨hfanf, ?_, ?_, ?_⟩
        · intro x i
          have happ : orig ++ (g :: rem) = (orig ++ [g]) ++ rem := by simp
          rw [happ]
          exact hevf x i
        · simp only [List.foldl_cons, List.length_cons]; omega
        · rintro ⟨g', hg', hpg'⟩
          simp only [List.foldl_cons, List.length_cons]
          rcases List.mem_cons.mp hg' with rfl | hg'rem
          · have heq0 := hhit' hpg'
            omega
          · have hlt := hhitf ⟨g', hg'rem, hpg'⟩
            omega
    have hinit_len : initEnv.length = k + ([] : List Gate).length := by simp [initEnv]
    have hinit_p : initEnv.getD p.val (Sum.inl false) = Sum.inl false := by
      simp [initEnv, List.getD_eq_getElem?_getD, p.isLt]
    have hinit_bd : ∀ v ∈ initEnv, ∀ j, v = Sum.inr j → j < k + ([] : List Gate).length := by
      intro v hv j hvj
      simp only [initEnv, List.mem_ofFn] at hv
      rcases hv with ⟨i, rfl⟩
      by_cases hip : i = p
      · simp [hip] at hvj
      · simp only [hip, ↓reduceIte, Sum.inr.injEq] at hvj
        have := i.isLt; simp; omega
    have hinit_eval : ∀ (x : Fin k → Bool) (i : ℕ),
        evalVal (([] : List Gate).foldl step (List.ofFn x)) (initEnv.getD i (Sum.inl false)) =
        (([] : List Gate).foldl step (List.ofFn (Function.update x p false))).getD i false := by
      intro x i
      simp only [List.foldl_nil]
      by_cases hi : i < k
      · simp only [initEnv, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some]
        by_cases hip : (⟨i, hi⟩ : Fin k) = p
        · simp [hip, evalVal]
        · simp [hip, evalVal, List.getD_eq_getElem?_getD, hi]
      · rw [hgetD_of_le initEnv _ i (by simp [initEnv]; omega),
            hgetD_of_le _ _ i (by simp; omega)]
    have hres := hfoldC C.gates [] ([], initEnv) hfanC hinit_len hinit_p
      (by simp) hinit_bd hinit_eval
    rcases hres with ⟨hfan', heval', _, hsz_red⟩
    have hsz_lt : (C.gates.foldl stepC ([], initEnv)).1.length + 1 ≤ r := by
      have h1 := hsz_red hex_read
      simp only [List.length_nil, zero_add] at h1
      change C.gates.length ≤ r at hsizeC
      omega
    cases hout : (C.gates.foldl stepC ([], initEnv)).2.getD C.output (Sum.inl false) with
    | inl b =>
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := heval' x C.output
      have hy := heval' y C.output
      rw [hout] at hx hy
      simp only [List.nil_append, evalVal] at hx hy
      have h1 : h (Function.update x p false) = b := by rw [← hevalC, hceval]; exact hx.symm
      have h2 : h (Function.update y p false) = b := by rw [← hevalC, hceval]; exact hy.symm
      exact absurd (h1.trans h2.symm) hxy
    | inr outW =>
      refine ⟨(C.gates.foldl stepC ([], initEnv)).1.length, hsz_lt,
        ⟨⟨(C.gates.foldl stepC ([], initEnv)).1, outW⟩, hfan', le_rfl, fun x => ?_⟩⟩
      have hx := heval' x C.output
      rw [hout] at hx
      simp only [List.nil_append, evalVal] at hx
      dsimp only
      rw [← hevalC, hceval, hceval]
      exact hx
  have strip : ∀ (B : Finset (Fin n)) (h : (Fin n → Bool) → Bool) (r : ℕ),
      (∀ u v, G.Adj u v → u ∉ B) →
      (∀ x, h x = true ↔ (∃ a ∈ B, x a = true) ∨
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      HasCircuitSize n h r →
      ∃ (t : ℕ) (g : (Fin n → Bool) → Bool), t + B.card ≤ r ∧
        HasCircuitSize n g t ∧
        (∀ x, g x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro h r _ hsp hsm
      exact ⟨r, h, by simp, hsm, by simpa using hsp⟩
    | @insert a B ha ih =>
      intro h r hisoB hsp hsm
      have hzero : h (fun _ => false) = false := by
        have hn : ¬ h (fun _ => false) = true := by rw [hsp]; simp
        cases he : h (fun _ => false) <;> simp_all
      have hdep : ∃ x, h (Function.update x a (!x a)) ≠ h x := by
        refine ⟨fun _ => false, ?_⟩
        have ht : h (Function.update (fun _ => false) a true) = true :=
          (hsp _).mpr (Or.inl ⟨a, by simp, by simp⟩)
        simp [hzero, ht]
      have hnc : ∃ x y, h (Function.update x a false) ≠ h (Function.update y a false) := by
        obtain ⟨u, v, huv⟩ := hedge
        have hua : u ≠ a := fun e => hisoB u v huv (by simp [e])
        have hva : v ≠ a := fun e => hisoB v u huv.symm (by simp [e])
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have hz : Function.update (fun _ : Fin n => false) a false = (fun _ => false) := by
          funext i; by_cases hi : i = a <;> simp [hi, Function.update_of_ne]
        have ht : h (Function.update (fun _ => true) a false) = true :=
          (hsp _).mpr (Or.inr ⟨u, v, huv, by simp [Function.update_of_ne hua],
            by simp [Function.update_of_ne hva]⟩)
        rw [hz, hzero, ht]; decide
      obtain ⟨r', hr', hsm'⟩ := elim n h a r hdep hnc hsm
      have hiso' : ∀ u v, G.Adj u v → u ∉ B :=
        fun u v huv hu => hisoB u v huv (Finset.mem_insert_of_mem hu)
      have hsp' : ∀ x, h (Function.update x a false) = true ↔
          (∃ b ∈ B, x b = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        intro x
        rw [hsp]
        apply or_congr
        · constructor
          · rintro ⟨b, hb, hx⟩
            have hba : b ≠ a := by rintro rfl; simp at hx
            exact ⟨b, (Finset.mem_insert.mp hb).resolve_left hba,
              by simpa [Function.update_of_ne hba] using hx⟩
          · rintro ⟨b, hb, hx⟩
            have hba : b ≠ a := fun e => ha (e ▸ hb)
            exact ⟨b, Finset.mem_insert_of_mem hb, by simpa [Function.update_of_ne hba] using hx⟩
        · constructor
          · rintro ⟨u, v, huv, hu, hv⟩
            have hua : u ≠ a := fun e => hisoB u v huv (by simp [e])
            have hva : v ≠ a := fun e => hisoB v u huv.symm (by simp [e])
            exact ⟨u, v, huv, by simpa [Function.update_of_ne hua] using hu,
              by simpa [Function.update_of_ne hva] using hv⟩
          · rintro ⟨u, v, huv, hu, hv⟩
            have hua : u ≠ a := fun e => hisoB u v huv (by simp [e])
            have hva : v ≠ a := fun e => hisoB v u huv.symm (by simp [e])
            exact ⟨u, v, huv, by simpa [Function.update_of_ne hua] using hu,
              by simpa [Function.update_of_ne hva] using hv⟩
      obtain ⟨t, g, ht, hg, hgsp⟩ := ih _ r' hiso' hsp' hsm'
      refine ⟨t, g, ?_, hg, hgsp⟩
      rw [Finset.card_insert_of_notMem ha]
      omega
  obtain ⟨t, gE, ht, hgE, hgEsp⟩ := strip A f s hiso hspec hs
  obtain ⟨u0, v0, huv0⟩ := hedge
  let U := {v : Fin n // v ∉ A}
  let m := Fintype.card U
  let emb : Fin m ↪ Fin n :=
    ⟨fun v => ((Fintype.equivFin U).symm v).val,
      fun _ _ h => (Fintype.equivFin U).symm.injective (Subtype.ext h)⟩
  let back (i : Fin n) : Fin m :=
    if hi : i ∉ A then Fintype.equivFin U ⟨i, hi⟩ else Fintype.equivFin U ⟨u0, hiso u0 v0 huv0⟩
  have hinU (v : Fin m) : emb v ∉ A := ((Fintype.equivFin U).symm v).property
  have hsecBack (v : Fin m) : back (emb v) = v := by
    simp only [back, dite_eq_left (hinU v)]
    exact (Fintype.equivFin U).apply_symm_apply v
  have hsecEmb (i : Fin n) (hi : i ∉ A) : emb (back i) = i := by
    change ((Fintype.equivFin U).symm (back i)).val = i
    simp [back, hi]
  let H : SimpleGraph (Fin m) := G.comap emb
  let hom : H →g G := ⟨emb, fun h => h⟩
  have hcolH : H.Colorable 2 := SimpleGraph.Colorable.of_hom hom hcol
  have hdegH (v : Fin m) : (H.neighborSet v).ncard = 3 := by
    rw [← hdeg (emb v) (hinU v)]
    apply Set.ncard_congr (fun q _ => emb q) (fun _ h => h)
      (fun _ _ _ _ h => emb.injective h)
    intro z hz
    change G.Adj (emb v) z at hz
    have rev := hsecEmb z (hiso _ _ hz.symm)
    refine ⟨back z, ?_, rev⟩
    change G.Adj (emb v) (emb (back z))
    rwa [rev]
  have hgirthH7 (v : Fin m) (w : H.Walk v v) (hcyc : w.IsCycle) : 7 ≤ w.length := by
    simpa using hgirth (emb v) (w.map hom) (hcyc.map emb.injective)
  have hgirthH8 (v : Fin m) (w : H.Walk v v) (hcyc : w.IsCycle) : 8 ≤ w.length := by
    obtain ⟨c⟩ := hcolH
    have heven_walk : ∀ {a b : Fin m} (p : H.Walk a b), Even p.length ↔ c a = c b := by
      intro a b p
      induction p with
      | nil => simp
      | @cons a d b had p' ih =>
        simp only [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih]
        have hne : c a ≠ c d := c.valid had
        have ha2 := (c a).isLt
        have hd2 := (c d).isLt
        have hb2 := (c b).isLt
        constructor
        · intro h
          apply Fin.ext
          have h1 : (c a).val ≠ (c d).val := fun e => hne (Fin.ext e)
          have h2 : (c d).val ≠ (c b).val := fun e => h (Fin.ext e)
          omega
        · intro h heq
          exact hne (h.trans heq.symm)
    have hev : Even w.length := (heven_walk w).mpr rfl
    have h7 := hgirthH7 v w hcyc
    rcases hev with ⟨q, hq⟩
    omega
  have hedgeH : ∃ u v, H.Adj u v := by
    refine ⟨back u0, back v0, ?_⟩
    change G.Adj (emb (back u0)) (emb (back v0))
    rwa [hsecEmb _ (hiso _ _ huv0), hsecEmb _ (hiso _ _ huv0.symm)]
  let fH : (Fin m → Bool) → Bool := fun y => gE (fun i => y (back i))
  have hfHsp (y : Fin m → Bool) :
      fH y = true ↔ ∃ u v, H.Adj u v ∧ y u = true ∧ y v = true := by
    dsimp only [fH]
    rw [hgEsp]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨back i, back j, ?_, hi, hj⟩
      change G.Adj (emb (back i)) (emb (back j))
      rwa [hsecEmb _ (hiso _ _ hij), hsecEmb _ (hiso _ _ hij.symm)]
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨emb u, emb v, huv, by rwa [hsecBack], by rwa [hsecBack]⟩
  have hrewire : HasCircuitSize m fH t := by
    obtain ⟨C, hfanC, hsizeC, hevalC⟩ := hgE
    let remap (i : ℕ) : ℕ := if hi : i < n then (back ⟨i, hi⟩).val else m + (i - n)
    let C' : Circuit := ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map remap), remap C.output⟩
    refine ⟨C', ?_, ?_, fun y => ?_⟩
    · intro g' hg'
      rcases List.mem_map.mp hg' with ⟨g, hg, rfl⟩
      have := hfanC g hg
      exact ⟨this.1, by simpa using this.2⟩
    · change C'.gates.length ≤ t
      change C.gates.length ≤ t at hsizeC
      simpa [C'] using hsizeC
    · have hsim : ∀ (gs : List Gate) (w1 w2 : List Bool),
          w1.length = n + (w1.length - n) →
          w2.length = m + (w1.length - n) →
          n ≤ w1.length →
          (∀ i, w2.getD (remap i) false = w1.getD i false) →
          ((gs.map fun g => Gate.mk g.op (g.inputs.map remap)).foldl step w2).length =
            m + ((gs.foldl step w1).length - n) ∧
          n ≤ (gs.foldl step w1).length ∧
          ∀ i, ((gs.map fun g => Gate.mk g.op (g.inputs.map remap)).foldl step w2).getD (remap i) false =
            (gs.foldl step w1).getD i false := by
        intro gs
        induction gs with
        | nil =>
          intro w1 w2 _ hw2 hn hagr
          exact ⟨hw2, hn, hagr⟩
        | cons g gs ih =>
          intro w1 w2 hw1 hw2 hn hagr
          simp only [List.map_cons, List.foldl_cons]
          have hmap : ((g.inputs.map remap).map fun i => w2.getD i false) =
              (g.inputs.map fun i => w1.getD i false) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro i _
            exact hagr i
          have hlen1 : (step w1 g).length = w1.length + 1 := by simp [step]
          have hlen2 : (step w2 (Gate.mk g.op (g.inputs.map remap))).length = w2.length + 1 := by
            simp [step]
          apply ih (step w1 g) (step w2 (Gate.mk g.op (g.inputs.map remap)))
          · omega
          · omega
          · omega
          · intro i
            dsimp only [step]
            rw [hmap]
            by_cases hi : i < w1.length
            · have hri : remap i < w2.length := by
                dsimp only [remap]
                split_ifs with hlt
                · have := (back ⟨i, hlt⟩).isLt; omega
                · omega
              rw [hgetD_snoc_lt w2 _ _ _ hri, hgetD_snoc_lt w1 _ _ _ hi, hagr i]
            · by_cases heq : i = w1.length
              · subst heq
                have hri : remap w1.length = w2.length := by
                  dsimp only [remap]
                  rw [dif_neg (by omega)]; omega
                rw [hri, hgetD_snoc_eq w2, hgetD_snoc_eq w1]
              · have hri : w2.length + 1 ≤ remap i := by
                  dsimp only [remap]
                  rw [dif_neg (by omega)]; omega
                rw [hgetD_of_le _ _ _ (by simp; omega), hgetD_of_le _ _ _ (by simp; omega)]
      have hbase := (hsim C.gates (List.ofFn (fun i => y (back i))) (List.ofFn y)
        (by simp) (by simp) (by simp) (fun i => by
          by_cases hi : i < n
          · dsimp only [remap]
            rw [dif_pos hi]
            simp [List.getD_eq_getElem?_getD, hi, (back ⟨i, hi⟩).isLt]
          · dsimp only [remap]
            rw [dif_neg hi]
            have h1 : (List.ofFn y).getD (m + (i - n)) false = false :=
              hgetD_of_le _ _ _ (by simp only [List.length_ofFn]; omega)
            have h2 : (List.ofFn (fun i => y (back i))).getD i false = false :=
              hgetD_of_le _ _ _ (by simp only [List.length_ofFn]; omega)
            rw [h1, h2])).2.2 C.output
      dsimp only [fH]
      rw [← hevalC, hceval, hceval]
      exact hbase
  let _ : DecidableRel G.Adj := Classical.decRel _
  have hdeg_in : ∀ i ∈ A, G.degree i = 0 := by
    intro i hi
    exact (G.degree_eq_zero i).2 (fun j hij => hiso i j hij hi)
  have hdeg_out : ∀ i ∈ Aᶜ, G.degree i = 3 := by
    intro i hi
    rw [← G.ncard_neighborSet]
    exact hdeg i (Finset.mem_compl.1 hi)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl hdeg_in, Finset.sum_congr rfl hdeg_out] at hsum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at hsum
  have hedgeCount : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcards : m = (Finset.univ \ A).card := by
    change Fintype.card {v : Fin n // v ∉ A} = _
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp
  have hcompl : Aᶜ = Finset.univ \ A := by ext v; simp
  rw [hcompl, ← hcards, ← hedgeCount] at hsum
  have hevenM : Even m := by
    refine ⟨m / 2, ?_⟩
    omega
  have hexM : ∃ k, HasCircuitSize m fH k := ⟨t, hrewire⟩
  let sMin := Nat.find hexM
  have hsMin_le : sMin ≤ t := Nat.find_min' hexM hrewire
  obtain ⟨C, hfanC, hsizeC, hevalC⟩ := Nat.find_spec hexM
  have hcfunC : circuitFun m C = fH := funext hevalC
  have hminC : IsMinimalCircuit m C := by
    refine ⟨hfanC, fun D hfanD hDeq => ?_⟩
    have hD : HasCircuitSize m fH D.size := ⟨D, hfanD, le_rfl, fun x => by
      have := congrFun hDeq x; rw [hcfunC] at this; exact this⟩
    have := Nat.find_min' hexM hD
    omega
  have hCsp : ∀ x, circuitFun m C x = true ↔ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro x; rw [hcfunC]; exact hfHsp x
  have hmain : 2 * m ≤ C.size + 1 := by
    by_cases hmono : Monotone2 C
    · exact monotone m H C hevenM hcolH hdegH hgirthH8 hedgeH hminC hmono hCsp
    · have hhasNot : ∃ g ∈ C.gates, g.op = GateOp.not := by
        by_contra hnoNot
        push Not at hnoNot
        apply hmono
        intro g hg
        have hfg := hfanC g hg
        refine ⟨?_, hfg.2⟩
        rcases hop_cases hfg.1 with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd h3 (hnoNot g hg)
      by_contra hlt
      push Not at hlt
      let slots : List ℕ := C.output :: C.gates.flatMap eff
      have hgate_live : ∀ j : Fin C.size, 1 ≤ slots.count (m + j.val) := by
        intro j
        apply List.count_pos_iff.mpr
        by_contra hdead
        have hout_ne : C.output ≠ m + j.val := fun e => hdead (by simp [slots, e])
        have hno_eff : ∀ g ∈ C.gates, m + j.val ∉ eff g := fun g hg hi =>
          hdead (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))
        let dropIdx (w : ℕ) : ℕ := if w < m + j.val then w else w - 1
        let pre : List Gate := C.gates.take j.val
        let gj : Gate := C.gates[j.val]'j.isLt
        let post : List Gate := C.gates.drop (j.val + 1)
        have hpre_len : pre.length = j.val := List.length_take_of_le (Nat.le_of_lt j.isLt)
        have hsplit : C.gates = pre ++ gj :: post := by
          apply List.ext_getElem
          · simp only [List.length_append, List.length_cons, hpre_len, post, List.length_drop]
            have hjlt : j.val < C.gates.length := j.isLt
            omega
          · intro idx h1 h2
            by_cases hlt : idx < j.val
            · rw [List.getElem_append_left (by omega : idx < pre.length)]
              simp [pre]
            · by_cases heq : idx = j.val
              · subst heq
                rw [List.getElem_append_right (by omega : pre.length ≤ j.val)]
                simp only [hpre_len, Nat.sub_self, List.getElem_cons_zero, gj]
                rfl
              · rw [List.getElem_append_right (by omega : pre.length ≤ idx)]
                have hsub : idx - pre.length = (idx - j.val - 1) + 1 := by omega
                simp only [hsub, List.getElem_cons_succ, post, List.getElem_drop]
                congr 1
                omega
        let pre' : List Gate := pre.map fun g => Gate.mk g.op ((eff g).map dropIdx)
        let post' : List Gate := post.map fun g => Gate.mk g.op ((eff g).map dropIdx)
        let C' : Circuit := ⟨pre' ++ post', dropIdx C.output⟩
        have hfanC' : FanInTwo C' := by
          intro g' hg'
          have hmem : g' ∈ (pre ++ post).map (fun g => Gate.mk g.op ((eff g).map dropIdx)) := by
            simpa [C', pre', post', List.map_append] using hg'
          rcases List.mem_map.mp hmem with ⟨g, hg, rfl⟩
          have hgC : g ∈ C.gates := by
            rw [hsplit]
            rcases List.mem_append.mp hg with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
          have hfg := hfanC g hgC
          exact ⟨hfg.1, by simpa using heff_len g hfg.1 hfg.2⟩
        have hszC' : C'.size < C.size := by
          change (pre' ++ post').length < C.gates.length
          have hlen_split : C.gates.length = pre.length + 1 + post.length := by
            conv_lhs => rw [hsplit]
            simp; omega
          simp only [List.length_append, pre', post', List.length_map]
          omega
        have hsim_pre : ∀ (gs : List Gate) (w : List Bool),
            w.length + gs.length ≤ m + j.val →
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
              g.inputs.length ≤ 2 ∧ m + j.val ∉ eff g) →
            ((gs.map fun g => Gate.mk g.op ((eff g).map dropIdx)).foldl step w) =
            gs.foldl step w := by
          intro gs
          induction gs with
          | nil => intro w _ _; rfl
          | cons g gs ih =>
            intro w hwl hgs
            simp only [List.map_cons, List.foldl_cons]
            have hg := hgs g List.mem_cons_self
            have hmap : ((eff g).map dropIdx).map (fun i => w.getD i false) =
                (eff g).map (fun i => w.getD i false) := by
              rw [List.map_map]
              apply List.map_congr_left
              intro i hi
              dsimp only [Function.comp_apply, dropIdx]
              by_cases hilt : i < m + j.val
              · simp only [hilt, ↓reduceIte]
              · simp only [hilt, ↓reduceIte]
                have hine : i ≠ m + j.val := fun e => hg.2.2 (e ▸ hi)
                have hgt : m + j.val < i := by omega
                have hle1 : w.length ≤ i - 1 := by simp at hwl; omega
                have hle2 : w.length ≤ i := by omega
                rw [hgetD_of_le _ _ _ hle1, hgetD_of_le _ _ _ hle2]
            have hstep_eq : step w (Gate.mk g.op ((eff g).map dropIdx)) = step w g := by
              dsimp only [step]
              rw [hmap, heff_eval g w hg.1 hg.2.1]
            rw [hstep_eq]
            apply ih (step w g)
            · simp [step] at hwl ⊢; omega
            · intro g' hg'; exact hgs g' (List.mem_cons_of_mem g hg')
        have hsim_post : ∀ (gs : List Gate) (w1 w2 : List Bool),
            w1.length = w2.length + 1 →
            m + j.val ≤ w2.length →
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
              g.inputs.length ≤ 2 ∧ m + j.val ∉ eff g) →
            (∀ i, i ≠ m + j.val → w2.getD (dropIdx i) false = w1.getD i false) →
            (gs.foldl step w1).length =
              ((gs.map fun g => Gate.mk g.op ((eff g).map dropIdx)).foldl step w2).length + 1 ∧
            ∀ i, i ≠ m + j.val →
              ((gs.map fun g => Gate.mk g.op ((eff g).map dropIdx)).foldl step w2).getD (dropIdx i) false =
              (gs.foldl step w1).getD i false := by
          intro gs
          induction gs with
          | nil => intro w1 w2 hl _ _ hagr; exact ⟨hl, hagr⟩
          | cons g gs ih =>
            intro w1 w2 hl hmj hgs hagr
            simp only [List.map_cons, List.foldl_cons]
            have hg := hgs g List.mem_cons_self
            have hmap : ((eff g).map dropIdx).map (fun i => w2.getD i false) =
                (eff g).map (fun i => w1.getD i false) := by
              rw [List.map_map]
              apply List.map_congr_left
              intro i hi
              exact hagr i (fun e => hg.2.2 (e ▸ hi))
            have hev : g.op.eval (((eff g).map dropIdx).map fun i => w2.getD i false) =
                g.op.eval (g.inputs.map fun i => w1.getD i false) := by
              rw [hmap, ← heff_eval g w1 hg.1 hg.2.1]
            apply ih (step w1 g) (step w2 (Gate.mk g.op ((eff g).map dropIdx)))
            · simp [step]; omega
            · simp [step]; omega
            · intro g' hg'; exact hgs g' (List.mem_cons_of_mem g hg')
            · intro i hine
              dsimp only [step]
              rw [hev]
              by_cases hlt : i < m + j.val
              · have hdi : dropIdx i = i := by simp [dropIdx, hlt]
                rw [hdi, hgetD_snoc_lt w2 _ _ i (by omega), hgetD_snoc_lt w1 _ _ i (by omega)]
                simpa [hdi] using hagr i hine
              · have hgt : m + j.val < i := by omega
                have hdi : dropIdx i = i - 1 := by simp [dropIdx, hlt]
                rw [hdi]
                by_cases hilt1 : i < w1.length
                · rw [hgetD_snoc_lt w2 _ _ (i - 1) (by omega), hgetD_snoc_lt w1 _ _ i hilt1]
                  simpa [hdi] using hagr i hine
                · by_cases heq1 : i = w1.length
                  · have heq2 : i - 1 = w2.length := by omega
                    rw [heq2, heq1, hgetD_snoc_eq w2, hgetD_snoc_eq w1]
                  · rw [hgetD_of_le _ _ _ (by simp; omega), hgetD_of_le _ _ _ (by simp; omega)]
        have hcfunC' : circuitFun m C' = circuitFun m C := by
          funext x
          rw [hcfun_eq, hcfun_eq]
          dsimp only [C']
          rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons]
          have hpre_eq : pre'.foldl step (List.ofFn x) = pre.foldl step (List.ofFn x) := by
            apply hsim_pre pre (List.ofFn x)
            · simp [hpre_len]
            · intro g hg
              have hgC : g ∈ C.gates := by rw [hsplit]; exact List.mem_append_left _ hg
              exact ⟨(hfanC g hgC).1, (hfanC g hgC).2, hno_eff g hgC⟩
          rw [hpre_eq]
          let w0 := pre.foldl step (List.ofFn x)
          have hw0_len : w0.length = m + j.val := by
            dsimp only [w0]; rw [hfold_len]; simp [hpre_len]
          have hpost_eq := (hsim_post post (step w0 gj) w0
            (by simp [step]) (by omega)
            (fun g hg => by
              have hgC : g ∈ C.gates := by
                rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
              exact ⟨(hfanC g hgC).1, (hfanC g hgC).2, hno_eff g hgC⟩)
            (fun i hine => by
              by_cases hlt : i < m + j.val
              · have hdi : dropIdx i = i := by simp [dropIdx, hlt]
                rw [hdi]; dsimp only [step]; rw [hgetD_snoc_lt w0 _ _ i (by omega)]
              · have hdi : dropIdx i = i - 1 := by simp [dropIdx, hlt]
                rw [hdi, hgetD_of_le w0 _ (i - 1) (by omega),
                  hgetD_of_le (step w0 gj) _ i (by simp [step]; omega)])).2 C.output hout_ne
          exact hpost_eq
        have hle := hminC.2 C' hfanC' hcfunC'
        omega
      have hinp_live : ∀ v : Fin m, 1 ≤ slots.count v.val ∧ C.output ≠ v.val := by
        intro v
        have hv_out : C.output ≠ v.val := by
          intro hout
          let xv : Fin m → Bool := fun i => decide (i = v)
          have h1 : circuitFun m C xv = true := by
            rw [hcfun_eq, hout, hfold_stable C.gates _ v.val (by simp)]
            simp [xv, List.getD_eq_getElem?_getD, v.isLt]
          rcases (hCsp xv).mp h1 with ⟨a, b, hab, ha, hb⟩
          simp only [xv, decide_eq_true_eq] at ha hb
          subst ha; subst hb
          exact H.loopless.irrefl _ hab
        refine ⟨?_, hv_out⟩
        apply List.count_pos_iff.mpr
        by_contra hnv
        have hno_eff : ∀ g ∈ C.gates, v.val ∉ eff g := fun g hg hi =>
          hnv (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))
        have hne_nb : (H.neighborSet v).Nonempty := by
          apply Set.nonempty_of_ncard_ne_zero
          rw [hdegH v]; decide
        obtain ⟨u, huv⟩ := hne_nb
        let xu : Fin m → Bool := fun i => decide (i = u)
        let xuv : Fin m → Bool := Function.update xu v true
        have hagr := (hwires_agree C.gates v.val (List.ofFn xu) (List.ofFn xuv)
          (by simp) (by simp) hfanC (by
            intro i hiv
            by_cases hi : i < m
            · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte]
              have hne : (⟨i, hi⟩ : Fin m) ≠ v := fun e => hiv (congrArg Fin.val e)
              simp [xuv, Function.update_of_ne hne]
            · rw [hgetD_of_le _ _ _ (by simp; omega), hgetD_of_le _ _ _ (by simp; omega)])
          hno_eff).2 C.output hv_out
        have hfxu : circuitFun m C xu = false := by
          cases he : circuitFun m C xu with
          | false => rfl
          | true =>
            rcases (hCsp xu).mp he with ⟨a, b, hab, ha, hb⟩
            simp only [xu, decide_eq_true_eq] at ha hb
            subst ha; subst hb
            exact absurd hab (H.loopless.irrefl _)
        have hfxuv : circuitFun m C xuv = true := by
          apply (hCsp xuv).mpr
          have hvu : u ≠ v := fun e => H.loopless.irrefl v (e ▸ huv)
          exact ⟨v, u, huv, by simp [xuv], by simp [xuv, xu, Function.update_of_ne hvu]⟩
        have heq : circuitFun m C xu = circuitFun m C xuv := hagr
        rw [hfxu, hfxuv] at heq
        exact absurd heq (by decide)
      have hcount_sum_le : ∀ (l : List ℕ) (T : Finset ℕ),
          T.sum (fun a => l.count a) ≤ l.length := by
        intro l
        induction l with
        | nil => intro T; simp
        | cons x xs ih =>
          intro T
          have hstep_sum : T.sum (fun a => (x :: xs).count a) =
              T.sum (fun a => xs.count a) + (if x ∈ T then 1 else 0) := by
            have hpt : ∀ a ∈ T, (x :: xs).count a = xs.count a + (if a = x then 1 else 0) := by
              intro a _
              rw [List.count_cons]
              by_cases hax : a = x
              · subst hax; simp
              · simp [beq_false_of_ne (Ne.symm hax), hax]
            rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_ite_eq']
          rw [hstep_sum, List.length_cons]
          have := ih T
          split_ifs <;> omega
      have hbin_read_once : ∃ v : Fin m, slots.count v.val = 1 ∧
          ∃ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
            g.inputs.length = 2 ∧ v.val ∈ g.inputs := by
        by_contra hno_bin
        push Not at hno_bin
        let S1 : Finset (Fin m) := Finset.univ.filter (fun v => slots.count v.val = 1)
        have hpick : ∀ v : Fin m, v ∈ S1 →
            ∃ j : Fin C.size, eff (C.gates[j.val]'j.isLt) = [v.val] := by
          intro v hvS1
          have hc1 : slots.count v.val = 1 := (Finset.mem_filter.mp hvS1).2
          have hmem : v.val ∈ slots := List.count_pos_iff.mp (by omega)
          rcases List.mem_cons.mp hmem with hout | hflat
          · exact absurd hout.symm (hinp_live v).2
          · rcases List.mem_flatMap.mp hflat with ⟨g, hg, hvg⟩
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
            refine ⟨⟨j, hj⟩, ?_⟩
            have hfg := hfanC _ hg
            have helen : (eff C.gates[j]).length ≤ 1 := by
              rcases hop_cases hfg.1 with hop | hop | hop
              · have heff_eq : eff C.gates[j] = C.gates[j].inputs := by
                  rw [heff_and _ hop, List.take_of_length_le hfg.2]
                rw [heff_eq] at hvg ⊢
                have hne2 := hno_bin v hc1 C.gates[j] hg (Or.inl hop)
                by_cases h2 : C.gates[j].inputs.length = 2
                · exact absurd hvg (hne2 h2)
                · omega
              · have heff_eq : eff C.gates[j] = C.gates[j].inputs := by
                  rw [heff_or _ hop, List.take_of_length_le hfg.2]
                rw [heff_eq] at hvg ⊢
                have hne2 := hno_bin v hc1 C.gates[j] hg (Or.inr hop)
                by_cases h2 : C.gates[j].inputs.length = 2
                · exact absurd hvg (hne2 h2)
                · omega
              · rw [heff_not _ hop, List.length_take]
                omega
            cases he : eff C.gates[j] with
            | nil => rw [he] at hvg; simp at hvg
            | cons a rest =>
              cases rest with
              | nil =>
                rw [he] at hvg
                simp only [List.mem_singleton] at hvg
                rw [hvg]
              | cons b rest2 =>
                rw [he] at helen; simp at helen
        choose idx hidx using hpick
        let img : Finset (Fin C.size) := S1.attach.image (fun x => idx x.1 x.2)
        have himg_card : img.card = S1.card := by
          rw [← Finset.card_attach (s := S1)]
          apply Finset.card_image_of_injective
          intro x y hxy
          dsimp only at hxy
          have hx := hidx x.1 x.2
          have hy := hidx y.1 y.2
          rw [hxy] at hx
          have hval : x.1.val = y.1.val := (List.cons.inj (hx.symm.trans hy)).1
          exact Subtype.ext (Fin.ext hval)
        have hlen_bound : (Finset.univ : Finset (Fin C.size)).sum
            (fun j => (eff (C.gates[j.val]'j.isLt)).length) + S1.card ≤ 2 * C.size := by
          rw [← himg_card]
          have hcard_sum : img.card = (Finset.univ : Finset (Fin C.size)).sum
              (fun j => if j ∈ img then 1 else 0) := by
            rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
            simp
          rw [hcard_sum, ← Finset.sum_add_distrib]
          calc
            (Finset.univ : Finset (Fin C.size)).sum
                (fun j => (eff (C.gates[j.val]'j.isLt)).length + (if j ∈ img then 1 else 0))
              ≤ (Finset.univ : Finset (Fin C.size)).sum (fun _ => 2) := by
                apply Finset.sum_le_sum
                intro j _
                by_cases hj : j ∈ img
                · simp only [hj, ↓reduceIte]
                  rcases Finset.mem_image.mp hj with ⟨x, _, rfl⟩
                  rw [hidx x.1 x.2]; simp
                · simp only [hj, ↓reduceIte]
                  have hfg := hfanC _ (List.getElem_mem j.isLt)
                  have := heff_len _ hfg.1 hfg.2
                  omega
            _ = 2 * C.size := by simp [mul_comm]
        have hslots_len : slots.length = 1 + (Finset.univ : Finset (Fin C.size)).sum
            (fun j => (eff (C.gates[j.val]'j.isLt)).length) := by
          dsimp only [slots]
          rw [List.length_cons, List.length_flatMap]
          have hsum_list : (C.gates.map fun g => (eff g).length).sum =
              (Finset.univ : Finset (Fin C.size)).sum
                (fun j => (eff (C.gates[j.val]'j.isLt)).length) := by
            have hof : C.gates.map (fun g => (eff g).length) =
                List.ofFn (fun j : Fin C.gates.length => (eff (C.gates[j.val]'j.isLt)).length) := by
              apply List.ext_getElem <;> simp
            rw [hof, List.sum_ofFn]
            rfl
          omega
        let T1 : Finset ℕ := (Finset.univ : Finset (Fin m)).image Fin.val
        let T2 : Finset ℕ := (Finset.univ : Finset (Fin C.size)).image (fun j => m + j.val)
        have hdisj : Disjoint T1 T2 := by
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          rcases Finset.mem_image.mp ha1 with ⟨v, _, rfl⟩
          rcases Finset.mem_image.mp ha2 with ⟨j, _, hj⟩
          have := v.isLt
          omega
        have hsum_T : T1.sum (fun a => slots.count a) + T2.sum (fun a => slots.count a) ≤
            slots.length := by
          rw [← Finset.sum_union hdisj]
          exact hcount_sum_le slots (T1 ∪ T2)
        have hsum_T1 : T1.sum (fun a => slots.count a) =
            (Finset.univ : Finset (Fin m)).sum (fun v => slots.count v.val) := by
          apply Finset.sum_image
          intro a _ b _ hab; exact Fin.ext hab
        have hsum_T2 : T2.sum (fun a => slots.count a) =
            (Finset.univ : Finset (Fin C.size)).sum (fun j => slots.count (m + j.val)) := by
          apply Finset.sum_image
          intro a _ b _ hab; dsimp only at hab; exact Fin.ext (by omega)
        have hT2_ge : C.size ≤ T2.sum (fun a => slots.count a) := by
          rw [hsum_T2]
          calc
            C.size = (Finset.univ : Finset (Fin C.size)).sum (fun _ => 1) := by simp
            _ ≤ (Finset.univ : Finset (Fin C.size)).sum (fun j => slots.count (m + j.val)) :=
              Finset.sum_le_sum (fun j _ => hgate_live j)
        have hT1_ge : 2 * m ≤ T1.sum (fun a => slots.count a) + S1.card := by
          rw [hsum_T1]
          have hS1_sum : S1.card = (Finset.univ : Finset (Fin m)).sum
              (fun v => if v ∈ S1 then 1 else 0) := by
            rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
            simp
          rw [hS1_sum, ← Finset.sum_add_distrib]
          calc
            2 * m = (Finset.univ : Finset (Fin m)).sum (fun _ => 2) := by simp [mul_comm]
            _ ≤ (Finset.univ : Finset (Fin m)).sum
                (fun v => slots.count v.val + (if v ∈ S1 then 1 else 0)) := by
              apply Finset.sum_le_sum
              intro v _
              have hge1 := (hinp_live v).1
              by_cases hv : v ∈ S1
              · simp only [hv, ↓reduceIte]
                have hc1 := (Finset.mem_filter.mp hv).2
                omega
              · simp only [hv, ↓reduceIte]
                have hne1 : slots.count v.val ≠ 1 := fun e =>
                  hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, e⟩)
                omega
        omega
      rcases hbin_read_once with ⟨v, hv1, g, hg, hop, hlen2, hvg⟩
      rcases hop with hand | hor
      · have := nonMonoAnd m H C hevenM hcolH hdegH hgirthH8 hedgeH hminC hhasNot
          ⟨v, hv1, g, hg, hand, hlen2, hvg⟩ hCsp
        omega
      · have := nonMonoOr m H C hevenM hcolH hdegH hgirthH8 hedgeH hminC hhasNot
          ⟨v, hv1, g, hg, hor, hlen2, hvg⟩ hCsp
        omega
  omega
