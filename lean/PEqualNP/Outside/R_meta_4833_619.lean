import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4833_619
    (hH0 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO
        (PEqualNP.EdgeOwnership.edgeGraph 10
          [(0, 3), (0, 7), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9),
           (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) D →
      19 ≤ D.size)
    (hH1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO
        (PEqualNP.EdgeOwnership.edgeGraph 10
          [(0, 8), (0, 9), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9),
           (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) D →
      19 ≤ D.size)
    (hH2 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO
        (PEqualNP.EdgeOwnership.edgeGraph 10
          [(0, 8), (0, 9), (1, 3), (1, 7), (2, 5), (2, 6), (3, 7), (3, 9),
           (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) D →
      19 ≤ D.size)
    (hH3 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsLeastAO
        (PEqualNP.EdgeOwnership.edgeGraph 10
          [(0, 8), (0, 9), (1, 3), (1, 7), (2, 4), (2, 9), (3, 7), (3, 9),
           (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]) D →
      19 ≤ D.size)
    : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (19 : ℕ) ≤ x3.size := by
  classical
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x; simp [run, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
  have getD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t h; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have getD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b; simp [List.getD_eq_getElem?_getD]
  have run_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => simp
    | append_singleton hs g ih =>
      rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]
  have run_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have := run_prefix [] gs x i (by simpa using hi)
    simpa [run] using this
  have run_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := run_length gs x
      have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · exact run_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with h | h
      · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
        exact ih j h
      · have hjj : j = gs.length := by simp at hj; omega
        subst hjj
        have hg : (gs ++ [g])[gs.length] = g := by simp
        rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  let rv : List Bool → Bool ⊕ ℕ → Bool := fun w r => Sum.elim id (fun t => w.getD t false) r
  have rv_ext : ∀ (hs e : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool) (r : Bool ⊕ ℕ),
      (∀ t, r = Sum.inr t → t < y.length + hs.length) →
      rv (run (hs ++ e) y) r = rv (run hs y) r := by
    intro hs e y r h
    rcases r with b | t
    · rfl
    · exact run_prefix hs e y t (h t rfl)
  have hElimFalse : ∀ (v : Fin 11) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 11 C →
      (¬∃ b : Bool, ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 11 C (v.insertNth false x) = b) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 10 D ∧ D.size ≤ C.size ∧
        ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 D x =
          PEqualNP.MetaComplexity.circuitFun 11 C (v.insertNth false x) := by
    intro v C hAO hnc
    let src : (Fin 10 → Bool) → List Bool := fun x => List.ofFn (v.insertNth false x)
    let tgt : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x
    have hkey : ∀ k ≤ C.gates.length, ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → Bool ⊕ ℕ),
        (∀ g ∈ hs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length = 2) ∧
        (∀ j (hj : j < hs.length), ∀ w ∈ hs[j].inputs, w < 10 + j) ∧
        hs.length ≤ k ∧
        (∀ w t, w < 11 + k → m w = Sum.inr t → t < 10 + hs.length) ∧
        ∀ x : Fin 10 → Bool, ∀ w < 11 + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
      intro k
      induction k with
      | zero =>
        intro _
        let m0 : ℕ → Bool ⊕ ℕ := fun w =>
          if w < v.val then Sum.inr w else if w = v.val then Sum.inl false else Sum.inr (w - 1)
        refine ⟨[], m0, by simp, ?_, le_rfl, ?_, ?_⟩
        · intro j hj; cases hj
        · intro w t hw ht
          dsimp only [m0] at ht
          split_ifs at ht with h1 h2
          · cases ht; have := v.isLt; simp; omega
          · cases ht; simp; omega
        · intro x w hw
          have hw11 : w < 11 := by omega
          rw [run_input _ _ _ (by simp [src, hw11])]
          dsimp only [m0, rv, src, tgt]
          split_ifs with h1 h2
          · have hlt : w < 10 := by have := v.isLt; omega
            have hidx : (⟨w, hw11⟩ : Fin 11) = v.succAbove ⟨w, hlt⟩ := by
              apply Fin.ext
              simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
              rw [if_pos h1]
              rfl
            simp only [Sum.elim_inr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw11, hlt, ↓reduceDIte, Option.getD_some, run, List.foldl_nil]
            rw [hidx, Fin.insertNth_apply_succAbove]
          · have hidx : (⟨w, hw11⟩ : Fin 11) = v := Fin.ext h2
            simp only [Sum.elim_inl, id_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw11, ↓reduceDIte, Option.getD_some]
            rw [hidx, Fin.insertNth_apply_same]
          · have hlt : w - 1 < 10 := by omega
            have hidx : (⟨w, hw11⟩ : Fin 11) = v.succAbove ⟨w - 1, hlt⟩ := by
              apply Fin.ext
              simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
              rw [if_neg (by omega)]
              simp only [Fin.val_succ]
              omega
            simp only [Sum.elim_inr, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw11, hlt, ↓reduceDIte, Option.getD_some, run, List.foldl_nil]
            rw [hidx, Fin.insertNth_apply_succAbove]
      | succ k ih =>
        intro hk
        obtain ⟨hs, m, hhsok, hhsrb, hhslen, hm_bd, hm_ev⟩ := ih (by omega)
        have hk' : k < C.gates.length := by omega
        have hg_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
        have hop := hAO.1 C.gates[k] hg_mem
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 C.gates[k] hg_mem)
        have hrb_k := hAO.2.1 k hk'
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
          change C.gates.getD k _ = C.gates[k]
          exact List.getD_eq_getElem _ _ hk'
        have ha_lt : a < 11 + k := hrb_k a (by rw [hgat, hab]; simp)
        have hb_lt : b < 11 + k := hrb_k b (by rw [hgat, hab]; simp)
        have hstep_fin : ∀ (r : Bool ⊕ ℕ) (e : List PEqualNP.CircuitLowerBounds.Gate),
            e.length ≤ 1 →
            (∀ g ∈ e, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
            (∀ g ∈ e, ∀ w ∈ g.inputs, w < 10 + hs.length) →
            (∀ t, r = Sum.inr t → t < 10 + hs.length + e.length) →
            (∀ x : Fin 10 → Bool, (run C.gates (src x)).getD (11 + k) false = rv (run (hs ++ e) (tgt x)) r) →
            ∃ (hs' : List PEqualNP.CircuitLowerBounds.Gate) (m' : ℕ → Bool ⊕ ℕ),
              (∀ g ∈ hs', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
              (∀ j (hj : j < hs'.length), ∀ w ∈ hs'[j].inputs, w < 10 + j) ∧
              hs'.length ≤ k + 1 ∧
              (∀ w t, w < 11 + (k + 1) → m' w = Sum.inr t → t < 10 + hs'.length) ∧
              ∀ x : Fin 10 → Bool, ∀ w < 11 + (k + 1), (run C.gates (src x)).getD w false = rv (run hs' (tgt x)) (m' w) := by
          intro r e helen heok herb hrbd hval
          refine ⟨hs ++ e, Function.update m (11 + k) r, ?_, ?_, ?_, ?_, ?_⟩
          · intro g hg
            rcases List.mem_append.1 hg with hg | hg
            · exact hhsok g hg
            · exact heok g hg
          · intro j hj w hw
            rcases Nat.lt_or_ge j hs.length with hjlt | hjge
            · rw [List.getElem_append_left hjlt] at hw
              exact hhsrb j hjlt w hw
            · rw [List.getElem_append_right hjge] at hw
              have hj' : j - hs.length < e.length := by rw [List.length_append] at hj; omega
              have hmem : e[j - hs.length]'hj' ∈ e := List.getElem_mem hj'
              have := herb _ hmem w hw
              omega
          · rw [List.length_append]; omega
          · intro w t hw ht
            rw [List.length_append]
            by_cases hwe : w = 11 + k
            · subst hwe; rw [Function.update_self] at ht; have := hrbd t ht; omega
            · rw [Function.update_of_ne hwe] at ht; have := hm_bd w t (by omega) ht; omega
          · intro x w hw
            by_cases hwe : w = 11 + k
            · subst hwe; rw [Function.update_self]; exact hval x
            · rw [Function.update_of_ne hwe, hm_ev x w (by omega)]
              exact (rv_ext hs e (tgt x) (m w) (fun t ht => by simp only [tgt, List.length_ofFn]; exact hm_bd w t (by omega) ht)).symm
        have hgate_ev : ∀ x : Fin 10 → Bool, (run C.gates (src x)).getD (11 + k) false =
            C.gates[k].op.eval [rv (run hs (tgt x)) (m a), rv (run hs (tgt x)) (m b)] := by
          intro x
          have rg := run_gate C.gates (src x) k hk'
          simp only [src, List.length_ofFn] at rg
          rw [rg, hab]
          simp only [List.map_cons, List.map_nil, if_pos ha_lt, if_pos hb_lt]
          rw [hm_ev x a ha_lt, hm_ev x b hb_lt]
        rcases hma : m a with ca | ta <;> rcases hmb : m b with cb | tb
        · refine hstep_fin (Sum.inl (C.gates[k].op.eval [ca, cb])) [] (by simp) (by simp) (by simp) (by simp) (fun x => ?_)
          rw [hgate_ev x, hma, hmb]; rfl
        · rcases hop with hop | hop
          · cases ca
            · refine hstep_fin (Sum.inl false) [] (by simp) (by simp) (by simp) (by simp) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop]; simp [andEval, rv]
            · refine hstep_fin (Sum.inr tb) [] (by simp) (by simp) (by simp) (fun t ht => by cases ht; simpa using hm_bd b tb hb_lt hmb) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop, List.append_nil]; simp [andEval, rv]
          · cases ca
            · refine hstep_fin (Sum.inr tb) [] (by simp) (by simp) (by simp) (fun t ht => by cases ht; simpa using hm_bd b tb hb_lt hmb) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop, List.append_nil]; simp [orEval, rv]
            · refine hstep_fin (Sum.inl true) [] (by simp) (by simp) (by simp) (by simp) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop]; simp [orEval, rv]
        · rcases hop with hop | hop
          · cases cb
            · refine hstep_fin (Sum.inl false) [] (by simp) (by simp) (by simp) (by simp) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop]; simp [andEval, rv]
            · refine hstep_fin (Sum.inr ta) [] (by simp) (by simp) (by simp) (fun t ht => by cases ht; simpa using hm_bd a ta ha_lt hma) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop, List.append_nil]; simp [andEval, rv]
          · cases cb
            · refine hstep_fin (Sum.inr ta) [] (by simp) (by simp) (by simp) (fun t ht => by cases ht; simpa using hm_bd a ta ha_lt hma) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop, List.append_nil]; simp [orEval, rv]
            · refine hstep_fin (Sum.inl true) [] (by simp) (by simp) (by simp) (by simp) (fun x => ?_)
              rw [hgate_ev x, hma, hmb, hop]; simp [orEval, rv]
        · let gnew : PEqualNP.CircuitLowerBounds.Gate := ⟨C.gates[k].op, [ta, tb]⟩
          refine hstep_fin (Sum.inr (10 + hs.length)) [gnew] (by simp) (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨hop, rfl⟩)
            (by
              intro g hg w hw
              simp only [List.mem_singleton] at hg; subst hg
              simp only [gnew, List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with hw | hw
              · rw [hw]; exact hm_bd a ta ha_lt hma
              · rw [hw]; exact hm_bd b tb hb_lt hmb)
            (by intro t ht; cases ht; simp) (fun x => ?_)
          rw [hgate_ev x, hma, hmb]
          dsimp only [rv, Sum.elim]
          have hlen : 10 + hs.length = (run hs (tgt x)).length := by rw [run_length]; simp [tgt]
          rw [run_snoc, hlen, getD_at]
          rfl
    obtain ⟨hs, m, hhsok, hhsrb, hhslen, hm_bd, hm_ev⟩ := hkey C.gates.length le_rfl
    have hout : C.output < 11 + C.gates.length := by
      by_contra h
      refine hnc ⟨false, fun x => ?_⟩
      change (run C.gates (src x)).getD C.output false = false
      rw [List.getD_eq_default _ _ (by rw [run_length]; simp [src]; omega)]
    rcases hmout : m C.output with b | out
    · exfalso
      refine hnc ⟨b, fun x => ?_⟩
      have := hm_ev x C.output hout
      rw [hmout] at this
      exact this
    · refine ⟨⟨hs, out⟩, ⟨fun g hg => (hhsok g hg).1, ?_, fun g hg => (hhsok g hg).2⟩, hhslen, fun x => ?_⟩
      · intro j hj w hw
        have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨hs, out⟩ j = hs[j] := by
          change hs.getD j _ = hs[j]
          exact List.getD_eq_getElem _ _ hj
        rw [hgat] at hw
        exact hhsrb j hj w hw
      · have := hm_ev x C.output hout
        rw [hmout] at this
        exact this.symm
  have hMin : ∀ (H : SimpleGraph (Fin 10)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 10 D →
      PEqualNP.MetaComplexity.circuitFun 10 D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ →
      ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO H E ∧ E.size ≤ D.size := by
    intro H _ D hDAO hDfun
    have hex : ∃ s : ℕ, ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 10 E ∧
        PEqualNP.MetaComplexity.circuitFun 10 E = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ ∧
        E.size = s := ⟨D.size, D, hDAO, hDfun, rfl⟩
    obtain ⟨E, hEAO, hEfun, hEsz⟩ := Nat.find_spec hex
    refine ⟨E, ⟨hEAO, hEfun, fun C' hC'AO hC'fun => ?_⟩, ?_⟩
    · rw [hEsz]
      exact Nat.find_min' hex ⟨C', hC'AO, hC'fun, rfl⟩
    · rw [hEsz]
      exact Nat.find_min' hex ⟨D, hDAO, hDfun, rfl⟩
  let G11 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let H0 : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 3), (0, 7), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9),
     (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]
  let H1 : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 8), (0, 9), (1, 4), (1, 9), (2, 5), (2, 6), (3, 7), (3, 9),
     (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]
  let H2 : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 8), (0, 9), (1, 3), (1, 7), (2, 5), (2, 6), (3, 7), (3, 9),
     (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]
  let H3 : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 8), (0, 9), (1, 3), (1, 7), (2, 4), (2, 9), (3, 7), (3, 9),
     (4, 7), (4, 8), (5, 6), (5, 9), (6, 8), (7, 8)]
  have hAdj0 : ∀ a b : Fin 10, G11.Adj ((0 : Fin 11).succAbove a) ((0 : Fin 11).succAbove b) ↔ H0.Adj a b := by
    decide +kernel
  have hAdj1 : ∀ a b : Fin 10, G11.Adj ((1 : Fin 11).succAbove a) ((1 : Fin 11).succAbove b) ↔ H1.Adj a b := by
    decide +kernel
  have hAdj2 : ∀ a b : Fin 10, G11.Adj ((2 : Fin 11).succAbove a) ((2 : Fin 11).succAbove b) ↔ H2.Adj a b := by
    decide +kernel
  have hAdj3 : ∀ a b : Fin 10, G11.Adj ((3 : Fin 11).succAbove a) ((3 : Fin 11).succAbove b) ↔ H3.Adj a b := by
    decide +kernel
  have hFunEq : ∀ (v : Fin 11) (H : SimpleGraph (Fin 10)) [DecidableRel H.Adj],
      (∀ a b : Fin 10, G11.Adj (v.succAbove a) (v.succAbove b) ↔ H.Adj a b) →
      ∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G11 ∅ (v.insertNth false x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x := by
    intro v H _ hadj x
    apply Bool.eq_iff_iff.mpr
    let y : Fin 11 → Bool := v.insertNth false x
    change (decide (∃ a ∈ (∅ : Finset (Fin 11)), y a = true) ||
      decide (∃ a b : Fin 11, G11.Adj a b ∧ y a = true ∧ y b = true)) = true ↔
      (decide (∃ a ∈ (∅ : Finset (Fin 10)), x a = true) ||
      decide (∃ a b : Fin 10, H.Adj a b ∧ x a = true ∧ x b = true)) = true
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      by_cases hav : a = v
      · subst hav; dsimp only [y] at ha; rw [Fin.insertNth_apply_same] at ha; cases ha
      · by_cases hbv : b = v
        · subst hbv; dsimp only [y] at hb; rw [Fin.insertNth_apply_same] at hb; cases hb
        · obtain ⟨a', rfl⟩ := Fin.exists_succAbove_eq hav
          obtain ⟨b', rfl⟩ := Fin.exists_succAbove_eq hbv
          dsimp only [y] at ha hb
          rw [Fin.insertNth_apply_succAbove] at ha hb
          exact ⟨a', b', (hadj a' b').1 hab, ha, hb⟩
    · rintro ⟨a', b', hab, ha, hb⟩
      exact ⟨v.succAbove a', v.succAbove b', (hadj a' b').2 hab,
        by dsimp only [y]; rw [Fin.insertNth_apply_succAbove]; exact ha,
        by dsimp only [y]; rw [Fin.insertNth_apply_succAbove]; exact hb⟩
  have hSolveCase : ∀ (v : Fin 11) (H : SimpleGraph (Fin 10)) [DecidableRel H.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b : Fin 10, G11.Adj (v.succAbove a) (v.succAbove b) ↔ H.Adj a b) →
      (∃ a b : Fin 10, H.Adj a b) →
      PEqualNP.TopForm.IsAO2 11 C →
      (∀ x : Fin 11 → Bool, x v = false → PEqualNP.MetaComplexity.circuitFun 11 C x =
        PEqualNP.MetaComplexity.NestedCover.graphFun G11 ∅ x) →
      (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO H E → 19 ≤ E.size) →
      19 ≤ C.size := by
    intro v H _ C hadj hedge hAO hagree hbound
    rcases hedge with ⟨e1, e2, he12⟩
    have hnc : ¬∃ b : Bool, ∀ x : Fin 10 → Bool,
        PEqualNP.MetaComplexity.circuitFun 11 C (v.insertNth false x) = b := by
      rintro ⟨b, hb⟩
      have h0 := hb (fun _ => false)
      have h1 := hb (fun _ => true)
      rw [hagree _ (Fin.insertNth_apply_same _ _ _), hFunEq v H hadj] at h0 h1
      have h0' : PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ (fun _ => false) = false := by
        change (decide (∃ a ∈ (∅ : Finset (Fin 10)), false = true) ||
          decide (∃ a b : Fin 10, H.Adj a b ∧ false = true ∧ false = true)) = false
        simp
      have h1' : PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ (fun _ => true) = true := by
        change (decide (∃ a ∈ (∅ : Finset (Fin 10)), true = true) ||
          decide (∃ a b : Fin 10, H.Adj a b ∧ true = true ∧ true = true)) = true
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
        exact ⟨e1, e2, he12, by simp, by simp⟩
      rw [h0'] at h0; rw [h1'] at h1
      rw [← h0] at h1; cases h1
    obtain ⟨D, hDAO, hDsz, hDev⟩ := hElimFalse v C hAO hnc
    have hDfun : PEqualNP.MetaComplexity.circuitFun 10 D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ := by
      funext x
      rw [hDev x, hagree _ (Fin.insertNth_apply_same _ _ _), hFunEq v H hadj x]
    obtain ⟨E, hELeast, hEsz⟩ := hMin H D hDAO hDfun
    exact (hbound E hELeast).trans (hEsz.trans hDsz)
  intro _ v C hv hAO hagree
  have hv_cases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
    have := v.isLt
    rcases (show v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 by omega) with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hv_cases with rfl | rfl | rfl | rfl
  · exact hSolveCase 0 H0 C hAdj0 ⟨7, 8, by decide +kernel⟩ hAO hagree hH0
  · exact hSolveCase 1 H1 C hAdj1 ⟨7, 8, by decide +kernel⟩ hAO hagree hH1
  · exact hSolveCase 2 H2 C hAdj2 ⟨7, 8, by decide +kernel⟩ hAO hagree hH2
  · exact hSolveCase 3 H3 C hAdj3 ⟨7, 8, by decide +kernel⟩ hAO hagree hH3
