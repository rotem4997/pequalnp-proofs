import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1745_619
    (hMono : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (7 : ℕ) ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = Bool.true ↔
        (∃ a ∈ A, x a = Bool.true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → C.size ≤ t) →
      (∀ v ∉ A,
        (C.gates.filter fun g => g.inputs.contains v.val).length ≤ (3 : ℕ) ∧
        ((C.gates.filter fun g => g.inputs.contains v.val).length = (3 : ℕ) →
          ∀ g ∈ C.gates.filter fun g => g.inputs.contains v.val,
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∀ T : Finset (Fin n), Disjoint A T →
        (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + (1 : ℕ) < A.card + G.edgeSet.ncard + T.card) →
      ∃ v ∉ A, ∃ t : ℕ, t + (4 : ℕ) ≤ C.size ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update x v Bool.false)) t)
    (hWithNot : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (7 : ℕ) ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = Bool.true ↔
        (∃ a ∈ A, x a = Bool.true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → C.size ≤ t) →
      (∀ v ∉ A,
        have rs : List PEqualNP.CircuitLowerBounds.Gate :=
          List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
            (List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs).contains ↑v) C.gates;
        rs.length ≤ (3 : ℕ) ∧ (rs.length = (3 : ℕ) → ∀ g ∈ rs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∀ T : Finset (Fin n), Disjoint A T →
        (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + (1 : ℕ) < A.card + G.edgeSet.ncard + T.card) →
      ∃ v ∉ A, ∃ t : ℕ, t + (4 : ℕ) ≤ C.size ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => f (Function.update x v Bool.false)) t)
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have run_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    simp [run, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
  have getD_lt : ∀ (l : List Bool) (b : Bool) (t : ℕ), t < l.length →
      (l ++ [b]).getD t false = l.getD t false := by
    intro l b t h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have getD_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
    intro l b
    simp [List.getD_eq_getElem?_getD]
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
  let fok : PEqualNP.CircuitLowerBounds.Gate → Prop := fun g =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2
  have hOrChain : ∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List ℕ),
      ws ≠ [] → (∀ w ∈ ws, w < n + gs.length) →
      ∃ (e : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
        e.length + 1 = ws.length ∧ (∀ g ∈ e, fok g) ∧ out < n + gs.length + e.length ∧
        ∀ x : Fin n → Bool, (run (gs ++ e) (List.ofFn x)).getD out false =
          ws.any (fun w => (run gs (List.ofFn x)).getD w false) := by
    intro n gs ws
    induction ws with
    | nil => intro h; exact absurd rfl h
    | cons w rest ih =>
      intro _ hbd
      rcases rest with _ | ⟨u, rest'⟩
      · refine ⟨[], w, by simp, by simp, ?_, fun x => ?_⟩
        · simpa using hbd w (by simp)
        · simp
      · obtain ⟨e, out, helen, heok, hout, hev⟩ := ih (by simp) (fun z hz => hbd z (List.mem_cons_of_mem _ hz))
        let gnew : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [w, out]⟩
        refine ⟨e ++ [gnew], n + gs.length + e.length, ?_, ?_, ?_, fun x => ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil] at helen ⊢; omega
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact heok g hg
          · simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp [gnew], by simp [gnew]⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rw [← List.append_assoc, run_snoc]
          have hlen : n + gs.length + e.length = (run (gs ++ e) (List.ofFn x)).length := by
            rw [run_length, List.length_ofFn, List.length_append]; omega
          rw [hlen, getD_at]
          simp only [gnew, orEval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
          rw [run_prefix gs e (List.ofFn x) w (by rw [List.length_ofFn]; exact hbd w (by simp)), hev x]
          simp [List.any_cons]
  have hStarCoverAny : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (A T : Finset (Fin n)),
      (∀ i j : Fin n, H.Adj i j → i ∈ T ∨ j ∈ T) →
      (∃ i j : Fin n, H.Adj i j) →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => decide ((∃ a ∈ A, x a = true) ∨ ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true))
        (A.card + H.edgeFinset.card + T.card - 1) := by
    intro n H A T hcov hedge
    let star : Fin n → Finset (Fin n) := fun t => (H.neighborFinset t).filter fun u => u ∉ T ∨ t.val < u.val
    have hBuildStars : ∀ (L : List (Fin n)), (∀ t ∈ L, (star t).Nonempty) →
        ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (outs : List ℕ),
          outs.length = L.length ∧
          gs.length = (L.map fun t => (star t).card).sum ∧
          (∀ g ∈ gs, fok g) ∧
          (∀ w ∈ outs, w < n + gs.length) ∧
          ∀ x : Fin n → Bool, outs.any (fun w => (run gs (List.ofFn x)).getD w false) =
            decide (∃ t ∈ L, x t = true ∧ ∃ u ∈ star t, x u = true) := by
      intro L
      induction L with
      | nil =>
        intro _
        refine ⟨[], [], rfl, rfl, by simp, by simp, fun x => by simp⟩
      | cons t rest ih =>
        intro hne
        obtain ⟨gs, outs, holen, hgslen, hgsok, houtsbd, houtsev⟩ := ih (fun z hz => hne z (List.mem_cons_of_mem _ hz))
        let nbs : List (Fin n) := (star t).toList
        have hnbs_ne : nbs ≠ [] := by
          intro hempty
          obtain ⟨u, hu⟩ := hne t (by simp)
          have hmem : u ∈ nbs := Finset.mem_toList.2 hu
          rw [hempty] at hmem; cases hmem
        let ws : List ℕ := nbs.map Fin.val
        have hws_ne : ws ≠ [] := by simp [ws, hnbs_ne]
        have hws_len : ws.length = (star t).card := by simp [ws, nbs]
        obtain ⟨e1, out1, he1len, he1ok, hout1bd, he1ev⟩ := hOrChain n gs ws hws_ne (by
          intro w hw
          obtain ⟨u, _, rfl⟩ := List.mem_map.1 hw
          have := u.isLt; omega)
        let gand : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [t.val, out1]⟩
        let gs' := gs ++ (e1 ++ [gand])
        let out_t := n + gs.length + e1.length
        refine ⟨gs', out_t :: outs, by simp [holen], ?_, ?_, ?_, fun x => ?_⟩
        · simp only [gs', List.length_append, List.length_singleton, List.map_cons, List.sum_cons]
          omega
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact hgsok g hg
          · rcases List.mem_append.1 hg with hg | hg
            · exact he1ok g hg
            · simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp [gand], by simp [gand]⟩
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · simp only [gs', out_t, List.length_append, List.length_singleton]; omega
          · have := houtsbd w hw
            simp only [gs', List.length_append, List.length_singleton]; omega
        · simp only [List.any_cons]
          have hrest : outs.any (fun w => (run gs' (List.ofFn x)).getD w false) =
              outs.any (fun w => (run gs (List.ofFn x)).getD w false) := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true]
            refine exists_congr fun w => and_congr_right fun hw => ?_
            rw [run_prefix gs (e1 ++ [gand]) (List.ofFn x) w (by rw [List.length_ofFn]; exact houtsbd w hw)]
          have hcur : (run gs' (List.ofFn x)).getD out_t false =
              (x t && decide (∃ u ∈ star t, x u = true)) := by
            have hassoc : gs' = (gs ++ e1) ++ [gand] := by simp [gs', List.append_assoc]
            rw [hassoc, run_snoc]
            have hlen : out_t = (run (gs ++ e1) (List.ofFn x)).length := by
              rw [run_length, List.length_ofFn, List.length_append]; omega
            rw [hlen, getD_at]
            simp only [gand, andEval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
            have hxt : (run (gs ++ e1) (List.ofFn x)).getD t.val false = x t := by
              rw [run_input _ _ _ (by simp [t.isLt])]
              simp [List.getD_eq_getElem?_getD, t.isLt]
            rw [hxt, he1ev x]
            congr 1
            apply Bool.eq_iff_iff.mpr
            simp only [ws, nbs, List.any_eq_true, List.mem_map, decide_eq_true_eq]
            constructor
            · rintro ⟨w, ⟨u, hu, rfl⟩, hxu⟩
              rw [Finset.mem_toList] at hu
              rw [run_input _ _ _ (by simp [u.isLt])] at hxu
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt, ↓reduceDIte, Option.getD_some] at hxu
              exact ⟨u, hu, hxu⟩
            · rintro ⟨u, hu, hxu⟩
              refine ⟨u.val, ⟨u, Finset.mem_toList.2 hu, rfl⟩, ?_⟩
              rw [run_input _ _ _ (by simp [u.isLt])]
              simp [List.getD_eq_getElem?_getD, u.isLt, hxu]
          rw [hcur, hrest, houtsev x]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
          constructor
          · rintro (⟨hxt, u, hu, hxu⟩ | ⟨z, hz, hxz, u, hu, hxu⟩)
            · exact ⟨t, Or.inl rfl, hxt, u, hu, hxu⟩
            · exact ⟨z, Or.inr hz, hxz, u, hu, hxu⟩
          · rintro ⟨z, rfl | hz, hxz, u, hu, hxu⟩
            · exact Or.inl ⟨hxz, u, hu, hxu⟩
            · exact Or.inr ⟨z, hz, hxz, u, hu, hxu⟩
    have hown : ∀ i j : Fin n, H.Adj i j → (i ∈ T ∧ j ∈ star i) ∨ (j ∈ T ∧ i ∈ star j) := by
      intro i j hij
      have hne : i ≠ j := H.ne_of_adj hij
      by_cases hi : i ∈ T
      · by_cases hj : j ∈ T
        · rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
          · exact Or.inl ⟨hi, Finset.mem_filter.2 ⟨(H.mem_neighborFinset i j).2 hij, Or.inr hlt⟩⟩
          · exact Or.inr ⟨hj, Finset.mem_filter.2 ⟨(H.mem_neighborFinset j i).2 hij.symm, Or.inr hgt⟩⟩
        · exact Or.inl ⟨hi, Finset.mem_filter.2 ⟨(H.mem_neighborFinset i j).2 hij, Or.inl hj⟩⟩
      · have hj : j ∈ T := (hcov i j hij).resolve_left hi
        exact Or.inr ⟨hj, Finset.mem_filter.2 ⟨(H.mem_neighborFinset j i).2 hij.symm, Or.inl hi⟩⟩
    let T' : Finset (Fin n) := T.filter fun t => (star t).Nonempty
    have hT'ne : T'.Nonempty := by
      obtain ⟨i, j, hij⟩ := hedge
      rcases hown i j hij with ⟨hi, hj⟩ | ⟨hj, hi⟩
      · exact ⟨i, Finset.mem_filter.2 ⟨hi, ⟨j, hj⟩⟩⟩
      · exact ⟨j, Finset.mem_filter.2 ⟨hj, ⟨i, hi⟩⟩⟩
    let L : List (Fin n) := T'.toList
    have hLne : L ≠ [] := by
      intro h
      obtain ⟨t, ht⟩ := hT'ne
      have hmem : t ∈ L := Finset.mem_toList.2 ht
      rw [h] at hmem; cases hmem
    obtain ⟨gs, outs, holen, hgslen, hgsok, houtsbd, houtsev⟩ :=
      hBuildStars L (fun t ht => (Finset.mem_filter.1 (Finset.mem_toList.1 ht)).2)
    have houts_ne : outs ≠ [] := by
      intro h; rw [h] at holen; exact hLne (List.eq_nil_of_length_eq_zero holen.symm)
    let aWires : List ℕ := A.toList.map Fin.val
    let allWires : List ℕ := outs ++ aWires
    have hall_ne : allWires ≠ [] := by
      intro h
      have := List.append_eq_nil_iff.1 h
      exact houts_ne this.1
    obtain ⟨e2, out2, he2len, he2ok, _, he2ev⟩ := hOrChain n gs allWires hall_ne (by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact houtsbd w hw
      · obtain ⟨a, _, rfl⟩ := List.mem_map.1 hw
        have := a.isLt; omega)
    have hsum_le : (L.map fun t => (star t).card).sum ≤ H.edgeFinset.card := by
      have hsum_eq : (L.map fun t => (star t).card).sum = ∑ t ∈ T', (star t).card := by
        simp [L]
      rw [hsum_eq]
      have hdisj : Set.PairwiseDisjoint (T' : Set (Fin n)) (fun t => (star t).image fun u => s(t, u)) := by
        intro t1 ht1 t2 ht2 hne
        exact Finset.disjoint_left.2 fun e he1 he2 => by
          obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.1 he1
          obtain ⟨u2, hu2, heq⟩ := Finset.mem_image.1 he2
          have ht1T : t1 ∈ T := (Finset.mem_filter.1 ht1).1
          have ht2T : t2 ∈ T := (Finset.mem_filter.1 ht2).1
          have h1cond : u1 ∉ T ∨ t1.val < u1.val := (Finset.mem_filter.1 hu1).2
          have h2cond : u2 ∉ T ∨ t2.val < u2.val := (Finset.mem_filter.1 hu2).2
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h12, _⟩ | ⟨h1, h2⟩
          · exact hne h12.symm
          · subst h1; subst h2
            have hlt1 : u2.val < t2.val := h1cond.resolve_left (not_not.2 ht2T)
            have hlt2 : t2.val < u2.val := h2cond.resolve_left (not_not.2 ht1T)
            omega
      have hsub : T'.biUnion (fun t => (star t).image fun u => s(t, u)) ⊆ H.edgeFinset := by
        intro e he
        obtain ⟨t, _, he'⟩ := Finset.mem_biUnion.1 he
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he'
        exact SimpleGraph.mem_edgeFinset.2 ((H.mem_neighborFinset t u).1 (Finset.mem_filter.1 hu).1)
      calc
        ∑ t ∈ T', (star t).card
            = ∑ t ∈ T', ((star t).image fun u => s(t, u)).card := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Finset.card_image_of_injective]
              intro u1 u2 heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        _ = (T'.biUnion fun t => (star t).image fun u => s(t, u)).card := (Finset.card_biUnion hdisj).symm
        _ ≤ H.edgeFinset.card := Finset.card_le_card hsub
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hT'pos : 0 < T'.card := Finset.card_pos.2 hT'ne
    have hLlen : L.length = T'.card := Finset.length_toList T'
    have hallLen : allWires.length = outs.length + A.card := by
      simp [allWires, aWires]
    refine ⟨⟨gs ++ e2, out2⟩, ?_, ?_, fun x => ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ⟨by simpa using (hgsok g hg).1, (hgsok g hg).2⟩
      · exact ⟨by simpa using (he2ok g hg).1, (he2ok g hg).2⟩
    · change (gs ++ e2).length ≤ A.card + H.edgeFinset.card + T.card - 1
      rw [List.length_append]
      omega
    · change (run (gs ++ e2) (List.ofFn x)).getD out2 false = _
      rw [he2ev x]
      simp only [allWires, List.any_append, houtsev x]
      have haEv : aWires.any (fun w => (run gs (List.ofFn x)).getD w false) = decide (∃ a ∈ A, x a = true) := by
        apply Bool.eq_iff_iff.mpr
        simp only [aWires, List.any_eq_true, List.mem_map, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨a, ha, rfl⟩, hxa⟩
          rw [Finset.mem_toList] at ha
          rw [run_input _ _ _ (by simp [a.isLt])] at hxa
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, a.isLt, ↓reduceDIte, Option.getD_some] at hxa
          exact ⟨a, ha, hxa⟩
        · rintro ⟨a, ha, hxa⟩
          refine ⟨a.val, ⟨a, Finset.mem_toList.2 ha, rfl⟩, ?_⟩
          rw [run_input _ _ _ (by simp [a.isLt])]
          simp [List.getD_eq_getElem?_getD, a.isLt, hxa]
      rw [haEv]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨t, _, hxt, u, hu, hxu⟩ | ⟨a, ha, hxa⟩)
        · exact Or.inr ⟨t, u, (H.mem_neighborFinset t u).1 (Finset.mem_filter.1 hu).1, hxt, hxu⟩
        · exact Or.inl ⟨a, ha, hxa⟩
      · rintro (⟨a, ha, hxa⟩ | ⟨i, j, hij, hxi, hxj⟩)
        · exact Or.inr ⟨a, ha, hxa⟩
        · rcases hown i j hij with ⟨hi, hj⟩ | ⟨hj, hi⟩
          · exact Or.inl ⟨i, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨hi, ⟨j, hj⟩⟩), hxi, j, hj, hxj⟩
          · exact Or.inl ⟨j, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨hj, ⟨i, hi⟩⟩), hxj, i, hi, hxi⟩
  intro n G A f C hdeg hgirth hisol hedge hspec hfan hfun hmin hread
  have hedgeCardEq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  by_cases hbench : ∃ T : Finset (Fin n), Disjoint A T ∧
      (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      A.card + G.edgeFinset.card + T.card ≤ C.size + 1
  · obtain ⟨T, hdisj, hcov, hbud⟩ := hbench
    obtain ⟨i0, j0, hij0⟩ := hedge
    have hmarked : ∃ v ∈ T, ∃ u : Fin n, G.Adj u v := by
      rcases hcov i0 j0 hij0 with hi | hj
      · exact ⟨i0, hi, j0, hij0.symm⟩
      · exact ⟨j0, hj, i0, hij0⟩
    obtain ⟨v, hvT, u, huv⟩ := hmarked
    have hvA : v ∉ A := fun h => (Finset.disjoint_left.1 hdisj) h hvT
    let H := G.deleteIncidenceSet v
    let T' := T.erase v
    have hkeep : ∃ w : Fin n, G.Adj u w ∧ w ≠ v := by
      by_contra hnone
      have hsub : G.neighborSet u ⊆ {v} := by
        intro w hw
        by_contra hwv
        exact hnone ⟨w, hw, hwv⟩
      have hle := Set.ncard_le_ncard hsub
      have hdu := hdeg u (hisol u v huv)
      rw [hdu, Set.ncard_singleton] at hle
      omega
    obtain ⟨w, huw, hwv⟩ := hkeep
    have hkept : H.Adj u w := SimpleGraph.deleteIncidenceSet_adj.2 ⟨huw, huv.ne, hwv⟩
    have hHpos : 0 < H.edgeFinset.card :=
      Finset.card_pos.2 ⟨s(u, w), SimpleGraph.mem_edgeFinset.2 hkept⟩
    have hcov' : ∀ a b : Fin n, H.Adj a b → a ∈ T' ∨ b ∈ T' := by
      intro a b hab
      obtain ⟨old, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.1 hab
      rcases hcov a b old with h | h
      · exact Or.inl (Finset.mem_erase.2 ⟨ha, h⟩)
      · exact Or.inr (Finset.mem_erase.2 ⟨hb, h⟩)
    have hHe : H.edgeFinset.card = G.edgeFinset.card - 3 := by
      have hd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (hdeg v hvA)
      have hdel := G.card_edgeFinset_deleteIncidenceSet v
      rw [hd] at hdel
      convert hdel using 1
    have hT'c : T'.card = T.card - 1 := Finset.card_erase_of_mem hvT
    have hTpos : 0 < T.card := Finset.card_pos.2 ⟨v, hvT⟩
    let s := A.card + H.edgeFinset.card + T'.card - 1
    have hs4 : s + 4 ≤ C.size := by
      dsimp only [s]
      omega
    have hcut := hStarCoverAny n H A T' hcov' ⟨u, w, hkept⟩
    have heq : ∀ x : Fin n → Bool,
        ((∃ a ∈ A, x a = true) ∨ ∃ a b : Fin n, H.Adj a b ∧ x a = true ∧ x b = true) ↔
        f (Function.update x v false) = true := by
      intro x
      rw [hspec]
      constructor
      · rintro (⟨a, ha, hxa⟩ | ⟨a, b, hab, hxa, hxb⟩)
        · have hav : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hav] using hxa⟩
        · obtain ⟨old, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.1 hab
          exact Or.inr ⟨a, b, old,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
      · rintro (⟨a, ha, hxa⟩ | ⟨a, b, hab, hxa, hxb⟩)
        · have hav : a ≠ v := fun e => hvA (e ▸ ha)
          exact Or.inl ⟨a, ha, by simpa [Function.update_of_ne hav] using hxa⟩
        · have ha : a ≠ v := fun e => by subst e; simp at hxa
          have hb : b ≠ v := fun e => by subst e; simp at hxb
          exact Or.inr ⟨a, b, SimpleGraph.deleteIncidenceSet_adj.2 ⟨hab, ha, hb⟩,
            by simpa [Function.update_of_ne ha] using hxa,
            by simpa [Function.update_of_ne hb] using hxb⟩
    obtain ⟨D, hD, hDsz, hDev⟩ := hcut
    refine ⟨v, hvA, s, hs4, D, hD, ?_, fun x => ?_⟩
    · convert hDsz using 1
      dsimp only [s]
      congr 2; congr 1; apply congrArg Finset.card; ext e; simp only [SimpleGraph.mem_edgeFinset]
    · rw [hDev x]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact heq x
  · have hsmall : ∀ T : Finset (Fin n), Disjoint A T →
        (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeSet.ncard + T.card := by
      intro T hdisj hcov
      rw [hedgeCardEq]
      exact lt_of_not_ge fun h => hbench ⟨T, hdisj, hcov, h⟩
    by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    · exact hWithNot n G A f C hdeg hgirth hisol hedge hspec hfan hnot hfun hmin hread hsmall
    · have hmono : PEqualNP.MetaComplexity.Monotone2 C := by
        intro g hg
        have hfg := hfan g hg
        have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hfg.1
        refine ⟨?_, hfg.2⟩
        rcases hop with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact False.elim (hnot ⟨g, hg, h1⟩)
      have hread_mono : ∀ v ∉ A,
          (C.gates.filter fun g => g.inputs.contains v.val).length ≤ (3 : ℕ) ∧
          ((C.gates.filter fun g => g.inputs.contains v.val).length = (3 : ℕ) →
            ∀ g ∈ C.gates.filter fun g => g.inputs.contains v.val,
              g.op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
        intro v hv
        have hfilt : C.gates.filter (fun g => (List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs).contains v.val) =
            C.gates.filter (fun g => g.inputs.contains v.val) := by
          refine List.filter_congr fun g hg => ?_
          have hmg := hmono g hg
          have hev : g.op.eval [Bool.false] = false := by
            rcases hmg.1 with hop | hop
            · rw [hop, andEval]; rfl
            · rw [hop, orEval]; rfl
          rw [hev]
          change (List.take 2 g.inputs).contains v.val = g.inputs.contains v.val
          rw [List.take_of_length_le hmg.2]
        have hr := hread v hv
        dsimp only at hr
        rw [hfilt] at hr
        exact hr
      exact hMono n G A f C hdeg hgirth hisol hedge hspec hmono hfun hmin hread_mono hsmall
