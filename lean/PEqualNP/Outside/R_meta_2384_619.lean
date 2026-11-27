import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2384_619
    (hJunk2Indep :
      let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        let U := PEqualNP.TopForm.Ustar G C
        let B := 2 * (PEqualNP.TopForm.centreless G C).card + 2 +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
        C.size ≤ 21 → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).card = 2 →
        a ∈ PEqualNP.TopForm.junk G C → b ∈ PEqualNP.TopForm.junk G C → a < b →
        U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
        (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K →
          B - U.card < (U.filter (fun e => ∀ v ∈ K, v ∉ e)).card) →
        (∀ t : Fin 2, ¬ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C b t) a) →
        (∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
            ∀ t : Fin 2, ∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true) →
        ∃ (K X : Finset (Fin 11)),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
          G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card)
    (hJunk2Dep :
      let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        let U := PEqualNP.TopForm.Ustar G C
        let B := 2 * (PEqualNP.TopForm.centreless G C).card + 2 +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
        C.size ≤ 21 → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).card = 2 →
        a ∈ PEqualNP.TopForm.junk G C → b ∈ PEqualNP.TopForm.junk G C → a < b →
        U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
        (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K →
          B - U.card < (U.filter (fun e => ∀ v ∈ K, v ∉ e)).card) →
        (∃ t : Fin 2, PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C b t) a) →
        (∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
            ∀ t : Fin 2, (∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true) ∨
              (j = b ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C j t) a ∧
                PEqualNP.ReadTwo.wval C x (11 + a) = true)) →
        ∃ (K X : Finset (Fin 11)),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
          G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card)
    (hJunkGe3 :
      let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        let U := PEqualNP.TopForm.Ustar G C
        let B := 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
        C.size ≤ 21 → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        3 ≤ (PEqualNP.TopForm.junk G C).card →
        a ∈ PEqualNP.TopForm.junk G C → b ∈ PEqualNP.TopForm.junk G C → a < b →
        U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
        (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K →
          B - U.card < (U.filter (fun e => ∀ v ∈ K, v ∉ e)).card) →
        (∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
            ∀ t : Fin 2, (∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true) ∨
              (j = b ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C j t) a ∧
                PEqualNP.ReadTwo.wval C x (11 + a) = true)) →
        ∃ (K X : Finset (Fin 11)),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
          G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card)
    : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  classical
  dsimp only
  intro C hSz21 hLeast hTop hJunk2
  let G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G C
  let B : ℕ := 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
    (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
  change U.card ≤ B → B < 2 * U.card →
    ∃ (K X : Finset (Fin 11)),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
      G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card
  intro hlo hhi
  by_cases hLarge : 7 ≤ B - U.card
  · let H := G.deleteEdges (↑U)
    let Q (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
    have ex : ∃ m, Q m := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hc, hk⟩ := Nat.find_spec ex
    have hm : PEqualNP.MetaComplexity.NestedCover.IsMinCover H K :=
      ⟨hc, fun T ht => hk.trans_le (Nat.find_min' ex ⟨T, ht, rfl⟩)⟩
    let X : Finset (Fin 11) := {0, 1, 3, 5, 7, 8, 10}
    have hx : G.IsVertexCover (↑X) := by
      change ∀ u v : Fin 11, G.Adj u v → u ∈ X ∨ v ∈ X
      dsimp [G, X]
      decide +kernel
    refine ⟨K, X, hm, ?_, ?_⟩
    · intro u v huv
      exact (hx huv).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
    · have h7 : X.card = 7 := by decide
      omega
  have hLt7 : B - U.card < 7 := Nat.lt_of_not_ge hLarge
  by_cases hEasy : ∃ K : Finset (Fin 11),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
      (U.filter (fun e => ∀ v ∈ K, v ∉ e)).card ≤ B - U.card
  · obtain ⟨K, hKmin, hUncLe⟩ := hEasy
    let unc : Finset (Sym2 (Fin 11)) := U.filter (fun e => ∀ v ∈ K, v ∉ e)
    let X : Finset (Fin 11) := unc.image (fun e => e.out.1)
    refine ⟨K, X, hKmin, ?_, (Finset.card_image_le).trans hUncLe⟩
    intro u v huv
    by_cases hmemU : s(u, v) ∈ U
    · by_cases hcovK : u ∈ K ∨ v ∈ K
      · exact hcovK.imp (Finset.mem_union_left X) (Finset.mem_union_left X)
      · have hunc : s(u, v) ∈ unc := by
          rw [Finset.mem_filter]
          refine ⟨hmemU, fun w hwK hwe => ?_⟩
          rw [Sym2.mem_iff] at hwe
          rcases hwe with rfl | rfl
          · exact hcovK (Or.inl hwK)
          · exact hcovK (Or.inr hwK)
        have hout_mem : (s(u, v)).out.1 ∈ s(u, v) := by
          have heq : s((s(u, v)).out.1, (s(u, v)).out.2) = s(u, v) := Quot.out_eq (s(u, v))
          have hm : (s(u, v)).out.1 ∈ s((s(u, v)).out.1, (s(u, v)).out.2) := Sym2.mem_mk_left _ _
          rwa [heq] at hm
        have hinX : (s(u, v)).out.1 ∈ X := Finset.mem_image_of_mem _ hunc
        rw [Sym2.mem_iff] at hout_mem
        rcases hout_mem with h1 | h2
        · exact Or.inl (Finset.mem_union_right K (h1 ▸ hinX))
        · exact Or.inr (Finset.mem_union_right K (h2 ▸ hinX))
    · have hadj : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, hmemU⟩
      exact (hKmin.1 hadj).imp (Finset.mem_union_left X) (Finset.mem_union_left X)
  have hHard : ∀ K : Finset (Fin 11),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K →
      B - U.card < (U.filter (fun e => ∀ v ∈ K, v ∉ e)).card := by
    intro K hK
    by_contra hle
    exact hEasy ⟨K, hK, Nat.le_of_not_lt hle⟩
  have hAO2 : PEqualNP.TopForm.IsAO2 11 C := hLeast.1
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := hAO2.1
  have hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 11 C := hAO2.2.1
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := hAO2.2.2
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]; rfl
  have hrun_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [hrun_snoc]; simp [ih]; omega
  have hgetD_lt : ∀ {α : Type} (l : List α) (b d : α) (t : ℕ), t < l.length →
      (l ++ [b]).getD t d = l.getD t d := by
    intro α l b d t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ {α : Type} (l : List α) (b d : α), (l ++ [b]).getD l.length d = b := by
    intro α l b d; simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1; exact h1
  have hrun_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map fun i =>
            if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := hrun_len gs x
      have hsame : ∀ k ≤ gs.length, ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hrun_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · have hgd : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd, hsame j (Nat.le_of_lt hlt), hrun_prefix gs [g] x _ (by omega)]
        exact ih j hlt
      · have hjeq : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
        subst hjeq
        have hgd : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hgd, hsame gs.length le_rfl, hrun_snoc, ← hlen, hgetD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hwval_in : ∀ (x : Fin 11 → Bool) (w : ℕ) (hw : w < 11),
      PEqualNP.ReadTwo.wval C x w = x ⟨w, hw⟩ := by
    intro x w hw
    change (run C.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [hrun_input C.gates (List.ofFn x) w (by simp [hw])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw]
    rfl
  have hgate_inputs : ∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs =
        [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] := by
    intro j hj
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
      change C.gates.getD j _ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 := hLen2 _ hmem
    rcases hgl : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · rw [hgl] at hlen; cases hlen
    · rw [hgl] at hlen; cases hlen
    · unfold PEqualNP.TopForm.opnd; rw [hgl]; rfl
    · rw [hgl] at hlen; cases hlen
  have hopnd_lt : ∀ j < C.gates.length, ∀ t : Fin 2, PEqualNP.TopForm.opnd C j t < 11 + j := by
    intro j hj t
    have hin := hgate_inputs j hj
    refine hRB j hj (PEqualNP.TopForm.opnd C j t) ?_
    rw [hin]
    fin_cases t <;> simp
  have hwval_gate : ∀ (x : Fin 11 → Bool) (j : ℕ) (hj : j < C.gates.length),
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.ReadTwo.wval C x (11 + j) =
          (PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 0) &&
           PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 1))) ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        PEqualNP.ReadTwo.wval C x (11 + j) =
          (PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 0) ||
           PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 1))) := by
    intro x j hj
    have hrg := hrun_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hrg
    have hin := hgate_inputs j hj
    have hlt0 : PEqualNP.TopForm.opnd C j 0 < 11 + j := hopnd_lt j hj 0
    have hlt1 : PEqualNP.TopForm.opnd C j 1 < 11 + j := hopnd_lt j hj 1
    change PEqualNP.ReadTwo.wval C x (11 + j) = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i =>
        if i < 11 + j then PEqualNP.ReadTwo.wval C x i else false) at hrg
    rw [hin, List.map_cons, List.map_cons, List.map_nil, ite_eq_left hlt0, ite_eq_left hlt1] at hrg
    constructor
    · intro hop; rw [hrg, hop, andEval]; simp
    · intro hop; rw [hrg, hop, orEval]; simp
  have hfold_append_rec : ∀ (f : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List (List ℕ)),
      (gs.foldl (fun cs g => cs ++ [f cs g]) init).length = init.length + gs.length := by
    intro f gs
    induction gs using List.reverseRecOn with
    | nil => intro init; simp
    | append_singleton gs g ih =>
      intro init; rw [List.foldl_append]; simp [ih]; omega
  have hfold_prefix : ∀ (f : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ)
      (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (init : List (List ℕ)) (i : ℕ),
      i < init.length + gs.length →
      ((gs ++ hs).foldl (fun cs g => cs ++ [f cs g]) init).getD i [] =
      (gs.foldl (fun cs g => cs ++ [f cs g]) init).getD i [] := by
    intro f gs hs init i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hgetD_lt _ _ _ _ (by rw [hfold_append_rec, List.length_append]; omega)]
      exact ih
  have hfold_at : ∀ (f : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ) (hm : m < gs.length),
      (gs.foldl (fun cs g => cs ++ [f cs g]) []).getD m [] =
      f ((gs.take m).foldl (fun cs g => cs ++ [f cs g]) []) (gs.getD m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩) := by
    intro f gs m hm
    have hsplit : gs = gs.take m ++ [gs[m]] ++ gs.drop (m + 1) := by
      have h1 : gs.take m ++ gs.drop m = gs := List.take_append_drop m gs
      have h2 : gs.drop m = gs[m] :: gs.drop (m + 1) := List.drop_eq_getElem_cons hm
      rw [h2] at h1
      rw [List.append_assoc]
      exact h1.symm
    have hlen_t : (gs.take m).length = m := List.length_take_of_le (Nat.le_of_lt hm)
    conv_lhs => rw [hsplit]
    rw [hfold_prefix f (gs.take m ++ [gs[m]]) (gs.drop (m + 1)) [] m (by rw [List.length_nil, Nat.zero_add, List.length_append, hlen_t, List.length_singleton]; omega)]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen_f : ((gs.take m).foldl (fun cs g => cs ++ [f cs g]) []).length = m := by
      rw [hfold_append_rec, List.length_nil, Nat.zero_add, hlen_t]
    have hat := hgetD_at ((gs.take m).foldl (fun cs g => cs ++ [f cs g]) [])
      (f ((gs.take m).foldl (fun cs g => cs ++ [f cs g]) []) gs[m]) []
    rw [hlen_f] at hat
    rw [hat]
    congr 1
    exact (List.getD_eq_getElem _ _ hm).symm
  have hfold_take_getD : ∀ (f : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ)
      (gs : List PEqualNP.CircuitLowerBounds.Gate) (m k : ℕ), k < m → m ≤ gs.length →
      ((gs.take m).foldl (fun cs g => cs ++ [f cs g]) []).getD k [] =
      (gs.foldl (fun cs g => cs ++ [f cs g]) []).getD k [] := by
    intro f gs m k hkm hm
    have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
    have hlen_t : (gs.take m).length = m := List.length_take_of_le hm
    conv_rhs => rw [hsplit]
    rw [hfold_prefix f (gs.take m) (gs.drop m) [] k (by rw [List.length_nil, Nat.zero_add, hlen_t]; exact hkm)]
  have horSets_at : ∀ m < C.gates.length,
      (PEqualNP.CleanedNonEdge.orSets 11 C).getD m [] =
      m :: (if (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.or then
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + m))).flatMap
          (fun w => (PEqualNP.CleanedNonEdge.orSets 11 C).getD (w - 11) [])
        else []) := by
    intro m hm
    let stepF : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun cs g =>
      cs.length :: (@ite (List ℕ) (g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (PEqualNP.MetaComplexity.NestedCover.gateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.or)
        ((g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
          (fun w => cs.getD (w - 11) []))
        [])
    have h1 := hfold_at stepF C.gates m hm
    have hlen : ((C.gates.take m).foldl (fun cs g => cs ++ [stepF cs g]) []).length = m := by
      rw [hfold_append_rec, List.length_nil, Nat.zero_add, List.length_take_of_le (Nat.le_of_lt hm)]
    change (C.gates.foldl (fun cs g => cs ++ [stepF cs g]) []).getD m [] = _
    rw [h1]
    dsimp only [stepF]
    rw [hlen]
    congr 1
    by_cases hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.or
    · rw [ite_eq_left hop]
      have hop' : (C.gates.getD m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or := hop
      rw [ite_eq_left hop']
      refine List.flatMap_congr fun w hw => ?_
      have hwf := (List.mem_filter.mp hw).2
      rw [decide_eq_true_eq] at hwf
      exact hfold_take_getD stepF C.gates m (w - 11) (by omega) (Nat.le_of_lt hm)
    · rw [ite_eq_right hop]
      have hop' : ¬ (C.gates.getD m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or := hop
      rw [ite_eq_right hop']
  have hcones_at : ∀ m < C.gates.length,
      (PEqualNP.EdgeOwnership.cones 11 C).getD m [] =
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + m))).flatMap
        (fun w => (w - 11) :: (PEqualNP.EdgeOwnership.cones 11 C).getD (w - 11) []) := by
    intro m hm
    let stepC : List (List ℕ) → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun cs g =>
      (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
        (fun w => (w - 11) :: cs.getD (w - 11) [])
    have h1 := hfold_at stepC C.gates m hm
    have hlen : ((C.gates.take m).foldl (fun cs g => cs ++ [stepC cs g]) []).length = m := by
      rw [hfold_append_rec, List.length_nil, Nat.zero_add, List.length_take_of_le (Nat.le_of_lt hm)]
    change (C.gates.foldl (fun cs g => cs ++ [stepC cs g]) []).getD m [] = _
    rw [h1]
    dsimp only [stepC]
    rw [hlen]
    refine List.flatMap_congr fun w hw => ?_
    have hwf := (List.mem_filter.mp hw).2
    rw [decide_eq_true_eq] at hwf
    congr 1
    exact hfold_take_getD stepC C.gates m (w - 11) (by omega) (Nat.le_of_lt hm)
  have hOrSets_sub : ∀ m < C.gates.length, ∀ k ∈ (PEqualNP.CleanedNonEdge.orSets 11 C).getD m [],
      k ≤ m ∧ (k = m ∨ k ∈ (PEqualNP.EdgeOwnership.cones 11 C).getD m []) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm k hk
      rw [horSets_at m hm, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact ⟨le_rfl, Or.inl rfl⟩
      · split_ifs at hk with hop
        · rw [List.mem_flatMap] at hk
          rcases hk with ⟨w, hw, hkw⟩
          have hwf := (List.mem_filter.mp hw).2
          rw [decide_eq_true_eq] at hwf
          have hsub := ih (w - 11) (by omega) (by omega) k hkw
          refine ⟨by omega, Or.inr ?_⟩
          rw [hcones_at m hm, List.mem_flatMap]
          refine ⟨w, hw, ?_⟩
          rw [List.mem_cons]
          exact hsub.2
        · cases hk
  have hOrReaches_inCone : ∀ j < C.gates.length, ∀ t : Fin 2, ∀ k : ℕ,
      PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C j t) k →
      k < j ∧ PEqualNP.EdgeOwnership.InCone 11 C k j := by
    intro j hj t k hr
    have hlt : PEqualNP.TopForm.opnd C j t < 11 + j := hopnd_lt j hj t
    have hw11 : 11 ≤ PEqualNP.TopForm.opnd C j t := hr.1
    have hkm : k ∈ (PEqualNP.CleanedNonEdge.orSets 11 C).getD (PEqualNP.TopForm.opnd C j t - 11) [] := hr.2
    have hsub := hOrSets_sub (PEqualNP.TopForm.opnd C j t - 11) (by omega) k hkm
    refine ⟨by omega, ?_⟩
    unfold PEqualNP.EdgeOwnership.InCone
    rw [hcones_at j hj, List.mem_flatMap]
    refine ⟨PEqualNP.TopForm.opnd C j t, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨?_, decide_eq_true ⟨hw11, hlt⟩⟩
      rw [hgate_inputs j hj]
      fin_cases t <;> simp
    · rw [List.mem_cons]
      exact hsub.2
  have hOrReaches_or_step : ∀ m < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ∀ k : ℕ, PEqualNP.CleanedNonEdge.OrReaches 11 C (11 + m) k ↔
        k = m ∨ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C m 0) k ∨
          PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C m 1) k := by
    intro m hm hop k
    unfold PEqualNP.CleanedNonEdge.OrReaches
    have h11 : 11 ≤ 11 + m := by omega
    have hsub : 11 + m - 11 = m := by omega
    rw [and_iff_right h11, hsub, horSets_at m hm, ite_eq_left hop, List.mem_cons, List.mem_flatMap]
    have hin := hgate_inputs m hm
    have hlt0 := hopnd_lt m hm 0
    have hlt1 := hopnd_lt m hm 1
    constructor
    · rintro (rfl | ⟨w, hw, hkw⟩)
      · exact Or.inl rfl
      · rw [List.mem_filter, hin, List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hw
        rcases hw.1 with rfl | rfl
        · exact Or.inr (Or.inl ⟨hw.2.1, hkw⟩)
        · exact Or.inr (Or.inr ⟨hw.2.1, hkw⟩)
    · rintro (rfl | ⟨hw0, hk0⟩ | ⟨hw1, hk1⟩)
      · exact Or.inl rfl
      · refine Or.inr ⟨PEqualNP.TopForm.opnd C m 0, ?_, hk0⟩
        rw [List.mem_filter, hin]
        exact ⟨by simp, decide_eq_true ⟨hw0, hlt0⟩⟩
      · refine Or.inr ⟨PEqualNP.TopForm.opnd C m 1, ?_, hk1⟩
        rw [List.mem_filter, hin]
        exact ⟨by simp, decide_eq_true ⟨hw1, hlt1⟩⟩
  have hWireChar : ∀ (x : Fin 11 → Bool) (w : ℕ), w < 11 + C.gates.length →
      (PEqualNP.ReadTwo.wval C x w = true ↔
        (∃ v ∈ PEqualNP.TopForm.orIn 11 C w, x v = true) ∨
        (∃ k < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches 11 C w k ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.ReadTwo.wval C x (11 + k) = true)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt
      by_cases hw11 : w < 11
      · rw [hwval_in x w hw11]
        constructor
        · intro hx
          refine Or.inl ⟨⟨w, hw11⟩, ?_, hx⟩
          unfold PEqualNP.TopForm.orIn
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl trivial
        · rintro (⟨v, hv, hxv⟩ | ⟨k, _, hkr, _, _⟩)
          · unfold PEqualNP.TopForm.orIn at hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            rcases hv with hvw | ⟨k, _, hkr, _, _⟩
            · have : v = ⟨w, hw11⟩ := Fin.ext hvw
              rwa [← this]
            · exfalso; have := hkr.1; omega
          · exfalso; have := hkr.1; omega
      · let m : ℕ := w - 11
        have hwm : w = 11 + m := by omega
        have hmC : m < C.gates.length := by omega
        rw [hwm]
        have hgm_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C m ∈ C.gates := by
          change C.gates.getD m _ ∈ C.gates
          rw [List.getD_eq_getElem _ _ hmC]
          exact List.getElem_mem hmC
        rcases hAO (PEqualNP.MetaComplexity.NestedCover.gateAt C m) hgm_mem with hand | hor
        · have hor_only : ∀ k, PEqualNP.CleanedNonEdge.OrReaches 11 C (11 + m) k ↔ k = m := by
            intro k
            unfold PEqualNP.CleanedNonEdge.OrReaches
            have h11 : 11 ≤ 11 + m := by omega
            have hsub : 11 + m - 11 = m := by omega
            rw [and_iff_right h11, hsub, horSets_at m hmC]
            have hne : ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
              rw [hand]; intro h; cases h
            rw [ite_eq_right hne]
            simp
          constructor
          · intro hval
            exact Or.inr ⟨m, hmC, (hor_only m).mpr rfl, hand, hval⟩
          · rintro (⟨v, hv, _⟩ | ⟨k, _, hkr, _, hkv⟩)
            · exfalso
              unfold PEqualNP.TopForm.orIn at hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
              rcases hv with hvw | ⟨k, _, hkr, hkor, _⟩
              · have := v.isLt; omega
              · have hkm := (hor_only k).mp hkr
                subst hkm; rw [hand] at hkor; cases hkor
            · have hkm := (hor_only k).mp hkr
              subst hkm; exact hkv
        · rw [(hwval_gate x m hmC).2 hor, Bool.or_eq_true]
          have hlt0 := hopnd_lt m hmC 0
          have hlt1 := hopnd_lt m hmC 1
          rw [ih (PEqualNP.TopForm.opnd C m 0) (by omega) (by omega)]
          rw [ih (PEqualNP.TopForm.opnd C m 1) (by omega) (by omega)]
          have hin := hgate_inputs m hmC
          have horIn_step : ∀ v : Fin 11,
              v ∈ PEqualNP.TopForm.orIn 11 C (11 + m) ↔
                v ∈ PEqualNP.TopForm.orIn 11 C (PEqualNP.TopForm.opnd C m 0) ∨
                v ∈ PEqualNP.TopForm.orIn 11 C (PEqualNP.TopForm.opnd C m 1) := by
            intro v
            unfold PEqualNP.TopForm.orIn
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (hvw | ⟨k, hkC, hkr, hkor, hvk⟩)
              · exfalso; have := v.isLt; omega
              · rcases (hOrReaches_or_step m hmC hor k).mp hkr with rfl | hr0 | hr1
                · rw [hin, List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hvk
                  rcases hvk with hv0 | hv1
                  · exact Or.inl (Or.inl hv0)
                  · exact Or.inr (Or.inl hv1)
                · exact Or.inl (Or.inr ⟨k, hkC, hr0, hkor, hvk⟩)
                · exact Or.inr (Or.inr ⟨k, hkC, hr1, hkor, hvk⟩)
            · rintro ((hv0 | ⟨k, hkC, hr0, hkor, hvk⟩) | (hv1 | ⟨k, hkC, hr1, hkor, hvk⟩))
              · refine Or.inr ⟨m, hmC, (hOrReaches_or_step m hmC hor m).mpr (Or.inl rfl), hor, ?_⟩
                rw [hin, hv0]; simp
              · exact Or.inr ⟨k, hkC, (hOrReaches_or_step m hmC hor k).mpr (Or.inr (Or.inl hr0)), hkor, hvk⟩
              · refine Or.inr ⟨m, hmC, (hOrReaches_or_step m hmC hor m).mpr (Or.inl rfl), hor, ?_⟩
                rw [hin, hv1]; simp
              · exact Or.inr ⟨k, hkC, (hOrReaches_or_step m hmC hor k).mpr (Or.inr (Or.inr hr1)), hkor, hvk⟩
          constructor
          · rintro ((⟨v, hv, hxv⟩ | ⟨k, hkC, hr0, hkand, hkv⟩) | (⟨v, hv, hxv⟩ | ⟨k, hkC, hr1, hkand, hkv⟩))
            · exact Or.inl ⟨v, (horIn_step v).mpr (Or.inl hv), hxv⟩
            · exact Or.inr ⟨k, hkC, (hOrReaches_or_step m hmC hor k).mpr (Or.inr (Or.inl hr0)), hkand, hkv⟩
            · exact Or.inl ⟨v, (horIn_step v).mpr (Or.inr hv), hxv⟩
            · exact Or.inr ⟨k, hkC, (hOrReaches_or_step m hmC hor k).mpr (Or.inr (Or.inr hr1)), hkand, hkv⟩
          · rintro (⟨v, hv, hxv⟩ | ⟨k, hkC, hkr, hkand, hkv⟩)
            · rcases (horIn_step v).mp hv with hv0 | hv1
              · exact Or.inl (Or.inl ⟨v, hv0, hxv⟩)
              · exact Or.inr (Or.inl ⟨v, hv1, hxv⟩)
            · rcases (hOrReaches_or_step m hmC hor k).mp hkr with rfl | hr0 | hr1
              · exfalso; rw [hor] at hkand; cases hkand
              · exact Or.inl (Or.inr ⟨k, hkC, hr0, hkand, hkv⟩)
              · exact Or.inr (Or.inr ⟨k, hkC, hr1, hkand, hkv⟩)
  let J := PEqualNP.TopForm.junk G C
  have hJ2 : 2 ≤ J.card := hJunk2
  have hJpos : J.Nonempty := Finset.card_pos.mp (by omega)
  let a := J.min' hJpos
  have haJ : a ∈ J := J.min'_mem hJpos
  let Kset := J.erase a
  have hKcard : Kset.card = J.card - 1 := Finset.card_erase_of_mem haJ
  have hKpos : Kset.Nonempty := Finset.card_pos.mp (by omega)
  let b := Kset.min' hKpos
  have hbK : b ∈ Kset := Kset.min'_mem hKpos
  have hbSplit := Finset.mem_erase.mp hbK
  have hbJ : b ∈ J := hbSplit.2
  have hab : a < b := lt_of_le_of_ne (J.min'_le b hbJ) (Ne.symm hbSplit.1)
  have hEarly : ∀ k ∈ J, k < b → k = a := by
    intro k hk hkb
    by_contra hka
    exact (not_lt_of_ge (Kset.min'_le k (Finset.mem_erase.mpr ⟨hka, hk⟩))) hkb
  have hJunkMem : ∀ j ∈ J, j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro j hj
    have hj' : j ∈ (Finset.range C.gates.length).filter (fun i => PEqualNP.CleanedNonEdge.IsDirtyAnd 11 G C i) := hj
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    exact ⟨hj'.1, hj'.2.1⟩
  have hNotBelowF_of_dirty : ∀ k < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.TopForm.BelowF G C k → k ∈ J := by
    intro k hk hand hnb
    change k ∈ (Finset.range C.gates.length).filter (fun i => PEqualNP.CleanedNonEdge.IsDirtyAnd 11 G C i)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hk, hand, hk, ?_⟩
    by_contra hall
    apply hnb
    intro x hkx
    cases hfx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
    · exact False.elim (hall ⟨x, hkx, hfx⟩)
    · rfl
  have hAndChar : ∀ j ∈ J, (∀ k ∈ J, k < j → k = a) → ∀ x : Fin 11 → Bool,
      PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
        ∀ t : Fin 2, (∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true) ∨
          (j ≠ a ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C j t) a ∧
            PEqualNP.ReadTwo.wval C x (11 + a) = true) := by
    intro j hjJ hltj x
    obtain ⟨hjC, hjand⟩ := hJunkMem j hjJ
    rw [(hwval_gate x j hjC).1 hjand, Bool.and_eq_true]
    have hfin2 : (PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 0) = true ∧
        PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j 1) = true) ↔
        ∀ t : Fin 2, PEqualNP.ReadTwo.wval C x (PEqualNP.TopForm.opnd C j t) = true := by
      constructor
      · intro h t; fin_cases t; exact h.1; exact h.2
      · intro h; exact ⟨h 0, h 1⟩
    rw [hfin2]
    refine forall_congr' fun t => ?_
    have hlt := hopnd_lt j hjC t
    rw [hWireChar x (PEqualNP.TopForm.opnd C j t) (by omega)]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨k, hkC, hkr, hkand, hkv⟩
      obtain ⟨hkj, hcone⟩ := hOrReaches_inCone j hjC t k hkr
      have hnb : ¬ PEqualNP.TopForm.BelowF G C k := fun hbf =>
        hTop k hkC j hjC hkand hbf hjand hcone
      have hkJ : k ∈ J := hNotBelowF_of_dirty k hkC hkand hnb
      have hka : k = a := hltj k hkJ hkj
      subst hka
      exact ⟨by omega, hkr, hkv⟩
    · rintro ⟨_, har, hav⟩
      exact ⟨a, (hJunkMem a haJ).1, har, (hJunkMem a haJ).2, hav⟩
  have hCharA : ∀ x : Fin 11 → Bool,
      PEqualNP.ReadTwo.wval C x (11 + a) = true ↔
        ∀ t : Fin 2, ∃ v ∈ PEqualNP.TopForm.side (n := 11) C a t, x v = true := by
    intro x
    rw [hAndChar a haJ (fun k hk hka => absurd hka (not_lt_of_ge (J.min'_le k hk))) x]
    refine forall_congr' fun t => ?_
    simp
  have hCharB : ∀ x : Fin 11 → Bool,
      PEqualNP.ReadTwo.wval C x (11 + b) = true ↔
        ∀ t : Fin 2, (∃ v ∈ PEqualNP.TopForm.side (n := 11) C b t, x v = true) ∨
          (PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C b t) a ∧
            PEqualNP.ReadTwo.wval C x (11 + a) = true) := by
    intro x
    rw [hAndChar b hbJ hEarly x]
    refine forall_congr' fun t => ?_
    have hba : b ≠ a := by omega
    simp [hba]
  have hCharBoth : ∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
      PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
        ∀ t : Fin 2, (∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true) ∨
          (j = b ∧ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C j t) a ∧
            PEqualNP.ReadTwo.wval C x (11 + a) = true) := by
    intro j hj x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · rw [hCharA x]
      refine forall_congr' fun t => ?_
      have hne : a ≠ b := by omega
      simp [hne]
    · rw [hCharB x]
      refine forall_congr' fun t => ?_
      simp
  by_cases hJeq2 : (PEqualNP.TopForm.junk G C).card = 2
  · have hBeq : B = 2 * (PEqualNP.TopForm.centreless G C).card + 2 +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card := by
      dsimp only [B]; rw [hJeq2]
    rw [hBeq] at hlo hhi hLt7 hHard ⊢
    by_cases hDep : ∃ t : Fin 2, PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C b t) a
    · exact hJunk2Dep C a b hSz21 hLeast hTop hJeq2 haJ hbJ hab hlo hhi hLt7 hHard hDep hCharBoth
    · have hIndep : ∀ t : Fin 2, ¬ PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C b t) a := by
        intro t ht; exact hDep ⟨t, ht⟩
      have hCharAB : ∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          PEqualNP.ReadTwo.wval C x (11 + j) = true ↔
            ∀ t : Fin 2, ∃ v ∈ PEqualNP.TopForm.side (n := 11) C j t, x v = true := by
        intro j hj x
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl
        · exact hCharA x
        · rw [hCharB x]
          refine forall_congr' fun t => ?_
          simp [hIndep t]
      exact hJunk2Indep C a b hSz21 hLeast hTop hJeq2 haJ hbJ hab hlo hhi hLt7 hHard hIndep hCharAB
  · have hJge3 : 3 ≤ (PEqualNP.TopForm.junk G C).card := by
      change 2 ≤ (PEqualNP.TopForm.junk G C).card at hJunk2
      omega
    exact hJunkGe3 C a b hSz21 hLeast hTop hJge3 haJ hbJ hab hlo hhi hLt7 hHard hCharBoth
