import PEqualNP.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Order.Preorder.Finite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The small-support argument is adapted from brandonbodily's L-meta-4039, PR 8309.
-- Input relabeling follows MetaComplexity/Helpers/PermInputs.lean.
-- Explicit plane symmetries reduce the independent supports to two fixed pairs.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_4328_741
    (sameShore :
      let edge (u v : Fin 42) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x)=true ↔
          ∃ u v, edge u v ∧ x u=true ∧ x v=true) →
        (∃ j g, C.gates[j]?=some g ∧ g.op=GateOp.and ∧
          (C.wires (List.ofFn (fun i : Fin 42 => decide (i=0 ∨ i=1)))).getD (42+j) false=true) → False)
    (crossShore :
      let edge (u v : Fin 42) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x)=true ↔
          ∃ u v, edge u v ∧ x u=true ∧ x v=true) →
        (∃ j g, C.gates[j]?=some g ∧ g.op=GateOp.and ∧
          (C.wires (List.ofFn (fun i : Fin 42 => decide (i=0 ∨ i=22)))).getD (42+j) false=true) → False)
    :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (124 : ℕ) → (∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) → (∀ (x7 x8 : Fin (42 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7 ∨ x10 = x8)) = Bool.true) → (∀ (x8 : Fin (42 : ℕ) → Bool), x2 x8 → x3.eval (List.ofFn x8) = Bool.false) → False := by
  classical
  have eval_and (xs : List Bool) : GateOp.and.eval xs = xs.all id := by rfl
  have eval_or (xs : List Bool) : GateOp.or.eval xs = xs.any id := by rfl
  have eval_not (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := by rfl
  have wires_def (C : Circuit) (xs : List Bool) : C.wires xs =
      C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs := by rfl
  have size_def (C : Circuit) : C.size = C.gates.length := by rfl

  let s_step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let s_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
    (gs.foldl s_step (List.ofFn x)).getD i false

  have s_fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl s_step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_cons]
      simp only [s_step, List.length_append, List.length_cons, List.length_nil]
      omega

  have s_val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
      s_val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
    unfold s_val
    by_cases h : i < n
    · simp [List.getD_eq_getElem?_getD, h]
    · simp [List.getD_eq_getElem?_getD, h]

  have s_val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
      s_val (gs ++ [g]) x i =
        if i = n + gs.length then g.op.eval (g.inputs.map fun j => s_val gs x j)
        else s_val gs x i := by
    unfold s_val
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, s_step]
    have hl : (gs.foldl s_step (List.ofFn x)).length = n + gs.length := by
      rw [s_fold_length]
      simp
    simp only [s_step, List.getD_eq_getElem?_getD] at hl
    rcases lt_trichotomy i (n + gs.length) with h | h | h
    · rw [if_neg (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rw [if_pos h]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp [hl, h]
    · rw [if_neg (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

  have s_val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
      s_val gs x i = false := by
    unfold s_val
    have hl : (gs.foldl s_step (List.ofFn x)).length = n + gs.length := by
      rw [s_fold_length]
      simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

  have s_val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      s_val gs x i = x ⟨i, hi⟩ := by
    induction gs using List.reverseRecOn with
    | nil =>
      rw [s_val_nil]
      simp [hi]
    | append_singleton gs g ih =>
      rw [s_val_snoc, if_neg (by omega)]
      exact ih

  have s_val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
      ∀ (k : ℕ) (hk : k < gs.length), s_val gs x (n + k) =
        gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then s_val gs x j else false) := by
    induction gs using List.reverseRecOn with
    | nil =>
      intro k hk
      simp at hk
    | append_singleton gs g ih =>
      intro k hk
      by_cases hkl : k = gs.length
      · subst hkl
        have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
        rw [hgl, s_val_snoc, if_pos rfl]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases hj : j < n + gs.length
        · rw [if_pos hj, s_val_snoc, if_neg (by omega)]
        · rw [if_neg hj, s_val_ge gs x j (by omega)]
      · have hk' : k < gs.length + 1 := by simpa using hk
        have hk2 : k < gs.length := by omega
        have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
        rw [hget, s_val_snoc, if_neg (by omega), ih k hk2]
        congr 1
        apply List.map_congr_left
        intro j _
        by_cases hj : j < n + k
        · rw [if_pos hj, if_pos hj, s_val_snoc, if_neg (by omega)]
        · rw [if_neg hj, if_neg hj]

  have s_mono {n : ℕ} (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
      ∀ i, s_val gs x i = true → s_val gs x' i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h1 : i < n
      · rw [s_val_lt gs x i h1] at hi
        rw [s_val_lt gs x' i h1]
        exact hle _ hi
      · by_cases h2 : n + gs.length ≤ i
        · rw [s_val_ge gs x i h2] at hi
          exact absurd hi (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
          have hk : k < gs.length := by omega
          rw [s_val_gate gs x k hk] at hi
          rw [s_val_gate gs x' k hk]
          obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
          generalize gs[k] = g at hi hop hlen ⊢
          obtain ⟨op, ins⟩ := g
          simp only at hi hop hlen ⊢
          have rd : ∀ a : ℕ, (if a < n + k then s_val gs x a else false) = true →
              (if a < n + k then s_val gs x' a else false) = true := by
            intro a ha
            by_cases hlt : a < n + k
            · rw [if_pos hlt] at ha ⊢
              exact ih a hlt ha
            · rw [if_neg hlt] at ha
              exact absurd ha (by simp)
          rcases hop with rfl | rfl
          · simp only [eval_and, eval_or, eval_not, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro b ⟨a,ha,rfl⟩
            exact rd a (hi _ ⟨a,ha,rfl⟩)
          · simp only [eval_and, eval_or, eval_not, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            obtain ⟨_,⟨a,ha,rfl⟩,hv⟩ := hi
            exact ⟨_,⟨a,ha,rfl⟩,rd a hv⟩


  let s_ind {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ S)

  have s_ind_mono {n : ℕ} (S T : Finset (Fin n)) (h : S ⊆ T) :
      ∀ v, s_ind S v = true → s_ind T v = true := by
    intro v hv
    simp only [s_ind, decide_eq_true_eq] at hv ⊢
    exact h hv

  -- below the first true AND gate, a true wire is already true at one element of S
  have s_single {n : ℕ} (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (S : Finset (Fin n)) (k0 : ℕ)
      (hmin : ∀ j, j < k0 → ∀ hj : j < gs.length, gs[j].op = GateOp.and →
        s_val gs (s_ind S) (n + j) ≠ true) :
      ∀ w, w < n + k0 → s_val gs (s_ind S) w = true →
        ∃ i ∈ S, s_val gs (s_ind {i}) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hi
      by_cases h1 : w < n
      · rw [s_val_lt gs _ w h1] at hi
        refine ⟨⟨w, h1⟩, ?_, ?_⟩
        · simpa [s_ind] using hi
        · rw [s_val_lt gs _ w h1]
          simp [s_ind]
      · by_cases h2 : n + gs.length ≤ w
        · rw [s_val_ge gs _ w h2] at hi
          exact absurd hi (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < gs.length := by omega
          have hk0 : k < k0 := by omega
          rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
          · exact absurd hi (hmin k hk0 hk hop)
          · rw [s_val_gate gs _ k hk, hop] at hi
            simp only [eval_and, eval_or, eval_not, List.any_eq_true, List.mem_map, id_eq] at hi
            obtain ⟨b, ⟨a, ha, hab⟩, hb⟩ := hi
            subst hab
            by_cases hlt : a < n + k
            · rw [if_pos hlt] at hb
              obtain ⟨i, hiS, hv⟩ := ih a hlt (by omega) hb
              refine ⟨i, hiS, ?_⟩
              rw [s_val_gate gs _ k hk, hop]
              simp only [eval_and, eval_or, eval_not, List.any_eq_true, List.mem_map, id_eq]
              exact ⟨_, ⟨a, ha, rfl⟩, by rw [if_pos hlt]; exact hv⟩
            · rw [if_neg hlt] at hb
              exact absurd hb (by simp)

  have s_gather {n : ℕ} (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (S : Finset (Fin n)) (l : List ℕ)
      (h : ∀ a ∈ l, ∃ i ∈ S, s_val gs (s_ind {i}) a = true) :
      ∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≤ l.length ∧ ∀ a ∈ l, s_val gs (s_ind T) a = true := by
    induction l with
    | nil => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | cons a l ih =>
      obtain ⟨T, hTS, hTc, hT⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      obtain ⟨i, hiS, hv⟩ := h a (List.mem_cons_self)
      refine ⟨insert i T, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hiS hTS
      · have := Finset.card_insert_le i T
        simp only [List.length_cons]
        omega
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact s_mono gs hg _ _ (s_ind_mono _ _ (by simp)) _ hv
        · exact s_mono gs hg _ _ (s_ind_mono _ _ (Finset.subset_insert _ _)) _ (hT b hb)

  have s_core {n : ℕ} (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (S : Finset (Fin n)) (k : ℕ) (hk : k < gs.length) (hop : gs[k].op = GateOp.and)
      (hv : s_val gs (s_ind S) (n + k) = true) :
      ∃ T ⊆ S, T.card ≤ 2 ∧ ∃ k', ∃ hk' : k' < gs.length, gs[k'].op = GateOp.and ∧
        s_val gs (s_ind T) (n + k') = true := by
    classical
    have hex : ∃ j, ∃ hj : j < gs.length, gs[j].op = GateOp.and ∧ s_val gs (s_ind S) (n + j) = true :=
      ⟨k, hk, hop, hv⟩
    obtain ⟨hk0, hop0, hv0⟩ := Nat.find_spec hex
    have hmin : ∀ j, j < Nat.find hex → ∀ hj : j < gs.length, gs[j].op = GateOp.and →
        s_val gs (s_ind S) (n + j) ≠ true := by
      intro j hj hjl hjop hjv
      exact Nat.find_min hex hj ⟨hjl, hjop, hjv⟩
    generalize Nat.find hex = k0 at hk0 hop0 hv0 hmin
    have hall : ∀ a ∈ gs[k0].inputs, a < n + k0 ∧ s_val gs (s_ind S) a = true := by
      intro a ha
      rw [s_val_gate gs _ k0 hk0, hop0] at hv0
      simp only [eval_and, eval_or, eval_not, List.all_eq_true, List.mem_map, id_eq] at hv0
      have h := hv0 _ ⟨a, ha, rfl⟩
      by_cases hlt : a < n + k0
      · rw [if_pos hlt] at h
        exact ⟨hlt, h⟩
      · rw [if_neg hlt] at h
        exact absurd h (by simp)
    obtain ⟨T, hTS, hTc, hT⟩ := s_gather gs hg S gs[k0].inputs
      (fun a ha => s_single gs hg S k0 hmin a (hall a ha).1 (hall a ha).2)
    refine ⟨T, hTS, le_trans hTc (hg _ (List.getElem_mem hk0)).2, k0, hk0, hop0, ?_⟩
    rw [s_val_gate gs _ k0 hk0, hop0]
    simp only [eval_and, eval_or, eval_not, List.all_eq_true, List.mem_map, id_eq]
    rintro b ⟨a, ha, rfl⟩
    rw [if_pos (hall a ha).1]
    exact hT a ha

  have s_main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x2 →
      ∀ (x5 : Finset (Fin x1)),
        (∃ (x5' : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5']? = Option.some x6 ∧
          x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x5))).getD (x1 + x5') Bool.false = Bool.true) →
        ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧
          ∃ (x5' : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5']? = Option.some x6 ∧
            x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            (x2.wires (List.ofFn fun (x8 : Fin x1) => Decidable.decide (x8 ∈ x7))).getD (x1 + x5') Bool.false = Bool.true := by
    intro n C hM S hh
    rcases hh with ⟨k, g, hkg, hop, hv⟩
    have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hgm
      obtain ⟨h1, h2⟩ := hM g hgm
      refine ⟨?_, h2⟩
      simpa using h1
    obtain ⟨hk, hkeq⟩ := List.getElem?_eq_some_iff.mp hkg
    subst hkeq
    have hv' : s_val C.gates (s_ind S) (n + k) = true := hv
    obtain ⟨T, hTS, hTc, k', hk', hop', hv''⟩ := s_core C.gates hg S k hk hop hv'
    exact ⟨T, hTS, hTc, k', C.gates[k'], List.getElem?_eq_getElem hk', hop', hv''⟩

  have r_getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by simp

  let r_wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let r_relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (r_wmap n m π)⟩

  let r_relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (r_relGate n m π), r_wmap n m π C.output⟩

  let r_step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let r_Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (r_wmap n m π w) false = W.getD w false

  have r_rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : r_Rel n m π W W') : r_Rel n m π (r_step W g) (r_step W' (r_relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (r_relGate n m π g).op.eval
        ((r_relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [r_relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [r_step]; omega, by simp [r_step]; omega, ?_⟩
    intro w
    simp only [r_step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : r_wmap n m π w < W'.length := by
        unfold r_wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : r_wmap n m π w = W'.length := by
        unfold r_wmap
        split
        · omega
        · omega
      rw [he, hw, r_getD_snoc_eq, r_getD_snoc_eq]
    · have hge : W'.length + 1 ≤ r_wmap n m π w := by
        unfold r_wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have r_rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, r_Rel n m π W W' →
        r_Rel n m π (gs.foldl r_step W) ((gs.map (r_relGate n m π)).foldl r_step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (r_rel_step n m π W W' g h)

  have r_rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
      r_Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp; omega, ?_⟩
    intro w
    unfold r_wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]


  have r_size (n : Nat) (π : Fin n → Fin n) (C : Circuit) :
      (r_relabel n n π C).size = C.size := by simp [r_relabel,size_def]

  have r_monotone2 (n : Nat) (π : Fin n → Fin n) (C : Circuit) (h : Monotone2 C) :
      Monotone2 (r_relabel n n π C) := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g0 hg0).1, by simpa [r_relGate] using (h g0 hg0).2⟩

  have r_eval (n : Nat) (π : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
      (r_relabel n n π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
    exact (r_rel_fold n n π C.gates _ _ (r_rel_init n n π x)).2.2 C.output

  have r_gate_value (n : Nat) (π : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (j : Nat) :
      ((r_relabel n n π C).wires (List.ofFn x)).getD (n+j) false =
        (C.wires (List.ofFn (x ∘ π))).getD (n+j) false := by
    have h := (r_rel_fold n n π C.gates _ _ (r_rel_init n n π x)).2.2 (n+j)
    have hw : r_wmap n n π (n+j) = n+j := by
      simp only [r_wmap,show ¬ n+j<n by omega,dite_false]
      omega
    rw [hw] at h
    exact h

  have r_gate_at (n : Nat) (π : Fin n → Fin n) (C : Circuit) (j : Nat) (g : Gate)
      (h : C.gates[j]? = some g) :
      (r_relabel n n π C).gates[j]? = some (r_relGate n n π g) := by
    simp only [r_relabel,List.getElem?_map,h,Option.map_some]

  let g_edge (u v : Fin 42) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
  let g_adj (u v : Fin 42) : Bool := decide ((u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∨ (v.val < 21 ∧ 21 ≤ u.val ∧ (u.val + 21 - v.val) % 21 ∈ ([0,5,7,17,20] : List Nat)))
  have g_adj_spec (u v : Fin 42) : g_adj u v = true ↔ g_edge u v ∨ g_edge v u := by simp [g_adj,g_edge]
  let g_auto_0 : Fin 42 → Fin 42 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
  let g_inv_0 : Fin 42 → Fin 42 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
  let g_auto_1 : Fin 42 → Fin 42 := ![0,2,1,3,11,17,12,14,16,18,19,4,6,13,7,15,8,5,9,10,20,28,22,29,31,37,38,40,21,23,39,24,32,34,33,35,36,25,26,30,27,41]
  let g_inv_1 : Fin 42 → Fin 42 := ![0,2,1,3,11,17,12,14,16,18,19,4,6,13,7,15,8,5,9,10,20,28,22,29,31,37,38,40,21,23,39,24,32,34,33,35,36,25,26,30,27,41]
  let g_auto_2 : Fin 42 → Fin 42 := ![0,20,2,5,13,14,1,7,8,4,10,11,18,9,3,19,15,12,17,16,6,41,40,22,33,34,21,27,28,25,30,31,39,35,29,24,36,32,38,37,23,26]
  let g_inv_2 : Fin 42 → Fin 42 := ![0,6,2,14,9,3,20,7,8,13,10,11,17,4,5,16,19,18,12,15,1,26,23,40,35,29,41,27,28,34,30,31,37,24,25,33,36,39,38,32,22,21]
  let g_auto_3 : Fin 42 → Fin 42 := ![0,2,14,17,11,19,6,16,1,5,3,4,15,10,7,12,8,20,13,9,18,28,40,34,37,39,26,23,21,22,31,24,32,36,27,33,29,25,41,30,35,38]
  let g_inv_3 : Fin 42 → Fin 42 := ![0,8,1,10,11,9,6,14,16,19,13,4,15,18,2,12,7,3,20,5,17,28,29,27,31,37,26,34,21,36,39,30,32,35,23,40,33,24,41,25,22,38]
  let g_auto_4 : Fin 42 → Fin 42 := ![0,19,2,15,9,12,17,7,8,10,4,11,16,13,6,20,5,14,1,18,3,26,40,22,35,29,38,24,28,36,30,32,37,33,34,27,25,31,21,39,23,41]
  let g_inv_4 : Fin 42 → Fin 42 := ![0,18,2,20,10,16,14,7,8,4,9,11,5,13,17,3,12,6,19,1,15,38,23,40,27,36,21,35,28,25,30,37,31,33,34,24,29,32,26,39,22,41]
  let g_auto_5 : Fin 42 → Fin 42 := ![0,19,14,17,5,20,13,1,4,3,11,16,7,10,9,12,6,2,8,15,18,26,40,34,22,25,41,39,21,24,31,37,33,27,30,29,32,23,28,36,35,38]
  let g_inv_5 : Fin 42 → Fin 42 := ![0,7,17,9,8,4,16,12,18,14,13,10,15,6,2,19,11,3,20,1,5,28,24,37,29,25,21,33,38,35,34,30,36,32,23,40,39,31,41,27,22,26]
  let g_auto_6 : Fin 42 → Fin 42 := ![0,20,14,17,3,2,8,4,16,11,5,1,9,10,15,12,13,19,6,7,18,41,40,34,24,23,28,25,21,37,31,22,29,30,36,32,33,39,26,27,35,38]
  let g_inv_6 : Fin 42 → Fin 42 := ![0,11,5,4,7,10,18,19,6,12,13,9,15,16,2,14,8,3,20,17,1,28,31,25,24,27,38,39,26,32,33,30,35,36,23,40,34,29,41,37,22,21]
  let g_auto_7 : Fin 42 → Fin 42 := ![0,12,14,6,10,2,8,1,4,11,3,16,15,5,18,19,17,20,13,7,9,38,40,34,27,30,28,29,21,32,31,23,36,22,25,39,24,37,41,33,35,26]
  let g_inv_7 : Fin 42 → Fin 42 := ![0,7,5,10,8,13,3,19,6,20,4,9,1,18,2,12,11,16,14,15,17,28,33,31,36,34,41,24,26,27,25,30,29,39,23,40,32,37,21,35,22,38]
  let g_auto_8 : Fin 42 → Fin 42 := ![0,12,14,13,10,19,6,4,16,5,11,1,7,3,18,20,17,2,8,9,15,38,40,34,30,36,26,32,21,33,31,39,27,24,23,25,37,22,28,29,35,41]
  let g_inv_8 : Fin 42 → Fin 42 := ![0,11,17,13,7,9,6,12,18,19,4,10,1,3,2,20,8,16,14,5,15,28,37,34,33,35,26,32,38,39,24,30,27,29,23,40,25,36,21,31,22,41]
  let g_auto_9 : Fin 42 → Fin 42 := ![2,0,1,19,8,4,13,15,5,9,3,17,6,12,7,14,11,16,18,10,20,28,21,39,36,25,30,41,22,26,29,24,34,32,33,35,31,37,23,38,27,40]
  let g_inv_9 : Fin 42 → Fin 42 := ![1,2,0,10,5,8,12,14,4,9,19,16,13,6,15,7,17,11,18,3,20,22,28,38,31,25,29,40,21,30,26,36,33,34,32,35,24,37,39,23,41,27]
  let g_auto_10 : Fin 42 → Fin 42 := ![13,0,2,5,20,11,1,4,9,19,14,10,6,12,3,7,15,8,17,18,16,41,28,22,25,37,39,21,30,26,40,31,27,32,29,24,35,36,34,38,23,33]
  let g_inv_10 : Fin 42 → Fin 42 := ![1,6,2,14,7,3,12,15,17,8,11,5,13,0,10,16,20,18,19,9,4,27,23,40,35,24,29,32,22,34,28,31,33,41,38,36,37,25,39,26,30,21]
  let g_auto_11 : Fin 42 → Fin 42 := ![17,0,2,4,18,11,9,5,1,16,6,15,14,3,12,7,10,8,13,20,19,38,28,30,25,39,37,26,22,21,23,32,35,31,29,33,27,36,34,41,40,24]
  let g_inv_11 : Fin 42 → Fin 42 := ![1,8,2,13,3,7,10,15,17,6,16,5,14,18,12,11,9,0,4,20,19,29,28,30,41,24,27,36,22,34,23,33,31,35,38,32,37,26,21,25,40,39]
  let g_auto_12 : Fin 42 → Fin 42 := ![9,0,2,15,19,11,17,10,13,20,12,4,3,14,6,7,5,8,1,16,18,26,28,22,36,39,37,38,30,41,40,32,24,31,34,27,33,25,29,21,23,35]
  let g_inv_12 : Fin 42 → Fin 42 := ![1,18,2,12,11,16,14,15,17,0,7,5,10,8,13,3,19,6,20,4,9,39,23,40,32,37,21,35,22,38,28,33,31,36,34,41,24,26,27,25,30,29]
  let g_auto_13 : Fin 42 → Fin 42 := ![19,0,11,17,5,8,16,1,18,10,14,13,12,3,6,7,9,2,20,15,4,26,28,37,22,25,36,21,39,38,31,34,33,29,23,27,35,30,40,41,32,24]
  let g_inv_13 : Fin 42 → Fin 42 := ![1,7,17,13,20,4,14,15,5,16,9,2,12,11,10,19,6,3,8,0,18,27,24,34,41,25,21,35,22,33,37,30,40,32,31,36,26,23,29,28,38,39]
  let g_auto_14 : Fin 42 → Fin 42 := ![20,0,7,17,13,2,19,6,10,12,5,1,18,16,15,11,3,8,4,14,9,41,28,24,34,30,40,26,27,38,33,22,39,23,36,32,31,29,25,21,35,37]
  let g_inv_14 : Fin 42 → Fin 42 := ![1,11,5,16,18,10,7,2,17,20,8,15,9,4,19,14,13,3,12,6,0,39,31,33,23,38,27,28,22,37,25,36,35,30,24,40,34,41,29,32,26,21]
  let g_auto_15 : Fin 42 → Fin 42 := ![12,0,8,13,18,2,14,1,3,20,4,9,15,5,10,7,17,11,6,19,16,38,28,34,39,23,40,21,29,41,25,30,35,22,31,27,24,37,32,26,36,33]
  let g_inv_15 : Fin 42 → Fin 42 := ![1,7,5,8,10,13,18,15,2,11,14,17,0,3,6,12,20,16,4,19,9,27,33,25,36,30,39,35,22,28,31,34,38,41,23,32,40,37,21,24,26,29]
  let g_auto_16 : Fin 42 → Fin 42 := ![12,0,8,6,18,7,13,3,9,5,20,1,19,4,10,11,17,2,14,16,15,38,28,34,23,35,33,41,29,26,25,27,39,24,30,31,37,22,40,21,36,32]
  let g_inv_16 : Fin 42 → Fin 42 := ![1,11,17,7,13,9,3,5,2,8,14,15,0,6,18,20,19,16,4,12,10,39,37,24,33,30,29,31,22,28,34,35,41,26,23,25,40,36,21,32,38,27]
  let g_auto_17 : Fin 42 → Fin 42 := ![10,2,0,1,13,8,16,18,17,15,3,12,5,20,9,7,4,11,14,19,6,30,28,21,39,34,36,23,38,22,41,29,33,25,37,35,24,32,31,40,26,27]
  let g_inv_17 : Fin 42 → Fin 42 := ![2,3,1,10,16,12,20,15,5,14,0,17,11,4,18,9,6,8,7,19,13,23,29,27,36,33,40,41,22,31,21,38,37,32,25,35,26,34,28,24,39,30]
  let g_auto_18 : Fin 42 → Fin 42 := ![12,2,0,16,20,8,1,17,18,3,15,10,6,13,19,7,14,11,4,9,5,40,28,21,37,25,29,22,38,23,41,36,27,34,39,24,35,31,32,30,26,33]
  let g_inv_18 : Fin 42 → Fin 42 := ![2,6,1,9,18,20,12,15,5,19,11,17,0,13,16,10,3,7,8,14,4,23,27,29,35,25,40,32,22,26,39,37,38,41,33,36,31,24,28,34,21,30]
  let g_auto_19 : Fin 42 → Fin 42 := ![4,2,0,17,9,8,18,16,1,5,6,14,15,19,13,7,10,11,12,20,3,30,28,38,37,29,25,23,21,22,26,34,35,36,39,33,27,31,32,40,41,24]
  let g_inv_19 : Fin 42 → Fin 42 := ![2,8,1,20,0,9,10,15,5,4,16,17,18,14,11,12,7,3,6,13,19,28,29,27,41,26,30,36,22,25,21,37,38,35,31,32,33,24,23,34,39,40]
  let g_auto_20 : Fin 42 → Fin 42 := ![18,2,0,14,3,8,4,10,12,20,13,17,19,15,6,7,16,11,1,5,9,23,28,21,31,29,25,30,38,40,41,34,24,36,32,27,33,37,39,22,26,35]
  let g_inv_20 : Fin 42 → Fin 42 := ![2,18,1,4,6,19,14,15,5,20,7,17,8,10,3,13,16,11,0,12,9,23,39,21,32,26,40,35,22,25,27,24,34,36,31,41,33,37,28,38,29,30]
  let g_auto_21 : Fin 42 → Fin 42 := ![14,11,0,17,5,7,18,1,16,9,19,4,20,6,3,8,10,2,12,15,13,31,28,38,22,33,35,39,21,37,26,24,25,27,23,29,36,30,40,32,41,34]
  let g_inv_21 : Fin 42 → Fin 42 := ![2,7,17,14,11,4,13,5,15,9,16,1,18,20,0,19,8,3,6,10,12,28,24,34,31,32,30,33,22,35,37,21,39,25,41,26,36,29,23,27,38,40]
  let g_auto_22 : Fin 42 → Fin 42 := ![14,7,0,17,9,2,12,16,4,19,5,1,3,6,15,8,18,11,10,20,13,35,28,38,37,30,40,33,21,24,26,22,29,23,32,36,25,39,31,27,41,34]
  let g_inv_22 : Fin 42 → Fin 42 := ![2,11,5,12,8,10,13,1,15,4,18,17,6,20,0,14,7,3,16,9,19,28,31,33,29,36,30,39,22,32,25,38,34,27,41,21,35,24,23,37,26,40]
  let g_auto_23 : Fin 42 → Fin 42 := ![14,8,0,10,6,2,12,1,16,19,9,4,15,5,13,11,17,7,18,20,3,34,28,38,27,23,40,29,21,36,26,30,32,22,33,39,37,24,35,25,41,31]
  let g_inv_23 : Fin 42 → Fin 42 := ![2,7,5,20,11,13,4,17,1,10,3,15,6,14,0,12,8,16,18,9,19,28,33,25,37,39,30,24,22,27,31,41,32,34,21,38,29,36,23,35,26,40]
  let g_auto_24 : Fin 42 → Fin 42 := ![14,8,0,18,6,11,10,16,4,5,19,1,20,9,13,7,17,2,12,3,15,34,28,38,23,32,31,36,21,25,26,39,27,37,30,33,24,22,40,29,41,35]
  let g_inv_24 : Fin 42 → Fin 42 := ![2,11,17,19,8,9,4,15,1,13,6,5,18,14,0,20,7,16,3,10,12,28,37,24,36,29,30,32,22,39,34,26,25,35,21,41,27,33,23,31,38,40]
  let g_auto_25 : Fin 42 → Fin 42 := ![15,14,2,11,18,20,0,1,5,3,16,17,10,6,9,12,7,19,8,13,4,35,40,28,39,25,41,21,22,31,23,37,38,27,26,29,33,24,36,34,30,32]
  let g_inv_25 : Fin 42 → Fin 42 := ![6,7,2,9,20,8,13,16,18,14,12,3,15,19,1,0,10,11,4,17,5,27,28,30,37,25,34,33,23,35,40,29,41,36,39,21,38,31,32,24,22,26]
  let g_auto_26 : Fin 42 → Fin 42 := ![17,19,2,11,3,12,0,5,1,18,6,15,13,16,4,20,7,14,8,10,9,24,40,28,31,29,38,26,22,39,23,32,41,33,21,25,27,35,34,36,30,37]
  let g_inv_26 : Fin 42 → Fin 42 := ![6,8,2,4,14,7,10,16,18,20,19,3,5,12,17,11,13,0,9,1,15,34,28,30,21,35,27,36,23,25,40,24,31,33,38,37,39,41,26,29,22,32]
  let g_auto_27 : Fin 42 → Fin 42 := ![6,2,14,4,18,19,0,8,13,9,7,17,10,15,3,12,16,20,1,5,11,23,40,21,25,39,26,28,34,30,35,24,38,36,41,29,33,37,27,22,31,32]
  let g_inv_27 : Fin 42 → Fin 42 := ![6,18,1,14,3,19,0,10,7,9,12,20,15,8,2,13,16,11,4,5,17,23,39,21,31,24,26,38,27,35,29,40,41,36,28,30,33,37,32,25,22,34]
  let g_auto_28 : Fin 42 → Fin 42 := ![13,16,18,17,5,3,0,1,11,20,4,19,9,8,7,6,12,2,10,15,14,33,23,38,22,31,41,21,39,37,25,24,26,29,28,27,32,40,30,36,35,34]
  let g_inv_28 : Fin 42 → Fin 42 := ![6,7,17,5,10,4,15,14,13,12,18,8,16,0,20,19,1,3,2,11,9,27,24,22,31,30,32,35,34,33,38,25,36,21,41,40,39,29,23,28,37,26]
  let g_auto_29 : Fin 42 → Fin 42 := ![8,19,12,17,16,2,0,9,3,7,5,1,4,13,15,14,10,20,18,11,6,36,40,38,37,23,28,26,29,24,33,22,21,30,41,35,31,27,25,39,32,34]
  let g_inv_29 : Fin 42 → Fin 42 := ![6,11,5,8,12,10,20,9,0,7,16,19,2,13,15,14,4,3,18,1,17,32,31,25,29,38,27,37,26,28,33,36,40,30,41,35,21,24,23,39,22,34]
  let g_auto_30 : Fin 42 → Fin 42 := ![8,14,12,18,13,2,0,1,9,7,16,3,15,5,6,20,17,19,10,11,4,34,40,38,39,30,28,21,29,35,33,23,41,22,26,27,37,24,36,31,32,25]
  let g_inv_30 : Fin 42 → Fin 42 := ![6,7,5,11,20,13,14,9,0,8,18,19,2,4,1,12,10,16,3,17,15,27,33,31,37,41,34,35,26,28,25,39,40,30,21,29,38,36,23,24,22,32]
  let g_auto_31 : Fin 42 → Fin 42 := ![6,13,10,12,14,9,0,20,7,5,3,1,16,11,8,4,17,2,18,19,15,34,30,38,40,35,26,41,27,33,31,29,21,37,28,25,24,22,23,39,36,32]
  let g_inv_31 : Fin 42 → Fin 42 := ![6,11,17,10,15,9,0,8,14,5,2,13,3,1,4,20,12,16,18,19,7,32,37,38,36,35,26,28,34,31,22,30,41,29,21,25,40,33,23,39,24,27]
  let g_auto_32 : Fin 42 → Fin 42 := ![8,14,2,16,17,12,3,11,0,1,5,7,4,15,13,19,6,20,18,9,10,34,40,23,37,38,29,31,28,21,22,33,24,32,41,39,26,27,25,35,30,36]
  let g_inv_32 : Fin 42 → Fin 42 := ![8,9,2,6,12,10,16,11,0,19,20,7,5,14,1,13,3,4,18,15,17,29,30,23,32,38,36,37,28,26,40,27,33,31,21,39,41,24,25,35,22,34]
  let g_auto_33 : Fin 42 → Fin 42 := ![8,20,2,15,4,14,17,11,0,13,9,7,3,10,18,19,5,12,1,6,16,25,40,22,32,21,34,37,28,41,30,35,24,31,38,39,26,33,29,27,23,36]
  let g_inv_33 : Fin 42 → Fin 42 := ![8,18,2,12,4,16,19,11,0,10,13,7,17,9,5,3,20,6,14,15,1,25,23,40,32,21,36,39,28,38,30,33,24,37,26,31,41,27,34,35,22,29]
  let g_auto_34 : Fin 42 → Fin 42 := ![4,18,16,17,5,6,11,1,0,12,13,14,10,7,8,3,20,2,9,15,19,25,23,37,22,26,32,39,21,38,33,34,31,27,28,29,41,40,30,35,36,24]
  let g_inv_34 : Fin 42 → Fin 42 := ![8,7,17,15,0,4,5,13,14,18,12,6,9,10,11,19,2,3,1,20,16,28,24,22,41,21,25,33,34,35,38,32,26,30,31,39,40,23,29,27,37,36]
  let g_auto_35 : Fin 42 → Fin 42 := ![16,10,4,17,8,2,3,14,0,18,5,1,12,20,15,9,19,13,7,6,11,36,30,24,34,28,23,31,21,38,25,22,29,40,41,35,26,39,33,27,32,37]
  let g_inv_35 : Fin 42 → Fin 42 := ![8,11,5,6,2,10,19,18,4,15,1,20,12,17,7,14,0,3,9,16,13,28,31,26,23,30,36,39,25,32,22,27,40,38,24,35,21,41,29,37,33,34]
  let g_auto_36 : Fin 42 → Fin 42 := ![4,3,16,20,7,2,9,1,0,13,12,14,15,5,19,18,17,6,11,10,8,24,23,37,27,28,30,29,21,41,33,40,35,22,26,39,38,34,32,31,36,25]
  let g_inv_36 : Fin 42 → Fin 42 := ![8,7,5,1,0,13,17,4,20,6,19,18,10,9,11,12,2,16,15,14,3,28,33,22,21,41,34,24,25,27,26,39,38,30,37,32,40,23,36,35,31,29]
  let g_auto_37 : Fin 42 → Fin 42 := ![16,9,4,19,20,13,7,14,0,5,18,1,6,8,11,10,17,2,3,12,15,37,30,24,40,41,33,35,21,26,25,39,27,34,28,31,38,22,23,29,32,36]
  let g_inv_37 : Fin 42 → Fin 42 := ![8,11,17,18,2,9,12,6,13,1,15,14,19,5,7,20,0,16,10,3,4,28,37,38,23,30,29,32,34,39,22,35,40,26,33,27,41,21,36,31,24,25]
  let g_auto_38 : Fin 42 → Fin 42 := ![3,14,2,7,10,12,8,6,18,9,13,16,15,4,5,19,11,20,0,1,17,31,40,28,27,38,29,34,23,35,30,33,36,32,25,26,39,37,41,21,22,24]
  let g_inv_38 : Fin 42 → Fin 42 := ![18,19,2,0,13,14,7,3,6,9,4,16,5,10,1,12,11,20,8,15,17,39,40,28,41,34,35,24,23,26,30,21,33,31,27,29,32,37,25,36,22,38]
  let g_auto_39 : Fin 42 → Fin 42 := ![8,20,12,17,5,19,10,1,9,16,7,3,11,13,4,14,18,2,0,15,6,25,40,38,22,26,36,27,29,37,33,24,31,39,30,21,35,23,28,41,32,34]
  let g_inv_39 : Fin 42 → Fin 42 := ![18,7,17,11,14,4,20,10,0,8,6,12,2,13,15,19,9,3,16,5,1,35,24,37,31,21,25,27,38,28,34,32,40,30,41,36,26,29,23,33,22,39]
  let g_auto_40 : Fin 42 → Fin 42 := ![6,4,10,17,11,2,18,20,7,3,5,1,19,14,15,13,12,9,0,16,8,32,30,38,37,28,23,25,27,24,31,22,39,40,35,41,33,29,26,21,36,34]
  let g_inv_40 : Fin 42 → Fin 42 := ![18,11,5,9,1,10,0,8,20,17,2,4,16,15,13,14,19,3,6,12,7,39,31,26,29,27,38,28,25,37,22,30,21,36,41,34,40,24,23,32,33,35]
  let g_auto_41 : Fin 42 → Fin 42 := ![13,6,18,12,8,2,10,1,11,4,20,19,15,5,14,16,17,3,0,9,7,34,23,38,29,28,30,27,39,32,25,40,36,22,31,21,37,24,41,26,35,33]
  let g_inv_41 : Fin 42 → Fin 42 := ![18,7,5,17,9,13,1,20,4,19,6,8,3,0,14,12,15,16,2,11,10,35,33,22,37,30,39,27,25,24,26,34,29,41,21,40,32,36,23,28,31,38]
  let g_auto_42 : Fin 42 → Fin 42 := ![8,14,12,10,13,20,18,9,3,5,7,1,11,16,6,19,17,2,0,4,15,34,40,38,30,41,25,35,29,31,33,27,39,37,23,26,24,22,28,21,32,36]
  let g_inv_42 : Fin 42 → Fin 42 := ![18,11,17,8,19,9,14,10,0,7,3,12,2,4,1,20,13,16,6,15,5,39,37,34,36,26,35,31,38,28,24,29,40,30,21,27,41,33,23,32,22,25]
  let g_auto_43 : Fin 42 → Fin 42 := ![40,22,35,38,28,36,39,21,34,24,27,31,37,33,30,32,23,41,25,26,29,2,15,18,0,8,19,1,14,17,7,10,11,16,13,4,6,3,20,5,9,12]
  let g_inv_43 : Fin 42 → Fin 42 := ![24,27,21,37,35,39,36,30,25,40,31,32,41,34,28,22,33,29,23,26,38,7,1,16,9,18,19,10,4,20,14,11,15,13,8,2,5,12,3,6,0,17]
  let g_auto_44 : Fin 42 → Fin 42 := ![40,23,24,21,28,29,32,26,36,33,27,39,37,35,22,31,30,41,25,38,34,2,3,4,0,8,12,6,19,16,7,1,11,9,15,5,10,13,20,18,17,14]
  let g_inv_44 : Fin 42 → Fin 42 := ![24,31,21,22,23,35,27,30,25,33,36,32,26,37,41,34,29,40,39,28,38,3,14,1,2,18,7,10,4,5,16,15,6,9,20,13,8,12,19,11,0,17]
  let g_auto_45 : Fin 42 → Fin 42 := ![40,30,35,41,28,29,32,21,34,33,24,31,39,27,23,37,22,26,36,38,25,2,9,15,0,8,12,4,14,13,7,3,11,1,6,16,17,5,19,10,18,20]
  let g_inv_45 : Fin 42 → Fin 42 := ![24,33,21,31,27,37,34,30,25,22,39,32,26,29,28,23,35,36,40,38,41,7,16,14,10,20,17,13,4,5,1,11,6,9,8,2,18,15,19,12,0,3]
  let g_auto_46 : Fin 42 → Fin 42 := ![40,30,24,38,28,25,37,26,36,27,35,39,31,33,23,32,22,21,34,41,29,2,4,17,0,8,20,9,19,10,7,18,11,5,16,6,15,1,14,13,3,12]
  let g_inv_46 : Fin 42 → Fin 42 := ![24,37,21,40,22,33,35,30,25,27,29,32,41,39,38,36,34,23,31,28,26,17,16,14,2,5,7,9,4,20,1,12,15,13,18,10,8,6,3,11,0,19]
  let g_auto_47 : Fin 42 → Fin 42 := ![40,23,25,26,30,38,33,37,27,32,21,41,34,24,28,39,22,35,31,29,36,2,18,5,9,10,12,16,20,6,4,0,13,17,7,11,1,15,14,3,8,19]
  let g_inv_47 : Fin 42 → Fin 42 := ![31,36,21,39,30,23,29,34,40,24,25,35,26,32,38,37,27,33,22,41,28,10,16,1,13,2,3,8,14,19,4,18,9,6,12,17,20,7,5,15,0,11]
  let g_auto_48 : Fin 42 → Fin 42 := ![40,23,36,41,30,21,35,39,24,31,38,26,29,27,28,37,22,33,32,34,25,2,16,15,13,4,14,18,19,3,10,0,9,1,7,11,17,5,12,6,8,20]
  let g_inv_48 : Fin 42 → Fin 42 := ![31,33,21,29,25,37,39,34,40,32,30,35,38,24,26,23,22,36,27,28,41,5,16,1,8,20,11,13,14,12,4,9,18,17,19,6,2,15,10,7,0,3]
  let g_auto_49 : Fin 42 → Fin 42 := ![40,23,34,38,30,26,24,31,35,39,41,21,25,33,28,32,22,27,37,36,29,2,6,17,10,9,19,3,14,18,13,0,4,5,7,11,15,1,20,16,8,12]
  let g_inv_49 : Fin 42 → Fin 42 := ![31,37,21,27,32,33,22,34,40,25,24,35,41,30,28,36,39,23,29,26,38,11,16,1,6,12,5,17,14,20,4,7,15,13,2,8,19,18,3,9,0,10]
  let g_auto_50 : Fin 42 → Fin 42 := ![40,22,33,27,30,26,24,38,29,39,34,32,21,41,23,25,28,31,35,36,37,2,5,7,10,9,19,17,12,1,13,6,4,0,3,18,8,11,14,15,16,20]
  let g_inv_50 : Fin 42 → Fin 42 := ![33,29,21,34,32,22,31,23,36,25,24,37,28,30,38,39,40,27,35,26,41,12,1,14,6,15,5,3,16,8,4,17,11,2,10,18,19,20,7,9,0,13]
  let g_auto_51 : Fin 42 → Fin 42 := ![40,31,30,24,35,38,32,28,23,29,37,22,41,26,34,36,21,27,25,33,39,14,10,4,7,18,12,11,2,3,9,17,15,0,6,8,16,1,20,5,13,19]
  let g_inv_51 : Fin 42 → Fin 42 := ![33,37,28,29,23,39,34,24,35,30,22,27,26,40,21,32,36,31,25,41,38,16,11,8,3,18,13,17,7,9,2,1,6,19,14,4,15,10,5,20,0,12]
  let g_auto_52 : Fin 42 → Fin 42 := ![40,31,23,36,35,29,33,22,30,38,25,28,27,39,34,24,21,41,37,32,26,14,3,16,15,9,12,5,2,10,18,8,7,1,13,17,4,0,20,11,6,19]
  let g_inv_52 : Fin 42 → Fin 42 := ![37,33,28,22,36,27,40,32,31,25,29,39,26,34,21,24,23,35,30,41,38,16,7,2,15,10,20,12,11,5,8,1,19,6,14,4,3,18,9,13,0,17]
  let g_autos : Fin 53 → Fin 42 → Fin 42 := ![g_auto_0,g_auto_1,g_auto_2,g_auto_3,g_auto_4,g_auto_5,g_auto_6,g_auto_7,g_auto_8,g_auto_9,g_auto_10,g_auto_11,g_auto_12,g_auto_13,g_auto_14,g_auto_15,g_auto_16,g_auto_17,g_auto_18,g_auto_19,g_auto_20,g_auto_21,g_auto_22,g_auto_23,g_auto_24,g_auto_25,g_auto_26,g_auto_27,g_auto_28,g_auto_29,g_auto_30,g_auto_31,g_auto_32,g_auto_33,g_auto_34,g_auto_35,g_auto_36,g_auto_37,g_auto_38,g_auto_39,g_auto_40,g_auto_41,g_auto_42,g_auto_43,g_auto_44,g_auto_45,g_auto_46,g_auto_47,g_auto_48,g_auto_49,g_auto_50,g_auto_51,g_auto_52]
  let g_invs : Fin 53 → Fin 42 → Fin 42 := ![g_inv_0,g_inv_1,g_inv_2,g_inv_3,g_inv_4,g_inv_5,g_inv_6,g_inv_7,g_inv_8,g_inv_9,g_inv_10,g_inv_11,g_inv_12,g_inv_13,g_inv_14,g_inv_15,g_inv_16,g_inv_17,g_inv_18,g_inv_19,g_inv_20,g_inv_21,g_inv_22,g_inv_23,g_inv_24,g_inv_25,g_inv_26,g_inv_27,g_inv_28,g_inv_29,g_inv_30,g_inv_31,g_inv_32,g_inv_33,g_inv_34,g_inv_35,g_inv_36,g_inv_37,g_inv_38,g_inv_39,g_inv_40,g_inv_41,g_inv_42,g_inv_43,g_inv_44,g_inv_45,g_inv_46,g_inv_47,g_inv_48,g_inv_49,g_inv_50,g_inv_51,g_inv_52]
  have g_inverse_0 : ∀ v : Fin 42, g_inv_0 (g_auto_0 v) = v ∧ g_auto_0 (g_inv_0 v) = v := by
    dsimp only [g_auto_0, g_inv_0]
    decide +kernel
  have g_adj_0 : ∀ u v : Fin 42, g_adj (g_auto_0 u) (g_auto_0 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_0]
    decide +kernel
  have g_inverse_1 : ∀ v : Fin 42, g_inv_1 (g_auto_1 v) = v ∧ g_auto_1 (g_inv_1 v) = v := by
    dsimp only [g_auto_1, g_inv_1]
    decide +kernel
  have g_adj_1 : ∀ u v : Fin 42, g_adj (g_auto_1 u) (g_auto_1 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_1]
    decide +kernel
  have g_inverse_2 : ∀ v : Fin 42, g_inv_2 (g_auto_2 v) = v ∧ g_auto_2 (g_inv_2 v) = v := by
    dsimp only [g_auto_2, g_inv_2]
    decide +kernel
  have g_adj_2 : ∀ u v : Fin 42, g_adj (g_auto_2 u) (g_auto_2 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_2]
    decide +kernel
  have g_inverse_3 : ∀ v : Fin 42, g_inv_3 (g_auto_3 v) = v ∧ g_auto_3 (g_inv_3 v) = v := by
    dsimp only [g_auto_3, g_inv_3]
    decide +kernel
  have g_adj_3 : ∀ u v : Fin 42, g_adj (g_auto_3 u) (g_auto_3 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_3]
    decide +kernel
  have g_inverse_4 : ∀ v : Fin 42, g_inv_4 (g_auto_4 v) = v ∧ g_auto_4 (g_inv_4 v) = v := by
    dsimp only [g_auto_4, g_inv_4]
    decide +kernel
  have g_adj_4 : ∀ u v : Fin 42, g_adj (g_auto_4 u) (g_auto_4 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_4]
    decide +kernel
  have g_inverse_5 : ∀ v : Fin 42, g_inv_5 (g_auto_5 v) = v ∧ g_auto_5 (g_inv_5 v) = v := by
    dsimp only [g_auto_5, g_inv_5]
    decide +kernel
  have g_adj_5 : ∀ u v : Fin 42, g_adj (g_auto_5 u) (g_auto_5 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_5]
    decide +kernel
  have g_inverse_6 : ∀ v : Fin 42, g_inv_6 (g_auto_6 v) = v ∧ g_auto_6 (g_inv_6 v) = v := by
    dsimp only [g_auto_6, g_inv_6]
    decide +kernel
  have g_adj_6 : ∀ u v : Fin 42, g_adj (g_auto_6 u) (g_auto_6 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_6]
    decide +kernel
  have g_inverse_7 : ∀ v : Fin 42, g_inv_7 (g_auto_7 v) = v ∧ g_auto_7 (g_inv_7 v) = v := by
    dsimp only [g_auto_7, g_inv_7]
    decide +kernel
  have g_adj_7 : ∀ u v : Fin 42, g_adj (g_auto_7 u) (g_auto_7 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_7]
    decide +kernel
  have g_inverse_8 : ∀ v : Fin 42, g_inv_8 (g_auto_8 v) = v ∧ g_auto_8 (g_inv_8 v) = v := by
    dsimp only [g_auto_8, g_inv_8]
    decide +kernel
  have g_adj_8 : ∀ u v : Fin 42, g_adj (g_auto_8 u) (g_auto_8 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_8]
    decide +kernel
  have g_inverse_9 : ∀ v : Fin 42, g_inv_9 (g_auto_9 v) = v ∧ g_auto_9 (g_inv_9 v) = v := by
    dsimp only [g_auto_9, g_inv_9]
    decide +kernel
  have g_adj_9 : ∀ u v : Fin 42, g_adj (g_auto_9 u) (g_auto_9 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_9]
    decide +kernel
  have g_inverse_10 : ∀ v : Fin 42, g_inv_10 (g_auto_10 v) = v ∧ g_auto_10 (g_inv_10 v) = v := by
    dsimp only [g_auto_10, g_inv_10]
    decide +kernel
  have g_adj_10 : ∀ u v : Fin 42, g_adj (g_auto_10 u) (g_auto_10 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_10]
    decide +kernel
  have g_inverse_11 : ∀ v : Fin 42, g_inv_11 (g_auto_11 v) = v ∧ g_auto_11 (g_inv_11 v) = v := by
    dsimp only [g_auto_11, g_inv_11]
    decide +kernel
  have g_adj_11 : ∀ u v : Fin 42, g_adj (g_auto_11 u) (g_auto_11 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_11]
    decide +kernel
  have g_inverse_12 : ∀ v : Fin 42, g_inv_12 (g_auto_12 v) = v ∧ g_auto_12 (g_inv_12 v) = v := by
    dsimp only [g_auto_12, g_inv_12]
    decide +kernel
  have g_adj_12 : ∀ u v : Fin 42, g_adj (g_auto_12 u) (g_auto_12 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_12]
    decide +kernel
  have g_inverse_13 : ∀ v : Fin 42, g_inv_13 (g_auto_13 v) = v ∧ g_auto_13 (g_inv_13 v) = v := by
    dsimp only [g_auto_13, g_inv_13]
    decide +kernel
  have g_adj_13 : ∀ u v : Fin 42, g_adj (g_auto_13 u) (g_auto_13 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_13]
    decide +kernel
  have g_inverse_14 : ∀ v : Fin 42, g_inv_14 (g_auto_14 v) = v ∧ g_auto_14 (g_inv_14 v) = v := by
    dsimp only [g_auto_14, g_inv_14]
    decide +kernel
  have g_adj_14 : ∀ u v : Fin 42, g_adj (g_auto_14 u) (g_auto_14 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_14]
    decide +kernel
  have g_inverse_15 : ∀ v : Fin 42, g_inv_15 (g_auto_15 v) = v ∧ g_auto_15 (g_inv_15 v) = v := by
    dsimp only [g_auto_15, g_inv_15]
    decide +kernel
  have g_adj_15 : ∀ u v : Fin 42, g_adj (g_auto_15 u) (g_auto_15 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_15]
    decide +kernel
  have g_inverse_16 : ∀ v : Fin 42, g_inv_16 (g_auto_16 v) = v ∧ g_auto_16 (g_inv_16 v) = v := by
    dsimp only [g_auto_16, g_inv_16]
    decide +kernel
  have g_adj_16 : ∀ u v : Fin 42, g_adj (g_auto_16 u) (g_auto_16 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_16]
    decide +kernel
  have g_inverse_17 : ∀ v : Fin 42, g_inv_17 (g_auto_17 v) = v ∧ g_auto_17 (g_inv_17 v) = v := by
    dsimp only [g_auto_17, g_inv_17]
    decide +kernel
  have g_adj_17 : ∀ u v : Fin 42, g_adj (g_auto_17 u) (g_auto_17 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_17]
    decide +kernel
  have g_inverse_18 : ∀ v : Fin 42, g_inv_18 (g_auto_18 v) = v ∧ g_auto_18 (g_inv_18 v) = v := by
    dsimp only [g_auto_18, g_inv_18]
    decide +kernel
  have g_adj_18 : ∀ u v : Fin 42, g_adj (g_auto_18 u) (g_auto_18 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_18]
    decide +kernel
  have g_inverse_19 : ∀ v : Fin 42, g_inv_19 (g_auto_19 v) = v ∧ g_auto_19 (g_inv_19 v) = v := by
    dsimp only [g_auto_19, g_inv_19]
    decide +kernel
  have g_adj_19 : ∀ u v : Fin 42, g_adj (g_auto_19 u) (g_auto_19 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_19]
    decide +kernel
  have g_inverse_20 : ∀ v : Fin 42, g_inv_20 (g_auto_20 v) = v ∧ g_auto_20 (g_inv_20 v) = v := by
    dsimp only [g_auto_20, g_inv_20]
    decide +kernel
  have g_adj_20 : ∀ u v : Fin 42, g_adj (g_auto_20 u) (g_auto_20 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_20]
    decide +kernel
  have g_inverse_21 : ∀ v : Fin 42, g_inv_21 (g_auto_21 v) = v ∧ g_auto_21 (g_inv_21 v) = v := by
    dsimp only [g_auto_21, g_inv_21]
    decide +kernel
  have g_adj_21 : ∀ u v : Fin 42, g_adj (g_auto_21 u) (g_auto_21 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_21]
    decide +kernel
  have g_inverse_22 : ∀ v : Fin 42, g_inv_22 (g_auto_22 v) = v ∧ g_auto_22 (g_inv_22 v) = v := by
    dsimp only [g_auto_22, g_inv_22]
    decide +kernel
  have g_adj_22 : ∀ u v : Fin 42, g_adj (g_auto_22 u) (g_auto_22 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_22]
    decide +kernel
  have g_inverse_23 : ∀ v : Fin 42, g_inv_23 (g_auto_23 v) = v ∧ g_auto_23 (g_inv_23 v) = v := by
    dsimp only [g_auto_23, g_inv_23]
    decide +kernel
  have g_adj_23 : ∀ u v : Fin 42, g_adj (g_auto_23 u) (g_auto_23 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_23]
    decide +kernel
  have g_inverse_24 : ∀ v : Fin 42, g_inv_24 (g_auto_24 v) = v ∧ g_auto_24 (g_inv_24 v) = v := by
    dsimp only [g_auto_24, g_inv_24]
    decide +kernel
  have g_adj_24 : ∀ u v : Fin 42, g_adj (g_auto_24 u) (g_auto_24 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_24]
    decide +kernel
  have g_inverse_25 : ∀ v : Fin 42, g_inv_25 (g_auto_25 v) = v ∧ g_auto_25 (g_inv_25 v) = v := by
    dsimp only [g_auto_25, g_inv_25]
    decide +kernel
  have g_adj_25 : ∀ u v : Fin 42, g_adj (g_auto_25 u) (g_auto_25 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_25]
    decide +kernel
  have g_inverse_26 : ∀ v : Fin 42, g_inv_26 (g_auto_26 v) = v ∧ g_auto_26 (g_inv_26 v) = v := by
    dsimp only [g_auto_26, g_inv_26]
    decide +kernel
  have g_adj_26 : ∀ u v : Fin 42, g_adj (g_auto_26 u) (g_auto_26 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_26]
    decide +kernel
  have g_inverse_27 : ∀ v : Fin 42, g_inv_27 (g_auto_27 v) = v ∧ g_auto_27 (g_inv_27 v) = v := by
    dsimp only [g_auto_27, g_inv_27]
    decide +kernel
  have g_adj_27 : ∀ u v : Fin 42, g_adj (g_auto_27 u) (g_auto_27 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_27]
    decide +kernel
  have g_inverse_28 : ∀ v : Fin 42, g_inv_28 (g_auto_28 v) = v ∧ g_auto_28 (g_inv_28 v) = v := by
    dsimp only [g_auto_28, g_inv_28]
    decide +kernel
  have g_adj_28 : ∀ u v : Fin 42, g_adj (g_auto_28 u) (g_auto_28 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_28]
    decide +kernel
  have g_inverse_29 : ∀ v : Fin 42, g_inv_29 (g_auto_29 v) = v ∧ g_auto_29 (g_inv_29 v) = v := by
    dsimp only [g_auto_29, g_inv_29]
    decide +kernel
  have g_adj_29 : ∀ u v : Fin 42, g_adj (g_auto_29 u) (g_auto_29 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_29]
    decide +kernel
  have g_inverse_30 : ∀ v : Fin 42, g_inv_30 (g_auto_30 v) = v ∧ g_auto_30 (g_inv_30 v) = v := by
    dsimp only [g_auto_30, g_inv_30]
    decide +kernel
  have g_adj_30 : ∀ u v : Fin 42, g_adj (g_auto_30 u) (g_auto_30 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_30]
    decide +kernel
  have g_inverse_31 : ∀ v : Fin 42, g_inv_31 (g_auto_31 v) = v ∧ g_auto_31 (g_inv_31 v) = v := by
    dsimp only [g_auto_31, g_inv_31]
    decide +kernel
  have g_adj_31 : ∀ u v : Fin 42, g_adj (g_auto_31 u) (g_auto_31 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_31]
    decide +kernel
  have g_inverse_32 : ∀ v : Fin 42, g_inv_32 (g_auto_32 v) = v ∧ g_auto_32 (g_inv_32 v) = v := by
    dsimp only [g_auto_32, g_inv_32]
    decide +kernel
  have g_adj_32 : ∀ u v : Fin 42, g_adj (g_auto_32 u) (g_auto_32 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_32]
    decide +kernel
  have g_inverse_33 : ∀ v : Fin 42, g_inv_33 (g_auto_33 v) = v ∧ g_auto_33 (g_inv_33 v) = v := by
    dsimp only [g_auto_33, g_inv_33]
    decide +kernel
  have g_adj_33 : ∀ u v : Fin 42, g_adj (g_auto_33 u) (g_auto_33 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_33]
    decide +kernel
  have g_inverse_34 : ∀ v : Fin 42, g_inv_34 (g_auto_34 v) = v ∧ g_auto_34 (g_inv_34 v) = v := by
    dsimp only [g_auto_34, g_inv_34]
    decide +kernel
  have g_adj_34 : ∀ u v : Fin 42, g_adj (g_auto_34 u) (g_auto_34 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_34]
    decide +kernel
  have g_inverse_35 : ∀ v : Fin 42, g_inv_35 (g_auto_35 v) = v ∧ g_auto_35 (g_inv_35 v) = v := by
    dsimp only [g_auto_35, g_inv_35]
    decide +kernel
  have g_adj_35 : ∀ u v : Fin 42, g_adj (g_auto_35 u) (g_auto_35 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_35]
    decide +kernel
  have g_inverse_36 : ∀ v : Fin 42, g_inv_36 (g_auto_36 v) = v ∧ g_auto_36 (g_inv_36 v) = v := by
    dsimp only [g_auto_36, g_inv_36]
    decide +kernel
  have g_adj_36 : ∀ u v : Fin 42, g_adj (g_auto_36 u) (g_auto_36 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_36]
    decide +kernel
  have g_inverse_37 : ∀ v : Fin 42, g_inv_37 (g_auto_37 v) = v ∧ g_auto_37 (g_inv_37 v) = v := by
    dsimp only [g_auto_37, g_inv_37]
    decide +kernel
  have g_adj_37 : ∀ u v : Fin 42, g_adj (g_auto_37 u) (g_auto_37 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_37]
    decide +kernel
  have g_inverse_38 : ∀ v : Fin 42, g_inv_38 (g_auto_38 v) = v ∧ g_auto_38 (g_inv_38 v) = v := by
    dsimp only [g_auto_38, g_inv_38]
    decide +kernel
  have g_adj_38 : ∀ u v : Fin 42, g_adj (g_auto_38 u) (g_auto_38 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_38]
    decide +kernel
  have g_inverse_39 : ∀ v : Fin 42, g_inv_39 (g_auto_39 v) = v ∧ g_auto_39 (g_inv_39 v) = v := by
    dsimp only [g_auto_39, g_inv_39]
    decide +kernel
  have g_adj_39 : ∀ u v : Fin 42, g_adj (g_auto_39 u) (g_auto_39 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_39]
    decide +kernel
  have g_inverse_40 : ∀ v : Fin 42, g_inv_40 (g_auto_40 v) = v ∧ g_auto_40 (g_inv_40 v) = v := by
    dsimp only [g_auto_40, g_inv_40]
    decide +kernel
  have g_adj_40 : ∀ u v : Fin 42, g_adj (g_auto_40 u) (g_auto_40 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_40]
    decide +kernel
  have g_inverse_41 : ∀ v : Fin 42, g_inv_41 (g_auto_41 v) = v ∧ g_auto_41 (g_inv_41 v) = v := by
    dsimp only [g_auto_41, g_inv_41]
    decide +kernel
  have g_adj_41 : ∀ u v : Fin 42, g_adj (g_auto_41 u) (g_auto_41 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_41]
    decide +kernel
  have g_inverse_42 : ∀ v : Fin 42, g_inv_42 (g_auto_42 v) = v ∧ g_auto_42 (g_inv_42 v) = v := by
    dsimp only [g_auto_42, g_inv_42]
    decide +kernel
  have g_adj_42 : ∀ u v : Fin 42, g_adj (g_auto_42 u) (g_auto_42 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_42]
    decide +kernel
  have g_inverse_43 : ∀ v : Fin 42, g_inv_43 (g_auto_43 v) = v ∧ g_auto_43 (g_inv_43 v) = v := by
    dsimp only [g_auto_43, g_inv_43]
    decide +kernel
  have g_adj_43 : ∀ u v : Fin 42, g_adj (g_auto_43 u) (g_auto_43 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_43]
    decide +kernel
  have g_inverse_44 : ∀ v : Fin 42, g_inv_44 (g_auto_44 v) = v ∧ g_auto_44 (g_inv_44 v) = v := by
    dsimp only [g_auto_44, g_inv_44]
    decide +kernel
  have g_adj_44 : ∀ u v : Fin 42, g_adj (g_auto_44 u) (g_auto_44 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_44]
    decide +kernel
  have g_inverse_45 : ∀ v : Fin 42, g_inv_45 (g_auto_45 v) = v ∧ g_auto_45 (g_inv_45 v) = v := by
    dsimp only [g_auto_45, g_inv_45]
    decide +kernel
  have g_adj_45 : ∀ u v : Fin 42, g_adj (g_auto_45 u) (g_auto_45 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_45]
    decide +kernel
  have g_inverse_46 : ∀ v : Fin 42, g_inv_46 (g_auto_46 v) = v ∧ g_auto_46 (g_inv_46 v) = v := by
    dsimp only [g_auto_46, g_inv_46]
    decide +kernel
  have g_adj_46 : ∀ u v : Fin 42, g_adj (g_auto_46 u) (g_auto_46 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_46]
    decide +kernel
  have g_inverse_47 : ∀ v : Fin 42, g_inv_47 (g_auto_47 v) = v ∧ g_auto_47 (g_inv_47 v) = v := by
    dsimp only [g_auto_47, g_inv_47]
    decide +kernel
  have g_adj_47 : ∀ u v : Fin 42, g_adj (g_auto_47 u) (g_auto_47 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_47]
    decide +kernel
  have g_inverse_48 : ∀ v : Fin 42, g_inv_48 (g_auto_48 v) = v ∧ g_auto_48 (g_inv_48 v) = v := by
    dsimp only [g_auto_48, g_inv_48]
    decide +kernel
  have g_adj_48 : ∀ u v : Fin 42, g_adj (g_auto_48 u) (g_auto_48 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_48]
    decide +kernel
  have g_inverse_49 : ∀ v : Fin 42, g_inv_49 (g_auto_49 v) = v ∧ g_auto_49 (g_inv_49 v) = v := by
    dsimp only [g_auto_49, g_inv_49]
    decide +kernel
  have g_adj_49 : ∀ u v : Fin 42, g_adj (g_auto_49 u) (g_auto_49 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_49]
    decide +kernel
  have g_inverse_50 : ∀ v : Fin 42, g_inv_50 (g_auto_50 v) = v ∧ g_auto_50 (g_inv_50 v) = v := by
    dsimp only [g_auto_50, g_inv_50]
    decide +kernel
  have g_adj_50 : ∀ u v : Fin 42, g_adj (g_auto_50 u) (g_auto_50 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_50]
    decide +kernel
  have g_inverse_51 : ∀ v : Fin 42, g_inv_51 (g_auto_51 v) = v ∧ g_auto_51 (g_inv_51 v) = v := by
    dsimp only [g_auto_51, g_inv_51]
    decide +kernel
  have g_adj_51 : ∀ u v : Fin 42, g_adj (g_auto_51 u) (g_auto_51 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_51]
    decide +kernel
  have g_inverse_52 : ∀ v : Fin 42, g_inv_52 (g_auto_52 v) = v ∧ g_auto_52 (g_inv_52 v) = v := by
    dsimp only [g_auto_52, g_inv_52]
    decide +kernel
  have g_adj_52 : ∀ u v : Fin 42, g_adj (g_auto_52 u) (g_auto_52 v) = g_adj u v := by
    dsimp only [g_adj, g_auto_52]
    decide +kernel
  have g_inverses : ∀ k : Fin 53, ∀ v : Fin 42, g_invs k (g_autos k v) = v ∧ g_autos k (g_invs k v) = v := by
    intro k
    fin_cases k
    · exact g_inverse_0
    · exact g_inverse_1
    · exact g_inverse_2
    · exact g_inverse_3
    · exact g_inverse_4
    · exact g_inverse_5
    · exact g_inverse_6
    · exact g_inverse_7
    · exact g_inverse_8
    · exact g_inverse_9
    · exact g_inverse_10
    · exact g_inverse_11
    · exact g_inverse_12
    · exact g_inverse_13
    · exact g_inverse_14
    · exact g_inverse_15
    · exact g_inverse_16
    · exact g_inverse_17
    · exact g_inverse_18
    · exact g_inverse_19
    · exact g_inverse_20
    · exact g_inverse_21
    · exact g_inverse_22
    · exact g_inverse_23
    · exact g_inverse_24
    · exact g_inverse_25
    · exact g_inverse_26
    · exact g_inverse_27
    · exact g_inverse_28
    · exact g_inverse_29
    · exact g_inverse_30
    · exact g_inverse_31
    · exact g_inverse_32
    · exact g_inverse_33
    · exact g_inverse_34
    · exact g_inverse_35
    · exact g_inverse_36
    · exact g_inverse_37
    · exact g_inverse_38
    · exact g_inverse_39
    · exact g_inverse_40
    · exact g_inverse_41
    · exact g_inverse_42
    · exact g_inverse_43
    · exact g_inverse_44
    · exact g_inverse_45
    · exact g_inverse_46
    · exact g_inverse_47
    · exact g_inverse_48
    · exact g_inverse_49
    · exact g_inverse_50
    · exact g_inverse_51
    · exact g_inverse_52
  have g_adj_all : ∀ k : Fin 53, ∀ u v : Fin 42, g_adj (g_autos k u) (g_autos k v) = g_adj u v := by
    intro k
    fin_cases k
    · exact g_adj_0
    · exact g_adj_1
    · exact g_adj_2
    · exact g_adj_3
    · exact g_adj_4
    · exact g_adj_5
    · exact g_adj_6
    · exact g_adj_7
    · exact g_adj_8
    · exact g_adj_9
    · exact g_adj_10
    · exact g_adj_11
    · exact g_adj_12
    · exact g_adj_13
    · exact g_adj_14
    · exact g_adj_15
    · exact g_adj_16
    · exact g_adj_17
    · exact g_adj_18
    · exact g_adj_19
    · exact g_adj_20
    · exact g_adj_21
    · exact g_adj_22
    · exact g_adj_23
    · exact g_adj_24
    · exact g_adj_25
    · exact g_adj_26
    · exact g_adj_27
    · exact g_adj_28
    · exact g_adj_29
    · exact g_adj_30
    · exact g_adj_31
    · exact g_adj_32
    · exact g_adj_33
    · exact g_adj_34
    · exact g_adj_35
    · exact g_adj_36
    · exact g_adj_37
    · exact g_adj_38
    · exact g_adj_39
    · exact g_adj_40
    · exact g_adj_41
    · exact g_adj_42
    · exact g_adj_43
    · exact g_adj_44
    · exact g_adj_45
    · exact g_adj_46
    · exact g_adj_47
    · exact g_adj_48
    · exact g_adj_49
    · exact g_adj_50
    · exact g_adj_51
    · exact g_adj_52
  let g_selected (u : Fin 42) : Bool := decide (u.val ∈ ([0,1,2,6,8,18,24,31,33,37] : List Nat))
  let g_selectedList : Fin 10 → Fin 42 := ![0,1,2,6,8,18,24,31,33,37]
  let g_choose : Fin 10 → Fin 10 → Fin 53 := ![![0,0,1,2,3,4,5,6,7,8],![0,9,9,10,11,12,13,14,15,16],![1,9,17,18,19,20,21,22,23,24],![2,10,18,25,26,27,28,29,30,31],![3,11,19,26,32,33,34,35,36,37],![4,12,20,27,33,38,39,40,41,42],![5,13,21,28,34,39,43,44,45,46],![6,14,22,29,35,40,44,47,48,49],![7,15,23,30,36,41,45,48,50,51],![8,16,24,31,37,42,46,49,51,52]]
  have g_selected_iff : ∀ u : Fin 42, g_selected u = true ↔ ∃ i : Fin 10, g_selectedList i = u := by
    dsimp only [g_selected, g_selectedList]
    decide +kernel
  have g_choose_ok : ∀ i j : Fin 10,
      (g_autos (g_choose i j) (g_selectedList i) = 0 ∧ g_autos (g_choose i j) (g_selectedList j) = 0) ∨
      (g_autos (g_choose i j) (g_selectedList i) = 0 ∧ g_autos (g_choose i j) (g_selectedList j) = 1) ∨ (g_autos (g_choose i j) (g_selectedList j) = 0 ∧ g_autos (g_choose i j) (g_selectedList i) = 1) ∨
      (g_autos (g_choose i j) (g_selectedList i) = 0 ∧ g_autos (g_choose i j) (g_selectedList j) = 22) ∨ (g_autos (g_choose i j) (g_selectedList j) = 0 ∧ g_autos (g_choose i j) (g_selectedList i) = 22) := by
    dsimp only [g_choose, g_selectedList, g_autos, g_auto_0, g_auto_1, g_auto_2, g_auto_3, g_auto_4, g_auto_5, g_auto_6, g_auto_7, g_auto_8, g_auto_9, g_auto_10, g_auto_11, g_auto_12, g_auto_13, g_auto_14, g_auto_15, g_auto_16, g_auto_17, g_auto_18, g_auto_19, g_auto_20, g_auto_21, g_auto_22, g_auto_23, g_auto_24, g_auto_25, g_auto_26, g_auto_27, g_auto_28, g_auto_29, g_auto_30, g_auto_31, g_auto_32, g_auto_33, g_auto_34, g_auto_35, g_auto_36, g_auto_37, g_auto_38, g_auto_39, g_auto_40, g_auto_41, g_auto_42, g_auto_43, g_auto_44, g_auto_45, g_auto_46, g_auto_47, g_auto_48, g_auto_49, g_auto_50, g_auto_51, g_auto_52]
    decide +kernel
  have g_canonical : ∀ u v : Fin 42, g_selected u = true → g_selected v = true → ∃ k : Fin 53,
      (g_autos k u = 0 ∧ g_autos k v = 0) ∨
      (g_autos k u = 0 ∧ g_autos k v = 1) ∨ (g_autos k v = 0 ∧ g_autos k u = 1) ∨
      (g_autos k u = 0 ∧ g_autos k v = 22) ∨ (g_autos k v = 0 ∧ g_autos k u = 22) := by
    intro u v hu hv
    obtain ⟨i,rfl⟩ := (g_selected_iff u).mp hu
    obtain ⟨j,rfl⟩ := (g_selected_iff v).mp hv
    exact ⟨g_choose i j,g_choose_ok i j⟩

  let b_edge (u v : Fin 42) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)

  let b_target (x : Fin 42 → Bool) : Prop := ∃ u v, b_edge u v ∧ x u = true ∧ x v = true

  let b_independent (x : Fin 42 → Bool) : Prop :=
    ∀ u v, x u = true → x v = true → ¬ b_edge u v

  let b_closed (x : Fin 42 → Bool) : Prop :=
    ∀ u, x u = true ↔ ∀ v, x v = true → ¬ (b_edge u v ∨ b_edge v u)

  have b_bool_le (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
    cases a <;> cases b <;> decide

  have b_extend_maximal {n : Nat} (P : (Fin n → Bool) → Prop) (x : Fin n → Bool)
      (hx : P x) : ∃ y, P y ∧ x ≤ y ∧ ∀ z, P z → y ≤ z → z = y := by
    obtain ⟨y,hxy,hy,hmax⟩ := (Set.toFinite {y | P y}).exists_le_maximal hx
    exact ⟨y,hy,hxy,fun z hz hyz => le_antisymm (hmax hz hyz) hyz⟩

  have b_maximal_closed (y : Fin 42 → Bool) (hi : b_independent y)
      (hm : ∀ z, b_independent z → y ≤ z → z = y) : b_closed y := by
    intro u
    constructor
    · intro hu v hv hbad
      rcases hbad with h | h
      · exact hi u v hu hv h
      · exact hi v u hv hu h
    · intro hall
      by_contra hnot
      have hu : y u = false := Bool.eq_false_of_not_eq_true hnot
      let z := Function.update y u true
      have hiz : b_independent z := by
        intro a b ha hb
        by_cases hau : a = u
        · subst a
          by_cases hbu : b = u
          · subst b
            intro he
            have h1 := he.1
            have h2 := he.2.1
            omega
          · have hby : y b = true := by simpa [z,Function.update_of_ne hbu] using hb
            exact fun he => hall b hby (Or.inl he)
        · have hay : y a = true := by simpa [z,Function.update_of_ne hau] using ha
          by_cases hbu : b = u
          · subst b
            exact fun he => hall a hay (Or.inr he)
          · have hby : y b = true := by simpa [z,Function.update_of_ne hbu] using hb
            exact hi a b hay hby
      have hyz : y ≤ z := by
        intro v
        rw [b_bool_le]
        intro hv
        by_cases h : v = u
        · subst v; simp [z]
        · simpa [z,Function.update_of_ne h] using hv
      have he := congrFun (hm z hiz hyz) u
      simp [z,hu] at he

  have b_monotone_eval (C : Circuit) (h : Monotone2 C) (x y : Fin 42 → Bool)
      (hxy : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    exact s_mono C.gates
      (fun g hg => ⟨by simpa using (h g hg).1,(h g hg).2⟩) x y hxy C.output

  have b_boundary_complete (C : Circuit) (h : Monotone2 C)
      (positive : ∀ u v, b_edge u v →
        C.eval (List.ofFn (fun i => decide (i=u ∨ i=v))) = true)
      (negative : ∀ x, b_closed x → C.eval (List.ofFn x) = false) :
      ∀ x, C.eval (List.ofFn x) = true ↔ b_target x := by
    intro x
    constructor
    · intro hx
      by_contra hn
      have hi : b_independent x := by
        intro u v hu hv he
        exact hn ⟨u,v,he,hu,hv⟩
      obtain ⟨y,hy,hxy,hm⟩ := b_extend_maximal b_independent x hi
      have hcy := b_maximal_closed y hy hm
      have hpos := b_monotone_eval C h x y
        (fun i hi => (b_bool_le _ _).mp (hxy i) hi) hx
      rw [negative y hcy] at hpos
      contradiction
    · rintro ⟨u,v,he,hu,hv⟩
      exact b_monotone_eval C h _ x (fun i hi => by
        rcases of_decide_eq_true hi with rfl | rfl
        · exact hu
        · exact hv) (positive u v he)

  let c_active (C : Circuit) (x : Fin 42 → Bool) : Prop :=
    ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (C.wires (List.ofFn x)).getD (42+j) false = true

  let c_pair (u v : Fin 42) : Fin 42 → Bool := fun i => decide (i=u ∨ i=v)

  have c_pair_comm (u v : Fin 42) : c_pair u v = c_pair v u := by
    funext i
    simp only [c_pair,or_comm]

  have c_active_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin 42 → Bool)
      (hxy : ∀ i, x i=true → y i=true) : c_active C x → c_active C y := by
    rintro ⟨j,g,hj,hg,hv⟩
    exact ⟨j,g,hj,hg,s_mono C.gates
      (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) x y hxy (42+j) hv⟩

  have c_target_adj (x : Fin 42 → Bool) :
      b_target x ↔ ∃ u v, g_adj u v = true ∧ x u=true ∧ x v=true := by
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      exact ⟨u,v,(g_adj_spec u v).mpr (Or.inl he),hu,hv⟩
    · rintro ⟨u,v,he,hu,hv⟩
      rcases (g_adj_spec u v).mp he with he | he
      · exact ⟨u,v,he,hu,hv⟩
      · exact ⟨v,u,he,hv,hu⟩

  have c_target_auto (k : Fin 53) (x : Fin 42 → Bool) :
      b_target (x ∘ g_autos k) ↔ b_target x := by
    rw [c_target_adj,c_target_adj]
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      exact ⟨g_autos k u,g_autos k v,by rw [g_adj_all]; exact he,hu,hv⟩
    · rintro ⟨u,v,he,hu,hv⟩
      refine ⟨g_invs k u,g_invs k v,?_,?_,?_⟩
      · have hh := g_adj_all k (g_invs k u) (g_invs k v)
        rw [(g_inverses k u).2,(g_inverses k v).2] at hh
        exact hh ▸ he
      · simpa only [Function.comp_apply,(g_inverses k u).2] using hu
      · simpa only [Function.comp_apply,(g_inverses k v).2] using hv

  have c_pair_transport (k : Fin 53) (u v : Fin 42) :
      c_pair (g_autos k u) (g_autos k v) ∘ g_autos k = c_pair u v := by
    funext i
    have hinj : Function.Injective (g_autos k) :=
      Function.LeftInverse.injective (fun a => (g_inverses k a).1)
    simp only [Function.comp_apply,c_pair,hinj.eq_iff]

  have c_active_transport (C : Circuit) (k : Fin 53) (u v : Fin 42)
      (h : c_active C (c_pair u v)) :
      c_active (r_relabel 42 42 (g_autos k) C)
        (c_pair (g_autos k u) (g_autos k v)) := by
    rcases h with ⟨j,g,hj,hg,hv⟩
    refine ⟨j,r_relGate 42 42 (g_autos k) g,
      r_gate_at 42 (g_autos k) C j g hj,hg,?_⟩
    rw [r_gate_value,c_pair_transport]
    exact hv

  have c_small_cover (T : Finset (Fin 42))
      (hT : ∀ i ∈ T, g_selected i=true) (hc : T.card ≤ 2) :
      ∃ u v, g_selected u=true ∧ g_selected v=true ∧ T ⊆ {u,v} := by
    classical
    by_cases he : T.Nonempty
    · obtain ⟨u,hu⟩ := he
      by_cases h1 : T.card ≤ 1
      · refine ⟨u,u,hT u hu,hT u hu,?_⟩
        intro v hv
        have hvu := Finset.card_le_one.mp h1 v hv u hu
        simp [hvu]
      · obtain ⟨a,b,hab,ht⟩ := Finset.card_eq_two.mp (show T.card=2 by omega)
        subst T
        exact ⟨a,b,hT a (by simp),hT b (by simp),Finset.Subset.refl _⟩
    · have ht : T=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      exact ⟨0,0,by dsimp only [g_selected]; decide +kernel,by dsimp only [g_selected]; decide +kernel,by simp [ht]⟩

  have c_canonical_bound
      (hs : ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x, C.eval (List.ofFn x)=true ↔ b_target x) → c_active C (c_pair 0 1) → False)
      (hc : ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x, C.eval (List.ofFn x)=true ↔ b_target x) → c_active C (c_pair 0 22) → False)
      (C : Circuit) (hm : Monotone2 C) (hn : C.size ≤ 124)
      (hf : ∀ x, C.eval (List.ofFn x)=true ↔ b_target x)
      (u v : Fin 42) (hu : g_selected u=true) (hv : g_selected v=true)
      (ha : c_active C (c_pair u v)) : False := by
    obtain ⟨k,hk⟩ := g_canonical u v hu hv
    let D := r_relabel 42 42 (g_autos k) C
    have hdm : Monotone2 D := r_monotone2 42 (g_autos k) C hm
    have hdn : D.size ≤ 124 := by
      simpa only [D,r_size] using hn
    have hdf : ∀ x, D.eval (List.ofFn x)=true ↔ b_target x := by
      intro x
      rw [r_eval,hf,c_target_auto]
    have hda : c_active D (c_pair (g_autos k u) (g_autos k v)) := c_active_transport C k u v ha
    rcases hk with ⟨h0,h0'⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h22⟩ | ⟨h0,h22⟩
    · rw [h0,h0'] at hda
      apply hs D hdm hdn hdf
      exact c_active_mono D hdm _ _ (fun i hi => by
        simp only [c_pair,decide_eq_true_eq,or_self] at hi
        simp [c_pair,hi]) hda
    · rw [h0,h1] at hda
      exact hs D hdm hdn hdf hda
    · rw [h0,h1] at hda
      exact hs D hdm hdn hdf (by rw [c_pair_comm] at hda; exact hda)
    · rw [h0,h22] at hda
      exact hc D hdm hdn hdf hda
    · rw [h0,h22] at hda
      exact hc D hdm hdn hdf (by rw [c_pair_comm] at hda; exact hda)

  have c_main
      (hs : ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x, C.eval (List.ofFn x)=true ↔ b_target x) → c_active C (c_pair 0 1) → False)
      (hc : ∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
        (∀ x, C.eval (List.ofFn x)=true ↔ b_target x) → c_active C (c_pair 0 22) → False)
      (C : Circuit) (hm : Monotone2 C) (hn : C.size ≤ 124)
      (ha : c_active C g_selected)
      (hp : ∀ u v, b_edge u v →
        C.eval (List.ofFn (fun i => decide (i=u ∨ i=v))) = true)
      (hz : ∀ x, b_closed x → C.eval (List.ofFn x)=false) : False := by
    classical
    let S : Finset (Fin 42) := Finset.univ.filter (fun i => g_selected i=true)
    have hS : (fun i => decide (i∈S)) = g_selected := by
      funext i
      simp [S]
    have has : c_active C (fun i => decide (i∈S)) := by rw [hS]; exact ha
    obtain ⟨T,hTS,hT,j,g,hj,hg,hv⟩ := s_main 42 C hm S has
    obtain ⟨u,v,hu,hv',ht⟩ := c_small_cover T
      (fun i hi => (Finset.mem_filter.mp (hTS hi)).2) hT
    apply c_canonical_bound hs hc C hm hn (b_boundary_complete C hm hp hz) u v hu hv'
    apply c_active_mono C hm (fun i => decide (i∈T)) (c_pair u v) _ ⟨j,g,hj,hg,hv⟩
    intro i hi
    have hh := ht (of_decide_eq_true hi)
    simpa only [Finset.mem_insert,Finset.mem_singleton,c_pair,decide_eq_true_eq] using hh

  intro edge closed C hm hn ha hp hz
  exact c_main sameShore crossShore C hm hn ha hp hz
