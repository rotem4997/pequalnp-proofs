import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2084_2
    (hFan1 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∃ v ∉ A, (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 1) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1)
    (hFan2NonOr : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) →
      (∃ v ∉ A,
        have r := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val;
        r.length = 2 ∧ ∃ g ∈ r, g.op ≠ GateOp.or) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1)
    (hFan2AllOr : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      FanInTwo C → circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) →
      (∀ v ∉ A,
        have r := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val;
        r.length = 2 → ∀ g ∈ r, g.op = GateOp.or) →
      (∃ v ∉ A, (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 2) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  classical
  intro n k G A f hdeg hgirth hnoA hE htau hf s hs
  let wiresFrom : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append : ∀ (gs₁ gs₂ : List Gate) (w : List Bool),
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    intro gs₁ gs₂ w
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_length : ∀ (gs : List Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wiresFrom]
    | cons g gs ih =>
      intro w
      have h1 : wiresFrom (g :: gs) w =
          wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [h1, ih]
      simp
      omega
  have getD_snoc_lt : ∀ (w : List Bool) (v : Bool) (i : ℕ), i < w.length →
      (w ++ [v]).getD i false = w.getD i false := by
    intro w v i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ (w : List Bool) (v : Bool) (i : ℕ), i = w.length →
      (w ++ [v]).getD i false = v := by
    intro w v i hi
    subst hi
    simp
  have ofFn_getD_lt : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
  let substWire : ℕ → ℕ → ℕ → ℕ := fun k0 a i =>
    if i < k0 then i else if i = k0 then a else i - 1
  let substGate : ℕ → ℕ → Gate → Gate := fun k0 a g =>
    ⟨g.op, g.inputs.map (substWire k0 a)⟩
  let deleteGate : Circuit → ℕ → ℕ → Circuit := fun C j a =>
    ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (n + j) a),
      substWire (n + j) a C.output⟩
  have deleteGate_ok : ∀ (C : Circuit) (j a : ℕ), FanInTwo C → FanInTwo (deleteGate C j a) := by
    intro C j a hok g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hok g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      have h0 := hok g0 (List.mem_of_mem_drop hg0)
      exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
  have deleteGate_len : ∀ (C : Circuit) (j a : ℕ), j < C.gates.length →
      (deleteGate C j a).gates.length = C.gates.length - 1 := by
    intro C j a hj
    simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  have deleteDeadGate : ∀ (C : Circuit) (hC : FanInTwo C) (j : ℕ) (hj : j < C.gates.length),
      C.output ≠ n + j →
      (∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (n + j) ∉ C.gates[j'].inputs) →
      HasCircuitSize n (circuitFun n C) (C.gates.length - 1) := by
    intro C hC j hj hout hno
    refine ⟨deleteGate C j 0, deleteGate_ok C j 0 hC,
      by show (deleteGate C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len C j 0 hj], ?_⟩
    intro x
    show ((deleteGate C j 0).wires (List.ofFn x)).getD (substWire (n + j) 0 C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        rw [h2] at h1
        simpa only [List.append_assoc, List.singleton_append] using h1.symm
      set w₂ := wiresFrom (C.gates.take j) (List.ofFn x) with hw₂
      set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
      have hw₂_len : w₂.length = n + j := by
        rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      have hw₁_len : w₁.length = n + j + 1 := by
        rw [hw₁, wiresFrom_length, hw₂_len]; simp
      have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (n + j) ∉ g.inputs := by
        intro g hg
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_drop]
        exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
      have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
          w₁'.length = w₂'.length + 1 → n + j ≤ w₂'.length →
          (∀ g ∈ gs, (n + j) ∉ g.inputs) →
          (∀ i < w₁'.length, i ≠ n + j → w₂'.getD (substWire (n + j) 0 i) false = w₁'.getD i false) →
          ∀ i < (wiresFrom gs w₁').length, i ≠ n + j →
            (wiresFrom (gs.map (substGate (n + j) 0)) w₂').getD (substWire (n + j) 0 i) false =
              (wiresFrom gs w₁').getD i false := by
        intro gs
        induction gs with
        | nil =>
          intro w₁' w₂' _ _ _ hag i hi hne
          exact hag i hi hne
        | cons g rest ih =>
          intro w₁' w₂' hlen' hk' hnod hag'
          have hstep1 : wiresFrom (g :: rest) w₁' =
              wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)]) := rfl
          have hstep2 : wiresFrom ((g :: rest).map (substGate (n + j) 0)) w₂' =
              wiresFrom (rest.map (substGate (n + j) 0))
                (w₂' ++ [(substGate (n + j) 0 g).op.eval
                  ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false)]) := rfl
          rw [hstep1, hstep2]
          have hmap : ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false) =
              (g.inputs.map fun i => w₁'.getD i false) := by
            simp only [substGate, List.map_map]
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hne : i ≠ n + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
            by_cases hlti : i < w₁'.length
            · exact hag' i hlti hne
            · have hge : w₂'.length ≤ substWire (n + j) 0 i := by
                dsimp [substWire]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
          rw [hmap]
          apply ih _ _ (by simp [hlen']) (by simp; omega)
            (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
          intro i hi hne
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlti : i < w₁'.length
          · have hsublt : substWire (n + j) 0 i < w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_lt _ _ _ hsublt, getD_snoc_lt _ _ _ hlti]
            exact hag' i hlti hne
          · have hieq : i = w₁'.length := by omega
            have hsubeq : substWire (n + j) 0 i = w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ hsubeq, getD_snoc_eq _ _ _ hieq]
      show (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (n + j) 0)) (List.ofFn x)).getD
          (substWire (n + j) 0 C.output) false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
      rw [wiresFrom_append, ← hw₂]
      conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
      have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = n + C.gates.length := by
        rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
      apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ C.output (by omega) hout
      intro u hu hune
      have hltu : u < n + j := by omega
      simp only [substWire, hltu, ↓reduceIte]
      have hw1e : w₁ = w₂ ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w₂.getD i false)] := rfl
      rw [hw1e, getD_snoc_lt _ _ _ (by omega)]
    · have hge1 : (deleteGate C j 0).gates.length + n ≤ substWire (n + j) 0 C.output := by
        rw [deleteGate_len C j 0 hj]
        dsimp [substWire]
        split_ifs <;> omega
      have h1 : ((deleteGate C j 0).wires (List.ofFn x)).length =
          n + (deleteGate C j 0).gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have h2 : (C.wires (List.ofFn x)).length = n + C.gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  let reads : ℕ → Gate → Bool := fun v g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  have gate_eval_agree : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g.inputs.length ≤ 2 → ∀ (w₁ w₂ : List Bool) (v : ℕ),
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      reads v g = false →
      g.op.eval (g.inputs.map fun i => w₁.getD i false) =
        g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
    intro g hop hlen w₁ w₂ v hag hnr
    have hnr' : v ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
      intro hm
      have ht : reads v g = true := List.contains_iff_mem.2 hm
      rw [hnr] at ht
      cases ht
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    rcases hop' with h | h | h
    · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
        rw [h]
        have : GateOp.and.eval [false] = false := rfl
        rw [this]
        exact List.take_of_length_le hlen
      rw [ht2] at hnr'
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun he => hnr' (he ▸ hi))
    · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
        rw [h]
        have : GateOp.or.eval [false] = false := rfl
        rw [this]
        exact List.take_of_length_le hlen
      rw [ht2] at hnr'
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun he => hnr' (he ▸ hi))
    · rw [h] at hnr' ⊢
      have : GateOp.not.eval [false] = true := rfl
      rw [this] at hnr'
      rcases hgins : g.inputs with _ | ⟨a, rest⟩
      · rfl
      · rw [hgins] at hnr'
        have hav : a ≠ v := fun he => hnr' (by simp [he])
        show (!(w₁.getD a false)) = (!(w₂.getD a false))
        rw [hag a hav]
  have wiresFrom_agree_eff : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (v : ℕ) (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      (∀ g ∈ gs, reads v g = false) →
      ∀ i, i ≠ v → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    intro gs
    induction gs with
    | nil => intro _ v w₁ w₂ _ hag _ i hi; exact hag i hi
    | cons g rest ih =>
      intro hok v w₁ w₂ hlen hag hnr i hi
      have h1 : wiresFrom (g :: rest) w₁ =
          wiresFrom rest (w₁ ++ [g.op.eval (g.inputs.map fun k => w₁.getD k false)]) := rfl
      have h2 : wiresFrom (g :: rest) w₂ =
          wiresFrom rest (w₂ ++ [g.op.eval (g.inputs.map fun k => w₂.getD k false)]) := rfl
      rw [h1, h2]
      have hge := gate_eval_agree g (hok g List.mem_cons_self).1 (hok g List.mem_cons_self).2
        w₁ w₂ v hag (hnr g List.mem_cons_self)
      apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) v _ _
        (by simp [hlen]) _ (fun g' hg' => hnr g' (List.mem_cons_of_mem _ hg')) i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
        exact hag j hj
      · by_cases heq : j = w₁.length
        · rw [getD_snoc_eq _ _ _ heq, getD_snoc_eq _ _ _ (by omega), hge]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hex : ∃ t : ℕ, HasCircuitSize n f t := ⟨s, hs⟩
  obtain ⟨C, hC, hCsz, hCval⟩ := Nat.find_spec hex
  have hCs : C.size ≤ s := hCsz.trans (Nat.find_min' hex hs)
  have heval : circuitFun n C = f := funext hCval
  have hmin : ∀ m, HasCircuitSize n f m → C.size ≤ m := fun m hm =>
    hCsz.trans (Nat.find_min' hex hm)
  suffices hgoal : A.card + G.edgeSet.ncard + k ≤ C.size + 1 by omega
  let slots : Circuit → List ℕ := fun D => D.output :: D.gates.flatMap Gate.inputs
  have gateSlotBound : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g tail ih =>
      intro h
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have countBound : ∀ (xs : List ℕ) (S : Finset ℕ), ∑ i ∈ S, xs.count i ≤ xs.length := by
    intro xs
    induction xs with
    | nil => intro S; simp
    | cons a xs ih =>
      intro S
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> have := ih S <;> omega
  have filteredSlots : ∀ (v : ℕ) (gs : List Gate),
      (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
    intro v gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons, List.count_append, List.filter_cons]
      by_cases h : reads v g = true
      · simp only [h, ↓reduceIte]
        have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
        have hp := List.count_pos_iff.mpr hm
        simp only [List.length_cons]
        omega
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        omega
  have hread_pos : ∀ v ∉ A, 1 ≤ (C.gates.filter (reads v.val)).length := by
    intro v hv
    by_contra h0
    have hempty : ∀ g ∈ C.gates, reads v.val g = false := by
      intro g hg
      cases hr : reads v.val g with
      | false => rfl
      | true =>
        have hm : g ∈ C.gates.filter (reads v.val) := List.mem_filter.2 ⟨hg, hr⟩
        have hpos : 0 < (C.gates.filter (reads v.val)).length := List.length_pos_of_mem hm
        omega
    by_cases hout : C.output = v.val
    · let xv : Fin n → Bool := fun j => decide (j = v)
      have h1 : circuitFun n C xv = true := by
        show (wiresFrom C.gates (List.ofFn xv)).getD C.output false = true
        have hlen : (List.ofFn xv).length = n := List.length_ofFn
        have hkeep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
            (wiresFrom gs w).getD i false = w.getD i false := by
          intro gs
          induction gs with
          | nil => intro w i _; rfl
          | cons g rest ih =>
            intro w i hi
            have hstep : wiresFrom (g :: rest) w =
                wiresFrom rest (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) := rfl
            rw [hstep, ih _ i (by simp; omega), getD_snoc_lt _ _ _ hi]
        rw [hout, hkeep _ _ _ (by rw [hlen]; exact v.isLt), ofFn_getD_lt xv v.val v.isLt]
        simp [xv]
      rw [heval] at h1
      rcases (hf xv).1 h1 with ⟨a, haA, ha⟩ | ⟨u, w, huw, hu, hw⟩
      · have hav : a = v := by simpa [xv] using ha
        exact hv (hav ▸ haA)
      · have huv : u = v := by simpa [xv] using hu
        have hwv : w = v := by simpa [xv] using hw
        exact huw.ne (huv.trans hwv.symm)
    · have hnb : (G.neighborSet v).Nonempty := by
        have hpos : 0 < (G.neighborSet v).ncard := by rw [hdeg v hv]; omega
        exact Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨u, hu⟩ := hnb
      have huv : G.Adj v u := hu
      let x1 : Fin n → Bool := fun j => decide (j = u)
      let x2 : Fin n → Bool := fun j => decide (j = u ∨ j = v)
      have hag : ∀ i, i ≠ v.val → (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
        intro i hi
        by_cases hlt : i < n
        · rw [ofFn_getD_lt x1 i hlt, ofFn_getD_lt x2 i hlt]
          have hne : (⟨i, hlt⟩ : Fin n) ≠ v := fun e => hi (congrArg Fin.val e)
          simp [x1, x2, hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have heq : circuitFun n C x1 = circuitFun n C x2 :=
        wiresFrom_agree_eff C.gates hC v.val (List.ofFn x1) (List.ofFn x2) (by simp) hag hempty
          C.output hout
      rw [heval] at heq
      have hf2 : f x2 = true := (hf x2).2 (Or.inr ⟨v, u, huv, by simp [x2], by simp [x2]⟩)
      have hf1 : f x1 = false := by
        cases hfx : f x1 with
        | false => rfl
        | true =>
          rcases (hf x1).1 hfx with ⟨a, haA, ha⟩ | ⟨a, b, hab, ha, hb⟩
          · have hau : a = u := by simpa [x1] using ha
            exact False.elim (hnoA u v huv.symm (hau ▸ haA))
          · have hau : a = u := by simpa [x1] using ha
            have hbu : b = u := by simpa [x1] using hb
            exact False.elim (hab.ne (hau.trans hbu.symm))
      rw [hf1, hf2] at heq
      cases heq
  by_cases hge3 : ∀ v ∉ A, 3 ≤ (C.gates.filter (reads v.val)).length
  · let cnt : ℕ → ℕ := fun i => (slots C).count i
    have marked : ∀ a ∈ A, 1 ≤ cnt a.val := by
      intro a ha
      apply List.count_pos_iff.2
      by_contra hn
      have hout : C.output ≠ a.val := fun he => hn (by simp [slots, he])
      have hnr : ∀ g ∈ C.gates, reads a.val g = false := by
        intro g hg
        cases hr : reads a.val g with
        | false => rfl
        | true =>
          have hm : a.val ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.1 hr)
          exact absurd (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨g, hg, hm⟩)) hn
      let z : Fin n → Bool := fun _ => false
      let y : Fin n → Bool := fun j => decide (j = a)
      have hag : ∀ i, i ≠ a.val → (List.ofFn z).getD i false = (List.ofFn y).getD i false := by
        intro i hi
        by_cases hlt : i < n
        · rw [ofFn_getD_lt z i hlt, ofFn_getD_lt y i hlt]
          have hne : (⟨i, hlt⟩ : Fin n) ≠ a := fun e => hi (congrArg Fin.val e)
          simp [z, y, hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have heq : circuitFun n C z = circuitFun n C y :=
        wiresFrom_agree_eff C.gates hC a.val (List.ofFn z) (List.ofFn y) (by simp) hag hnr
          C.output hout
      rw [heval] at heq
      have hz : f z = false := by
        cases hfz : f z with
        | false => rfl
        | true =>
          rcases (hf z).1 hfz with ⟨b, _, hb⟩ | ⟨b, _, _, hb, _⟩ <;> simp [z] at hb
      have hy : f y = true := (hf y).2 (Or.inl ⟨a, ha, by simp [y]⟩)
      rw [hz, hy] at heq
      cases heq
    have unmarked : ∀ a ∈ Aᶜ, 3 ≤ cnt a.val := by
      intro a ha
      have h3 := hge3 a (Finset.mem_compl.1 ha)
      have hf0 := filteredSlots a.val C.gates
      simp only [cnt, slots, List.count_cons]
      omega
    have internal : ∀ i ∈ Finset.range C.gates.length, 1 ≤ cnt (n + i) := by
      intro i hi
      apply List.count_pos_iff.2
      by_contra hn
      have hout : C.output ≠ n + i := fun e => hn (by simp [slots, e])
      have hno : ∀ j, (hj : j < C.gates.length) → i < j → n + i ∉ C.gates[j].inputs := by
        intro j hj _ hm
        exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj, hm⟩))
      have bad := hmin _ (heval ▸ deleteDeadGate C hC i (Finset.mem_range.1 hi) hout hno)
      change C.gates.length ≤ C.gates.length - 1 at bad
      have hipos : 0 < C.gates.length := lt_of_le_of_lt (Nat.zero_le i) (Finset.mem_range.1 hi)
      omega
    have lowerA := Finset.sum_le_sum marked
    have lowerB := Finset.sum_le_sum unmarked
    have lowerI := Finset.sum_le_sum internal
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerA lowerB lowerI
    have inSum := A.sum_add_sum_compl (fun a : Fin n => cnt a.val)
    rw [Fin.sum_univ_eq_sum_range] at inSum
    have countAll := countBound (slots C) (Finset.range (n + C.gates.length))
    change ∑ i ∈ Finset.range (n + C.gates.length), cnt i ≤ (slots C).length at countAll
    rw [Finset.sum_range_add] at countAll
    have len := gateSlotBound C.gates (fun g hg => (hC g hg).2)
    simp only [slots, List.length_cons] at countAll
    have dA : ∀ a ∈ A, G.degree a = 0 := by
      intro a ha
      exact (G.degree_eq_zero a).2 (fun j h => hnoA a j h ha)
    have dB : ∀ a ∈ Aᶜ, G.degree a = 3 := by
      intro a ha
      rw [← G.ncard_neighborSet]
      exact hdeg a (Finset.mem_compl.1 ha)
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
    have hk : k ≤ Aᶜ.card := htau Aᶜ (fun u v huv => Or.inl (Finset.mem_compl.2 (hnoA u v huv)))
    have hedgeEq : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    change A.card + G.edgeSet.ncard + k ≤ C.gates.length + 1
    omega
  · push Not at hge3
    obtain ⟨v0, hv0A, hv0lt⟩ := hge3
    by_cases h1 : ∃ v ∉ A, (C.gates.filter (reads v.val)).length = 1
    · exact hFan1 n k G A f C hdeg hgirth hnoA hE htau hf hC heval hmin h1
    · have hge2 : ∀ v ∉ A, 2 ≤ (C.gates.filter (reads v.val)).length := by
        intro v hv
        have hp := hread_pos v hv
        have hne1 : (C.gates.filter (reads v.val)).length ≠ 1 := fun e => h1 ⟨v, hv, e⟩
        omega
      have hv02 : (C.gates.filter (reads v0.val)).length = 2 := by
        have := hge2 v0 hv0A
        omega
      by_cases hnonor : ∃ v ∉ A,
          (C.gates.filter (reads v.val)).length = 2 ∧
          ∃ g ∈ C.gates.filter (reads v.val), g.op ≠ GateOp.or
      · exact hFan2NonOr n k G A f C hdeg hgirth hnoA hE htau hf hC heval hmin hge2 hnonor
      · push Not at hnonor
        exact hFan2AllOr n k G A f C hdeg hgirth hnoA hE htau hf hC heval hmin hge2 hnonor ⟨v0, hv0A, hv02⟩
