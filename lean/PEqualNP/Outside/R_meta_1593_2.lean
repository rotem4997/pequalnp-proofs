import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1593_2
    (bipartite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool),
      G.Colorable 2 →
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i j : Fin n, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, HasCircuitSize n f s → ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬G.Adj u v ∧
        ∃ t, t + 8 ≤ s ∧ HasCircuitSize n
          (fun x => f (Function.update (Function.update x u false) v false)) t)
    (nonbipartite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool),
      ¬G.Colorable 2 →
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i j : Fin n, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, HasCircuitSize n f s → ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ G.Adj u v ∧
        ∃ t, t + 7 ≤ s ∧ HasCircuitSize n
          (fun x => f (Function.update (Function.update x u false) v false)) t) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wire (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) :=
    (gs.foldl step (List.ofFn x)).getD i false
  let valid (gs : List Gate) := FanInTwo (⟨gs, 0⟩ : Circuit)
  let binary (meet : Bool) (i j : ℕ) : Gate :=
    ⟨if meet then GateOp.and else GateOp.or, [i, j]⟩
  have length_wires (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have input_read (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
      wire n gs x v.val = x v := by
    dsimp only [wire]
    rw [stable gs _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, v.isLt]
  have missing (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
      wire n gs x i = false := by
    have h : (gs.foldl step (List.ofFn x)).length ≤ i := by simpa only [length_wires, List.length_ofFn] using hi
    simp only [wire, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
  have extend_read (n : ℕ) (gs extra : List Gate) (x : Fin n → Bool) (i : ℕ)
      (hi : i < n + gs.length) : wire n (gs ++ extra) x i = wire n gs x i := by
    simp only [wire, List.foldl_append]
    exact stable extra _ i (by simpa only [length_wires, List.length_ofFn] using hi)
  have push (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (k : Bool) (i j : ℕ) :
      wire n (gs ++ [binary k i j]) x (n + gs.length) =
        (if k then wire n gs x i && wire n gs x j else wire n gs x i || wire n gs x j) := by
    let w := gs.foldl step (List.ofFn x)
    have hw : w.length = n + gs.length := by simp [w, length_wires]
    simp only [wire, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (w ++ [_]).getD (n + gs.length) false = _
    rw [← hw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
    cases k
    · change (w.getD i false || (w.getD j false || false)) = (w.getD i false || w.getD j false)
      simp
    · change (w.getD i false && (w.getD j false && true)) = (w.getD i false && w.getD j false)
      simp
  have join_valid (gs hs : List Gate) (hgs : valid gs) (hhs : valid hs) : valid (gs ++ hs) := by
    intro g hg
    change g ∈ gs ++ hs at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hgs g hg
    · exact hhs g hg
  have one_valid (k : Bool) (i j : ℕ) : valid [binary k i j] := by
    intro g hg
    change g ∈ [binary k i j] at hg
    obtain rfl := List.mem_singleton.mp hg
    cases k <;> simp [binary]
  -- Combining d surviving neighbors takes d - 1 binary OR gates.
  have neighbor_or (n : ℕ) (gs : List Gate) (a : Fin n) (rest : List (Fin n)) :
      ∃ ex : List Gate, ∃ i : ℕ, ex.length = rest.length ∧ valid ex ∧
        ∀ x, wire n (gs ++ ex) x i = (x a || rest.any x) := by
    induction rest with
    | nil =>
      refine ⟨[], a.val, rfl, ?_, ?_⟩
      · intro g hg
        change g ∈ ([] : List Gate) at hg
        cases hg
      · intro x
        simpa using input_read n gs x a
    | cons b rest ih =>
      obtain ⟨ex, i, hlen, hok, hval⟩ := ih
      refine ⟨ex ++ [binary false i b.val], n + (gs ++ ex).length, by simp [hlen],
        join_valid _ _ hok (one_valid false i b.val), ?_⟩
      intro x
      rw [← List.append_assoc, push]
      simp only [Bool.false_eq_true, ite_false, hval, input_read, List.any_cons]
      ac_rfl
  have add_star (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (hc : HasCircuitSize n f s)
      (v a : Fin n) (rest : List (Fin n)) :
      HasCircuitSize n (fun x => f x || (x v && (x a || rest.any x))) (s + rest.length + 2) := by
    obtain ⟨C, hC, hsize, hfun⟩ := hc
    obtain ⟨ex, i, hlen, hex, hi⟩ := neighbor_or n C.gates a rest
    let base := C.gates ++ ex
    let prod := binary true v.val i
    let middle := base ++ [prod]
    let pi := n + base.length
    let oi := if C.output < n + C.gates.length then C.output else n + middle.length
    let finish := binary false oi pi
    let D : Circuit := ⟨middle ++ [finish], n + middle.length⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · exact join_valid _ _ (join_valid _ _ (join_valid _ _ hC hex) (one_valid true v.val i))
        (one_valid false oi pi)
    · change C.gates.length ≤ s at hsize
      change (middle ++ [finish]).length ≤ s + rest.length + 2
      simp only [middle, base, List.length_append, List.length_cons, List.length_nil, hlen]
      omega
    · intro x
      have old : wire n middle x oi = f x := by
        by_cases hv : C.output < n + C.gates.length
        · simp only [oi, ite_eq_left hv, middle, base, List.append_assoc]
          exact (extend_read n C.gates (ex ++ [prod]) x C.output hv).trans (hfun x)
        · simp only [oi, ite_eq_right hv]
          rw [missing n middle x _ (le_refl _)]
          exact (missing n C.gates x C.output (Nat.le_of_not_gt hv)).symm.trans (hfun x)
      change wire n (middle ++ [binary false oi pi]) x (n + middle.length) = _
      rw [push]
      change (wire n middle x oi || wire n (base ++ [binary true v.val i]) x (n + base.length)) = _
      rw [old, push]
      change (f x || (wire n base x v.val && wire n (C.gates ++ ex) x i)) = _
      rw [input_read, hi]
  intro n G A hdegree hgirth hmarked hedge
  let f (x : Fin n → Bool) := @decide ((∃ a ∈ A, x a = true) ∨
    ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)
  have hf (x : Fin n → Bool) : f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by simp [f]
  let single (u : Fin n) (x : Fin n → Bool) := @decide ((∃ a ∈ A, x a = true) ∨
    ∃ i j, (G.deleteEdges (G.incidenceSet u)).Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)
  -- Keep u deleted and restore exactly the surviving edges incident to v.
  have rebuild (u v : Fin n) (hu : u ∉ A) (hv : v ∉ A) (hne : u ≠ v) (t : ℕ)
      (hsmall : HasCircuitSize n (fun x => f (Function.update (Function.update x u false) v false)) t) :
      HasCircuitSize n (single u) (t + (if G.Adj u v then 3 else 4)) := by
    let N := (G.neighborSet v).toFinset.erase u
    have memN (w : Fin n) : w ∈ N ↔ G.Adj v w ∧ w ≠ u := by
      simp [N, and_comm]
    have degree_v : (G.neighborSet v).toFinset.card = 3 :=
      (Set.ncard_eq_toFinset_card' (G.neighborSet v)).symm.trans (hdegree v hv)
    have cardN : N.card = if G.Adj u v then 2 else 3 := by
      by_cases h : G.Adj u v
      · have hmem : u ∈ (G.neighborSet v).toFinset := by simpa using h.symm
        simp only [N, Finset.card_erase_of_mem hmem, degree_v, ite_eq_left h]
      · have hmem : u ∉ (G.neighborSet v).toFinset := by
          simpa using (fun hvu : G.Adj v u => h hvu.symm)
        simp only [N, Finset.erase_eq_of_notMem hmem, degree_v, ite_eq_right h]
    obtain ⟨a, rest, hlist⟩ : ∃ a rest, N.toList = a :: rest := by
      cases h : N.toList with
      | nil =>
        have hl := N.length_toList
        rw [h, List.length_nil, cardN] at hl
        split at hl <;> omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    have hcount := N.length_toList
    rw [hlist, List.length_cons, cardN] at hcount
    have budget : t + rest.length + 2 = t + (if G.Adj u v then 3 else 4) := by
      by_cases h : G.Adj u v <;> simp only [h, ↓reduceIte] at hcount ⊢ <;> omega
    have neighbors (x : Fin n → Bool) :
        (x a || rest.any x) = true ↔ ∃ w, (G.Adj v w ∧ w ≠ u) ∧ x w = true := by
      change ((a :: rest).any x) = true ↔ _
      rw [← hlist, List.any_eq_true]
      simp only [Finset.mem_toList, memN]
    have ident (x : Fin n → Bool) :
        (f (Function.update (Function.update x u false) v false) || (x v && (x a || rest.any x))) =
          single u x := by
      have off (i : Fin n) :
          Function.update (Function.update x u false) v false i = true ↔ i ≠ u ∧ i ≠ v ∧ x i = true := by
        by_cases iv : i = v
        · subst i
          simp
        · by_cases iu : i = u
          · subst i
            simp [Function.update_of_ne iv]
          · simp [iu, iv]
      have adj_del (i j : Fin n) :
          (G.deleteEdges (G.incidenceSet u)).Adj i j ↔ G.Adj i j ∧ i ≠ u ∧ j ≠ u :=
        SimpleGraph.deleteIncidenceSet_adj
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, hf, neighbors, single, decide_eq_true_eq,
        off, adj_del]
      constructor
      · rintro ((⟨a', ha, _, _, xa⟩ | ⟨i, j, hij, hi, hj⟩) | ⟨xv, w, ⟨vw, wu⟩, xw⟩)
        · exact Or.inl ⟨a', ha, xa⟩
        · exact Or.inr ⟨i, j, ⟨hij, hi.1, hj.1⟩, hi.2.2, hj.2.2⟩
        · exact Or.inr ⟨v, w, ⟨vw, hne.symm, wu⟩, xv, xw⟩
      · rintro (⟨i, ia, xi⟩ | ⟨i, j, ⟨ij, iu, ju⟩, xi, xj⟩)
        · exact Or.inl (Or.inl ⟨i, ia, fun eq => hu (eq ▸ ia), fun eq => hv (eq ▸ ia), xi⟩)
        · by_cases iv : i = v
          · subst i
            exact Or.inr ⟨xi, j, ⟨ij, ju⟩, xj⟩
          · by_cases jv : j = v
            · subst j
              exact Or.inr ⟨xj, i, ⟨ij.symm, iu⟩, xi⟩
            · exact Or.inl (Or.inr ⟨i, j, ij, ⟨iu, iv, xi⟩, ⟨ju, jv, xj⟩⟩)
    rw [← budget, ← funext ident]
    exact add_star n _ t hsmall v a rest
  -- A pair selected at the least size supplies one vertex for every larger budget.
  by_cases existsCircuit : ∃ s, HasCircuitSize n f s
  · let m := Nat.find existsCircuit
    have hm : HasCircuitSize n f m := Nat.find_spec existsCircuit
    have save : ∃ u, u ∉ A ∧ ∃ t, t + 4 ≤ m ∧ HasCircuitSize n (single u) t := by
      by_cases hb : G.Colorable 2
      · obtain ⟨u, v, hu, hv, hne, hadj, t, ht, hsmall⟩ :=
          bipartite n G A f hb hdegree hgirth hmarked hedge hf m hm
        exact ⟨u, hu, t + 4, by omega, by simpa [hadj] using rebuild u v hu hv hne t hsmall⟩
      · obtain ⟨u, v, hu, hv, hadj, t, ht, hsmall⟩ :=
          nonbipartite n G A f hb hdegree hgirth hmarked hedge hf m hm
        exact ⟨u, hu, t + 3, by omega, by simpa [hadj] using rebuild u v hu hv hadj.ne t hsmall⟩
    obtain ⟨u, hu, t, ht, hsmall⟩ := save
    exact ⟨u, hu, fun s hs => ⟨t, ht.trans (Nat.find_min' existsCircuit hs), hsmall⟩⟩
  · obtain ⟨i, j, hij⟩ := hedge
    exact ⟨i, hmarked i j hij, fun s hs => (existsCircuit ⟨s, hs⟩).elim⟩
