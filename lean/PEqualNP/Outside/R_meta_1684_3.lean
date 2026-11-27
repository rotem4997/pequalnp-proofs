import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1684_3
    (h1 : have D : Finset (Fin 13) := {0, 1, 3, 9}; ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧ (∀ p w : Fin 13, (∃ dd ∈ D, p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w2 + dd)) ∧ (∃ dd ∈ D, v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ D, p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w4 + dd)) → (∃ dd ∈ D, v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = ww + dd))))) = false)))
    (h2 : have D : Finset (Fin 13) := {0, 1, 3, 9}; have Q : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C => PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ D, p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w2 + dd)) ∧ (∃ dd ∈ D, v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ D, p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w4 + dd)) → (∃ dd ∈ D, v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = ww + dd))))) = false); ∀ C : PEqualNP.CircuitLowerBounds.Circuit, Q C → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, Q C2 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C2 1 ∨ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C2 1)) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  have snoc_lt : ∀ (α : Type) (L : List α) (a d : α) (i : ℕ), i < L.length → (L ++ [a]).getD i d = L.getD i d := by
    intro α L a d i h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have snoc_eq : ∀ (α : Type) (L : List α) (a d : α), (L ++ [a]).getD L.length d = a := by
    intro α L a d
    simp [List.getD_eq_getElem?_getD]
  have snoc_gt : ∀ (α : Type) (L : List α) (a d : α) (i : ℕ), L.length < i → (L ++ [a]).getD i d = d := by
    intro α L a d i h
    rw [List.getD_eq_default]
    simp
    omega
  have len : ∀ (α : Type) (F : PEqualNP.CircuitLowerBounds.Gate → List α → α) (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List α), (gs.foldl (fun L g => L ++ [F g L]) init).length = init.length + gs.length := by
    intro α F gs
    induction gs with
    | nil => intro init; simp
    | cons g gs ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp
      omega
  have gen : ∀ (α : Type) (d : α) (F : PEqualNP.CircuitLowerBounds.Gate → List α → α) (ρ : ℕ → ℕ) (n : ℕ), (∀ i, i < n → ρ i < n) → (∀ i, n ≤ i → ρ i = i) → (∀ (g : PEqualNP.CircuitLowerBounds.Gate) (L L' : List α), (∀ j, L'.getD (ρ j) d = L.getD j d) → F ⟨g.op, List.map ρ g.inputs⟩ L' = F g L) → ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init init' : List α), init.length = n → init'.length = n → (∀ j, init'.getD (ρ j) d = init.getD j d) → ∀ j, ((List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) gs).foldl (fun L g => L ++ [F g L]) init').getD (ρ j) d = (gs.foldl (fun L g => L ++ [F g L]) init).getD j d := by
    intro α d F ρ n hρlt hρge hF gs init init' hlen hlen' h0
    induction gs using List.reverseRecOn with
    | nil => intro j; simpa using h0 j
    | append_singleton gs g ih =>
      intro j
      have e1 : (gs.foldl (fun L g => L ++ [F g L]) init).length = n + gs.length := by
        rw [len, hlen]
      have e2 : ((List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) gs).foldl (fun L g => L ++ [F g L]) init').length = n + gs.length := by
        rw [len, hlen', List.length_map]
      rw [List.map_append, List.foldl_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      generalize (gs.foldl (fun L g => L ++ [F g L]) init) = L at ih e1 ⊢
      generalize ((List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) gs).foldl (fun L g => L ++ [F g L]) init') = L' at ih e2 ⊢
      rcases Nat.lt_trichotomy j (n + gs.length) with hj | hj | hj
      · have hρj : ρ j < n + gs.length := by
          by_cases hjn : j < n
          · have := hρlt j hjn
            omega
          · rw [hρge j (by omega)]
            exact hj
        rw [snoc_lt α L' _ d (ρ j) (by omega), snoc_lt α L _ d j (by omega)]
        exact ih j
      · have hρj : ρ j = j := hρge j (by omega)
        rw [hρj, hj]
        have a1 := snoc_eq α L' (F ⟨g.op, List.map ρ g.inputs⟩ L') d
        have a2 := snoc_eq α L (F g L) d
        rw [e2] at a1
        rw [e1] at a2
        rw [a1, a2]
        exact hF g L L' ih
      · rw [hρge j (by omega), snoc_gt α L' _ d j (by omega), snoc_gt α L _ d j (by omega)]
  have rel_val : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), (∀ i, i < 26 → ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) → ∀ (x y : Fin (13 + 13) → Bool), (∀ j : Fin (13 + 13), ∀ h : ρ j.val < 13 + 13, y j = x ⟨ρ j.val, h⟩) → PEqualNP.MetaComplexity.circuitFun (13 + 13) (⟨List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) C.gates, ρ C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = PEqualNP.MetaComplexity.circuitFun (13 + 13) C y := by
    intro C ρ hρlt hρge x y hxy
    have h0 : ∀ j, (List.ofFn x).getD (ρ j) false = (List.ofFn y).getD j false := by
      intro j
      by_cases hj : j < 13 + 13
      · have hr : ρ j < 13 + 13 := hρlt j hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr, hj, dite_true, Option.getD_some]
        exact (hxy ⟨j, hj⟩ hr).symm
      · rw [hρge j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact gen Bool false (fun g L => g.op.eval (g.inputs.map fun i => L.getD i false)) ρ 26 hρlt hρge
      (fun g L L' h => by
        show g.op.eval (List.map (fun i => L'.getD i false) (List.map ρ g.inputs)) = g.op.eval (List.map (fun i => L.getD i false) g.inputs)
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun j _ => h j))
      C.gates (List.ofFn y) (List.ofFn x) (by simp) (by simp) h0 C.output
  have rel_deg : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ρ : ℕ → ℕ), (∀ i, i < 26 → ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) → (∀ j, j < 26 → (ρ j ∈ Finset.Ico 13 26 ↔ j ∈ Finset.range 13)) → PEqualNP.CircuitLowerBounds.Circuit.lineDeg (⟨List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) C.gates, ρ C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) 26 (Finset.Ico 13 26) = PEqualNP.CircuitLowerBounds.Circuit.lineDeg C 26 (Finset.range 13) := by
    intro C ρ hρlt hρge hmark
    have h0 : ∀ j, ((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0).getD (ρ j) 0 = ((List.range 26).map fun i => if i ∈ Finset.range 13 then 1 else 0).getD j 0 := by
      intro j
      by_cases hj : j < 26
      · have hr := hρlt j hj
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hr, List.getElem?_range hj]
        simp only [Option.map_some, Option.getD_some]
        by_cases hm : j ∈ Finset.range 13
        · simp only [hm, (hmark j hj).mpr hm, ite_true]
        · have hm2 : ¬ (ρ j ∈ Finset.Ico 13 26) := fun h => hm ((hmark j hj).mp h)
          simp only [hm, hm2, ite_false]
      · rw [hρge j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact gen ℕ 0 (fun g L => g.lineDegree L) ρ 26 hρlt hρge
      (fun g L L' h => by
        have hl : List.map (fun i => L'.getD i 0) (List.map ρ g.inputs) = List.map (fun i => L.getD i 0) g.inputs := by
          rw [List.map_map]
          exact List.map_congr_left (fun j _ => h j)
        delta PEqualNP.CircuitLowerBounds.Gate.lineDegree
        dsimp only
        rw [hl])
      C.gates _ _ (by simp) (by simp) h0 C.output
  have flip : ∀ a b dd : Fin 13, a = b + dd ↔ -b = -a + dd := by
    intro a b dd
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      have hc := congrArg (fun t => t + a + b) h
      have e1 : -b + a + b = a := by abel
      have e2 : -a + dd + a + b = b + dd := by abel
      simp only [e1, e2] at hc
      exact hc
  have dual : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) → (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) → PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.range 13) C 1 → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C2 ∧ C2.size = C.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C2 1 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C2 (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C2 (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
    intro C hm hT hF hd
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ∀ j, ρ j = if j < 13 then 13 + (13 - j) % 13 else if j < 26 then (26 - j) % 13 else j := ⟨_, fun _ => rfl⟩
    have hρlt : ∀ i, i < 26 → ρ i < 26 := by
      intro i hi
      rw [hρ]
      split_ifs
      all_goals omega
    have hρge : ∀ i, 26 ≤ i → ρ i = i := by
      intro i hi
      rw [hρ]
      split_ifs
      all_goals omega
    have hmark : ∀ j, j < 26 → (ρ j ∈ Finset.Ico 13 26 ↔ j ∈ Finset.range 13) := by
      intro j hj
      rw [hρ]
      simp only [Finset.mem_Ico, Finset.mem_range]
      split_ifs
      all_goals omega
    refine ⟨(⟨List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) C.gates, ρ C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, ?_, ?_, ?_, ?_⟩
    · intro g2 hg2
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg2
      obtain ⟨k1, k2⟩ := hm g hg
      exact ⟨k1, by simpa using k2⟩
    · exact List.length_map _
    · show PEqualNP.CircuitLowerBounds.Circuit.lineDeg (⟨List.map (fun g : PEqualNP.CircuitLowerBounds.Gate => (⟨g.op, List.map ρ g.inputs⟩ : PEqualNP.CircuitLowerBounds.Gate)) C.gates, ρ C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) 26 (Finset.Ico 13 26) ≤ 1
      rw [rel_deg C ρ hρlt hρge hmark]
      exact hd
    · intro p w hpw
      refine (rel_val C ρ hρlt hρge _ (fun k => decide (k = Fin.castAdd 13 (-w) ∨ k = Fin.natAdd 13 (-p))) ?_).trans (hT (-w) (-p) ?_)
      · intro j hlt
        apply decide_eq_decide.mpr
        simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg']
        rw [hρ]
        have hj := j.isLt
        have hp := p.isLt
        have hw := w.isLt
        split_ifs
        all_goals omega
      · obtain ⟨dd, hdd, rfl⟩ := hpw
        exact ⟨dd, hdd, by abel⟩
    · intro P hclosed hdeg
      have memP : ∀ q : Fin 13, q ∈ (Finset.univ.filter (fun q : Fin 13 => ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd))) ↔ ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd) := by
        intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have key1 : ∀ w : Fin 13, (∀ q ∈ (Finset.univ.filter (fun q : Fin 13 => ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd))), ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = w + dd)) ↔ -w ∈ P := by
        intro w
        constructor
        · intro hw
          by_contra hnot
          obtain ⟨w2, hw2, dd, hdd, hvw⟩ := hclosed (-w) hnot
          refine hw (-w2) ((memP (-w2)).mpr ?_) ⟨dd, hdd, ?_⟩
          · rw [neg_neg]
            exact hw2
          · have h3 := (flip (-w) w2 dd).mp hvw
            rw [neg_neg] at h3
            exact h3
        · rintro hw q hq ⟨dd, hdd, hqe⟩
          exact (memP q).mp hq (-w) hw ⟨dd, hdd, (flip q w dd).mp hqe⟩
      refine (rel_val C ρ hρlt hρge _ (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ (Finset.univ.filter (fun q : Fin 13 => ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd))), kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ (Finset.univ.filter (fun q : Fin 13 => ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd))), ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) ?_).trans (hF (Finset.univ.filter (fun q : Fin 13 => ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = -q + dd))) ?_ ?_)
      · intro j
        induction j using Fin.addCases with
        | left q =>
          intro hlt
          have hA : (⟨ρ (Fin.castAdd 13 q).val, hlt⟩ : Fin (13 + 13)) = Fin.natAdd 13 (-q) := by
            apply Fin.ext
            simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg']
            rw [hρ]
            have hq := q.isLt
            split_ifs
            omega
          apply decide_eq_decide.mpr
          rw [hA]
          constructor
          · rintro (⟨pp, hpp, he⟩ | ⟨ww, he, _⟩)
            · have hqp : q = pp := by
                have h5 := congrArg Fin.val he
                simp only [Fin.val_castAdd] at h5
                exact Fin.ext h5
              subst hqp
              exact Or.inr ⟨-q, rfl, (memP q).mp hpp⟩
            · exfalso
              have h5 := congrArg Fin.val he
              simp only [Fin.val_castAdd, Fin.val_natAdd] at h5
              have hq := q.isLt
              omega
          · rintro (⟨pp, _, he⟩ | ⟨ww, he, hmiss⟩)
            · exfalso
              have h5 := congrArg Fin.val he
              simp only [Fin.val_castAdd, Fin.val_natAdd] at h5
              have hq := pp.isLt
              omega
            · have hwq : ww = -q := by
                have h5 := congrArg Fin.val he
                simp only [Fin.val_natAdd] at h5
                exact (Fin.ext (by omega)).symm
              subst hwq
              exact Or.inl ⟨q, (memP q).mpr hmiss, rfl⟩
        | right w =>
          intro hlt
          have hB : (⟨ρ (Fin.natAdd 13 w).val, hlt⟩ : Fin (13 + 13)) = Fin.castAdd 13 (-w) := by
            apply Fin.ext
            simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg']
            rw [hρ]
            have hq := w.isLt
            split_ifs
            all_goals omega
          apply decide_eq_decide.mpr
          rw [hB]
          constructor
          · rintro (⟨pp, _, he⟩ | ⟨ww, he, hmiss⟩)
            · exfalso
              have h5 := congrArg Fin.val he
              simp only [Fin.val_castAdd, Fin.val_natAdd] at h5
              have hq := pp.isLt
              omega
            · have hww : ww = w := by
                have h5 := congrArg Fin.val he
                simp only [Fin.val_natAdd] at h5
                exact (Fin.ext (by omega)).symm
              subst hww
              exact Or.inl ⟨-ww, (key1 ww).mp hmiss, rfl⟩
          · rintro (⟨pp, hpp, he⟩ | ⟨ww, he, _⟩)
            · have hpw : pp = -w := by
                have h5 := congrArg Fin.val he
                simp only [Fin.val_castAdd] at h5
                exact (Fin.ext h5).symm
              subst hpw
              exact Or.inr ⟨w, rfl, (key1 w).mpr hpp⟩
            · exfalso
              have h5 := congrArg Fin.val he
              simp only [Fin.val_castAdd, Fin.val_natAdd] at h5
              have hq := (-w).isLt
              omega
      · intro v hv
        have hex : ∃ q ∈ P, ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = -v + dd := by
          by_contra hno
          refine hv ((memP v).mpr ?_)
          intro pp hpp hdd
          exact hno ⟨pp, hpp, hdd⟩
        obtain ⟨q, hq, dd, hdd, hqe⟩ := hex
        refine ⟨-q, (key1 (-q)).mpr (by rw [neg_neg]; exact hq), dd, hdd, ?_⟩
        have h3 := (flip q (-v) dd).mp hqe
        rw [neg_neg] at h3
        exact h3
      · rcases hdeg with ⟨w3, hw3⟩ | ⟨v4, hv4⟩
        · refine Or.inr ⟨-w3, fun w4 hw4 => ?_⟩
          obtain ⟨dd, hdd, he⟩ := hw3 (-w4) ((key1 w4).mp hw4)
          have h3 := (flip (-w4) w3 dd).mp he
          rw [neg_neg] at h3
          exact ⟨dd, hdd, h3⟩
        · refine Or.inl ⟨-v4, fun p3 hp3 => ?_⟩
          obtain ⟨dd, hdd, he⟩ := hv4 (-p3) ((memP p3).mp hp3)
          have h3 := (flip v4 (-p3) dd).mp he
          rw [neg_neg] at h3
          exact ⟨dd, hdd, h3⟩
  rintro ⟨C, hm, hs, hT, hF⟩
  obtain ⟨C2, ⟨hm2, hs2, hT2, hF2⟩, hl | hd⟩ := h2 C ⟨hm, hs, hT, hF⟩
  · exact h1 ⟨C2, hm2, hs2, hl, hT2, hF2⟩
  · obtain ⟨C3, hm3, hsz, hl3, hT3, hF3⟩ := dual C2 hm2 hT2 hF2 hd
    exact h1 ⟨C3, hm3, by omega, hl3, hT3, hF3⟩
