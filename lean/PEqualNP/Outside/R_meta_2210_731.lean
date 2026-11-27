import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2210_731
    (lower : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 13)
    (shrinkAlias : ∀ (C : Circuit) (v : ℕ) (g : Gate), (v = 0 ∨ v = 2) →
      FanInTwo C → ReadsBack 10 C → C.output ≠ 9 →
      C.gates.filter (fun h => decide (9 ∈ h.inputs)) = [g] → g.op = .or →
      (g.inputs = [9, v] ∨ g.inputs = [v, 9]) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 && x 2]))
    (separate : ∀ C : Circuit,
      let readers (v : ℕ) := C.gates.filter (fun g => decide (v ∈ g.inputs))
      FanInTwo C → ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = .not → g.inputs.length = 1) ∧
        (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      C.size = 14 → (∃ g, g.op = .or ∧ readers 9 = [g]) →
      (∀ v ∈ ([0, 2] : List ℕ), (readers v).length = 1) →
      (∀ v ∈ ([4, 6, 7] : List ℕ), (readers v).length ≤ 2) →
      (∀ v : Fin 9, (readers v.val).length ≤ 3) →
      (∀ g ∈ C.gates, ¬ (0 ∈ g.inputs ∧ 2 ∈ g.inputs) ∧
        (9 ∈ g.inputs → 0 ∉ g.inputs ∧ 2 ∉ g.inputs)) →
      ¬ ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → (∀ x4 ∈ x1.gates, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (1 : ℕ)) ∧ (x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length = (2 : ℕ) ∧ x4.inputs.Nodup)) → x1.size = (14 : ℕ) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x7.inputs)) x1.gates = [x6]) → (∀ x7 ∈ [(0 : ℕ), (2 : ℕ)], (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x7 ∈ x9.inputs)) x1.gates).length = (1 : ℕ)) → (∀ x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x8 ∈ x10.inputs)) x1.gates).length ≤ (2 : ℕ)) → (∀ (x9 : Fin (9 : ℕ)), (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x9 ∈ x10.inputs)) x1.gates).length ≤ (3 : ℕ)) → ¬∀ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ))]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  classical
  let advance (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wireCount (gs : List Gate) (w : List Bool) :
      (gs.foldl advance w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [advance]
      omega

  have keepInput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl advance w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (advance w g) (by simp [advance]; omega)]
      simp only [advance, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have maskAgreement (gs : List Gate) (x y : List Bool) (bad : Finset Nat)
      (len : x.length = y.length)
      (inputs : ∀ i ∉ bad, x.getD i false = y.getD i false)
      (mask : ∀ g ∈ gs, (∃ i ∈ g.inputs, i ∈ bad) →
        (∀ i ∈ g.inputs, i < x.length) ∧
        g.op.eval (g.inputs.map fun i => x.getD i false) =
          g.op.eval (g.inputs.map fun i => y.getD i false)) :
      ∀ i ∉ bad, (gs.foldl advance x).getD i false = (gs.foldl advance y).getD i false := by
    induction gs using List.reverseRecOn with
    | nil => exact inputs
    | append_singleton gs g ih =>
      have eqPrev : ∀ i ∉ bad, (gs.foldl advance x).getD i false =
          (gs.foldl advance y).getD i false :=
        ih (fun h hh => mask h (List.mem_append_left _ hh))
      let w := gs.foldl advance x
      let z := gs.foldl advance y
      have lenNext : w.length = z.length := by simp [w, z, wireCount, len]
      have interp : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => z.getD i false) := by
        by_cases h : ∃ i ∈ g.inputs, i ∈ bad
        · obtain ⟨small, same⟩ := mask g (by simp) h
          have hx : g.inputs.map (fun i => w.getD i false) =
              g.inputs.map (fun i => x.getD i false) := by
            apply List.map_congr_left
            intro i hi
            exact keepInput gs x i (small i hi)
          have hy : g.inputs.map (fun i => z.getD i false) =
              g.inputs.map (fun i => y.getD i false) := by
            apply List.map_congr_left
            intro i hi
            exact keepInput gs y i (len ▸ small i hi)
          rwa [hx, hy]
        · congr 1
          apply List.map_congr_left
          intro i hi
          exact eqPrev i (fun hb => h ⟨i, hi, hb⟩)
      intro i hi
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (advance w g).getD i false = (advance z g).getD i false
      by_cases hw : i < w.length
      · have hz : i < z.length := lenNext ▸ hw
        simp only [advance, List.getD_eq_getElem?_getD, List.getElem?_append_left hw,
          List.getElem?_append_left hz]
        exact eqPrev i hi
      · have hz : z.length ≤ i := lenNext ▸ Nat.le_of_not_lt hw
        simp only [List.getD_eq_getElem?_getD] at interp
        simp only [advance, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hw), List.getElem?_append_right hz,
          lenNext, interp]

  let graph (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let rows (i : Nat) : Fin 9 → Bool := fun j => i.testBit j.val

  let fromInput (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 && x 2]

  have noSharedReader (C : Circuit)
      (h : ∀ x, C.eval (fromInput x) = graph x)
      (pipe : ∀ g ∈ C.gates, 0 ∈ g.inputs ∨ 2 ∈ g.inputs →
        g.op.eval (g.inputs.map (fun i => (fromInput (rows 17)).getD i false)) =
          g.op.eval (g.inputs.map (fun i => (fromInput (rows 20)).getD i false)) ∧
        ∀ i ∈ g.inputs, i < 10) :
      False := by
    have noZero : C.output ≠ 0 := by
      intro eq
      have he := h (rows 1)
      change (C.gates.foldl advance (fromInput (rows 1))).getD C.output false = graph (rows 1) at he
      rw [eq, keepInput _ _ _ (by decide)] at he
      have : true = false := he
      cases this
    have noTwo : C.output ≠ 2 := by
      intro eq
      have he := h (rows 4)
      change (C.gates.foldl advance (fromInput (rows 4))).getD C.output false = graph (rows 4) at he
      rw [eq, keepInput _ _ _ (by decide)] at he
      have : true = false := he
      cases this
    have agree : ∀ i ∉ ({0, 2} : Finset ℕ),
        (fromInput (rows 17)).getD i false = (fromInput (rows 20)).getD i false := by
      intro i hi
      by_cases hilt : i < 10
      · let j : Fin 10 := ⟨i, hilt⟩
        have ok : ∀ j : Fin 10, j.val ∉ ({0, 2} : Finset ℕ) →
            (fromInput (rows 17)).getD j.val false = (fromInput (rows 20)).getD j.val false := by decide
        exact ok j hi
      · have h17 : (fromInput (rows 17)).length ≤ i := by
          simpa [fromInput] using Nat.le_of_not_lt hilt
        have h20 : (fromInput (rows 20)).length ≤ i := by
          simpa [fromInput] using Nat.le_of_not_lt hilt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h17, List.getElem?_eq_none h20]
    have ev := maskAgreement C.gates (fromInput (rows 17)) (fromInput (rows 20)) {0, 2}
      (by decide) agree (by
        intro g hg hit
        obtain ⟨j, hj, he⟩ := hit
        have eq : j = 0 ∨ j = 2 := by simpa using he
        have hit : 0 ∈ g.inputs ∨ 2 ∈ g.inputs := by
          rcases eq with rfl | rfl
          · exact Or.inl hj
          · exact Or.inr hj
        obtain ⟨heq, hsmall⟩ := pipe g hg hit
        exact ⟨fun i hi => hsmall i hi, heq⟩)
    have evout := ev C.output (by simp [noZero, noTwo])
    change C.eval (fromInput (rows 17)) = C.eval (fromInput (rows 20)) at evout
    rw [h, h] at evout
    have : true = false := evout
    cases this


  have distinctReaders (C : Circuit) (fan : FanInTwo C)
      (clean : ∀ g ∈ C.gates, (g.op = .not → g.inputs.length = 1) ∧
        (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup))
      (unique : ∀ v ∈ ([0, 2] : List ℕ),
        (C.gates.filter fun g => decide (v ∈ g.inputs)).length = 1)
      (h : ∀ x, C.eval (fromInput x) = graph x) :
      ∀ g ∈ C.gates, ¬ (0 ∈ g.inputs ∧ 2 ∈ g.inputs) := by
    rintro g hg ⟨h0, h2⟩
    have get (v : ℕ) (hv : v ∈ ([0, 2] : List ℕ)) (hvg : v ∈ g.inputs) :
        C.gates.filter (fun d => decide (v ∈ d.inputs)) = [g] := by
      obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp (unique v hv)
      have hm : g ∈ C.gates.filter (fun d => decide (v ∈ d.inputs)) :=
        List.mem_filter.mpr ⟨hg, decide_eq_true_eq.mpr hvg⟩
      rw [hd, List.mem_singleton] at hm
      rw [hd, hm]
    have only0 := get 0 (by decide) h0
    have only2 := get 2 (by decide) h2
    have notOp : g.op ≠ .not := by
      intro hn
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp ((clean g hg).1 hn)
      rw [ha, List.mem_singleton] at h0 h2
      omega
    have pins : g.inputs = [0, 2] ∨ g.inputs = [2, 0] := by
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp ((clean g hg).2 notOp).1
      rw [hab] at h0 h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h2
      rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
      · omega
      · subst a; subst b; exact Or.inl hab
      · subst a; subst b; exact Or.inr hab
      · omega
    have op : g.op = .and ∨ g.op = .or := by
      have ho := (fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
      exact ho.elim Or.inl (fun e => e.elim Or.inr (fun e => (notOp e).elim))
    apply noSharedReader C h
    intro d hd reads
    have eg : d = g := by
      rcases reads with hzero | htwo
      · have hm : d ∈ C.gates.filter (fun j => decide (0 ∈ j.inputs)) :=
          List.mem_filter.mpr ⟨hd, decide_eq_true_eq.mpr hzero⟩
        simpa only [only0, List.mem_singleton] using hm
      · have hm : d ∈ C.gates.filter (fun j => decide (2 ∈ j.inputs)) :=
          List.mem_filter.mpr ⟨hd, decide_eq_true_eq.mpr htwo⟩
        simpa only [only2, List.mem_singleton] using hm
    subst d
    constructor
    · rcases pins with hp | hp <;> rcases op with ho | ho <;> rw [hp, ho] <;> decide
    · rcases pins with hp | hp <;> simp [hp]

  intro C fan back clean size h9 once degreeTwo three computes
  have noNine : C.output ≠ 9 := by
    intro eq
    have he := computes (rows 5)
    change (C.gates.foldl advance (fromInput (rows 5))).getD C.output false = graph (rows 5) at he
    rw [eq, keepInput _ _ _ (by decide)] at he
    have : true = false := he
    cases this
  have noShared := distinctReaders C fan clean once computes
  obtain ⟨g9, hop, hreads⟩ := h9
  have apart (g : Gate) (hg : g ∈ C.gates) (hgnine : 9 ∈ g.inputs)
      (v : ℕ) (hv : v = 0 ∨ v = 2) : v ∉ g.inputs := by
    intro hgv
    have hmem : g ∈ C.gates.filter (fun j => decide (9 ∈ j.inputs)) :=
      List.mem_filter.mpr ⟨hg, decide_eq_true_eq.mpr hgnine⟩
    rw [hreads, List.mem_singleton] at hmem
    subst g
    have noNot : g9.op ≠ .not := by
      intro impossible
      have clash : GateOp.or = GateOp.not := hop.symm.trans impossible
      cases clash
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp ((clean g9 hg).2 noNot).1
    rw [hab] at hgnine hgv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgnine hgv
    have nv : v ≠ 9 := by rcases hv with rfl | rfl <;> decide
    have hpins : g9.inputs = [9, v] ∨ g9.inputs = [v, 9] := by
      rcases hgnine with hgnine | hgnine <;> rcases hgv with hgv | hgv
      · omega
      · subst a; subst b; exact Or.inl hab
      · subst a; subst b; exact Or.inr hab
      · omega
    obtain ⟨D, hDf, hDs, hDe⟩ := shrinkAlias C v g9 hv fan back noNine hreads hop hpins
    apply lower
    exact ⟨D, hDf, by omega, fun x => (hDe x).trans (computes x)⟩
  apply separate C fan back clean size ⟨g9, hop, hreads⟩ once degreeTwo three _ computes
  intro g hg
  exact ⟨noShared g hg, fun hit => ⟨apart g hg hit 0 (Or.inl rfl),
    apart g hg hit 2 (Or.inr rfl)⟩⟩
