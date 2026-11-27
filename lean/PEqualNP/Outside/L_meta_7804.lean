import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace PEqualNP.Outside.L_meta_7804

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

private def inputs (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

private lemma inputs_length (g : Gate) : (inputs g).length ≤ 2 := by
  unfold inputs
  refine (List.length_take_le _ _).trans ?_
  cases g.op.eval [false] <;> decide

private def Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma eval_inputs {g : Gate} (hg : Legal g) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((inputs g).map f) := by
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with h | h | h
  · change g.op = GateOp.and at h
    have he : inputs g = g.inputs := by
      unfold inputs
      rw [h]
      exact List.take_of_length_le hlen
    rw [he]
  · change g.op = GateOp.or at h
    have he : inputs g = g.inputs := by
      unfold inputs
      rw [h]
      exact List.take_of_length_le hlen
    rw [he]
  · change g.op = GateOp.not at h
    unfold inputs
    rw [h]
    cases g.inputs <;> rfl

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [value g ws]) w

private lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [value g w])).length = _
    rw [ih]
    simp
    omega

private lemma getD_left (a b : List Bool) {i : ℕ} (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_right (a b : List Bool) {i : ℕ} (hi : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma run_prefix (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [value g w])).getD i false = _
    rw [ih _ (by simpa using Nat.lt_succ_of_lt hi), getD_left _ _ hi]

private def shift (k i : ℕ) : ℕ := if i < k then i else i - 1

private def renumber (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift k)⟩

private lemma legal_renumber (k : ℕ) {g : Gate} (hg : Legal g) :
    Legal (renumber k g) := by
  simpa [Legal, renumber] using hg

private lemma getD_skip (a b : List Bool) (bit : Bool) {i : ℕ} (hi : i ≠ a.length) :
    (a ++ b).getD (shift a.length i) false = (a ++ bit :: b).getD i false := by
  by_cases h : i < a.length
  · simp only [shift, h, ite_true, getD_left _ _ h]
  · have hlt : a.length < i := by omega
    have hpred : a.length ≤ i - 1 := by omega
    have hindex : i - a.length = (i - 1 - a.length) + 1 := by omega
    simp only [shift, h, ite_false]
    rw [getD_right _ _ hpred, getD_right _ _ (Nat.le_of_lt hlt), hindex]
    rfl

private lemma value_renumber (a b : List Bool) (bit : Bool) {g : Gate}
    (hg : Legal g) (hskip : a.length ∉ inputs g) :
    value (renumber a.length g) (a ++ b) = value g (a ++ bit :: b) := by
  unfold value
  change g.op.eval ((g.inputs.map (shift a.length)).map _) = _
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [eval_inputs hg (fun i => (a ++ b).getD (shift a.length i) false),
    eval_inputs hg (fun i => (a ++ bit :: b).getD i false)]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply getD_skip
  intro he
  exact hskip (he ▸ hi)

-- The two evaluations agree after deleting the selected wire and shifting later indices.
private lemma run_skip (a : List Bool) (bit : Bool) (gs : List Gate) (b : List Bool)
    (hlegal : ∀ g ∈ gs, Legal g) (hskip : ∀ g ∈ gs, a.length ∉ inputs g)
    {i : ℕ} (hi : i ≠ a.length) :
    (run (gs.map (renumber a.length)) (a ++ b)).getD (shift a.length i) false =
      (run gs (a ++ bit :: b)).getD i false := by
  induction gs generalizing b with
  | nil => exact getD_skip a b bit hi
  | cons g gs ih =>
    have he := value_renumber a b bit (hlegal g (by simp)) (hskip g (by simp))
    change (run (gs.map (renumber a.length))
      ((a ++ b) ++ [value (renumber a.length g) (a ++ b)])).getD _ _ =
      (run gs ((a ++ bit :: b) ++ [value g (a ++ bit :: b)])).getD _ _
    rw [he]
    simpa only [List.append_assoc, List.cons_append] using
      ih (b ++ [value g (a ++ bit :: b)])
        (fun h hh => hlegal h (List.mem_cons_of_mem _ hh))
        (fun h hh => hskip h (List.mem_cons_of_mem _ hh))

private lemma gate_read {n : ℕ} {C : Circuit} (hmin : IsMinimalCircuit n C)
    {j : ℕ} (hj : j < C.size) (hout : n + j ≠ C.output) :
    ∃ g ∈ C.gates, n + j ∈ inputs g := by
  by_contra! hskip
  let p := C.gates.take j
  let g := C.gates[j]'hj
  let s := C.gates.drop (j + 1)
  have hp : p.length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hgs : C.gates = p ++ g :: s := by
    change C.gates = C.gates.take j ++ C.gates[j]'hj :: C.gates.drop (j + 1)
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let D : Circuit := ⟨p ++ s.map (renumber (n + j)), shift (n + j) C.output⟩
  have hs : ∀ h ∈ s, h ∈ C.gates := fun h hh => by simp [hgs, hh]
  have hf : FanInTwo D := by
    intro h hh
    change h ∈ p ++ s.map (renumber (n + j)) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hmin.1 h (by simp [hgs, hh])
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
      exact legal_renumber _ (hmin.1 q (hs _ hq))
  have he : circuitFun n D = circuitFun n C := by
    funext x
    let a := run p (List.ofFn x)
    have ha : a.length = n + j := by simp [a, run_length, hp]
    change (run (p ++ s.map (renumber (n + j))) (List.ofFn x)).getD _ _ =
      (run C.gates (List.ofFn x)).getD _ _
    simp only [hgs, run, List.foldl_append, List.foldl_cons]
    change (run (s.map (renumber (n + j))) a).getD (shift (n + j) C.output) false =
      (run s (a ++ [value g a])).getD C.output false
    rw [← ha]
    simpa using run_skip a (value g a) s []
      (fun q hq => hmin.1 q (hs _ hq))
      (fun q hq => ha ▸ hskip q (hs _ hq))
      (fun hh => hout (ha.symm.trans hh.symm))
  have hsize := hmin.2 D hf he
  simp [D, Circuit.size, hgs] at hsize

private def reads (gs : List Gate) (i : ℕ) : ℕ :=
  (gs.filter fun g => (inputs g).contains i).length

private lemma reads_pos {gs : List Gate} {i : ℕ} :
    0 < reads gs i ↔ ∃ g ∈ gs, i ∈ inputs g := by
  simp only [reads, List.length_pos_iff_exists_mem, List.mem_filter, List.contains_iff_mem]

private lemma run_congr (gs : List Gate) (a b : List Bool) (i : ℕ)
    (hlen : a.length = b.length) (he : ∀ j ≠ i, a.getD j false = b.getD j false)
    (hlegal : ∀ g ∈ gs, Legal g) (hskip : ∀ g ∈ gs, i ∉ inputs g) :
    ∀ j ≠ i, (run gs a).getD j false = (run gs b).getD j false := by
  induction gs generalizing a b with
  | nil => exact he
  | cons g gs ih =>
    have hv : value g a = value g b := by
      unfold value
      rw [eval_inputs (hlegal g (by simp)), eval_inputs (hlegal g (by simp))]
      congr 1
      exact List.map_congr_left (fun j hj => he j (fun h => hskip g (by simp) (h ▸ hj)))
    change ∀ j ≠ i, (run gs (a ++ [value g a])).getD j false =
      (run gs (b ++ [value g b])).getD j false
    apply ih _ _ (by simp [hlen]) ?_
      (fun h hh => hlegal h (List.mem_cons_of_mem _ hh))
      (fun h hh => hskip h (List.mem_cons_of_mem _ hh))
    intro j hj
    by_cases h : j < a.length
    · rw [getD_left _ _ h, getD_left _ _ (hlen ▸ h), he j hj]
    · have ha := Nat.le_of_not_lt h
      rw [getD_right _ _ ha, getD_right _ _ (hlen ▸ ha), hv, hlen]


-- Each gate contributes at most the number of effective input slots it has.
private lemma sum_reads (gs : List Gate) (S : Finset ℕ) :
    (∑ i ∈ S, reads gs i) ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [reads]
  | cons g gs ih =>
    have hcons (i : ℕ) : reads (g :: gs) i =
        (if i ∈ inputs g then 1 else 0) + reads gs i := by
      by_cases hi : i ∈ inputs g <;> simp [reads, hi, Nat.add_comm]
    have hrow : (∑ i ∈ S, if i ∈ inputs g then 1 else 0) ≤ 2 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one]
      calc
        (S.filter fun i => i ∈ inputs g).card ≤ (inputs g).toFinset.card := by
          apply Finset.card_le_card
          intro i hi
          exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
        _ ≤ (inputs g).length := List.toFinset_card_le _
        _ ≤ 2 := inputs_length g
    simp only [hcons, Finset.sum_add_distrib, List.length_cons]
    omega

private lemma input_bound {n : ℕ} {C : Circuit} (hmin : IsMinimalCircuit n C) :
    (∑ v : Fin n, reads C.gates v.val) ≤ C.size + 1 := by
  have hall := sum_reads C.gates (Finset.range (n + C.size))
  change (∑ i ∈ Finset.range (n + C.size), reads C.gates i) ≤ 2 * C.size at hall
  rw [Finset.sum_range_add, ← Fin.sum_univ_eq_sum_range] at hall
  let R := (Finset.range C.size).erase (C.output - n)
  have hcard : C.size ≤ R.card + 1 := by
    by_cases h : C.output - n ∈ Finset.range C.size
    · simpa [R] using (Finset.card_erase_add_one h).ge
    · simp [R, Finset.erase_eq_of_notMem h]
  have hR : R.card ≤ ∑ j ∈ Finset.range C.size, reads C.gates (n + j) := by
    calc
      R.card = ∑ _j ∈ R, 1 := Finset.card_eq_sum_ones R
      _ ≤ ∑ j ∈ R, reads C.gates (n + j) := by
        apply Finset.sum_le_sum
        intro j hj
        have ⟨hne, hlt⟩ := Finset.mem_erase.mp hj
        exact reads_pos.mpr (gate_read hmin (Finset.mem_range.mp hlt) (by omega))
      _ ≤ ∑ j ∈ Finset.range C.size, reads C.gates (n + j) :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  omega

private lemma circuit_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (h : C.output < n) :
    circuitFun n C x = x ⟨C.output, h⟩ := by
  change (run C.gates (List.ofFn x)).getD C.output false = _
  rw [run_prefix _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

private lemma input_read {n : ℕ} {C : Circuit} (hf : FanInTwo C) (hout : n ≤ C.output)
    (v : Fin n) {x y : Fin n → Bool} (hxy : ∀ w ≠ v, x w = y w)
    (hne : circuitFun n C x ≠ circuitFun n C y) :
    0 < reads C.gates v.val := by
  by_contra! h
  have hskip : ∀ g ∈ C.gates, v.val ∉ inputs g := by
    intro g hg hv
    exact (Nat.not_lt_of_ge h) (reads_pos.mpr ⟨g, hg, hv⟩)
  apply hne
  exact run_congr C.gates (List.ofFn x) (List.ofFn y) v.val (by simp) (by
    intro i hi
    by_cases hlt : i < n
    · simpa [List.getD_eq_getElem?_getD, hlt] using
        hxy ⟨i, hlt⟩ (fun h => hi (congrArg Fin.val h))
    · simp [List.getD_eq_getElem?_getD, hlt])
    hf hskip C.output (by
      have hv := v.isLt
      omega)

private lemma degree_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : G.degree v = (G.neighborSet v).ncard := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
    SimpleGraph.coe_neighborFinset]

private lemma edge_cover_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hcover : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) :
    G.edgeFinset.card ≤ ∑ v ∈ S, G.degree v := by
  classical
  calc
    G.edgeFinset.card ≤ (S.biUnion (fun v => G.incidenceFinset v)).card := by
      apply Finset.card_le_card
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
        have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        apply Finset.mem_biUnion.mpr
        rcases hcover u v hadj with hu | hv
        · exact ⟨u, hu, SimpleGraph.mem_incidenceFinset.mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
        · exact ⟨v, hv, SimpleGraph.mem_incidenceFinset.mpr
            (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
    _ ≤ ∑ v ∈ S, G.degree v := by
      simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using
        (Finset.card_biUnion_le (s := S) (t := fun v => G.incidenceFinset v))

private lemma essential {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (v : Fin n)
    (h : v ∈ A ∨ ∃ w ∉ A, G.Adj v w) :
    ∃ x y : Fin n → Bool, (∀ w ≠ v, x w = y w) ∧
      graphFun G A x ≠ graphFun G A y := by
  rcases h with hv | ⟨w, hw, hvw⟩
  · refine ⟨fun t => decide (t = v), fun _ => false, fun t ht => by simp [ht], ?_⟩
    simp [graphFun, hv]
  · refine ⟨fun t => decide (t = v ∨ t = w), fun t => decide (t = w),
      fun t ht => by simp [ht], ?_⟩
    have ht : ∃ a b, G.Adj a b ∧ decide (a = v ∨ a = w) = true ∧
        decide (b = v ∨ b = w) = true := ⟨v, w, hvw, by simp, by simp⟩
    have hf : ¬ ∃ a ∈ A, decide (a = w) = true := by simpa using hw
    have he : ¬ ∃ a b, G.Adj a b ∧ decide (a = w) = true ∧ decide (b = w) = true := by
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      subst a
      subst b
      exact G.ne_of_adj hab rfl
    simp only [graphFun, decide_eq_true ht, decide_eq_false hf, decide_eq_false he,
      Bool.or_true, Bool.or_false]
    decide

private lemma solve (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit)
    (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (hiso : ∀ u v, G.Adj u v → u ∉ A)
    (hedge : ∃ u v, G.Adj u v)
    (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C = graphFun G A)
    (hsmall : ∀ S : Finset (Fin n), Disjoint A S →
      (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) →
      C.size + 1 < A.card + G.edgeFinset.card + S.card) :
    ∃ u v, G.Adj u v ∧ reads C.gates u.val ≤ 2 ∧ reads C.gates v.val ≤ 2 := by
  have hd v (hv : v ∉ A) : G.degree v = 3 := (degree_eq_ncard G v).trans (hdeg v hv)
  have he v : ∃ x y : Fin n → Bool, (∀ w ≠ v, x w = y w) ∧
      circuitFun n C x ≠ circuitFun n C y := by
    rw [hfun]
    apply essential G A v
    by_cases hv : v ∈ A
    · exact Or.inl hv
    · obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (by rw [hd v hv]; decide)
      exact Or.inr ⟨w, hiso _ _ hw.symm, hw⟩
  have hout : n ≤ C.output := by
    by_contra! h
    let out : Fin n := ⟨C.output, h⟩
    obtain ⟨u, v, huv⟩ := hedge
    have hne : ∃ w : Fin n, w ≠ out := by
      by_cases hu : u = out
      · exact ⟨v, fun hv => huv.ne (hu.trans hv.symm)⟩
      · exact ⟨u, hu⟩
    obtain ⟨w, hw⟩ := hne
    obtain ⟨x, y, hxy, hdiff⟩ := he w
    exact hdiff ((circuit_input C x h).trans ((hxy out (Ne.symm hw)).trans
      (circuit_input C y h).symm))
  have hp (v : Fin n) : 0 < reads C.gates v.val := by
    obtain ⟨x, y, hxy, hdiff⟩ := he v
    exact input_read hmin.1 hout v hxy hdiff
  by_contra! hn
  let S : Finset (Fin n) := Finset.univ.filter fun v => v ∉ A ∧ 2 < reads C.gates v.val
  have hs v : v ∈ S ↔ v ∉ A ∧ 2 < reads C.gates v.val := by simp [S]
  have hdis : Disjoint A S :=
    Finset.disjoint_left.mpr (fun _ hv hS => ((hs _).mp hS).1 hv)
  have hcov u v (huv : G.Adj u v) : u ∈ S ∨ v ∈ S := by
    by_cases hu : 2 < reads C.gates u.val
    · exact Or.inl ((hs u).mpr ⟨hiso _ _ huv, hu⟩)
    · exact Or.inr ((hs v).mpr ⟨hiso _ _ huv.symm, hn u v huv (by omega)⟩)
  have hE : G.edgeFinset.card ≤ 3 * S.card := by
    calc
      _ ≤ ∑ v ∈ S, G.degree v := edge_cover_bound G S hcov
      _ = 3 * S.card := by
        rw [Finset.sum_congr rfl (fun v hv => hd v ((hs v).mp hv).1)]
        simp [Nat.mul_comm]
  let B : Finset (Fin n) := Finset.univ \ A
  have hB : B.card + A.card = n := by
    simpa [B] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A))
  -- Vertices in A are isolated, and each remaining vertex has degree three.
  have hdegree :
      2 * G.edgeFinset.card = 3 * B.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      (∑ v : Fin n, G.degree v) = ∑ v : Fin n, if v ∉ A then 3 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ A
        · have hz := (G.degree_eq_zero v).mpr (fun w h => hiso v w h hv)
          simp [hv, hz]
        · simp [hv, hd v hv]
      _ = 3 * B.card := by
        rw [← Finset.sum_filter]
        simp [B, Finset.sdiff_eq_filter, Nat.mul_comm]
  have hlower : n + 2 * S.card ≤ ∑ v : Fin n, reads C.gates v.val := by
    calc
      n + 2 * S.card = ∑ v : Fin n, (1 + if v ∈ S then 2 else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ S
        · have hh := ((hs v).mp hv).2
          simp only [hv, ite_true]
          omega
        · have hh := hp v
          simp only [hv, ite_false, add_zero]
          omega
  have hupper := input_bound hmin
  have hstrict := hsmall S hdis hcov
  omega

end PEqualNP.Outside.L_meta_7804


theorem PEqualNP.Outside.L_meta_7804 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 → (∀ (x11 : Finset (Fin x1)), Disjoint x4 x11 → (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + x11.card) → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates).length ≤ (2 : ℕ) ∧ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x13) x5.gates).length ≤ (2 : ℕ) := by
  exact PEqualNP.Outside.L_meta_7804.solve
