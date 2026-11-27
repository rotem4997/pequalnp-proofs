import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17824

-- The monotonicity proof adapts L-meta-6206.
-- The support accounting adapts L-meta-1942 and L-meta-7021.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover

private def BitsLE (xs ys : List Bool) : Prop :=
  ∀ i, xs.getD i false = true → ys.getD i false = true

private lemma append_mono {xs ys as bs : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (hab : BitsLE as bs) :
    BitsLE (xs ++ as) (ys ++ bs) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hab _ hi

private lemma gate_mono {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (hxy : BitsLE xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨i, hi, rfl⟩
    exact hxy i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hxy i h⟩

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) :
    BitsLE (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · apply append_mono hlen hxy
      intro i hi
      cases i with
      | zero => exact gate_mono (hgs g List.mem_cons_self) hxy hi
      | succ i => simp at hi

private lemma wire_true_mono {C : Circuit} (hC : Monotone2 C) {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (i : ℕ) :
    wireVal C xs i = true → wireVal C ys i = true := by
  apply fold_mono C.gates _ xs ys hlen hxy i
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

private lemma ofFn_mono {n : ℕ} {f g : Fin n → Bool}
    (hfg : ∀ i, f i = true → g i = true) : BitsLE (List.ofFn f) (List.ofFn g) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    exact hfg ⟨i, h⟩ hi
  · have h' : (List.ofFn f).length ≤ i := by simpa using Nat.le_of_not_gt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hi
    cases hi

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (scan boolStep gs x).getD i false = (scan boolStep gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (scan boolStep gs x).length = j := by simp [scan_length, hx, j]
    have ey : (scan boolStep gs y).length = j := by simp [scan_length, hy, j]
    rw [scan_snoc, scan_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  show (scan boolStep C.gates (List.ofFn x)).getD C.output false =
    (scan boolStep C.gates (List.ofFn y)).getD C.output false
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

def catalog : List (Finset (Fin 13) × ℕ) :=
  [({0, 1, 2, 5}, 63897560), ({3, 4, 7, 9}, 24903015), ({6, 8, 10, 12}, 66931391)]

def vec (P L : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

def qvec (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  vec Q (missLines singerLines3 Q)

def incidenceOn (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def pivot (Q : Finset (Fin 13)) (i : Fin 26) : Prop :=
  incidenceOn (Function.update (qvec Q) i true)

private instance (x : Fin 26 → Bool) : Decidable (incidenceOn x) := by
  unfold incidenceOn
  infer_instance

private instance (Q : Finset (Fin 13)) (i : Fin 26) : Decidable (pivot Q i) := by
  unfold pivot
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private lemma catalog_sound :
    catalog.all (fun t => decide (IsQuadrangle singerLines3 t.1 ∧
      ∀ i : Fin 26, t.2.testBit i.val = true → pivot t.1 i)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private lemma catalog_cover :
    ∀ i j : Fin 26,
      catalog.any (fun t => t.2.testBit i.val && t.2.testBit j.val) = true := by
  decide +kernel

private theorem common_pivots (i j : Fin 26) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧ pivot Q i ∧ pivot Q j := by
  obtain ⟨t, ht, hij⟩ := List.any_eq_true.mp (catalog_cover i j)
  have h := of_decide_eq_true (List.all_eq_true.mp catalog_sound t ht)
  simp only [Bool.and_eq_true] at hij
  obtain ⟨hi, hj⟩ := hij
  exact ⟨t.1, h.1, h.2 _ hi, h.2 _ hj⟩

private theorem vec_list (P L : Finset (Fin 13)) :
    List.ofFn (vec P L) = incidenceInput P L :=
  List.ofFn_fin_append _ _

private theorem witness_true (C : Circuit) (hm : Monotone2 C) (w : ℕ)
    (hw : RightOnIncidentPairs singerLines3 ⟨C.gates, w⟩) (y : Fin 26 → Bool)
    (h : incidenceOn y) : wireVal C (List.ofFn y) w = true := by
  obtain ⟨p,l,hpl,hp,hl⟩ := h
  have hbits : ∀ i, vec {p} {l} i = true → y i = true := by
    intro i
    refine Fin.addCases (motive := fun k => vec {p} {l} k = true → y k = true)
      (fun j : Fin 13 => ?_) (fun j : Fin 13 => ?_) i
    · intro hj
      have hEq : j = p := by simpa [vec] using hj
      exact hEq ▸ hp
    · intro hj
      change vec {p} {l} (Fin.natAdd 13 j) = true at hj
      change y (Fin.natAdd 13 j) = true
      have hEq : j = l := by
        simpa only [vec, Fin.append_right, Finset.mem_singleton, decide_eq_true_eq] using hj
      exact hEq ▸ hl
  have hw' : wireVal C (List.ofFn (vec {p} {l})) w = true := by
    rw [vec_list]
    exact hw l p hpl
  exact wire_true_mono hm (by simp) (ofFn_mono hbits) w hw'

private def essential (C : Circuit) (w : ℕ) (i : Fin 26) : Prop :=
  ∃ x : Fin 26 → Bool, wireVal C (List.ofFn x) w = false ∧
    wireVal C (List.ofFn (Function.update x i true)) w = true

private theorem essential_prefix (C : Circuit) (hm : Monotone2 C) (w : ℕ)
    (hw : w < 26 + C.size) (he : ∀ i, essential C w i) : 50 ≤ w := by
  let D : Circuit := ⟨C.gates.take (w+1-26), w⟩
  have hgate : ∀ g ∈ D.gates, g.inputs.length ≤ 2 := by
    intro g hg
    exact (hm g (List.mem_of_mem_take hg)).2
  have ht : D.size = w+1-26 := by
    have hle : w+1-26 ≤ C.gates.length := by
      unfold Circuit.size at hw
      omega
    simp [D, Circuit.size, List.length_take]
    omega
  have hprefix (x : Fin 26 → Bool) :
      circuitFun 26 D x = wireVal C (List.ofFn x) w := by
    change (scan boolStep (C.gates.take (w+1-26)) _).getD w false =
      (scan boolStep C.gates _).getD w false
    conv_rhs =>
      rw [← List.take_append_drop (w+1-26) C.gates, scan_append]
    have hkeep (gs : List Gate) (l : List Bool) (i : ℕ) (hi : i < l.length) :
        (scan boolStep gs l).getD i false = l.getD i false := by
      induction gs generalizing l with
      | nil => rfl
      | cons g gs ih =>
        rw [scan_cons, ih]
        · rw [List.getD_append _ _ _ _ hi]
        · simp; omega
    symm
    apply hkeep
    rw [scan_length, List.length_ofFn]
    change w < 26 + D.size
    omega
  have hk := essential_bound D hgate (fun i => by
    obtain ⟨x,hx,hy⟩ := he i
    refine ⟨x, Function.update x i true, ?_, ?_⟩
    · intro j hj
      rw [Function.update_of_ne hj]
    · rw [hprefix, hprefix, hx, hy]
      decide)
  omega

theorem supportBound
    (C : Circuit) (a b : ℕ)
    (hm : Monotone2 C) (_hr : ReadsBack 26 C)
    (ha : a < 26 + C.size) (hb : b < 26 + C.size)
    (ra : RightOnIncidentPairs singerLines3 ⟨C.gates, a⟩)
    (rb : RightOnIncidentPairs singerLines3 ⟨C.gates, b⟩)
    (safe : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      wireVal C (incidenceInput Q (missLines singerLines3 Q)) a = false ∨
      wireVal C (incidenceInput Q (missLines singerLines3 Q)) b = false) :
    50 ≤ max a b ∧ ∃ w ∈ [a, b], ∀ i : Fin 26, ∃ x : Fin 26 → Bool,
      wireVal C (List.ofFn x) w = false ∧
      wireVal C (List.ofFn (Function.update x i true)) w = true := by
  classical
  have either : (∀ i, essential C a i) ∨ (∀ i, essential C b i) := by
    by_contra! h
    obtain ⟨i, hi⟩ := h.1
    obtain ⟨j, hj⟩ := h.2
    obtain ⟨Q, hQ, pi, pj⟩ := common_pivots i j
    have ai := witness_true C hm a ra _ pi
    have bj := witness_true C hm b rb _ pj
    rcases safe Q hQ with hqa | hqb
    · apply hi
      refine ⟨qvec Q, ?_, ai⟩
      simpa only [qvec, vec_list] using hqa
    · apply hj
      refine ⟨qvec Q, ?_, bj⟩
      simpa only [qvec, vec_list] using hqb
  rcases either with ea | eb
  · exact ⟨(essential_prefix C hm a ha ea).trans (le_max_left _ _), a, by simp, ea⟩
  · exact ⟨(essential_prefix C hm b hb eb).trans (le_max_right _ _), b, by simp, eb⟩

end PEqualNP.Outside.L_meta_17824

theorem PEqualNP.Outside.L_meta_17824 :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x10 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x10 → PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x2 = Bool.false ∨ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x3 = Bool.false) → (50 : ℕ) ≤ Max.max x2 x3 ∧ ∃ x11 ∈ [x2, x3], ∀ (x12 : Fin (26 : ℕ)), ∃ (x13 : Fin (26 : ℕ) → Bool), PEqualNP.LowMerge.wireVal x1 (List.ofFn x13) x11 = Bool.false ∧ PEqualNP.LowMerge.wireVal x1 (List.ofFn (Function.update x13 x12 Bool.true)) x11 = Bool.true :=
  PEqualNP.Outside.L_meta_17824.supportBound
