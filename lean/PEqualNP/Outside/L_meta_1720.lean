import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1720_aux

namespace LMeta1720Extract

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)


private def scan {α : Type} (δ : α) (f : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : List α :=
  gs.foldl (fun w g => w ++ [f g.op (g.inputs.map fun i => w.getD i δ)]) xs

private theorem scan_snoc {α : Type} (δ : α) (f : GateOp → List α → α) (gs : List Gate)
    (g : Gate) (xs : List α) :
    scan δ f (gs ++ [g]) xs = scan δ f gs xs ++
      [f g.op (g.inputs.map fun i => (scan δ f gs xs).getD i δ)] := by
  simp only [scan, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem scan_length {α : Type} (δ : α) (f : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (scan δ f gs xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [scan]
  | append_singleton gs g ih => rw [scan_snoc]; simp [ih]; omega

private theorem scan_input {α : Type} (δ : α) (f : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (scan δ f gs xs).getD i δ = xs.getD i δ := by
  induction gs using List.reverseRecOn with
  | nil => simp [scan]
  | append_singleton gs g ih =>
    rw [scan_snoc, List.getD_append _ _ _ _ (by rw [scan_length]; omega), ih]

private theorem scan_gate {α : Type} (δ : α) (f : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : ∀ (j : ℕ) (hj : j < gs.length),
    (scan δ f gs xs).getD (xs.length + j) δ =
      f gs[j].op (gs[j].inputs.map fun a =>
        if a < xs.length + j then (scan δ f gs xs).getD a δ else δ) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hl := scan_length δ f gs xs
    rw [scan_snoc]
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih j hjl]
      simp only [List.getElem_append_left hjl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < xs.length + j
      · rw [ite_eq_left hi, ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [List.getElem_append_right (Nat.le_refl _), hl, Nat.sub_self,
        List.getD_cons_zero, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < xs.length + gs.length
      · rw [ite_eq_left hi, List.getD_append _ _ _ _ (by omega)]
      · simp only [hi, ite_false]
        rw [List.getD_eq_default _ _ (by omega)]

private theorem scan_gate_back {α : Type} (δ : α) (f : GateOp → List α → α)
    (gs : List Gate) (xs : List α) (j : ℕ) (hj : j < gs.length)
    (hb : ∀ a ∈ gs[j].inputs, a < xs.length + j) :
    (scan δ f gs xs).getD (xs.length + j) δ =
      f gs[j].op (gs[j].inputs.map fun a => (scan δ f gs xs).getD a δ) := by
  rw [scan_gate δ f gs xs j hj]
  congr 1
  exact List.map_congr_left (fun a ha => ite_eq_left (hb a ha))

private theorem gateAt_get {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

private def degreeOp (op : GateOp) (l : List ℕ) : ℕ :=
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  if op = GateOp.and then l.sum else l.foldr max 0

private theorem degrees_scan (C : Circuit) (n : ℕ) (marks : Finset ℕ) :
    C.lineDegrees n marks =
      scan 0 degreeOp C.gates ((List.range n).map fun i => if i ∈ marks then 1 else 0) := rfl

private theorem wires_scan (C : Circuit) (xs : List Bool) :
    C.wires xs = scan false GateOp.eval C.gates xs := rfl


theorem wires_gate (C : Circuit) (xs : List Bool) {n j : ℕ} (hx : xs.length = n)
    (hC : ReadsBack n C) (hj : j < C.gates.length) :
    (C.wires xs).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun a => (C.wires xs).getD a false) := by
  subst n
  simp only [wires_scan, gateAt_get hj]
  exact scan_gate_back false GateOp.eval C.gates xs j hj
    (by simpa only [gateAt_get hj] using hC j hj)

private theorem wires_input (C : Circuit) (xs : List Bool) {i : ℕ} (hi : i < xs.length) :
    (C.wires xs).getD i false = xs.getD i false :=
  scan_input false GateOp.eval C.gates xs i hi


def leftDeg (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0


theorem leftDeg_input (N : ℕ) (C : Circuit) {i : ℕ} (hi : i < N + N) :
    leftDeg N C i = if i < N then 1 else 0 := by
  unfold leftDeg
  rw [degrees_scan, scan_input 0 degreeOp _ _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

private theorem leftDeg_gate (N : ℕ) (C : Circuit) (hC : ReadsBack (N + N) C)
    {j : ℕ} (hj : j < C.gates.length) :
    leftDeg N C (N + N + j) =
      degreeOp (gateAt C j).op ((gateAt C j).inputs.map fun a => leftDeg N C a) := by
  simpa only [leftDeg, degrees_scan, gateAt_get hj, List.length_map, List.length_range] using
    scan_gate_back 0 degreeOp C.gates
      ((List.range (N + N)).map fun i => if i ∈ Finset.range N then 1 else 0) j hj
      (by simpa only [gateAt_get hj, List.length_map, List.length_range] using hC j hj)

private theorem le_sum_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    rw [List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha
      omega

private theorem le_max_of_mem {a : ℕ} {l : List ℕ} (ha : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    rw [List.foldr_cons]
    rcases ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)


theorem leftDeg_parent_le (N : ℕ) (C : Circuit) (hC : ReadsBack (N + N) C)
    {j a : ℕ} (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs) :
    leftDeg N C a ≤ leftDeg N C (N + N + j) := by
  rw [leftDeg_gate N C hC hj, degreeOp]
  have hm : leftDeg N C a ∈ (gateAt C j).inputs.map (leftDeg N C) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  split
  · exact le_sum_of_mem hm
  · exact le_max_of_mem hm


theorem leftDeg_zero_operand (N : ℕ) (C : Circuit) (hC : ReadsBack (N + N) C)
    {j a : ℕ} (hj : j < C.gates.length) (hz : leftDeg N C (N + N + j) = 0)
    (ha : a ∈ (gateAt C j).inputs) : leftDeg N C a = 0 := by
  have := leftDeg_parent_le N C hC hj ha
  omega

private def kept (k : ℕ → Bool) (t : ℕ) : List ℕ := (List.range t).filter k

private def rank (k : ℕ → Bool) (t : ℕ) : ℕ := (kept k t).length

private theorem kept_split (k : ℕ → Bool) {s t : ℕ} (h : s ≤ t) :
    kept k t = kept k s ++ (List.range' s (t - s)).filter k := by
  unfold kept
  rw [← List.filter_append]
  congr 1
  rw [List.range_eq_range', List.range_eq_range']
  have := @List.range'_append_1 0 s (t - s)
  simp only [Nat.zero_add] at this
  rw [this]
  congr 1
  omega

private theorem rank_lt (k : ℕ → Bool) {s t : ℕ} (hst : s < t) (hs : k s = true) :
    rank k s < rank k t := by
  unfold rank
  rw [kept_split k hst.le, List.length_append]
  obtain ⟨m, hm⟩ : ∃ m, t - s = m + 1 := ⟨t - s - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hs]
  simp

private theorem kept_get (k : ℕ → Bool) {t j : ℕ} (hj : j < t) (hk : k j = true) :
    (kept k t)[rank k j]? = some j := by
  rw [kept_split k hj.le]
  unfold rank
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, t - j = m + 1 := ⟨t - j - 1, by omega⟩
  rw [hm, List.range'_succ, List.filter_cons_of_pos hk]
  simp

private theorem kept_back (k : ℕ → Bool) {t r : ℕ} (hr : r < (kept k t).length) :
    let j := (kept k t)[r]
    k j = true ∧ j < t ∧ rank k j = r := by
  dsimp only
  have hm : (kept k t)[r] ∈ (kept k t) := List.getElem_mem hr
  have hm2 := List.mem_filter.mp hm
  have hlt := List.mem_range.mp hm2.1
  refine ⟨hm2.2, hlt, ?_⟩
  obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp (kept_get k hlt hm2.2)
  have hnd : (kept k t).Nodup := List.nodup_range.filter _
  exact hnd.getElem_inj_iff.mp he

private def keep (N : ℕ) (C : Circuit) (j : ℕ) : Bool :=
  decide (leftDeg N C (N + N + j) = 0)


def remap (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if w < N + N then w - N else N + rank (keep N C) (w - (N + N))

theorem remap_right_input (N : ℕ) (C : Circuit) {i : ℕ} (hi : i < N) :
    remap N C (N + i) = i := by
  simp [remap, show N + i < N + N by omega]

private theorem remap_gate (N : ℕ) (C : Circuit) (j : ℕ) :
    remap N C (N + N + j) = N + rank (keep N C) j := by simp [remap]

private def mapGate (N : ℕ) (C : Circuit) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap N C)⟩


def project (N : ℕ) (C : Circuit) : Circuit :=
  ⟨(kept (keep N C) C.gates.length).map (fun j => mapGate N C (gateAt C j)),
    remap N C C.output⟩

private theorem project_get (N : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hz : leftDeg N C (N + N + j) = 0) :
    rank (keep N C) j < (project N C).gates.length ∧
      gateAt (project N C) (rank (keep N C) j) = mapGate N C (gateAt C j) := by
  obtain ⟨hr, hg⟩ := List.getElem?_eq_some_iff.mp
    (kept_get (keep N C) hj (by simp [keep, hz]))
  have hr' : rank (keep N C) j < (project N C).gates.length := by simpa [project] using hr
  exact ⟨hr', by rw [gateAt_get hr']; simp [project, hg]⟩

private theorem project_back (N : ℕ) (C : Circuit) {j : ℕ}
    (hj : j < (project N C).gates.length) :
    ∃ k < C.gates.length, leftDeg N C (N + N + k) = 0 ∧
      rank (keep N C) k = j ∧ gateAt (project N C) j = mapGate N C (gateAt C k) := by
  have hj' : j < (kept (keep N C) C.gates.length).length := by simpa [project] using hj
  let k := (kept (keep N C) C.gates.length)[j]
  obtain ⟨hk, hb, hr⟩ := kept_back (keep N C) hj'
  exact ⟨k, hb, by simpa [keep] using hk, hr, by rw [gateAt_get hj]; simp [project, k]⟩

private theorem source_of_mem (N : ℕ) (C : Circuit) {g : Gate}
    (hg : g ∈ (project N C).gates) : ∃ g' ∈ C.gates, g = mapGate N C g' := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have hj' : j < C.gates.length := List.mem_range.mp (List.mem_filter.mp hj).1
  exact ⟨gateAt C j, by rw [gateAt_get hj']; exact List.getElem_mem hj', rfl⟩


theorem project_monotone2 (N : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (project N C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := source_of_mem N C hg
  simpa only [mapGate, List.length_map] using hm g' hg'


theorem project_exact_two (N : ℕ) (C : Circuit) (hm : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ g ∈ (project N C).gates, g.inputs.length = 2 := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := source_of_mem N C hg
  simpa only [mapGate, List.length_map] using hm g' hg'


theorem project_size (N : ℕ) (C : Circuit) :
    (project N C).size =
      ((Finset.range C.gates.length).filter (fun j => leftDeg N C (N + N + j) = 0)).card := by
  have hs : (kept (keep N C) C.gates.length).toFinset =
      (Finset.range C.gates.length).filter (fun j => leftDeg N C (N + N + j) = 0) := by
    ext j
    simp [kept, keep]
  have hn : (kept (keep N C) C.gates.length).Nodup := List.nodup_range.filter _
  rw [← hs, List.toFinset_card_of_nodup hn]
  simp [Circuit.size, project]


theorem project_size_ncard (N : ℕ) (C : Circuit) :
    (project N C).size = Set.ncard
      {j : ℕ | j < C.gates.length ∧ (C.lineDegrees (N + N) (Finset.range N)).getD
        (N + N + j) 0 = 0} := by
  rw [project_size]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [leftDeg]

private theorem remap_lt (N : ℕ) (C : Circuit) {a j : ℕ} (ha : a < N + N + j)
    (hz : leftDeg N C a = 0) : remap N C a < N + rank (keep N C) j := by
  by_cases hin : a < N + N
  · rw [remap, ite_eq_left hin]
    omega
  · obtain ⟨s, rfl⟩ : ∃ s, a = N + N + s := ⟨a - (N + N), by omega⟩
    rw [remap_gate]
    have hs := rank_lt (keep N C) (show s < j by omega) (by simp [keep, hz])
    omega


theorem project_readsBack (N : ℕ) (C : Circuit) (hC : ReadsBack (N + N) C) :
    ReadsBack N (project N C) := by
  intro j hj a ha
  obtain ⟨k, hk, hz, hr, hg⟩ := project_back N C hj
  rw [hg] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  rw [← hr]
  exact remap_lt N C (hC k hk b hb) (leftDeg_zero_operand N C hC hk hz hb)


theorem remap_valid (N : ℕ) (C : Circuit) {h : ℕ} (hh : h < N + N + C.gates.length)
    (hz : leftDeg N C h = 0) : remap N C h < N + (project N C).gates.length := by
  simpa only [rank, project, List.length_map] using remap_lt N C hh hz


theorem project_wires (N : ℕ) (C : Circuit) (hC : ReadsBack (N + N) C)
    (x y : Fin N → Bool) {h : ℕ} (hh : h < N + N + C.gates.length)
    (hz : leftDeg N C h = 0) :
    ((project N C).wires (List.ofFn y)).getD (remap N C h) false =
      (C.wires (List.ofFn (Fin.append x y))).getD h false := by
  have hP := project_readsBack N C hC
  have hx : (List.ofFn (Fin.append x y)).length = N + N := by simp
  have hy : (List.ofFn y).length = N := by simp
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    by_cases hin : h < N + N
    · have hN : N ≤ h := by
        by_contra! hlt
        simp [leftDeg_input N C hin, hlt] at hz
      rw [remap, ite_eq_left hin, wires_input _ _ (by rw [hy]; omega),
        wires_input _ _ (by rw [hx]; exact hin), List.ofFn_fin_append,
        List.getD_append_right _ _ _ _ (by simpa using hN), List.length_ofFn]
    · obtain ⟨j, rfl⟩ : ∃ j, h = N + N + j := ⟨h - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨hr, hg⟩ := project_get N C hj hz
      rw [remap_gate, wires_gate _ _ hy hP hr, wires_gate _ _ hx hC hj, hg]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      have hlt := hC j hj a ha
      exact ih a hlt (hlt.trans hh) (leftDeg_zero_operand N C hC hj hz ha)


theorem rightProject (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hC : ReadsBack (N + N) C) :
    ∃ (D : Circuit) (r : ℕ → ℕ), Monotone2 D ∧ ReadsBack N D ∧
      D.size = Set.ncard {j : ℕ | j < C.gates.length ∧ (C.lineDegrees (N + N) (Finset.range N)).getD
        (N + N + j) 0 = 0} ∧
      (∀ i < N, r (N + i) = i) ∧
      ∀ h < N + N + C.gates.length, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0 →
        r h < N + D.gates.length ∧ ∀ y : Fin N → Bool,
          (D.wires (List.ofFn y)).getD (r h) false =
            (C.wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD h false := by
  refine ⟨project N C, remap N C, project_monotone2 N C hm, project_readsBack N C hC,
    project_size_ncard N C, fun _ hi => remap_right_input N C hi, ?_⟩
  intro h hh hz
  exact ⟨remap_valid N C hh hz, fun y => project_wires N C hC (fun _ => false) y hh hz⟩

end LMeta1720Extract

namespace LMeta1720Aggregate

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def value {N : ℕ} (C : Circuit) (x : Fin N → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private theorem wiresFrom_append (gs extra : List Gate) (w : List Bool) :
    wiresFrom (gs ++ extra) w = wiresFrom extra (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_suffix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [b]) = w ++ b :: t
    rw [ht, List.append_assoc, List.singleton_append]

private theorem length_wires {N : ℕ} (D : Circuit) (x : Fin N → Bool) :
    (D.wires (List.ofFn x)).length = N + D.gates.length := by
  obtain ⟨t, ht, hlen⟩ := wiresFrom_suffix D.gates (List.ofFn x)
  change (wiresFrom D.gates (List.ofFn x)).length = _
  simp [ht, hlen]

private theorem value_oob {N : ℕ} (D : Circuit) (x : Fin N → Bool) (i : ℕ)
    (hi : N + D.gates.length ≤ i) : value D x i = false :=
  List.getD_eq_default _ _ (by rw [length_wires]; exact hi)

private theorem value_append {N : ℕ} (C D : Circuit) (extra : List Gate)
    (he : D.gates = C.gates ++ extra) (x : Fin N → Bool) (i : ℕ)
    (hi : i < N + C.gates.length) : value D x i = value C x i := by
  change (wiresFrom D.gates (List.ofFn x)).getD i false = _
  rw [he, wiresFrom_append]
  obtain ⟨t, ht, _⟩ := wiresFrom_suffix extra (wiresFrom C.gates (List.ofFn x))
  rw [ht]
  exact List.getD_append _ _ _ _ (by change i < (C.wires (List.ofFn x)).length; rwa [length_wires])

private def orGate (i j : ℕ) : Gate := ⟨.or, [i, j]⟩

private def snocOr (D : Circuit) (i j : ℕ) : Circuit :=
  ⟨D.gates ++ [orGate i j], D.output⟩

private theorem readsBack_snoc {N : ℕ} {D : Circuit} (hR : ReadsBack N D)
    {i j : ℕ} (hi : i < N + D.gates.length) (hj : j < N + D.gates.length) :
    ReadsBack N (snocOr D i j) := by
  intro k hk w hw
  by_cases h : k < D.gates.length
  · have hgate : gateAt (snocOr D i j) k = gateAt D k :=
      List.getD_append _ _ _ _ h
    rw [hgate] at hw
    exact hR k h w hw
  · have he : k = D.gates.length := by
      simp only [snocOr, List.length_append, List.length_singleton] at hk
      omega
    subst k
    have hgate : gateAt (snocOr D i j) D.gates.length = orGate i j := by
      simp [gateAt, snocOr]
    rw [hgate] at hw
    change w ∈ [i, j] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption

private theorem wires_snoc {N : ℕ} (D : Circuit) (x : Fin N → Bool) (i j : ℕ) :
    (snocOr D i j).wires (List.ofFn x) =
      D.wires (List.ofFn x) ++ [value D x i || value D x j] := by
  simp [snocOr, orGate, Circuit.wires, List.foldl_append, GateOp.eval, value]

private theorem value_snoc_new {N : ℕ} (D : Circuit) (x : Fin N → Bool) (i j : ℕ) :
    value (snocOr D i j) x (N + D.gates.length) = (value D x i || value D x j) := by
  change ((snocOr D i j).wires (List.ofFn x)).getD (N + D.gates.length) false = _
  rw [wires_snoc, ← length_wires D x]
  simp

private def query {N : ℕ} (D : Circuit) (x : Fin N → Bool) (o : Option ℕ) : Bool :=
  o.elim false (value D x)

private theorem query_snoc_old {N : ℕ} (D : Circuit) (x : Fin N → Bool) (i j : ℕ)
    (o : Option ℕ) (ho : ∀ k, o = some k → k < N + D.gates.length) :
    query (snocOr D i j) x o = query D x o := by
  cases o with
  | none => rfl
  | some k => exact value_append D (snocOr D i j) [orGate i j] rfl x k (ho k rfl)

private theorem query_getD {N : ℕ} (D : Circuit) (x : Fin N → Bool) (o : Option ℕ) :
    value D x (o.getD (N + D.gates.length)) = query D x o := by
  cases o with
  | none => exact value_oob D x _ le_rfl
  | some k => rfl

private theorem exists_mem_cons {α : Type*} (a : α) (l : List α) (P : α → Prop) :
    (∃ t ∈ a :: l, P t) ↔ P a ∨ ∃ t ∈ l, P t := by
  constructor
  · rintro ⟨t, ht, hP⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Or.inl hP
    · exact Or.inr ⟨t, ht, hP⟩
  · rintro (hP | ⟨t, ht, hP⟩)
    · exact ⟨a, List.mem_cons_self, hP⟩
    · exact ⟨t, List.mem_cons_of_mem _ ht, hP⟩


private structure Assembly (N : ℕ) (C : Circuit) (β : Type*)
    (l : List (β × Fin (N + C.gates.length))) where
  circ : Circuit
  root : β → Option ℕ
  extra : List Gate
  gates_eq : circ.gates = C.gates ++ extra
  or_only : ∀ g ∈ extra, g.op = GateOp.or ∧ g.inputs.length = 2
  readsBack : ReadsBack N circ
  size_le : circ.size ≤ C.size + l.length
  valid : ∀ p j, root p = some j → j < N + circ.gates.length
  sem : ∀ (x : Fin N → Bool) (p : β), query circ x (root p) = true ↔
    ∃ t ∈ l, t.1 = p ∧ value C x t.2 = true

private def assemble {N : ℕ} {β : Type*} [DecidableEq β] (C : Circuit) (hR : ReadsBack N C) :
    (l : List (β × Fin (N + C.gates.length))) → Assembly N C β l
  | [] =>
    { circ := C, root := fun _ => none, extra := [], gates_eq := by simp,
      or_only := by simp, readsBack := hR, size_le := by simp,
      valid := by simp, sem := by simp [query] }
  | (p, i) :: l => by
    let R := assemble C hR l
    have hlen : C.gates.length ≤ R.circ.gates.length := by
      rw [R.gates_eq, List.length_append]; omega
    have hi : (i : ℕ) < N + R.circ.gates.length := by have := i.isLt; omega
    have hv (x : Fin N → Bool) : value R.circ x i = value C x i :=
      value_append C R.circ R.extra R.gates_eq x i i.isLt
    cases hp : R.root p with
    | none =>
      refine
        { circ := R.circ
          root := Function.update R.root p (some i.val)
          extra := R.extra
          gates_eq := R.gates_eq
          or_only := R.or_only
          readsBack := R.readsBack
          size_le := ?_
          valid := ?_
          sem := ?_ }
      · have hs := R.size_le
        simp only [List.length_cons]; omega
      · intro q j hj
        by_cases hq : q = p
        · subst q
          simp only [Function.update_self, Option.some.injEq] at hj
          subst j
          exact hi
        · rw [Function.update_of_ne hq] at hj
          exact R.valid q j hj
      · intro x q
        rw [exists_mem_cons]
        by_cases hq : q = p
        · subst q
          have htail : ¬ (∃ t ∈ l, t.1 = p ∧ value C x t.2 = true) := by
            intro he
            have hh := (R.sem x p).2 he
            simp [hp, query] at hh
          rw [Function.update_self]
          change value R.circ x i = true ↔ (p = p ∧ value C x i = true) ∨ _
          rw [hv x]
          constructor
          · intro h
            exact Or.inl ⟨rfl, h⟩
          · rintro (⟨_, h⟩ | h)
            · exact h
            · exact (htail h).elim
        · simpa [Function.update_of_ne hq, Ne.symm hq] using R.sem x q
    | some j =>
      let F := snocOr R.circ i j
      let k := N + R.circ.gates.length
      have hj := R.valid p j hp
      have hF : F.gates.length = R.circ.gates.length + 1 := by simp [F, snocOr]
      refine
        { circ := F
          root := Function.update R.root p (some k)
          extra := R.extra ++ [orGate i j]
          gates_eq := ?_
          or_only := ?_
          readsBack := readsBack_snoc R.readsBack hi hj
          size_le := ?_
          valid := ?_
          sem := ?_ }
      · change R.circ.gates ++ [orGate i j] = C.gates ++ (R.extra ++ [orGate i j])
        rw [R.gates_eq, List.append_assoc]
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact R.or_only g hg
        · simp only [List.mem_singleton] at hg
          subst g
          simp [orGate]
      · have hs := R.size_le
        change F.gates.length ≤ C.size + ((p, i) :: l).length
        rw [hF, List.length_cons]
        change R.circ.gates.length ≤ C.size + l.length at hs
        omega
      · intro q a ha
        by_cases hq : q = p
        · subst q
          simp only [Function.update_self, Option.some.injEq] at ha
          subst a
          rw [hF]; dsimp [k]; omega
        · rw [Function.update_of_ne hq] at ha
          have hqa := R.valid q a ha
          omega
      · intro x q
        rw [exists_mem_cons]
        by_cases hq : q = p
        · subst q
          have htail := R.sem x p
          simp [hp, query] at htail
          simp [query, F, k, value_snoc_new, hv x, htail]
        · have hold := query_snoc_old R.circ x i j (R.root q) (R.valid q)
          simpa [Function.update_of_ne hq, Ne.symm hq, F, hold] using R.sem x q


theorem aggregateWithPrefix {N : ℕ} {α β : Type*} [DecidableEq β]
    (C : Circuit) (s : Finset α) (wire : α → ℕ) (tag : α → Option β)
    (hM : Monotone2 C) (hR : ReadsBack N C) :
    ∃ (D : Circuit) (out : β → ℕ),
      (∃ extra : List Gate, D.gates = C.gates ++ extra ∧
        ∀ g ∈ extra, g.op = GateOp.or ∧ g.inputs.length = 2) ∧
      Monotone2 D ∧ ReadsBack N D ∧ D.size ≤ C.size + s.card ∧
      ∀ (x : Fin N → Bool) (p : β), (D.wires (List.ofFn x)).getD (out p) false =
        decide (∃ h ∈ s, tag h = some p ∧ (C.wires (List.ofFn x)).getD (wire h) false = true) := by
  let chosen (h : α) : Option (β × Fin (N + C.gates.length)) :=
    if hi : wire h < N + C.gates.length then (tag h).map (fun p => (p, ⟨wire h, hi⟩)) else none
  let l := s.toList.filterMap chosen
  let R := assemble C hR l
  refine ⟨R.circ, fun p => (R.root p).getD (N + R.circ.gates.length),
    ⟨R.extra, R.gates_eq, R.or_only⟩, ?_, R.readsBack, ?_, ?_⟩
  · intro g hg
    rw [R.gates_eq, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hM g hg
    · obtain ⟨ho, hl⟩ := R.or_only g hg
      simp [ho, hl]
  · have hcost : l.length ≤ s.card := by
      simpa [l, Finset.length_toList] using (List.length_filterMap_le (f := chosen) (l := s.toList))
    exact R.size_le.trans (Nat.add_le_add_left hcost _)
  · intro x p
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    change value R.circ x ((R.root p).getD (N + R.circ.gates.length)) = true ↔
      ∃ h ∈ s, tag h = some p ∧ value C x (wire h) = true
    rw [query_getD, R.sem]
    constructor
    · rintro ⟨t, ht, htp, hv⟩
      obtain ⟨h, hh, hsome⟩ := List.mem_filterMap.mp ht
      by_cases hi : wire h < N + C.gates.length
      · cases htag : tag h with
        | none => simp [chosen, hi, htag] at hsome
        | some q =>
          have he : (q, (⟨wire h, hi⟩ : Fin (N + C.gates.length))) = t :=
            Option.some.inj (by simpa only [chosen, dite_eq_left hi, htag, Option.map_some] using hsome)
          subst t
          exact ⟨h, Finset.mem_toList.mp hh, htag.trans (congrArg some htp), hv⟩
      · simp [chosen, hi] at hsome
    · rintro ⟨h, hh, htag, hv⟩
      have hi : wire h < N + C.gates.length := by
        by_contra hn
        simp [value_oob C x (wire h) (Nat.le_of_not_gt hn)] at hv
      refine ⟨(p, ⟨wire h, hi⟩), List.mem_filterMap.mpr ?_, rfl, hv⟩
      exact ⟨h, Finset.mem_toList.mpr hh, by simp [chosen, hi, htag]⟩


theorem aggregate {N : ℕ} {α β : Type*} [DecidableEq β]
    (C : Circuit) (s : Finset α) (wire : α → ℕ) (tag : α → Option β)
    (hM : Monotone2 C) (hR : ReadsBack N C) :
    ∃ (D : Circuit) (out : β → ℕ), Monotone2 D ∧ ReadsBack N D ∧
      D.size ≤ C.size + s.card ∧
      ∀ (x : Fin N → Bool) (p : β), (D.wires (List.ofFn x)).getD (out p) false =
        decide (∃ h ∈ s, tag h = some p ∧ (C.wires (List.ofFn x)).getD (wire h) false = true) := by
  obtain ⟨D, out, _, hm, hr, hsz, hv⟩ := aggregateWithPrefix C s wire tag hM hR
  exact ⟨D, out, hm, hr, hsz, hv⟩

end LMeta1720Aggregate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

namespace LMeta1720Math

abbrev Binary (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

abbrev dl (N : ℕ) (C : Circuit) (h : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD h 0

abbrev dr (N : ℕ) (C : Circuit) (h : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD h 0

abbrev IsMixed (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  0 < dl N C (N + N + j) ∧ 0 < dr N C (N + N + j)

def mixed (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (IsMixed N C)

def pureL (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => dr N C (N + N + j) = 0)

def pureR (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => dl N C (N + N + j) = 0)

abbrev Port (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  (dl N C h = 0 ∧ 0 < dr N C h ∧
    ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧ IsMixed N C j)

def ports (N : ℕ) (C : Circuit) : Finset ℕ :=
  ((mixed N C).biUnion (fun j => (gateAt C j).inputs.toFinset)).filter
    (fun h => dl N C h = 0 ∧ 0 < dr N C h)

lemma mem_ports {N : ℕ} {C : Circuit} {h : ℕ} : h ∈ ports N C ↔ Port N C h := by
  simp only [ports, Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset, mixed,
    Finset.mem_range, Port, IsMixed]
  constructor
  · rintro ⟨⟨j, ⟨hj, hm⟩, hi⟩, hz, hd⟩
    exact ⟨hz, hd, j, hj, hi, hm⟩
  · rintro ⟨hz, hd, j, hj, hi, hm⟩
    exact ⟨⟨j, ⟨hj, hm⟩, hi⟩, hz, hd⟩

lemma port_valid {N : ℕ} {C : Circuit} (hBack : ReadsBack (N + N) C) {h : ℕ}
    (hh : h ∈ ports N C) : h < N + N + C.gates.length := by
  obtain ⟨_, _, j, hj, hi, _⟩ := mem_ports.mp hh
  have hi' := hBack j hj h hi
  omega

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma ports_bound (N : ℕ) (C : Circuit) (hBin : Binary C) :
    (ports N C).card ≤ 2 * (mixed N C).card := by
  calc
    _ ≤ ((mixed N C).biUnion (fun j => (gateAt C j).inputs.toFinset)).card :=
      Finset.card_filter_le _ _
    _ ≤ ∑ j ∈ mixed N C, (gateAt C j).inputs.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ mixed N C, 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hi := (Finset.mem_filter.mp hj).1
      have hLen := (hBin _ (gateAt_mem (Finset.mem_range.mp hi))).2
      exact (List.toFinset_card_le _).trans (by omega)
    _ = _ := by simp [Nat.mul_comm]

lemma pureL_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ dr N C (N + N + j) = 0} = (pureL N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [pureL]

lemma pureR_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ dl N C (N + N + j) = 0} = (pureR N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [pureR]

lemma mixed_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ IsMixed N C j} = (mixed N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [mixed, IsMixed]

lemma gate_budget (N : ℕ) (C : Circuit) :
    (pureL N C).card + (pureR N C).card + 5 * (mixed N C).card ≤ 5 * C.size := by
  have hmL : Disjoint (pureL N C) (mixed N C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hm
    have hp := (Finset.mem_filter.mp hj).2
    have hpos := (Finset.mem_filter.mp hm).2.2
    omega
  have hmR : Disjoint (pureR N C) (mixed N C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hm
    have hp := (Finset.mem_filter.mp hj).2
    have hpos := (Finset.mem_filter.mp hm).2.1
    omega
  have bound (s : Finset ℕ) (hs : s ⊆ Finset.range C.gates.length)
      (hd : Disjoint s (mixed N C)) : s.card + (mixed N C).card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint hd, ← Finset.card_range C.gates.length]
    exact Finset.card_le_card (Finset.union_subset hs (Finset.filter_subset _ _))
  have hL := bound (pureL N C) (Finset.filter_subset _ _) hmL
  have hR := bound (pureR N C) (Finset.filter_subset _ _) hmR
  change _ ≤ 5 * C.gates.length
  omega

def atom {N : ℕ} (p : Fin N) (i : Fin N) : Bool := decide (i = p)

lemma atom_true {N : ℕ} {p i : Fin N} : atom p i = true ↔ i = p := by
  simp [atom]

lemma atom_card {N : ℕ} (l : Fin N) :
    (Finset.univ.filter (fun j => atom l j = true)).card = 1 := by
  have e : Finset.univ.filter (fun j => atom l j = true) = {l} := by
    ext j
    simp [atom]
  simp [e]

lemma atom_append {N : ℕ} (p l : Fin N) :
    Fin.append (atom p) (atom l) =
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have hn : Fin.castAdd N j ≠ Fin.natAdd N l := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = N + l.val at hv
      have hj := j.isLt
      omega
    have he : (Fin.castAdd N j = Fin.castAdd N p ∨ Fin.castAdd N j = Fin.natAdd N l) ↔ j = p := by
      constructor
      · rintro (hp | hl)
        · exact Fin.castAdd_inj.mp hp
        · exact (hn hl).elim
      · intro hp
        exact Or.inl (congrArg (Fin.castAdd N) hp)
    simp only [atom, he]
  · rw [Fin.append_right]
    have hn : Fin.natAdd N j ≠ Fin.castAdd N p := by
      intro he
      have hv := congrArg Fin.val he
      change N + j.val = p.val at hv
      have hp := p.isLt
      omega
    have he : (Fin.natAdd N j = Fin.castAdd N p ∨ Fin.natAdd N j = Fin.natAdd N l) ↔ j = l := by
      constructor
      · rintro (hp | hl)
        · exact (hn hp).elim
        · have hval := congrArg Fin.val hl
          change N + j.val = N + l.val at hval
          exact Fin.ext (by omega)
      · intro hl
        exact Or.inr (congrArg (Fin.natAdd N) hl)
    simp only [atom, he]

abbrev accept {N : ℕ} (C : Circuit) (x y : Fin N → Bool) : Bool :=
  circuitFun (N + N) C (Fin.append x y)

abbrev flag {N : ℕ} (C : Circuit) (h : ℕ) (y : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn (Fin.append (fun _ : Fin N => false) y))).getD h false

abbrev coeff {N : ℕ} (C : Circuit) (ph : ℕ → ℕ) (h : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD (ph h) false

lemma no_rectangle {N : ℕ} {I : Fin N → Fin N → Prop}
    (hLine : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l) {a b l m : Fin N}
    (hlm : l ≠ m) (hal : I a l) (ham : I a m) (hbl : I b l) (hbm : I b m) : a = b := by
  by_contra hn
  obtain ⟨z, _, hu⟩ := hLine a b hn
  exact hlm ((hu l ⟨hal, hbl⟩).trans (hu m ⟨ham, hbm⟩).symm)

noncomputable def tagL {N : ℕ} (b : ℕ → (Fin N → Bool) → Bool) (h : ℕ) : Option (Fin N) := by
  classical
  exact if e : ∃ l, b h (atom l) = true ∧ ∀ m, b h (atom m) = true → m = l
    then some (Classical.choose e) else none

noncomputable def tagR {N : ℕ} (a : ℕ → (Fin N → Bool) → Bool) (h : ℕ) : Option (Fin N) := by
  classical
  exact if e : ∃ p, a h (atom p) = true then some (Classical.choose e) else none

lemma tagL_spec {N : ℕ} {b : ℕ → (Fin N → Bool) → Bool} {h : ℕ} {l : Fin N}
    (e : tagL b h = some l) : b h (atom l) = true ∧ ∀ m, b h (atom m) = true → m = l := by
  classical
  unfold tagL at e
  split at e
  next hex =>
    have eq : Classical.choose hex = l := Option.some.inj e
    simpa only [eq] using Classical.choose_spec hex
  next => contradiction

lemma tagL_other {N : ℕ} {b : ℕ → (Fin N → Bool) → Bool} {h : ℕ} {l : Fin N}
    (e : tagL b h = none) (hl : b h (atom l) = true) : ∃ m, m ≠ l ∧ b h (atom m) = true := by
  classical
  unfold tagL at e
  split at e
  next => contradiction
  next hex =>
    by_contra hn
    apply hex
    refine ⟨l, hl, ?_⟩
    intro m hm
    by_contra hne
    exact hn ⟨m, hne, hm⟩

lemma tagR_spec {N : ℕ} {a : ℕ → (Fin N → Bool) → Bool} {h : ℕ} {p : Fin N}
    (e : tagR a h = some p) : a h (atom p) = true := by
  classical
  unfold tagR at e
  split at e
  next hex =>
    have eq : Classical.choose hex = p := Option.some.inj e
    simpa only [eq] using Classical.choose_spec hex
  next => contradiction

lemma tagR_exists {N : ℕ} {a : ℕ → (Fin N → Bool) → Bool} {h : ℕ}
    (hex : ∃ p : Fin N, a h (atom p) = true) : ∃ p, tagR a h = some p := by
  classical
  exact ⟨Classical.choose hex, by simp [tagR, dite_eq_left hex]⟩

lemma split_port {N : ℕ} {I : Fin N → Fin N → Prop}
    {a b : ℕ → (Fin N → Bool) → Bool} {h : ℕ} {p l : Fin N}
    (hLine : ∀ u v, u ≠ v → ∃! j, I u j ∧ I v j)
    (hSafe : ∀ u j, a h (atom u) = true → b h (atom j) = true → I u j)
    (hap : a h (atom p) = true) (hbl : b h (atom l) = true) :
    tagL b h = some l ∨ (tagL b h = none ∧ tagR a h = some p) := by
  cases e : tagL b h with
  | some l' =>
    have eq := (tagL_spec e).2 l hbl
    exact Or.inl (congrArg some eq.symm)
  | none =>
    obtain ⟨m, hml, hbm⟩ := tagL_other e hbl
    obtain ⟨p', hp'⟩ := tagR_exists (a := a) ⟨p, hap⟩
    have ha' := tagR_spec hp'
    have eq := no_rectangle hLine hml (hSafe p' m ha' hbm) (hSafe p' l ha' hbl)
      (hSafe p m hap hbm) (hSafe p l hap hbl)
    exact Or.inr ⟨rfl, hp'.trans (congrArg some eq)⟩

end LMeta1720Math

namespace LMeta1720Math

lemma binary_mono {C : Circuit} (h : Binary C) : Monotone2 C := by
  intro g hg
  obtain ⟨hop, har⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, har.le⟩

lemma binary_project (N : ℕ) (C : Circuit) (h : Binary C) :
    Binary (LMeta1720Extract.project N C) := by
  intro g hg
  exact ⟨(LMeta1720Extract.project_monotone2 N C (binary_mono h) g hg).1,
    LMeta1720Extract.project_exact_two N C (fun g hg => (h g hg).2) g hg⟩

lemma grouped {N : ℕ} (C : Circuit) (s : Finset ℕ) (wire : ℕ → ℕ)
    (tag : ℕ → Option (Fin N)) (h : Binary C) (hBack : ReadsBack N C) :
    ∃ (D : Circuit) (out : Fin N → ℕ), Binary D ∧ ReadsBack N D ∧ D.size ≤ C.size + s.card ∧
      ∀ (x : Fin N → Bool) (p : Fin N),
        (D.wires (List.ofFn x)).getD (out p) false = true ↔
          ∃ i ∈ s, tag i = some p ∧ (C.wires (List.ofFn x)).getD (wire i) false = true := by
  classical
  obtain ⟨D, out, ⟨extra, hD, hExtra⟩, _, hB, hsz, hsem⟩ :=
    LMeta1720Aggregate.aggregateWithPrefix C s wire tag (binary_mono h) hBack
  refine ⟨D, out, ?_, hB, hsz, fun x p => ?_⟩
  · intro g hg
    rw [hD, List.mem_append] at hg
    rcases hg with hg | hg
    · exact h g hg
    · exact ⟨Or.inr (hExtra g hg).1, (hExtra g hg).2⟩
  · rw [hsem x p, decide_eq_true_eq]

end LMeta1720Math

end PEqualNP.Outside.L_meta_1720_aux

open PEqualNP.Outside.L_meta_1720_aux PEqualNP.Outside.L_meta_1720_aux.LMeta1720Math
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1720 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true) := by
  classical
  intro hFlag hTrans q N k I _ C hq hN hLine hUnique hk hBin hBack hKM hComplete hSound
  have sound (x y : Fin N → Bool)
      (hy : (Finset.univ.filter (fun j => y j = true)).card ≤ k)
      (ht : accept C x y = true) : ∃ p l, I p l ∧ x p = true ∧ y l = true := by
    by_contra hnone
    have hf := hSound (Fin.append x y) (by simpa only [Fin.append_right] using hy)
      (by simpa only [Fin.append_left, Fin.append_right] using hnone)
    exact Bool.false_ne_true (hf.symm.trans ht)
  have onInc (p l : Fin N) (h : I p l) : accept C (atom p) (atom l) = true := by
    rw [accept, atom_append]
    exact hComplete p l h
  have onlyInc (p l : Fin N) (h : accept C (atom p) (atom l) = true) : I p l := by
    obtain ⟨a, b, hi, ha, hb⟩ := sound (atom p) (atom l) (by simpa [atom_card] using hk) h
    simpa only [atom_true.mp ha, atom_true.mp hb] using hi
  let zero : Fin N → Bool := fun _ => false
  have zeroY (x : Fin N → Bool) : accept C x zero = false := by
    cases h : accept C x zero with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, _, hc⟩ := sound x zero (by simp [zero]) h
      cases hc
  have zeroX (l : Fin N) : accept C zero (atom l) = false := by
    cases h : accept C zero (atom l) with
    | false => rfl
    | true =>
      obtain ⟨_, _, _, hc, _⟩ := sound zero (atom l) (by simpa [atom_card] using hk) h
      cases hc
  have hEdge : ∃ p l, I p l := by
    let l : Fin N := ⟨0, by omega⟩
    have hf := hLine l
    have hne : (Finset.univ.filter (fun p => I p l)).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, l, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨p₀, l₀, hi₀⟩ := hEdge
  have hi := onInc p₀ l₀ hi₀
  have hInd := (hFlag N C hBin hBack hKM).1
  have hPosR : 0 < dr N C C.output := by
    by_cases hz : dr N C C.output = 0
    · have e := (hInd C.output (atom p₀) (atom p₀) (atom l₀) zero).1 hz
      change accept C (atom p₀) (atom l₀) = accept C (atom p₀) zero at e
      rw [hi, zeroY] at e
      cases e
    · exact Nat.pos_of_ne_zero hz
  have hPosL : 0 < dl N C C.output := by
    by_cases hz : dl N C C.output = 0
    · have e := (hInd C.output (atom p₀) zero (atom l₀) (atom l₀)).2.1 hz
      change accept C (atom p₀) (atom l₀) = accept C zero (atom l₀) at e
      rw [hi, zeroX] at e
      cases e
    · exact Nat.pos_of_ne_zero hz
  obtain ⟨U, ph, H, ⟨hUBin, hUBack⟩, hUcost, _, hRep⟩ :=
    hTrans N C hBin hBack hKM hPosL hPosR
  rw [pureL_ncard N C, mixed_ncard N C] at hUcost
  have rep (x y : Fin N → Bool) : accept C x y = true ↔
      ∃ h ∈ ports N C, flag (N := N) C h y = true ∧ (h ∈ H ∨ coeff U ph h x = true) := by
    have h := hRep x y
    have hz : circuitFun (N + N) C (Fin.append x (fun _ : Fin N => false)) = false := zeroY x
    rw [hz] at h
    simp only [Bool.false_eq_true, false_or] at h
    constructor
    · intro ht
      obtain ⟨i, hf, hb, hc⟩ := h.mp ht
      exact ⟨i, mem_ports.mpr hf, hb, hc⟩
    · rintro ⟨i, hf, hb, hc⟩
      exact h.mpr ⟨i, mem_ports.mp hf, hb, hc⟩
  have pair (h : ℕ) (hh : h ∈ ports N C) (x y : Fin N → Bool)
      (ha : coeff U ph h x = true) (hb : flag (N := N) C h y = true) : accept C x y = true :=
    (rep x y).mpr ⟨h, hh, hb, Or.inr ha⟩
  have notConst (h : ℕ) (hh : h ∈ ports N C) (l : Fin N) (hb : flag (N := N) C h (atom l) = true) : h ∉ H := by
    intro hm
    have ht := (rep zero (atom l)).mpr ⟨h, hh, hb, Or.inl hm⟩
    rw [zeroX l] at ht
    cases ht
  let V := LMeta1720Extract.project N C
  let remap := LMeta1720Extract.remap N C
  have hVBin : Binary V := binary_project N C hBin
  have hVBack : ReadsBack N V := LMeta1720Extract.project_readsBack N C hBack
  have hVcost : V.size = (pureR N C).card := LMeta1720Extract.project_size N C
  have hProj (h : ℕ) (hh : h ∈ ports N C) (y : Fin N → Bool) :
      coeff V remap h y = flag (N := N) C h y :=
    LMeta1720Extract.project_wires N C hBack zero y (port_valid hBack hh) (mem_ports.mp hh).1
  let lefts := (ports N C).filter (fun h => tagL (flag (N := N) C) h ≠ none)
  let rights := (ports N C).filter (fun h => tagL (flag (N := N) C) h = none)
  have hParts : lefts.card + rights.card = (ports N C).card := by
    simpa only [lefts, rights, not_not] using
      Finset.card_filter_add_card_filter_not (s := ports N C) (fun h => tagL (flag (N := N) C) h ≠ none)
  have pBound := ports_bound N C hBin
  obtain ⟨X, ps, hXBin, hXBack, hXcost, hXsem⟩ := grouped U lefts ph (tagL (flag (N := N) C)) hUBin hUBack
  obtain ⟨Y, rh, hYBin, hYBack, hYcost, hYsem⟩ := grouped V rights remap (tagR (coeff U ph)) hVBin hVBack
  refine ⟨X, Y, ps, rh, ⟨hXBin, hXBack⟩, ⟨hYBin, hYBack⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hBudget := gate_budget N C
    omega
  · intro l p h
    obtain ⟨i, hs, hl, ha⟩ := (hXsem (atom p) l).mp h
    have hh := (Finset.mem_filter.mp hs).1
    exact onlyInc p l (pair i hh (atom p) (atom l) ha (tagL_spec hl).1)
  · intro l x hx
    cases e : (X.wires (List.ofFn x)).getD (ps l) false with
    | false => rfl
    | true =>
      obtain ⟨i, hs, hl, ha⟩ := (hXsem x l).mp e
      have hh := (Finset.mem_filter.mp hs).1
      obtain ⟨p, l', hi', hp, hl'⟩ := sound x (atom l) (by simpa [atom_card] using hk)
        (pair i hh x (atom l) ha (tagL_spec hl).1)
      have el := atom_true.mp hl'
      rw [el] at hi'
      rw [hx p hi'] at hp
      cases hp
  · intro p l h
    obtain ⟨i, hs, hp, hb⟩ := (hYsem (atom l) p).mp h
    have hh := (Finset.mem_filter.mp hs).1
    exact onlyInc p l (pair i hh (atom p) (atom l) (tagR_spec hp) ((hProj i hh (atom l)).symm.trans hb))
  · intro p y hy hyoff
    cases e : (Y.wires (List.ofFn y)).getD (rh p) false with
    | false => rfl
    | true =>
      obtain ⟨i, hs, hp, hb⟩ := (hYsem y p).mp e
      have hh := (Finset.mem_filter.mp hs).1
      obtain ⟨p', l, hi', hp', hl⟩ := sound (atom p) y hy
        (pair i hh (atom p) y (tagR_spec hp) ((hProj i hh y).symm.trans hb))
      rw [atom_true.mp hp'] at hi'
      rw [hyoff l hi'] at hl
      cases hl
  · intro p l hp
    obtain ⟨i, hh, hb, hc⟩ := (rep (atom p) (atom l)).mp (onInc p l hp)
    have ha : coeff U ph i (atom p) = true := hc.resolve_left (notConst i hh l hb)
    have hSafe (u j : Fin N) (hau : coeff U ph i (atom u) = true) (hbj : flag (N := N) C i (atom j) = true) :
        I u j := onlyInc u j (pair i hh (atom u) (atom j) hau hbj)
    rcases split_port hUnique hSafe ha hb with hl | ⟨hl, hp'⟩
    · exact Or.inl ((hXsem (atom p) l).mpr ⟨i,
        Finset.mem_filter.mpr ⟨hh, by rw [hl]; nofun⟩, hl, ha⟩)
    · exact Or.inr ((hYsem (atom l) p).mpr ⟨i,
        Finset.mem_filter.mpr ⟨hh, hl⟩, hp', (hProj i hh (atom l)).trans hb⟩)
