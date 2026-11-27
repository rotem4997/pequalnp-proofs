import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17261
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def live : List Gate → ℕ → ℕ → Finset ℕ
  | [], n, o => if o < n then {o} else ∅
  | g :: gs, n, o =>
    let t := live gs (n+1) o
    if n ∈ t then (t.erase n) ∪ (g.inputs.toFinset.filter (· < n)) else t

private theorem live_lt (gs : List Gate) (n o : ℕ) :
    ∀ i ∈ live gs n o, i < n := by
  induction gs generalizing n with
  | nil =>
    intro i hi
    by_cases h : o < n <;> simp_all [live]
  | cons g gs ih =>
    intro i hi
    by_cases h : n ∈ live gs (n+1) o
    · simp only [live, ite_eq_left h, Finset.mem_union, Finset.mem_erase, Finset.mem_filter] at hi
      rcases hi with ⟨hne, hi⟩ | ⟨_, hi⟩
      · have := ih (n+1) i hi
        omega
      · exact hi
    · simp only [live, ite_eq_right h] at hi
      have := ih (n+1) i hi
      by_contra hn
      have : i = n := by omega
      exact h (this ▸ hi)

private theorem live_card (gs : List Gate) (n o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) : (live gs n o).card ≤ gs.length + 1 := by
  induction gs generalizing n with
  | nil => by_cases ho : o < n <;> simp [live, ho]
  | cons g gs ih =>
    have ht := ih (n+1) (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hg := h g (List.mem_cons_self ..)
    by_cases he : n ∈ live gs (n+1) o
    · simp only [live, ite_eq_left he, List.length_cons]
      have hu := Finset.card_union_le ((live gs (n+1) o).erase n)
        (g.inputs.toFinset.filter (· < n))
      have hz := Finset.card_erase_add_one he
      have hf := Finset.card_le_card (Finset.filter_subset (· < n) g.inputs.toFinset)
      have hl := List.toFinset_card_le g.inputs
      omega
    · simp only [live, ite_eq_right he, List.length_cons]
      omega

private def advance (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getD_missing {x : List Bool} {i : ℕ} (h : x.length ≤ i) :
    x.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem getD_advance_lt (g : Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (advance g x).getD i false = x.getD i false := by
  simp [advance, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_advance_eq (g : Gate) (x : List Bool) :
    (advance g x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  simp [advance, List.getD_eq_getElem?_getD]

private theorem eval_agree (gs : List Gate) (n o : ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ live gs n o, x.getD i false = y.getD i false) :
    (Circuit.mk gs o).eval x = (Circuit.mk gs o).eval y := by
  induction gs generalizing n x y with
  | nil =>
    change x.getD o false = y.getD o false
    by_cases ho : o < n
    · exact h o (by simp [live, ho])
    · rw [getD_missing (by omega : x.length ≤ o), getD_missing (by omega : y.length ≤ o)]
  | cons g gs ih =>
    change (Circuit.mk gs o).eval (advance g x) = (Circuit.mk gs o).eval (advance g y)
    apply ih (n+1) (advance g x) (advance g y) (by simp [advance,hx]) (by simp [advance,hy])
    intro i hi
    have hlt := live_lt gs (n+1) o i hi
    by_cases he : i = n
    · subst i

      rw [show (advance g x).getD n false = _ by simpa only [hx] using getD_advance_eq g x]
      rw [show (advance g y).getD n false = _ by simpa only [hy] using getD_advance_eq g y]
      congr 1
      apply List.map_congr_left
      intro j hj
      by_cases hjn : j < n
      · exact h j (by simp [live, hi, hj, hjn])
      · rw [getD_missing (by omega : x.length ≤ j), getD_missing (by omega : y.length ≤ j)]
    · rw [getD_advance_lt _ _ _ (by omega), getD_advance_lt _ _ _ (by omega)]
      apply h i
      by_cases hn : n ∈ live gs (n+1) o <;> simp [live, hn, he, hi]

private theorem advance_len (g : Gate) (x : List Bool) :
    (advance g x).length = x.length + 1 := by simp [advance]

private def renameWire (n m : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then σ i else m + (i - n)

private def renGate (n m : ℕ) (σ : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n m σ)⟩

private def foldW (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => advance g w) x

private theorem foldW_append (g : Gate) (gs : List Gate) (x : List Bool) :
    foldW (gs ++ [g]) x = advance g (foldW gs x) := by simp [foldW]

private theorem foldW_len (gs : List Gate) (x : List Bool) :
    (foldW gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [foldW]
  | append_singleton gs g ih =>
    rw [foldW_append, advance_len, ih]
    simp
    omega

private theorem rename_values (gs : List Gate) (x y : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i < x.length, σ i < y.length ∨ y.length + gs.length ≤ σ i)
    (h : ∀ i < x.length, x.getD i false = y.getD (σ i) false) :
    ∀ i, (foldW gs x).getD i false =
      (foldW (gs.map (renGate x.length y.length σ)) y).getD
        (renameWire x.length y.length σ i) false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    change x.getD i false = y.getD (renameWire x.length y.length σ i) false
    by_cases hi : i < x.length
    · simpa only [renameWire, ite_eq_left hi] using h i hi
    · rw [renameWire, ite_eq_right hi, getD_missing (by omega : x.length ≤ i),
        getD_missing (Nat.le_add_right ..)]
  | append_singleton gs g ih =>
    let gx := foldW gs x
    let gy := foldW (gs.map (renGate x.length y.length σ)) y
    let k := x.length + gs.length
    let l := y.length + gs.length
    let r := renameWire x.length y.length σ
    have hgx : gx.length = k := foldW_len _ _
    have hgy : gy.length = l := by simp [gy, l, foldW_len]
    have hσ' (i : ℕ) (hi : i < x.length) : σ i < y.length ∨ y.length + gs.length ≤ σ i := by
      rcases hσ i hi with h | h
      · exact Or.inl h
      · exact Or.inr (by simp at h; omega)
    have H : ∀ i, gx.getD i false = gy.getD (r i) false := ih hσ'
    have hgate : g.op.eval (g.inputs.map (fun i => gx.getD i false)) =
        (renGate x.length y.length σ g).op.eval
          ((renGate x.length y.length σ g).inputs.map (fun i => gy.getD i false)) := by
      simp only [renGate, List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left (fun i _ => H i)
    intro i
    rw [foldW_append, List.map_append, List.map_singleton, foldW_append]
    change (advance g gx).getD i false =
      (advance (renGate x.length y.length σ g) gy).getD (r i) false
    by_cases hix : i < x.length
    · have hr : r i = σ i := by simp [r, renameWire, hix]
      rw [getD_advance_lt _ _ _ (by omega)]
      rcases hσ i hix with hlo | hhi
      · rw [getD_advance_lt _ _ _ (by omega)]
        exact H i
      · have hh : (advance (renGate x.length y.length σ g) gy).length ≤ r i := by
          rw [advance_len]
          simp at hhi
          omega
        rw [getD_missing hh, H i, getD_missing (Nat.le_trans (by rw [advance_len]; omega) hh : gy.length ≤ r i)]
    · have hr : r i = y.length + (i - x.length) := by simp [r, renameWire, hix]
      rcases lt_trichotomy i k with hk | hk | hk
      · rw [getD_advance_lt _ _ _ (by omega), getD_advance_lt _ _ _ (by omega)]
        exact H i
      · have hrk : r i = gy.length := by omega
        have hik : i = gx.length := by omega
        rw [hik, getD_advance_eq]
        have hrel : r gx.length = gy.length := by rw [← hik, hrk]
        rw [hrel, getD_advance_eq]
        exact hgate
      · rw [getD_missing (by rw [advance_len]; omega), getD_missing (by rw [advance_len]; omega)]

private theorem renamed_fan (gs : List Gate) (n m : ℕ) (σ : ℕ → ℕ) (o : ℕ)
    (h : FanInTwo ⟨gs, o⟩) : FanInTwo ⟨gs.map (renGate n m σ), renameWire n m σ o⟩ := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [renGate] using h q hq

private theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

private theorem sorted_getD {l : List ℕ} (h : l.Pairwise (· < ·)) (d i j : ℕ)
    (hij : i < j) (hj : j < l.length) : l.getD i d < l.getD j d := by
  have hi : i < l.length := hij.trans hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    using (List.pairwise_iff_getElem.mp h i j hi hj hij)

private theorem getD_of_mem {l : List ℕ} {w : ℕ} (hw : w ∈ l) (d : ℕ) :
    l.getD (l.idxOf w) d = w := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_idxOf hw]

private theorem main (n a b : ℕ) (A B : List (Fin n → Bool)) (C : Circuit)
    (hAB : A ⊆ B) (hC : FanInTwo C) (hs : C.size ≤ a+b) :
    ∃ (D : Circuit) (inputs : Fin (b+1) → Fin (B.length+a+1)) (F : (Fin (b+1) → Bool) → Bool),
      FanInTwo D ∧ D.size ≤ a ∧ HasCircuitSize (b+1) F b ∧
      (∀ i j, i < j → inputs i < inputs j ∨ inputs i = Fin.last (B.length+a) ∧
        inputs j = Fin.last (B.length+a)) ∧
      ∀ x, F (fun j => (D.wires (B.map fun f => f x)).getD (inputs j).val false) =
        C.eval (A.map fun f => f x) := by
  classical
  let gs := C.gates.take a
  let ts := C.gates.drop a
  have hgs : gs.length ≤ a := by simp [gs]
  have hts : ts.length ≤ b := by
    change C.gates.length ≤ a+b at hs
    simp [ts]
    omega
  have hsplit : gs ++ ts = C.gates := List.take_append_drop a C.gates
  let p (i : ℕ) : ℕ := if hi : i < A.length then B.idxOf A[i] else B.length
  have p_lt (i : ℕ) (hi : i < A.length) : p i < B.length := by
    simp only [p, dite_eq_left hi]
    exact List.idxOf_lt_length_of_mem (hAB (List.getElem_mem hi))
  let k := A.length+gs.length
  let m := B.length+gs.length
  let cap := B.length+a
  let r := renameWire A.length B.length p
  have r_lt (i : ℕ) (hi : i < k) : r i < m := by
    by_cases h : i < A.length
    · simpa only [r, renameWire, ite_eq_left h] using (p_lt i h).trans_le (Nat.le_add_right ..)
    · simp only [r, renameWire, ite_eq_right h]
      dsimp [k, m] at hi ⊢
      omega
  let S := (live ts k C.output).image r
  let wires := S.sort
  have hwire_len : wires.length ≤ b+1 := by
    rw [Finset.length_sort]
    exact (Finset.card_image_le.trans (live_card ts k C.output
      (fun g hg => (hC g (List.mem_of_mem_drop hg)).2))).trans (by omega)
  have hwsmall (w : ℕ) (hw : w ∈ wires) : w < m := by
    have hS : w ∈ S := by simpa [wires] using hw
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hS
    rw [← he]
    exact r_lt i (live_lt ts k C.output i hi)
  have hmcap : m ≤ cap := by dsimp [m, cap]; omega
  let lookup (i : ℕ) : ℕ := wires.getD i cap
  have lookup_lt (i : ℕ) (hi : i < wires.length) : lookup i < m := by
    have ee : lookup i = wires[i] := by
      simp [lookup, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [ee]
    exact hwsmall _ (List.getElem_mem hi)
  have lookup_pad (i : ℕ) (hi : wires.length ≤ i) : lookup i = cap := by
    simp [lookup, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have lookup_bound (i : ℕ) : lookup i < cap+1 := by
    by_cases hi : i < wires.length
    · exact (lookup_lt i hi).trans_le (by omega)
    · rw [lookup_pad i (by omega)]
      omega
  let args (j : Fin (b+1)) : Fin (cap+1) := ⟨lookup j.val, lookup_bound _⟩
  let rank (i : ℕ) : ℕ := if r i ∈ wires then wires.idxOf (r i) else b+1+ts.length
  have rank_bounds (i : ℕ) : rank i < b+1 ∨ b+1+ts.length ≤ rank i := by
    by_cases hi : r i ∈ wires
    · simp only [rank, ite_eq_left hi]
      exact Or.inl ((List.idxOf_lt_length_of_mem hi).trans_le hwire_len)
    · simp [rank, hi]
  let D : Circuit := ⟨gs.map (renGate A.length B.length p), cap⟩
  let E : Circuit := ⟨ts.map (renGate k (b+1) rank), renameWire k (b+1) rank C.output⟩
  let F := circuitFun (b+1) E
  have fanPrefix : FanInTwo ⟨gs, C.output⟩ := fun g hg => hC g (List.mem_of_mem_take hg)
  have fanTail : FanInTwo ⟨ts, C.output⟩ := fun g hg => hC g (List.mem_of_mem_drop hg)
  refine ⟨D, args, F, ?_, ?_, ?_, ?_, ?_⟩
  · exact renamed_fan gs _ _ p _ fanPrefix
  · simpa [D, Circuit.size] using hgs
  · exact ⟨E, renamed_fan ts _ _ rank _ fanTail, by simpa [E, Circuit.size] using hts, fun _ => rfl⟩
  · intro i j hij
    change lookup i.val < lookup j.val ∨ _ ∧ _
    by_cases hj : j.val < wires.length
    · left

      have hslt : wires.SortedLT := List.sortedLT_iff_nodup_and_sortedLE.mpr
        ⟨Finset.sort_nodup _ _, (Finset.pairwise_sort _ _).sortedLE⟩
      exact sorted_getD hslt.pairwise _ _ _ hij hj
    · rw [lookup_pad j.val (by omega)]
      by_cases hi : i.val < wires.length
      · exact Or.inl ((lookup_lt i.val hi).trans_le hmcap)
      · right
        constructor <;> apply Fin.ext
        · exact lookup_pad i.val (by omega)
        · exact lookup_pad j.val (by omega)
  · intro x
    let X := A.map fun f => f x
    let Y := B.map fun f => f x
    have lenX : X.length = A.length := by simp [X]
    have lenY : Y.length = B.length := by simp [Y]
    let WX := foldW gs X
    let WY := D.wires Y
    have lenWX : WX.length = k := by simp [WX, foldW_len, lenX, k]
    have lenWY : WY.length = m := by
      change (foldW (gs.map (renGate A.length B.length p)) Y).length = m
      simp [foldW_len, lenY, m]
    have agree (i : ℕ) (hi : i < X.length) : X.getD i false = Y.getD (p i) false := by
      have hA : i < A.length := by omega
      have hB : A[i] ∈ B := hAB (List.getElem_mem hA)
      simp only [p, dite_eq_left hA, X, Y, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hA, List.getElem?_idxOf hB, Option.map_some, Option.getD_some]
    have wEqual (i : ℕ) : WX.getD i false = WY.getD (r i) false := by
      have hbound (j : ℕ) (hj : j < X.length) : p j < Y.length ∨ Y.length+gs.length ≤ p j := by
        exact Or.inl (lenY.symm ▸ p_lt j (by omega))
      change (foldW gs X).getD i false =
        (foldW (gs.map (renGate A.length B.length p)) Y).getD (renameWire A.length B.length p i) false
      simpa only [lenX, lenY] using rename_values gs X Y p hbound agree i
    let V := List.ofFn fun j : Fin (b+1) => WY.getD (lookup j.val) false
    let W := List.ofFn fun i : Fin k => V.getD (rank i.val) false
    have lenV : V.length = b+1 := by simp [V]
    have lenW : W.length = k := by simp [W]
    have hinput (i : ℕ) (hi : i < W.length) : W.getD i false = V.getD (rank i) false := by
      exact ofFn_getD _ (⟨i, by omega⟩ : Fin k)
    have matchLive (i : ℕ) (hi : i ∈ live ts k C.output) :
        W.getD i false = WX.getD i false := by
      have hS : r i ∈ S := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have hrw : r i ∈ wires := by simpa [wires] using hS
      have hir : rank i = wires.idxOf (r i) := by simp [rank, hrw]
      have hj : rank i < b+1 := hir ▸ (List.idxOf_lt_length_of_mem hrw).trans_le hwire_len
      have htt : i < k := live_lt ts k C.output i hi
      rw [hinput i (by omega), ofFn_getD _ (⟨rank i, hj⟩ : Fin (b+1))]
      dsimp [lookup]
      rw [hir, getD_of_mem hrw, wEqual]
    have hTail (i : ℕ) (hi : i < W.length) :
        rank i < V.length ∨ V.length + ts.length ≤ rank i := by
      simpa only [lenV] using rank_bounds i
    have evalTail :
        (Circuit.mk ts C.output).eval W = E.eval V := by
      change (foldW ts W).getD C.output false =
        (foldW (ts.map (renGate k (b+1) rank)) V).getD (renameWire k (b+1) rank C.output) false
      simpa only [lenW, lenV] using rename_values ts W V rank hTail hinput C.output
    change E.eval V = C.eval X
    rw [← evalTail, eval_agree ts k C.output W WX lenW lenWX matchLive]
    change (ts.foldl (fun w g => advance g w) (gs.foldl (fun w g => advance g w) X)).getD C.output false = _
    rw [← List.foldl_append, hsplit]
    rfl

end PEqualNP.Outside.L_meta_17261

open PEqualNP.Outside.L_meta_17261

theorem PEqualNP.Outside.L_meta_17261 : (∀ (x1 x2 x3 : ℕ) (x4 x5 : List (Fin x1 → Bool)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x5 → PEqualNP.MetaComplexity.FanInTwo x6 → x6.size ≤ x2 + x3 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : Fin (x3 + (1 : ℕ)) → Fin (x5.length + x2 + (1 : ℕ))) (x12 : (Fin (x3 + (1 : ℕ)) → Bool) → Bool), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x10.size ≤ x2 ∧ PEqualNP.MetaComplexity.HasCircuitSize (x3 + (1 : ℕ)) x12 x3 ∧ (∀ (x13 x14 : Fin (x3 + (1 : ℕ))), x13 < x14 → x11 x13 < x11 x14 ∨ x11 x13 = Fin.last (x5.length + x2) ∧ x11 x14 = Fin.last (x5.length + x2)) ∧ ∀ (x13 : Fin x1), (x12 fun (x14 : Fin (x3 + (1 : ℕ))) => (x10.wires (List.map (fun (x15 : Fin x1 → Bool) => x15 x13) x5)).getD (↑(x11 x14)) Bool.false) = x6.eval (List.map (fun (x14 : Fin x1 → Bool) => x14 x13) x4)) := by
  exact main

