import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4235

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_len : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length
  | [], w => by simp
  | g :: gs, w => by
    rw [List.foldl_cons, fold_len gs]
    simp [step]
    omega

theorem fold_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false
  | [], w, i, _ => by simp
  | g :: gs, w, i, h => by
    rw [List.foldl_cons, fold_pre gs (step w g) i (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ h]

theorem wire_gate (C : Circuit) (z : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires z).getD (z.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map
        fun i => ((C.gates.take k).foldl step z).getD i false) ∧
    ∀ i < z.length + k, (C.wires z).getD i false = ((C.gates.take k).foldl step z).getD i false := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk]
    simp
  have hw : C.wires z =
      (C.gates.drop (k + 1)).foldl step (step ((C.gates.take k).foldl step z) C.gates[k]) := by
    show C.gates.foldl step z = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hPlen : ((C.gates.take k).foldl step z).length = z.length + k := by
    rw [fold_len]
    simp [List.length_take]
    omega
  constructor
  · rw [hw, fold_pre _ _ _ (by simp [step, hPlen])]
    simp only [step]
    rw [← hPlen]
    simp
  · intro i hi
    rw [hw, fold_pre _ _ _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ (by omega)]

theorem prefix_len (C : Circuit) (z : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.take k).foldl step z).length = z.length + k := by
  rw [fold_len]
  simp [List.length_take]
  omega

theorem wires_len (C : Circuit) (z : List Bool) : (C.wires z).length = z.length + C.gates.length :=
  fold_len C.gates z

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

/-- The earlier wires gate `w - n` reads. -/
def inp (C : Circuit) (n w : ℕ) : Finset ℕ := (gateAt C (w - n)).inputs.toFinset.filter (· < w)

theorem mem_inp {C : Circuit} {n w i : ℕ} : i ∈ inp C n w ↔ i ∈ (gateAt C (w - n)).inputs ∧ i < w := by
  simp [inp]

/-- The input wires in the cone of wire `w`. -/
def dep (C : Circuit) (n : ℕ) (w : ℕ) : Finset ℕ :=
  if w < n then {w} else if w < n + C.gates.length then
    (inp C n w).attach.biUnion (fun i => dep C n i.1) else ∅
termination_by w
decreasing_by exact (mem_inp.mp i.2).2

/-- The gates in the cone of wire `w`, itself included. -/
def gs (C : Circuit) (n : ℕ) (w : ℕ) : Finset ℕ :=
  if w < n then ∅ else if w < n + C.gates.length then
    insert (w - n) ((inp C n w).attach.biUnion (fun i => gs C n i.1)) else ∅
termination_by w
decreasing_by exact (mem_inp.mp i.2).2

theorem dep_lt {C : Circuit} {n w : ℕ} (h : w < n) : dep C n w = {w} := by
  rw [dep, if_pos h]

theorem dep_mid {C : Circuit} {n w : ℕ} (h1 : ¬ w < n) (h2 : w < n + C.gates.length) :
    dep C n w = (inp C n w).biUnion (dep C n) := by
  rw [dep, if_neg h1, if_pos h2]
  ext v
  simp

theorem dep_hi {C : Circuit} {n w : ℕ} (h1 : ¬ w < n) (h2 : ¬ w < n + C.gates.length) :
    dep C n w = ∅ := by
  rw [dep, if_neg h1, if_neg h2]

theorem gs_lt {C : Circuit} {n w : ℕ} (h : w < n) : gs C n w = ∅ := by
  rw [gs, if_pos h]

theorem gs_mid {C : Circuit} {n w : ℕ} (h1 : ¬ w < n) (h2 : w < n + C.gates.length) :
    gs C n w = insert (w - n) ((inp C n w).biUnion (gs C n)) := by
  rw [gs, if_neg h1, if_pos h2]
  ext v
  simp

theorem gs_hi {C : Circuit} {n w : ℕ} (h1 : ¬ w < n) (h2 : ¬ w < n + C.gates.length) :
    gs C n w = ∅ := by
  rw [gs, if_neg h1, if_neg h2]

theorem gs_bound (C : Circuit) (n : ℕ) : ∀ w, ∀ g ∈ gs C n w,
    n ≤ w ∧ g ≤ w - n ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro g hg
    by_cases h1 : w < n
    · rw [gs_lt h1] at hg
      simp at hg
    · by_cases h2 : w < n + C.gates.length
      · rw [gs_mid h1 h2] at hg
        rw [Finset.mem_insert, Finset.mem_biUnion] at hg
        rcases hg with rfl | ⟨i, hi, hgi⟩
        · omega
        · have hi2 := (mem_inp.mp hi).2
          have := ih i hi2 g hgi
          omega
      · rw [gs_hi h1 h2] at hg
        simp at hg

theorem gs_self {C : Circuit} {n w : ℕ} (hne : (gs C n w).Nonempty) : w - n ∈ gs C n w := by
  by_cases h1 : w < n
  · rw [gs_lt h1] at hne
    simp at hne
  · by_cases h2 : w < n + C.gates.length
    · rw [gs_mid h1 h2]
      exact Finset.mem_insert_self _ _
    · rw [gs_hi h1 h2] at hne
      simp at hne

theorem dep_sub_of_gs_empty {C : Circuit} {n w : ℕ} (h : gs C n w = ∅) : dep C n w ⊆ {w} := by
  by_cases h1 : w < n
  · rw [dep_lt h1]
  · by_cases h2 : w < n + C.gates.length
    · rw [gs_mid h1 h2] at h
      simp at h
    · rw [dep_hi h1 h2]
      exact Finset.empty_subset _

theorem inp_card {C : Circuit} {n w : ℕ} (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (h2 : w < n + C.gates.length) (h1 : ¬ w < n) : (inp C n w).card ≤ 2 := by
  have hk : w - n < C.gates.length := by omega
  calc (inp C n w).card ≤ (gateAt C (w - n)).inputs.toFinset.card := Finset.card_filter_le _ _
    _ ≤ (gateAt C (w - n)).inputs.length := List.toFinset_card_le _
    _ ≤ 2 := by
      rw [gateAt_eq C _ hk]
      exact hfan _ (List.getElem_mem hk)

theorem count (C : Circuit) (n : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ m, ∀ W : Finset ℕ, (W.biUnion (gs C n)).card = m →
      (W.biUnion (dep C n)).card ≤ m + W.card := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W hm
    by_cases hU : (W.biUnion (gs C n)).Nonempty
    · set U := W.biUnion (gs C n) with hUdef
      set g := U.max' hU with hgdef
      have hgU : g ∈ U := Finset.max'_mem U hU
      obtain ⟨w0, hw0W, hgw0⟩ := Finset.mem_biUnion.mp hgU
      obtain ⟨hnw0, hgle, hgs⟩ := gs_bound C n w0 g hgw0
      have hself : w0 - n ∈ gs C n w0 := gs_self ⟨g, hgw0⟩
      have hle2 : w0 - n ≤ g := Finset.le_max' U _ (Finset.mem_biUnion.mpr ⟨w0, hw0W, hself⟩)
      have hgeq : g = w0 - n := by omega
      have h1 : ¬ w0 < n := by omega
      have h2 : w0 < n + C.gates.length := by omega
      set W' := W.erase w0 ∪ inp C n w0 with hW'
      have hdep : W.biUnion (dep C n) ⊆ W'.biUnion (dep C n) := by
        intro v hv
        obtain ⟨u, huW, hvu⟩ := Finset.mem_biUnion.mp hv
        by_cases hu : u = w0
        · subst hu
          rw [dep_mid h1 h2] at hvu
          obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvu
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_union_right _ hi, hvi⟩
        · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hu, huW⟩), hvu⟩
      have hgsub : W'.biUnion (gs C n) ⊆ U.erase g := by
        intro h hh
        obtain ⟨u, huW', hhu⟩ := Finset.mem_biUnion.mp hh
        rcases Finset.mem_union.mp huW' with hu | hu
        · obtain ⟨hne, huW⟩ := Finset.mem_erase.mp hu
          have hU' : h ∈ U := Finset.mem_biUnion.mpr ⟨u, huW, hhu⟩
          refine Finset.mem_erase.mpr ⟨?_, hU'⟩
          intro hhg
          obtain ⟨hnu, hle, _⟩ := gs_bound C n u h hhu
          have hs' : u - n ∈ gs C n u := gs_self ⟨h, hhu⟩
          have : u - n ≤ g := Finset.le_max' U _ (Finset.mem_biUnion.mpr ⟨u, huW, hs'⟩)
          apply hne
          omega
        · have hilt := (mem_inp.mp hu).2
          have hgw0' : h ∈ gs C n w0 := by
            rw [gs_mid h1 h2]
            exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hhu⟩)
          have hU' : h ∈ U := Finset.mem_biUnion.mpr ⟨w0, hw0W, hgw0'⟩
          refine Finset.mem_erase.mpr ⟨?_, hU'⟩
          obtain ⟨hnu, hle, _⟩ := gs_bound C n u h hhu
          omega
      have hW'card : W'.card ≤ W.card + 1 := by
        calc W'.card ≤ (W.erase w0).card + (inp C n w0).card := Finset.card_union_le _ _
          _ ≤ (W.card - 1) + 2 := by
            rw [Finset.card_erase_of_mem hw0W]
            have := inp_card (n := n) hfan h2 h1
            omega
          _ ≤ W.card + 1 := by
            have : 0 < W.card := Finset.card_pos.mpr ⟨w0, hw0W⟩
            omega
      have hm' : (W'.biUnion (gs C n)).card < m := by
        have := Finset.card_le_card hgsub
        rw [Finset.card_erase_of_mem hgU] at this
        have : 0 < U.card := Finset.card_pos.mpr hU
        omega
      have := ih _ hm' W' rfl
      have := Finset.card_le_card hdep
      have := Finset.card_le_card hgsub
      rw [Finset.card_erase_of_mem hgU] at this
      omega
    · have hU : W.biUnion (gs C n) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hsub : W.biUnion (dep C n) ⊆ W := by
        intro v hv
        obtain ⟨u, huW, hvu⟩ := Finset.mem_biUnion.mp hv
        have hgu : gs C n u = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro h hh
          have : h ∈ W.biUnion (gs C n) := Finset.mem_biUnion.mpr ⟨u, huW, hh⟩
          rw [hU] at this
          simp at this
        have := dep_sub_of_gs_empty hgu hvu
        rw [Finset.mem_singleton] at this
        rw [this]
        exact huW
      have := Finset.card_le_card hsub
      omega

theorem sem (C : Circuit) (n : ℕ) (xs ys : Fin n → Bool) : ∀ w,
    (∀ i : Fin n, (i : ℕ) ∈ dep C n w → xs i = ys i) →
    (C.wires (List.ofFn xs)).getD w false = (C.wires (List.ofFn ys)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hag
    have hx : (List.ofFn xs).length = n := List.length_ofFn
    have hy : (List.ofFn ys).length = n := List.length_ofFn
    by_cases h1 : w < n
    · rw [show C.wires (List.ofFn xs) = C.gates.foldl step (List.ofFn xs) from rfl,
        show C.wires (List.ofFn ys) = C.gates.foldl step (List.ofFn ys) from rfl,
        fold_pre _ _ _ (by omega), fold_pre _ _ _ (by omega)]
      have := hag ⟨w, h1⟩ (by rw [dep_lt h1]; simp)
      simp [List.getD_eq_getElem?_getD, h1, this]
    · by_cases h2 : w < n + C.gates.length
      · have hk : w - n < C.gates.length := by omega
        obtain ⟨ax, bx⟩ := wire_gate C (List.ofFn xs) (w - n) hk
        obtain ⟨ay, b_y⟩ := wire_gate C (List.ofFn ys) (w - n) hk
        rw [hx] at ax bx
        rw [hy] at ay b_y
        have hw : w = n + (w - n) := by omega
        rw [hw, ax, ay]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hi2 : i < n + (w - n)
        · rw [← bx i hi2, ← b_y i hi2]
          apply ih i (by omega)
          intro t ht
          apply hag
          rw [dep_mid h1 h2]
          refine Finset.mem_biUnion.mpr ⟨i, ?_, ht⟩
          rw [mem_inp, gateAt_eq C _ hk]
          exact ⟨hi, by omega⟩
        · rw [List.getD_eq_default _ _ (by rw [prefix_len C _ _ hk, hx]; omega),
            List.getD_eq_default _ _ (by rw [prefix_len C _ _ hk, hy]; omega)]
      · rw [List.getD_eq_default _ _ (by rw [wires_len, hx]; omega),
          List.getD_eq_default _ _ (by rw [wires_len, hy]; omega)]

def verts {N : ℕ} (x7 : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  Finset.univ.filter fun v => ∃ e ∈ x7, v ∈ e

theorem peel {N : ℕ} (x9 : ℕ) : ∀ m, ∀ x7 : Finset (Sym2 (Fin N)), x7.card = m →
    ∃ x10 ⊆ x7, x7.card ≤ x9 * (verts x7).card + x10.card ∧
      ∀ v : Fin N, (x10.filter fun e => v ∈ e).card = 0 ∨ x9 < (x10.filter fun e => v ∈ e).card := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x7 hm
    by_cases hall : ∀ v : Fin N, (x7.filter fun e => v ∈ e).card = 0 ∨
        x9 < (x7.filter fun e => v ∈ e).card
    · exact ⟨x7, Finset.Subset.refl _, Nat.le_add_left _ _, hall⟩
    · push Not at hall
      obtain ⟨v, hv0, hvle⟩ := hall
      set x7' := x7.filter fun e => v ∉ e with hx7'
      have hsplit : (x7.filter fun e => v ∈ e).card + x7'.card = x7.card :=
        Finset.card_filter_add_card_filter_not _
      have hlt : x7'.card < m := by
        have : 0 < (x7.filter fun e => v ∈ e).card := Nat.pos_of_ne_zero hv0
        omega
      obtain ⟨x10, hsub, hc, hdeg⟩ := ih _ hlt x7' rfl
      refine ⟨x10, hsub.trans (Finset.filter_subset _ _), ?_, hdeg⟩
      have hV : verts x7' ⊆ (verts x7).erase v := by
        intro u hu
        simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨e, he, hue⟩ := hu
        rw [hx7', Finset.mem_filter] at he
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · rintro rfl
          exact he.2 hue
        · simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, he.1, hue⟩
      have hvmem : v ∈ verts x7 := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hv0)
        rw [Finset.mem_filter] at he
        simp only [verts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, he.1, he.2⟩
      have hVc : (verts x7').card + 1 ≤ (verts x7).card := by
        have := Finset.card_le_card hV
        rw [Finset.card_erase_of_mem hvmem] at this
        have : 0 < (verts x7).card := Finset.card_pos.mpr ⟨v, hvmem⟩
        omega
      have hmul : x9 * ((verts x7').card + 1) ≤ x9 * (verts x7).card := Nat.mul_le_mul_left _ hVc
      rw [mul_add, mul_one] at hmul
      omega

end PEqualNP.Outside.L_meta_4235

theorem PEqualNP.Outside.L_meta_4235 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x7 ⊆ x2.edgeFinset, ∀ (x9 : ℕ), ∃ x10 ⊆ x7, x7.card ≤ x9 * (x4.size + (1 : ℕ)) + x10.card ∧ ∀ (x11 : Fin x1), {x12 ∈ x10 | x11 ∈ x12}.card = (0 : ℕ) ∨ x9 < {x12 ∈ x10 | x11 ∈ x12}.card := by
  intro N G _ C hmono hfun x7 hx7 x9
  obtain ⟨x10, hsub, hc, hdeg⟩ := PEqualNP.Outside.L_meta_4235.peel x9 _ x7 rfl
  refine ⟨x10, hsub, ?_, hdeg⟩
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hmono g hg).2
  have hV : (PEqualNP.Outside.L_meta_4235.verts x7).card ≤ C.size + 1 := by
    have hsubdep : (PEqualNP.Outside.L_meta_4235.verts x7).map Fin.valEmbedding ⊆
        PEqualNP.Outside.L_meta_4235.dep C N C.output := by
      intro t ht
      rw [Finset.mem_map] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [PEqualNP.Outside.L_meta_4235.verts, Finset.mem_filter, Finset.mem_univ,
        true_and] at hv
      obtain ⟨e, he, hve⟩ := hv
      have heG : e ∈ G.edgeFinset := hx7 he
      have hadj : G.Adj v (Sym2.Mem.other hve) := by
        rw [SimpleGraph.mem_edgeFinset, ← Sym2.other_spec hve] at heG
        exact heG
      by_contra hnot
      have heq := PEqualNP.Outside.L_meta_4235.sem C N
        (fun i => decide (i = v ∨ i = Sym2.Mem.other hve)) (fun i => decide (i = Sym2.Mem.other hve))
        C.output (by
          intro i hi
          have hiv : i ≠ v := by
            rintro rfl
            exact hnot hi
          simp [hiv])
      have h1 := congrFun hfun (fun i => decide (i = v ∨ i = Sym2.Mem.other hve))
      have h2 := congrFun hfun (fun i => decide (i = Sym2.Mem.other hve))
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval] at h1 h2
      rw [heq, h2] at h1
      have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
          (fun i => decide (i = v ∨ i = Sym2.Mem.other hve)) = true := by
        simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
          exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
        exact ⟨v, Sym2.Mem.other hve, hadj, by simp, by simp⟩
      have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
          (fun i => decide (i = Sym2.Mem.other hve)) = false := by
        simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
          exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not, not_exists, not_and,
          decide_eq_true_eq]
        intro a b hab ha hb
        subst ha
        subst hb
        exact G.irrefl hab
      rw [hx, hy] at h1
      exact absurd h1 (by decide)
    have hcard := Finset.card_le_card hsubdep
    rw [Finset.card_map] at hcard
    have hc2 := PEqualNP.Outside.L_meta_4235.count C N hfan _ {C.output} rfl
    rw [Finset.singleton_biUnion, Finset.singleton_biUnion, Finset.card_singleton] at hc2
    have hgs : (PEqualNP.Outside.L_meta_4235.gs C N C.output).card ≤ C.size := by
      have hss : PEqualNP.Outside.L_meta_4235.gs C N C.output ⊆ Finset.range C.gates.length :=
        fun g hg => Finset.mem_range.mpr (PEqualNP.Outside.L_meta_4235.gs_bound C N _ g hg).2.2
      exact (Finset.card_le_card hss).trans (by simp [PEqualNP.CircuitLowerBounds.Circuit.size])
    omega
  calc x7.card ≤ x9 * (PEqualNP.Outside.L_meta_4235.verts x7).card + x10.card := hc
    _ ≤ x9 * (C.size + 1) + x10.card := by gcongr
