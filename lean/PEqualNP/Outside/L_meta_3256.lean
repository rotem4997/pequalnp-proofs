import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_3256
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this


theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _


def val (C : Circuit) (n : ℕ) (l : Fin n) (Z : Finset (Fin n)) (w : ℕ) : Bool :=
  (C.wires (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n)))).getD w false

theorem inc_len (n : ℕ) (Z Y : Finset (Fin n)) :
    (PEqualNP.GenericRejection.incidenceInput Z Y).length = n + n := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem val_mono (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (Z Z' : Finset (Fin n)) (h : Z ⊆ Z') (w : ℕ) :
    val C n l Z w = true → val C n l Z' w = true := by
  obtain ⟨hao, _, h2⟩ := hC
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  refine mono2 C.gates hleg _ _ (by rw [inc_len, inc_len]) ?_ w
  refine app_mono _ _ _ _ (by simp) ?_ (fun _ => id)
  exact ofFn_mono n _ _ (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; exact h hv)

theorem val_input (C : Circuit) (n : ℕ) (l : Fin n) (Z Z' : Finset (Fin n)) (w : ℕ)
    (hw : w < n + n) (hn : n ≤ w) : val C n l Z w = val C n l Z' w := by
  unfold val
  show (wf C.gates _).getD w false = (wf C.gates _).getD w false
  rw [wf_keep _ _ _ (by rw [inc_len]; exact hw), wf_keep _ _ _ (by rw [inc_len]; exact hw)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  simp

theorem val_point (C : Circuit) (n : ℕ) (l : Fin n) (p : Fin n) (w : ℕ)
    (hw : w < n) : val C n l {p} w = true → p.val = w := by
  unfold val
  show (wf C.gates _).getD w false = true → _
  rw [wf_keep _ _ _ (by rw [inc_len]; omega)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw]
  intro h
  simp at h
  rw [← h]

theorem val_gate (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (k : ℕ) (hk : k < C.size) :
    ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] ∧
      a < n + n + k ∧ b < n + n + k ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
      ∀ Z, val C n l Z (n + n + k) =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval [val C n l Z a, val C n l Z b] := by
  obtain ⟨hao, hrb, h2⟩ := hC
  have hk' : k < C.gates.length := hk
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk']
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hlt : ∀ i ∈ [a, b], i < n + n + k := by
    intro i hi
    have := hrb k hk' i
    rw [hG, hin] at this
    exact this hi
  refine ⟨a, b, by rw [hG, hin], hlt a (by simp), hlt b (by simp), by rw [hG]; exact hao _ hmem, ?_⟩
  intro Z
  have hlen := inc_len n Z ({l} : Finset (Fin n))
  have g1 := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n))) k hk'
  rw [hlen, hin] at g1
  unfold val
  show (wf C.gates _).getD (n + n + k) false = _
  rw [g1, hG]
  show _ = C.gates[k].op.eval [(wf C.gates _).getD a false, (wf C.gates _).getD b false]
  rw [wire_take C.gates _ k a (by rw [hlen]; exact hlt a (by simp)) (le_of_lt hk'),
    wire_take C.gates _ k b (by rw [hlen]; exact hlt b (by simp)) (le_of_lt hk')]
  simp

theorem graph_count {n : ℕ} (S : Finset ℕ) (f : ℕ → Sym2 (Fin n)) (X : Finset (Fin n))
    (hX : ∀ u ∈ X, ∀ v ∈ X, (SimpleGraph.fromEdgeSet (f '' (S : Set ℕ))).Reachable u v) :
    X.card ≤ S.card + 1 := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
  · simp
  set G := SimpleGraph.fromEdgeSet (f '' (S : Set ℕ)) with hG
  set c := G.connectedComponentMk u with hc
  have h1 := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hmem : ∀ x ∈ X, x ∈ c := by
    intro x hx
    exact (SimpleGraph.ConnectedComponent.sound (hX u hu x hx)).symm
  have h2 : X.card ≤ Nat.card c := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun x : X => (⟨x.1, hmem x.1 x.2⟩ : c)) ?_
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have h3 : Nat.card c.toSimpleGraph.edgeSet ≤ Nat.card G.edgeSet :=
    Nat.card_le_card_of_injective _
      (SimpleGraph.Hom.mapEdgeSet.injective c.toSimpleGraph_hom Subtype.val_injective)
  have h4 : Nat.card G.edgeSet ≤ S.card := by
    rw [Nat.card_coe_set_eq]
    calc G.edgeSet.ncard ≤ (f '' (S : Set ℕ)).ncard :=
          Set.ncard_le_ncard (by rw [hG, SimpleGraph.edgeSet_fromEdgeSet]; exact Set.sdiff_subset)
            ((S.finite_toSet).image f)
      _ ≤ (S : Set ℕ).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  omega

theorem reach (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (G : SimpleGraph (Fin n)) (Zb : Finset (Fin n))
    (hedge : ∀ k < C.size, ∀ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
      val C n l Zb (n + n + k) = false → ∀ u v : Fin n, u ≠ v →
      val C n l {u} a = true → val C n l {v} b = true →
      ∃ u' v', val C n l {u'} a = true ∧ val C n l {v'} b = true ∧ G.Reachable u' v') :
    ∀ w, w < n + n + C.size → val C n l Zb w = false → ∀ u v : Fin n,
      val C n l {u} w = true → val C n l {v} w = true → G.Reachable u v := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hgood u v hu hv
  by_cases h1 : w < n
  · have e1 := val_point C n l u w h1 hu
    have e2 := val_point C n l v w h1 hv
    have : u = v := Fin.ext (by omega)
    rw [this]
  by_cases h2 : w < n + n
  · rw [val_input C n l {u} Zb w h2 (by omega)] at hu
    rw [hu] at hgood
    exact absurd hgood (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + n + k := ⟨w - (n + n), by omega⟩
  have hk : k < C.size := by omega
  obtain ⟨a, b, hin, ha, hb, hop, hval⟩ := val_gate C n l hC k hk
  rw [hval] at hgood hu hv
  rcases hop with hop | hop
  · rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true,
      Bool.and_eq_false_iff] at hgood hu hv
    rcases hgood with hg | hg
    · exact ih a ha (by omega) hg u v hu.1 hv.1
    · exact ih b hb (by omega) hg u v hu.2 hv.2
  · have hop' := hop
    rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true,
      Bool.or_eq_false_iff] at hgood hu hv
    have hgw : val C n l Zb (n + n + k) = false := by
      rw [hval, hop]; simp [GateOp.eval, hgood.1, hgood.2]
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact ih a ha (by omega) hgood.1 u v hu hv
    · by_cases huv : u = v
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw u v huv hu hv
      exact ((ih a ha (by omega) hgood.1 u u' hu hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' v hv' hv)
    · by_cases huv : v = u
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw v u huv hv hu
      exact (((ih a ha (by omega) hgood.1 v u' hv hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' u hv' hu)).symm
    · exact ih b hb (by omega) hgood.2 u v hu hv

end PEqualNP.Outside.L_meta_3256

open PEqualNP.Outside.L_meta_3256 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C X l hC hout hacc hrej
  classical
  have hrej' : val C n l Xᶜ C.output = false := hrej
  have hacc' : ∀ p ∈ X, val C n l {p} C.output = true := hacc
  have hsub : ∀ w, val C n l Xᶜ w = false → ∀ p : Fin n, val C n l {p} w = true → p ∈ X := by
    intro w hw p hp
    by_contra hpX
    have := val_mono C n l hC {p} Xᶜ (by simpa using hpX) w hp
    rw [hw] at this
    exact absurd this (by simp)
  refine ⟨(Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true),
    ?_, ?_⟩
  · rcases X.eq_empty_or_nonempty with hX | ⟨p0, _⟩
    · rw [hX]; simp
    let A : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
    let B : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
    let f : ℕ → Sym2 (Fin n) := fun j =>
      if h : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A j) = true ∧ val C n l {v} (B j) = true
      then s(h.choose, h.choose_spec.choose) else s(p0, p0)
    apply graph_count _ f X
    intro u hu v hv
    refine reach C n l hC _ Xᶜ ?_ C.output hout hrej' u v (hacc' u hu) (hacc' v hv)
    intro k hk a b hin hop hgood u v huv hua hvb
    have hAk : A k = a := by simp [A, hin]
    have hBk : B k = b := by simp [B, hin]
    have hex : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A k) = true ∧ val C n l {v} (B k) = true :=
      ⟨u, v, huv, hAk ▸ hua, hBk ▸ hvb⟩
    obtain ⟨a', b', hin', _, _, _, hval⟩ := val_gate C n l hC k hk
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have hk9 : k ∈ (Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hgood, u, v, huv, ?_, ?_⟩
      · rw [hval, hop]; simp [GateOp.eval, hua]
      · rw [hval, hop]; simp [GateOp.eval, hvb]
    have hfk : f k = s(hex.choose, hex.choose_spec.choose) := by
      simp only [f, hex, dite_true]
    obtain ⟨hne, h1, h2⟩ := hex.choose_spec.choose_spec
    refine ⟨hex.choose, hex.choose_spec.choose, hAk ▸ h1, hBk ▸ h2, ?_⟩
    apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨k, hk9, hfk⟩, hne⟩
  · intro j hj
    obtain ⟨hjr, hop, hgood, p, q, hpq, hp, hq⟩ := Finset.mem_filter.mp hj
    refine ⟨Finset.mem_range.mp hjr, hop, ?_⟩
    show val C n l Xᶜ (n + n + j) = false ∧
      (∃ (x13 : Fin n) (x14 : Fin n), x13 ≠ x14 ∧ val C n l {x13} (n + n + j) = true ∧
        val C n l {x14} (n + n + j) = true) ∧
      ∀ (x13 : Fin n), val C n l {x13} (n + n + j) = true → x13 ∈ X
    exact ⟨hgood, ⟨p, q, hpq, hp, hq⟩, hsub _ hgood⟩
