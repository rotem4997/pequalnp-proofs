import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def uvec (L : List ℕ) (u : ℕ) : List ℕ :=
  L.map fun j => if j = u then 1 else 0

lemma mem_insertNew_of_mem {A : List (List ℕ)} {v w : List ℕ} (h : w ∈ A) :
    w ∈ insertNew A v := by
  unfold insertNew
  split_ifs
  · exact h
  · exact List.mem_append_left _ h

lemma mem_insertNew_self (A : List (List ℕ)) (v : List ℕ) :
    v ∈ insertNew A v := by
  unfold insertNew
  split_ifs with h
  · exact h
  · exact List.mem_append_right _ (List.mem_singleton_self _)

lemma mem_foldl_insertNew_of_mem_acc {B A : List (List ℕ)} {w : List ℕ} (h : w ∈ A) :
    w ∈ B.foldl insertNew A := by
  induction B generalizing A with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (mem_insertNew_of_mem h)

lemma mem_foldl_insertNew_of_mem_list {B A : List (List ℕ)} {w : List ℕ} (h : w ∈ B) :
    w ∈ B.foldl insertNew A := by
  induction B generalizing A with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hxs
    · exact mem_foldl_insertNew_of_mem_acc (mem_insertNew_self A w)
    · exact ih hxs

lemma mem_foldl_orStep_of_mem_acc {ins : List (List (List ℕ))} {acc : List (List ℕ)}
    {w : List ℕ} (h : w ∈ acc) :
    w ∈ ins.foldl (fun a X => X.foldl insertNew a) acc := by
  induction ins generalizing acc with
  | nil => exact h
  | cons X Xs ih =>
    simp only [List.foldl_cons]
    exact ih (mem_foldl_insertNew_of_mem_acc h)

lemma mem_foldl_orStep {ins : List (List (List ℕ))} {acc : List (List ℕ)}
    {A : List (List ℕ)} {w : List ℕ} (hA : A ∈ ins) (hw : w ∈ A) :
    w ∈ ins.foldl (fun a X => X.foldl insertNew a) acc := by
  induction ins generalizing acc with
  | nil => cases hA
  | cons X Xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hA with rfl | hXs
    · exact mem_foldl_orStep_of_mem_acc (mem_foldl_insertNew_of_mem_list hw)
    · exact ih hXs

lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {u v : List ℕ} (hu : u ∈ A) (hv : v ∈ B) :
    capAdd k u v ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem_list
  rw [List.mem_flatMap]
  refine ⟨u, hu, ?_⟩
  rw [List.mem_map]
  exact ⟨v, hv, rfl⟩

lemma capAdd_zero_uvec (L : List ℕ) (u : ℕ) :
    capAdd 1 (L.map fun _ => 0) (uvec L u) = uvec L u := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [capAdd, uvec, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> rfl

lemma mem_uvec_le_one (L : List ℕ) (u : ℕ) :
    ∀ c ∈ uvec L u, c ≤ 1 := by
  intro c hc
  simp only [uvec, List.mem_map] at hc
  rcases hc with ⟨j, _, rfl⟩
  split_ifs <;> omega

lemma mem_capAdd_uvec_le_one (L : List ℕ) (u v : ℕ) (huv : u ≠ v) :
    ∀ c ∈ capAdd 1 (uvec L u) (uvec L v), c ≤ 1 := by
  induction L with
  | nil =>
    intro c hc
    simp [capAdd, uvec] at hc
  | cons a t ih =>
    intro c hc
    simp only [capAdd, uvec, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with rfl | hct
    · split_ifs with h1 h2
      · exact False.elim (huv (h1.symm.trans h2))
      · decide
      · decide
      · decide
    · exact ih c hct

lemma foldl_append_length {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_append_getD_lt {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [f init g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (init ++ [f init g]) hi']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_take_getD {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) (d : α) :
    ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init).getD i d =
      (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, List.foldl_append]
  have hlen : ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init).length = init.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  symm
  exact foldl_append_getD_lt f (gs.drop j) _ i d (by omega)

lemma foldl_append_getD_gate {α : Type*} (f : List α → Gate → α) (gs : List Gate) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) init).getD (init.length + j) d =
      f ((gs.take j).foldl (fun acc g => acc ++ [f acc g]) init) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set pref := (gs.take j).foldl (fun acc g => acc ++ [f acc g]) init
  have hlen : pref.length = init.length + j := by
    simp only [pref, foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : init.length + j < (pref ++ [f pref gs[j]]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [foldl_append_getD_lt f (gs.drop (j + 1)) (pref ++ [f pref gs[j]]) (init.length + j) d hlt]
  rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_append_length _ C.gates x

lemma wires_getD_lt (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  unfold Circuit.wires
  exact foldl_append_getD_lt _ C.gates x w false hw

lemma wires_getD_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  unfold Circuit.wires
  have h := foldl_append_getD_gate
    (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates x j hj false
  rw [hx] at h
  rw [h, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hrb j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have ht := foldl_append_take_getD
    (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates x j i (Nat.le_of_lt hj) (by omega) false
  exact ht

lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (L : List ℕ) (k w : ℕ) (hw : w < n) :
    (readVectors C n L k).getD w [] = leafVectors L k w := by
  unfold readVectors
  have hw' : w < ((List.range n).map (leafVectors L k)).length := by
    simp [hw]
  rw [foldl_append_getD_lt _ C.gates _ w [] hw']
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
  rfl

lemma readVectors_getD_gate (n : ℕ) (C : Circuit) (L : List ℕ) (k : ℕ)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (readVectors C n L k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n L k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [L.map fun _ => 0]
      | _ => [] := by
  unfold readVectors
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    match g.op with
    | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => ins.foldl (andStep k) [L.map fun _ => 0]
    | _ => []
  let init := (List.range n).map (leafVectors L k)
  have hinit : init.length = n := by simp [init]
  have h := foldl_append_getD_gate step C.gates init j hj []
  rw [hinit] at h
  change (C.gates.foldl (fun R g => R ++ [step R g]) init).getD (n + j) [] = _
  rw [h]
  dsimp only [step]
  rw [gateAt_eq_getElem C j hj]
  have hmap : C.gates[j].inputs.map (fun i => ((C.gates.take j).foldl (fun R g => R ++ [step R g]) init).getD i []) =
      C.gates[j].inputs.map (fun i => (C.gates.foldl (fun R g => R ++ [step R g]) init).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < n + j := by
      have := hrb j hj i
      rw [gateAt_eq_getElem C j hj] at this
      exact this hi
    exact foldl_append_take_getD step C.gates init j i (Nat.le_of_lt hj) (by omega) []
  rw [hmap]
  rfl

lemma mem_setList_of_wire_true {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (w : ℕ) (hw : w < n)
    (ht : (C.wires (List.ofFn (setInput S))).getD w false = true) :
    w ∈ setList S := by
  have hxlen : (List.ofFn (setInput S)).length = n := List.length_ofFn
  rw [wires_getD_lt C (List.ofFn (setInput S)) w (by omega)] at ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at ht
  simp only [Option.getD_some, List.getElem_ofFn, setInput, decide_eq_true_eq] at ht
  unfold setList
  rw [List.mem_map]
  refine ⟨⟨w, hw⟩, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨List.mem_finRange _, by simp [ht]⟩

lemma uvec_mem_leafVectors (L : List ℕ) (w : ℕ) (hw : w ∈ L) :
    uvec L w ∈ leafVectors L 1 w := by
  simp [leafVectors, hw, uvec]

lemma pure_wire_unit_vec (x1 x2 : ℕ) (C : Circuit) (P : Bool → Finset ℕ)
    (S : Finset (Fin (x1 + x2)))
    (hrb : ReadsBack (x1 + x2) C)
    (hP : ∀ side : Bool, ∀ w ∈ P side,
      w < x1 + x2 ∧ Decidable.decide (x1 ≤ w) = side ∨
      ∃ g < C.size, w = x1 + x2 + g ∧ (gateAt C g).op = GateOp.or ∧
        ∀ i ∈ (gateAt C g).inputs, i ∈ P side) :
    ∀ w : ℕ, ∀ side : Bool, w ∈ P side →
      (C.wires (List.ofFn (setInput S))).getD w false = true →
      ∃ u : ℕ, Decidable.decide (x1 ≤ u) = side ∧
        uvec (setList S) u ∈ (readVectors C (x1 + x2) (setList S) 1).getD w [] := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro side hw hval
    rcases hP side w hw with ⟨hw_lt, hdec⟩ | ⟨g, hg_lt, rfl, hop, hins⟩
    · refine ⟨w, hdec, ?_⟩
      rw [readVectors_getD_lt C (x1 + x2) (setList S) 1 w hw_lt]
      exact uvec_mem_leafVectors (setList S) w (mem_setList_of_wire_true S C w hw_lt hval)
    · have hg_len : g < C.gates.length := hg_lt
      rw [wires_getD_gate (x1 + x2) C (List.ofFn (setInput S)) List.length_ofFn hrb g hg_len] at hval
      rw [hop] at hval
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hval
      rcases hval with ⟨_, ⟨i, hi_mem, rfl⟩, hi_val⟩
      have hi_lt : i < x1 + x2 + g := hrb g hg_len i hi_mem
      rcases ih i hi_lt side (hins i hi_mem) hi_val with ⟨u, hdec, hu_mem⟩
      refine ⟨u, hdec, ?_⟩
      rw [readVectors_getD_gate (x1 + x2) C (setList S) 1 hrb g hg_len]
      dsimp only
      rw [hop]
      apply mem_foldl_orStep _ hu_mem
      rw [List.mem_map]
      exact ⟨i, hi_mem, rfl⟩

lemma wire_has_read1_vec (x1 x2 : ℕ) (C : Circuit) (P : Bool → Finset ℕ)
    (S : Finset (Fin (x1 + x2)))
    (hao : IsAO2 (x1 + x2) C)
    (hP : ∀ side : Bool, ∀ w ∈ P side,
      w < x1 + x2 ∧ Decidable.decide (x1 ≤ w) = side ∨
      ∃ g < C.size, w = x1 + x2 + g ∧ (gateAt C g).op = GateOp.or ∧
        ∀ i ∈ (gateAt C g).inputs, i ∈ P side)
    (hAnd : ∀ g < C.size, (gateAt C g).op = GateOp.and →
      ∃ a b : ℕ, (gateAt C g).inputs = [a, b] ∧ a ∈ P Bool.false ∧ b ∈ P Bool.true) :
    ∀ w : ℕ, w < x1 + x2 + C.gates.length →
      (C.wires (List.ofFn (setInput S))).getD w false = true →
      ∃ v ∈ (readVectors C (x1 + x2) (setList S) 1).getD w [], ∀ c ∈ v, c ≤ 1 := by
  have hrb : ReadsBack (x1 + x2) C := hao.2.1
  have haoo : AndOrOnly C := hao.1
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hlt : w < x1 + x2
    · refine ⟨uvec (setList S) w, ?_, mem_uvec_le_one (setList S) w⟩
      rw [readVectors_getD_lt C (x1 + x2) (setList S) 1 w hlt]
      exact uvec_mem_leafVectors (setList S) w (mem_setList_of_wire_true S C w hlt hval)
    · set g := w - (x1 + x2)
      have hw_eq : w = x1 + x2 + g := by omega
      have hg_lt : g < C.gates.length := by omega
      rw [hw_eq] at hval ⊢
      have hg_mem : gateAt C g ∈ C.gates := by
        rw [gateAt_eq_getElem C g hg_lt]
        exact List.getElem_mem hg_lt
      rcases haoo (gateAt C g) hg_mem with hop | hop
      · rcases hAnd g hg_lt hop with ⟨a, b, hins, haP, hbP⟩
        rw [wires_getD_gate (x1 + x2) C (List.ofFn (setInput S)) List.length_ofFn hrb g hg_lt] at hval
        rw [hop, hins] at hval
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hval
        rcases hval with ⟨ha_val, hb_val⟩
        rcases pure_wire_unit_vec x1 x2 C P S hrb hP a Bool.false haP ha_val with ⟨u, hu_dec, hu_mem⟩
        rcases pure_wire_unit_vec x1 x2 C P S hrb hP b Bool.true hbP hb_val with ⟨v, hv_dec, hv_mem⟩
        have huv : u ≠ v := by
          intro heq
          subst heq
          rw [hu_dec] at hv_dec
          exact Bool.noConfusion hv_dec
        refine ⟨capAdd 1 (uvec (setList S) u) (uvec (setList S) v), ?_,
          mem_capAdd_uvec_le_one (setList S) u v huv⟩
        rw [readVectors_getD_gate (x1 + x2) C (setList S) 1 hrb g hg_lt]
        dsimp only
        rw [hop, hins]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        have hstep1 : uvec (setList S) u ∈
            andStep 1 [((setList S).map fun _ => 0)] ((readVectors C (x1 + x2) (setList S) 1).getD a []) := by
          rw [← capAdd_zero_uvec (setList S) u]
          exact mem_andStep (List.mem_singleton_self _) hu_mem
        exact mem_andStep hstep1 hv_mem
      · rw [wires_getD_gate (x1 + x2) C (List.ofFn (setInput S)) List.length_ofFn hrb g hg_lt] at hval
        rw [hop] at hval
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hval
        rcases hval with ⟨_, ⟨i, hi_mem, rfl⟩, hi_val⟩
        have hi_lt : i < x1 + x2 + g := hrb g hg_lt i hi_mem
        have hi_lt_w : i < w := by omega
        have hi_bound : i < x1 + x2 + C.gates.length := by omega
        rcases ih i hi_lt_w hi_bound hi_val with ⟨v, hv_mem, hv_le⟩
        refine ⟨v, ?_, hv_le⟩
        rw [readVectors_getD_gate (x1 + x2) C (setList S) 1 hrb g hg_lt]
        dsimp only
        rw [hop]
        apply mem_foldl_orStep _ hv_mem
        rw [List.mem_map]
        exact ⟨i, hi_mem, rfl⟩

end PEqualNP.Outside.L_meta_6579

theorem PEqualNP.Outside.L_meta_6579 :
    ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 x3 x4 hao hP hAnd S hS
  have hval : (x3.wires (List.ofFn (PEqualNP.ReadK.setInput S))).getD x3.output false = true :=
    hS.1
  have hout : x3.output < x1 + x2 + x3.gates.length := by
    by_contra hge
    have hlen : (x3.wires (List.ofFn (PEqualNP.ReadK.setInput S))).length = x1 + x2 + x3.gates.length := by
      rw [PEqualNP.Outside.L_meta_6579.wires_length, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hval
    exact Bool.noConfusion hval
  rcases PEqualNP.Outside.L_meta_6579.wire_has_read1_vec x1 x2 x3 x4 S hao hP hAnd x3.output hout hval with
    ⟨v, hv_mem, hv_le⟩
  unfold PEqualNP.ReadK.readsAtMost
  rw [List.any_eq_true]
  refine ⟨v, hv_mem, ?_⟩
  rw [List.all_eq_true]
  intro a ha
  exact decide_eq_true (hv_le a ha)
