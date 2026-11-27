import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5865_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.LowMerge
open PEqualNP.GenericRejection
open PEqualNP.HeptadCover

private def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

private theorem isOrOp_iff (op : GateOp) : isOrOp op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOrOp]

private theorem getD_append_left {α : Type} :
    ∀ (xs ys : List α) (d : α) (i : ℕ), i < xs.length → (xs ++ ys).getD i d = xs.getD i d
  | [], _, _, _, hi => by simp at hi
  | _ :: _, _, _, 0, _ => rfl
  | _ :: xs, ys, d, i + 1, hi => getD_append_left xs ys d i (by simpa using hi)

private theorem getD_append_right {α : Type} :
    ∀ (xs ys : List α) (d : α) (i : ℕ), xs.length ≤ i →
      (xs ++ ys).getD i d = ys.getD (i - xs.length) d
  | [], ys, d, i, _ => by simp
  | _ :: _, _, _, 0, hi => by simp at hi
  | _ :: xs, ys, d, i + 1, hi => by
    have h := getD_append_right xs ys d i (by simpa using hi)
    have hsub : i + 1 - (xs.length + 1) = i - xs.length := by omega
    simpa [hsub] using h

private theorem getD_append_len {α : Type} :
    ∀ (xs : List α) (v d : α), (xs ++ [v]).getD xs.length d = v
  | [], _, _ => rfl
  | _ :: xs, v, d => getD_append_len xs v d

private theorem getD_ge_len {α : Type} :
    ∀ (xs : List α) (d : α) (i : ℕ), xs.length ≤ i → xs.getD i d = d
  | [], _, 0, _ => rfl
  | [], _, _ + 1, _ => rfl
  | _ :: _, _, 0, hi => by simp at hi
  | _ :: xs, d, i + 1, hi => getD_ge_len xs d i (by simpa using hi)

private theorem getD_mem :
    ∀ (gs : List Gate) (d : Gate) (i : ℕ), i < gs.length → gs.getD i d ∈ gs
  | [], _, _, hi => by simp at hi
  | g :: _, _, 0, _ => List.mem_cons.mpr (Or.inl rfl)
  | _ :: gs, d, i + 1, hi =>
    List.mem_cons.mpr (Or.inr (getD_mem gs d i (by simpa using hi)))

private theorem getD_ofFn :
    ∀ (n : ℕ) (f : Fin n → Bool) (i : ℕ) (hi : i < n),
      (List.ofFn f).getD i false = f ⟨i, hi⟩
  | 0, _, _, hi => by omega
  | n + 1, f, 0, _ => by rw [List.ofFn_succ]; rfl
  | n + 1, f, i + 1, hi => by
    rw [List.ofFn_succ]
    exact getD_ofFn n (fun j => f j.succ) i (by omega)

private theorem getD_set_eq :
    ∀ (xs : List Bool) (i : ℕ) (v : Bool), i < xs.length → (xs.set i v).getD i false = v
  | [], _, _, hi => by simp at hi
  | _ :: _, 0, v, _ => rfl
  | _ :: xs, i + 1, v, hi => getD_set_eq xs i v (by simpa using hi)

private theorem getD_set_ne :
    ∀ (xs : List Bool) (i j : ℕ) (v : Bool), i ≠ j → (xs.set i v).getD j false = xs.getD j false
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hne => False.elim (hne rfl)
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: xs, i + 1, j + 1, v, hne => getD_set_ne xs i j v (fun h => hne (by omega))

private theorem count_false_le_card (xs : List Bool) :
    List.count false xs ≤
      ((Finset.range xs.length).filter (fun i => xs.getD i false = false)).card := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton ys b ih =>
    have hlen : (ys ++ [b]).length = ys.length + 1 := by simp
    have hcnt : List.count false (ys ++ [b]) = List.count false ys + (if b = false then 1 else 0) := by
      rw [List.count_append]
      cases b <;> simp
    rw [hcnt, hlen, Finset.range_add_one, Finset.filter_insert]
    have hfilt : (Finset.range ys.length).filter (fun i => (ys ++ [b]).getD i false = false) =
        (Finset.range ys.length).filter (fun i => ys.getD i false = false) := by
      apply Finset.filter_congr
      intro i hi
      rw [getD_append_left ys [b] false i (Finset.mem_range.mp hi)]
    rw [hfilt, getD_append_len ys b false]
    let S := (Finset.range ys.length).filter (fun i => ys.getD i false = false)
    change List.count false ys + (if b = false then 1 else 0) ≤
      (if b = false then insert ys.length S else S).card
    by_cases hb : b = false
    · subst hb
      simp only [↓reduceIte]
      have hcard : S.card + 1 ≤ (insert ys.length S).card := by
        apply Classical.byContradiction
        intro hlt
        have heq := Finset.eq_of_subset_of_card_le (Finset.subset_insert ys.length S) (by omega)
        have hmem : ys.length ∈ S := heq ▸ Finset.mem_insert_self ys.length S
        exact Nat.lt_irrefl ys.length (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)
      have hih : List.count false ys ≤ S.card := ih
      omega
    · rw [if_neg hb, if_neg hb, Nat.add_zero]
      exact ih

private def ListLe (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i : ℕ, a.getD i false = true → b.getD i false = true

private theorem cons_mono (x y : Bool) (xs ys : List Bool)
    (hxy : x = true → y = true) (h : ListLe xs ys) :
    ListLe (x :: xs) (y :: ys) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  cases i with
  | zero => exact hxy hi
  | succ j => exact h.2 j hi

private theorem append_mono (a1 a2 b1 b2 : List Bool)
    (ha : ListLe a1 a2) (hb : ListLe b1 b2) :
    ListLe (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => exact hb
    | cons _ _ => simp [ListLe] at ha
  | cons x xs ih =>
    cases a2 with
    | nil => simp [ListLe] at ha
    | cons y ys =>
      have hxs : ListLe xs ys := ⟨by simpa using ha.1, fun j hj => ha.2 (j + 1) hj⟩
      exact cons_mono x y (xs ++ b1) (ys ++ b2) (ha.2 0) (ih ys hxs)

private theorem map_all_mono (a b : List Bool) (h : ListLe a b) :
    ∀ ins : List ℕ,
      (ins.map (fun i => a.getD i false)).all id = true →
      (ins.map (fun i => b.getD i false)).all id = true
  | [], _ => rfl
  | k :: ks, hk => by
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hk ⊢
    exact ⟨h.2 k hk.1, map_all_mono a b h ks hk.2⟩

private theorem map_any_mono (a b : List Bool) (h : ListLe a b) :
    ∀ ins : List ℕ,
      (ins.map (fun i => a.getD i false)).any id = true →
      (ins.map (fun i => b.getD i false)).any id = true
  | [], hk => hk
  | k :: ks, hk => by
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true] at hk ⊢
    rcases hk with hk1 | hk2
    · exact Or.inl (h.2 k hk1)
    · exact Or.inr (map_any_mono a b h ks hk2)

private theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : ListLe a b) :
    g.op.eval (g.inputs.map (fun i => a.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => b.getD i false)) = true := by
  rcases hg with hop | hop <;> rw [hop]
  · exact map_all_mono a b h g.inputs
  · exact map_any_mono a b h g.inputs

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : ListLe a b) :
    ListLe (gs.foldl gateStep a) (gs.foldl gateStep b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g rest ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (List.mem_cons.mpr (Or.inl rfl))
    have hstep : ListLe (gateStep a g) (gateStep b g) :=
      append_mono a b _ _ h (cons_mono _ _ [] [] (gate_mono g hg a b h) ⟨rfl, fun _ hx => hx⟩)
    exact ih (fun g' hg' => hgs g' (List.mem_cons.mpr (Or.inr hg'))) _ _ hstep

private theorem foldl_gateStep_len (z : List Bool) (gs : List Gate) :
    (gs.foldl gateStep z).length = z.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, gateStep]
    simp [ih, Nat.add_assoc]

private theorem foldl_gateStep_input (z : List Bool) (gs : List Gate) (i : ℕ) (hi : i < z.length) :
    (gs.foldl gateStep z).getD i false = z.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, gateStep]
    have hlen : i < (xs.foldl gateStep z).length := by
      rw [foldl_gateStep_len]
      omega
    rw [getD_append_left _ _ false i hlen]
    exact ih

private theorem foldl_gateStep_gate (z : List Bool) (gs : List Gate) :
    ∀ k < gs.length,
      (gs.foldl gateStep z).getD (z.length + k) false =
        (gs.getD k ⟨GateOp.or, []⟩).op.eval
          ((gs.getD k ⟨GateOp.or, []⟩).inputs.map (fun u =>
            if u < z.length + k then (gs.foldl gateStep z).getD u false else false)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton xs g ih =>
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    let ws := xs.foldl gateStep z
    have hws_len : ws.length = z.length + xs.length := foldl_gateStep_len z xs
    let val := g.op.eval (g.inputs.map (fun u => ws.getD u false))
    have hfold : (xs ++ [g]).foldl gateStep z = ws ++ [val] := by
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [hfold]
    by_cases hlt : k < xs.length
    · have h1 : (ws ++ [val]).getD (z.length + k) false = ws.getD (z.length + k) false :=
        getD_append_left ws [val] false (z.length + k) (by omega)
      have h2 : (xs ++ [g]).getD k ⟨GateOp.or, []⟩ = xs.getD k ⟨GateOp.or, []⟩ :=
        getD_append_left xs [g] ⟨GateOp.or, []⟩ k hlt
      rw [h1, h2, ih k hlt]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases hu : u < z.length + k
      · simp only [hu, ↓reduceIte]
        exact (getD_append_left ws [val] false u (by omega)).symm
      · simp [hu]
    · have hkeq : k = xs.length := by omega
      subst hkeq
      have h1 : (ws ++ [val]).getD (z.length + xs.length) false = val := by
        rw [← hws_len]
        exact getD_append_len ws val false
      have h2 : (xs ++ [g]).getD xs.length ⟨GateOp.or, []⟩ = g :=
        getD_append_len xs g ⟨GateOp.or, []⟩
      rw [h1, h2]
      dsimp only [val]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases hu : u < z.length + xs.length
      · simp only [hu, ↓reduceIte]
        exact (getD_append_left ws [val] false u (by omega)).symm
      · simp only [hu, ↓reduceIte]
        exact getD_ge_len ws false u (by omega)

private theorem wireVal_input (C : Circuit) (z : List Bool) (hz : z.length = 26)
    (i : ℕ) (hi : i < 26) :
    wireVal C z i = z.getD i false := by
  unfold wireVal Circuit.wires
  exact foldl_gateStep_input z C.gates i (by omega)

private theorem wireVal_ge (C : Circuit) (z : List Bool) (hz : z.length = 26)
    (w : ℕ) (hw : 26 + C.gates.length ≤ w) :
    wireVal C z w = false := by
  unfold wireVal Circuit.wires
  apply getD_ge_len
  change (C.gates.foldl gateStep z).length ≤ w
  rw [foldl_gateStep_len]
  omega

private theorem wireVal_gate (C : Circuit) (z : List Bool) (hz : z.length = 26)
    (w : ℕ) (hw1 : 26 ≤ w) (hw2 : w < 26 + C.gates.length) :
    wireVal C z w =
      (gateAt C (w - 26)).op.eval
        ((gateAt C (w - 26)).inputs.map (fun u =>
          if u < w then wireVal C z u else false)) := by
  unfold wireVal Circuit.wires gateAt
  change (C.gates.foldl gateStep z).getD w false =
    (C.gates.getD (w - 26) ⟨GateOp.or, []⟩).op.eval
      ((C.gates.getD (w - 26) ⟨GateOp.or, []⟩).inputs.map (fun u =>
        if u < w then (C.gates.foldl gateStep z).getD u false else false))
  have h := foldl_gateStep_gate z C.gates (w - 26) (by omega)
  have heq : z.length + (w - 26) = w := by omega
  simpa [heq] using h

private def findBad (C : Circuit) (x7 : List Bool) (w : ℕ) : List ℕ → Option ℕ
  | [] => none
  | u :: us =>
    if (if u < w then wireVal C x7 u else false) = false then some u
    else findBad C x7 w us

private theorem findBad_spec (C : Circuit) (x7 : List Bool) (w : ℕ) :
    ∀ (ins : List ℕ),
      (ins.map (fun u => if u < w then wireVal C x7 u else false)).all id = false →
      ∃ u, findBad C x7 w ins = some u ∧ u ∈ ins ∧
        (if u < w then wireVal C x7 u else false) = false
  | [], h => by simp at h
  | u :: us, h => by
    unfold findBad
    by_cases hu : (if u < w then wireVal C x7 u else false) = false
    · simp only [hu, ↓reduceIte]
      exact ⟨u, rfl, List.mem_cons.mpr (Or.inl rfl), hu⟩
    · simp only [hu]
      have hut : (if u < w then wireVal C x7 u else false) = true := by
        revert hu
        cases (if u < w then wireVal C x7 u else false) <;> simp
      simp only [List.map_cons, List.all_cons, id_eq, hut, Bool.true_and] at h
      rcases findBad_spec C x7 w us h with ⟨v, hv1, hv2, hv3⟩
      exact ⟨v, hv1, List.mem_cons.mpr (Or.inr hv2), hv3⟩

private def collapseAux (C : Circuit) (x7 : List Bool) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, w =>
    if w < 26 then
      if x7.getD w false = false then some w else none
    else if w < 26 + C.gates.length then
      let g := gateAt C (w - 26)
      if isOrOp g.op = true then
        if wireVal C x7 w = false then some w else none
      else
        match findBad C x7 w g.inputs with
        | some u => if u < w then collapseAux C x7 fuel u else none
        | none => none
    else none

private theorem collapseAux_eq (C : Circuit) (x7 : List Bool) :
    ∀ (f1 f2 w : ℕ), w < f1 → w < f2 → collapseAux C x7 f1 w = collapseAux C x7 f2 w
  | 0, _, _, h1, _ => by omega
  | _ + 1, 0, _, _, h2 => by omega
  | f1 + 1, f2 + 1, w, h1, h2 => by
    unfold collapseAux
    by_cases hw26 : w < 26
    · simp [hw26]
    · by_cases hwlen : w < 26 + C.gates.length
      · simp only [hw26, hwlen, ↓reduceIte]
        cases isOrOp (gateAt C (w - 26)).op
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases findBad C x7 w (gateAt C (w - 26)).inputs with
          | none => rfl
          | some u =>
            by_cases hu : u < w
            · simp only [hu, ↓reduceIte]
              exact collapseAux_eq C x7 f1 f2 u (by omega) (by omega)
            · simp [hu]
        · simp
      · simp [hw26, hwlen]

private def collapse (C : Circuit) (x7 : List Bool) (w : ℕ) : Option ℕ :=
  collapseAux C x7 (w + 1) w

private theorem collapse_unfold (C : Circuit) (x7 : List Bool) (w : ℕ) :
    collapse C x7 w =
      if w < 26 then
        if x7.getD w false = false then some w else none
      else if w < 26 + C.gates.length then
        let g := gateAt C (w - 26)
        if isOrOp g.op = true then
          if wireVal C x7 w = false then some w else none
        else
          match findBad C x7 w g.inputs with
          | some u => if u < w then collapse C x7 u else none
          | none => none
      else none := by
  unfold collapse
  conv_lhs => unfold collapseAux
  by_cases hw26 : w < 26
  · simp [hw26]
  · by_cases hwlen : w < 26 + C.gates.length
    · simp only [hw26, hwlen, ↓reduceIte]
      cases isOrOp (gateAt C (w - 26)).op
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases findBad C x7 w (gateAt C (w - 26)).inputs with
        | none => rfl
        | some u =>
          by_cases hu : u < w
          · simp only [hu, ↓reduceIte]
            exact collapseAux_eq C x7 w (u + 1) u hu (Nat.lt_succ_self u)
          · simp [hu]
      · simp
    · simp [hw26, hwlen]

private def ValidNode (C : Circuit) (x7 : List Bool) (v : ℕ) : Prop :=
  (v < 26 ∧ x7.getD v false = false) ∨
    (26 ≤ v ∧ v < 26 + C.gates.length ∧
      (gateAt C (v - 26)).op = GateOp.or ∧ wireVal C x7 v = false)

private theorem collapse_valid (C : Circuit) (x7 : List Bool) :
    ∀ (w v : ℕ), collapse C x7 w = some v → v ≤ w ∧ ValidNode C x7 v := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hc
    rw [collapse_unfold] at hc
    by_cases hw26 : w < 26
    · simp only [hw26, ↓reduceIte] at hc
      by_cases hxf : x7.getD w false = false
      · simp only [hxf, ↓reduceIte, Option.some.injEq] at hc
        subst hc
        exact ⟨Nat.le_refl _, Or.inl ⟨hw26, hxf⟩⟩
      · simp only [hxf] at hc
        cases hc
    · by_cases hwlen : w < 26 + C.gates.length
      · simp only [hw26, hwlen, ↓reduceIte] at hc
        cases hor : isOrOp (gateAt C (w - 26)).op
        · simp only [hor, Bool.false_eq_true, ↓reduceIte] at hc
          cases hf : findBad C x7 w (gateAt C (w - 26)).inputs with
          | none => simp [hf] at hc
          | some u =>
            simp only [hf] at hc
            by_cases hu : u < w
            · simp only [hu, ↓reduceIte] at hc
              rcases ih u hu v hc with ⟨hvu, hval⟩
              exact ⟨by omega, hval⟩
            · simp [hu] at hc
        · simp only [hor, ↓reduceIte] at hc
          by_cases hwf : wireVal C x7 w = false
          · simp only [hwf, ↓reduceIte, Option.some.injEq] at hc
            subst hc
            exact ⟨Nat.le_refl _, Or.inr ⟨by omega, hwlen, (isOrOp_iff _).mp hor, hwf⟩⟩
          · simp only [hwf] at hc
            cases hc
      · simp [hw26, hwlen] at hc

private theorem collapse_sens (C : Circuit) (hmono : Monotone2 C)
    (x7 : List Bool) (hx7 : x7.length = 26) (i : ℕ) :
    ∀ (w : ℕ), wireVal C x7 w = false → wireVal C (x7.set i true) w = true →
      ∃ v, collapse C x7 w = some v ∧ wireVal C (x7.set i true) v = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwf hwt
    have hx7s : (x7.set i true).length = 26 := by simp [hx7]
    rw [collapse_unfold]
    by_cases hw26 : w < 26
    · have hxf : x7.getD w false = false := by
        rw [← wireVal_input C x7 hx7 w hw26]
        exact hwf
      simp only [hw26, hxf, ↓reduceIte]
      exact ⟨w, rfl, hwt⟩
    · by_cases hwlen : w < 26 + C.gates.length
      · simp only [hw26, hwlen, ↓reduceIte]
        cases hor : isOrOp (gateAt C (w - 26)).op
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hg_mem : gateAt C (w - 26) ∈ C.gates :=
            getD_mem C.gates ⟨GateOp.or, []⟩ (w - 26) (by omega)
          have hg_ops : (gateAt C (w - 26)).op = GateOp.and ∨ (gateAt C (w - 26)).op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hmono _ hg_mem).1
          have hand : (gateAt C (w - 26)).op = GateOp.and := by
            rcases hg_ops with h1 | h2
            · exact h1
            · rw [(isOrOp_iff _).mpr h2] at hor
              cases hor
          have hall_f :
              ((gateAt C (w - 26)).inputs.map (fun u =>
                if u < w then wireVal C x7 u else false)).all id = false := by
            have hg := wireVal_gate C x7 hx7 w (by omega) hwlen
            rw [hg, hand] at hwf
            exact hwf
          have hall_t :
              ((gateAt C (w - 26)).inputs.map (fun u =>
                if u < w then wireVal C (x7.set i true) u else false)).all id = true := by
            have hg := wireVal_gate C (x7.set i true) hx7s w (by omega) hwlen
            rw [hg, hand] at hwt
            exact hwt
          rcases findBad_spec C x7 w (gateAt C (w - 26)).inputs hall_f with ⟨u, hfb, hu_mem, hu_f⟩
          rw [hfb]
          have hu_t : (if u < w then wireVal C (x7.set i true) u else false) = true := by
            rw [List.all_map, List.all_eq_true] at hall_t
            exact hall_t u hu_mem
          have hu_lt : u < w := by
            apply Classical.byContradiction
            intro hge
            simp [hge] at hu_t
          simp only [hu_lt, ↓reduceIte] at hu_f hu_t ⊢
          exact ih u hu_lt hu_f hu_t
        · simp only [hwf, ↓reduceIte]
          exact ⟨w, rfl, hwt⟩
      · have hf := wireVal_ge C (x7.set i true) hx7s w (by omega)
        rw [hf] at hwt
        cases hwt

private def optSet : Option ℕ → Finset ℕ
  | some v => {v}
  | none => ∅

private theorem optSet_card_le (o : Option ℕ) : (optSet o).card ≤ 1 := by
  cases o <;> simp [optSet]

private def orKids (C : Circuit) (x7 : List Bool) (v : ℕ) : Finset ℕ :=
  if 26 ≤ v ∧ v < 26 + C.gates.length ∧ isOrOp (gateAt C (v - 26)).op = true then
    match (gateAt C (v - 26)).inputs with
    | [] => ∅
    | [a] => optSet (if a < v then collapse C x7 a else none)
    | a :: b :: _ =>
      optSet (if a < v then collapse C x7 a else none) ∪
        optSet (if b < v then collapse C x7 b else none)
  else ∅

private theorem orKids_card_le_two (C : Circuit) (x7 : List Bool) (v : ℕ) :
    (orKids C x7 v).card ≤ 2 := by
  unfold orKids
  by_cases hv : 26 ≤ v ∧ v < 26 + C.gates.length ∧ isOrOp (gateAt C (v - 26)).op = true
  · simp only [hv, and_self, ↓reduceIte]
    rcases (gateAt C (v - 26)).inputs with _ | ⟨a, _ | ⟨b, _⟩⟩
    · simp
    · exact Nat.le_trans (optSet_card_le _) (by omega)
    · dsimp only
      have h1 := Finset.card_union_le
        (optSet (if a < v then collapse C x7 a else none))
        (optSet (if b < v then collapse C x7 b else none))
      have h2 := optSet_card_le (if a < v then collapse C x7 a else none)
      have h3 := optSet_card_le (if b < v then collapse C x7 b else none)
      omega
  · simp [hv]

private theorem optSet_mem_valid (C : Circuit) (x7 : List Bool) (a v v' : ℕ)
    (hm : v' ∈ optSet (if a < v then collapse C x7 a else none)) :
    v' < v ∧ ValidNode C x7 v' := by
  by_cases ha : a < v
  · simp only [ha, ↓reduceIte] at hm
    cases hc : collapse C x7 a with
    | none => simp [hc, optSet] at hm
    | some w =>
      simp only [hc, optSet, Finset.mem_singleton] at hm
      subst hm
      rcases collapse_valid C x7 a v' hc with ⟨hle, hval⟩
      exact ⟨by omega, hval⟩
  · simp [ha, optSet] at hm

private theorem orKids_valid (C : Circuit) (x7 : List Bool) (v v' : ℕ)
    (hm : v' ∈ orKids C x7 v) :
    v' < v ∧ ValidNode C x7 v' := by
  unfold orKids at hm
  by_cases hv : 26 ≤ v ∧ v < 26 + C.gates.length ∧ isOrOp (gateAt C (v - 26)).op = true
  · simp only [hv, and_self, ↓reduceIte] at hm
    rcases h : (gateAt C (v - 26)).inputs with _ | ⟨a, _ | ⟨b, _⟩⟩
    · simp [h] at hm
    · simp only [h] at hm
      exact optSet_mem_valid C x7 a v v' hm
    · simp only [h, Finset.mem_union] at hm
      rcases hm with hm1 | hm2
      · exact optSet_mem_valid C x7 a v v' hm1
      · exact optSet_mem_valid C x7 b v v' hm2
  · simp [hv] at hm

private theorem mem_orKids_of_mem (C : Circuit) (hmono : Monotone2 C) (x7 : List Bool)
    (v u v' : ℕ) (hv1 : 26 ≤ v) (hv2 : v < 26 + C.gates.length)
    (hor : (gateAt C (v - 26)).op = GateOp.or)
    (hu_mem : u ∈ (gateAt C (v - 26)).inputs) (hu_lt : u < v)
    (hc : collapse C x7 u = some v') :
    v' ∈ orKids C x7 v := by
  have hg_mem : gateAt C (v - 26) ∈ C.gates :=
    getD_mem C.gates ⟨GateOp.or, []⟩ (v - 26) (by omega)
  have hlen2 : (gateAt C (v - 26)).inputs.length ≤ 2 := (hmono _ hg_mem).2
  have horb : isOrOp (gateAt C (v - 26)).op = true := (isOrOp_iff _).mpr hor
  unfold orKids
  have hv_cond : 26 ≤ v ∧ v < 26 + C.gates.length ∧ isOrOp (gateAt C (v - 26)).op = true :=
    ⟨hv1, hv2, horb⟩
  simp only [hv_cond, and_self, ↓reduceIte]
  rcases h : (gateAt C (v - 26)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rw [h] at hu_mem; simp at hu_mem
  · rw [h] at hu_mem
    simp only [List.mem_singleton] at hu_mem
    subst hu_mem
    simp [hu_lt, hc, optSet]
  · rw [h] at hu_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
    rcases hu_mem with rfl | rfl
    · simp [hu_lt, hc, optSet]
    · simp [hu_lt, hc, optSet]
  · rw [h] at hlen2; simp at hlen2

private def reachAux (C : Circuit) (x7 : List Bool) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | fuel + 1, v => insert v ((orKids C x7 v).biUnion (reachAux C x7 fuel))

private theorem reachAux_eq (C : Circuit) (x7 : List Bool) :
    ∀ (f1 f2 v : ℕ), v < f1 → v < f2 → reachAux C x7 f1 v = reachAux C x7 f2 v
  | 0, _, _, h1, _ => by omega
  | _ + 1, 0, _, _, h2 => by omega
  | f1 + 1, f2 + 1, v, h1, h2 => by
    unfold reachAux
    congr 1
    apply Finset.biUnion_congr rfl
    intro v' hv'
    have hlt := (orKids_valid C x7 v v' hv').1
    exact reachAux_eq C x7 f1 f2 v' (by omega) (by omega)

private def reach (C : Circuit) (x7 : List Bool) (v : ℕ) : Finset ℕ :=
  reachAux C x7 (v + 1) v

private theorem reach_unfold (C : Circuit) (x7 : List Bool) (v : ℕ) :
    reach C x7 v = insert v ((orKids C x7 v).biUnion (reach C x7)) := by
  unfold reach
  conv_lhs => unfold reachAux
  congr 1
  apply Finset.biUnion_congr rfl
  intro v' hv'
  have hlt := (orKids_valid C x7 v v' hv').1
  exact reachAux_eq C x7 v (v' + 1) v' hlt (Nat.lt_succ_self v')

private theorem reach_valid (C : Circuit) (x7 : List Bool) :
    ∀ (v : ℕ), ValidNode C x7 v → ∀ z ∈ reach C x7 v, z ≤ v ∧ ValidNode C x7 z := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv z hz
    rw [reach_unfold, Finset.mem_insert] at hz
    rcases hz with rfl | hz'
    · exact ⟨Nat.le_refl _, hv⟩
    · rw [Finset.mem_biUnion] at hz'
      rcases hz' with ⟨v', hv'_mem, hzv'⟩
      rcases orKids_valid C x7 v v' hv'_mem with ⟨hv'_lt, hv'_val⟩
      rcases ih v' hv'_lt hv'_val z hzv' with ⟨hz_le, hz_val⟩
      exact ⟨by omega, hz_val⟩

private theorem reach_parent (C : Circuit) (x7 : List Bool) :
    ∀ (v z : ℕ), z ∈ reach C x7 v → z ≠ v →
      ∃ p ∈ reach C x7 v, 26 ≤ p ∧ z ∈ orKids C x7 p := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro z hz hne
    rw [reach_unfold, Finset.mem_insert] at hz
    rcases hz with rfl | hz'
    · exact False.elim (hne rfl)
    · rw [Finset.mem_biUnion] at hz'
      rcases hz' with ⟨v', hv'_mem, hzv'⟩
      have hv26 : 26 ≤ v := by
        apply Classical.byContradiction
        intro hlt
        unfold orKids at hv'_mem
        have hnot : ¬ (26 ≤ v ∧ v < 26 + C.gates.length ∧ isOrOp (gateAt C (v - 26)).op = true) := by
          intro hc; exact hlt hc.1
        simp [hnot] at hv'_mem
      by_cases hzv'_eq : z = v'
      · subst hzv'_eq
        refine ⟨v, ?_, hv26, hv'_mem⟩
        rw [reach_unfold]
        exact Finset.mem_insert_self v _
      · have hv'_lt := (orKids_valid C x7 v v' hv'_mem).1
        rcases ih v' hv'_lt z hzv' hzv'_eq with ⟨p, hp_mem, hp26, hzp⟩
        refine ⟨p, ?_, hp26, hzp⟩
        rw [reach_unfold]
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v', hv'_mem, hp_mem⟩)

private theorem reach_sens (C : Circuit) (hmono : Monotone2 C)
    (x7 : List Bool) (hx7 : x7.length = 26) (i : ℕ) :
    ∀ (v : ℕ), ValidNode C x7 v → wireVal C (x7.set i true) v = true → i ∈ reach C x7 v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv hvt
    have hx7s : (x7.set i true).length = 26 := by simp [hx7]
    rcases hv with ⟨hv26, hvf⟩ | ⟨hv1, hv2, hor, hvf⟩
    · have hget : (x7.set i true).getD v false = true := by
        rw [← wireVal_input C (x7.set i true) hx7s v hv26]
        exact hvt
      have hieq : i = v := by
        apply Classical.byContradiction
        intro hne
        rw [getD_set_ne x7 i v true hne, hvf] at hget
        cases hget
      subst hieq
      rw [reach_unfold]
      exact Finset.mem_insert_self i _
    · have hany_t :
          ((gateAt C (v - 26)).inputs.map (fun u =>
            if u < v then wireVal C (x7.set i true) u else false)).any id = true := by
        have hg := wireVal_gate C (x7.set i true) hx7s v hv1 hv2
        rw [hg, hor] at hvt
        exact hvt
      have hany_f :
          ((gateAt C (v - 26)).inputs.map (fun u =>
            if u < v then wireVal C x7 u else false)).any id = false := by
        have hg := wireVal_gate C x7 hx7 v hv1 hv2
        rw [hg, hor] at hvf
        exact hvf
      rw [List.any_map, List.any_eq_true] at hany_t
      rcases hany_t with ⟨u, hu_mem, hu_t⟩
      simp only [Function.comp_apply, id_eq] at hu_t
      have hu_lt : u < v := by
        apply Classical.byContradiction
        intro hge
        simp [hge] at hu_t
      simp only [hu_lt, ↓reduceIte] at hu_t
      have hu_f : wireVal C x7 u = false := by
        rw [List.any_map, List.any_eq_false] at hany_f
        have huf := hany_f u hu_mem
        simpa [hu_lt] using huf
      rcases collapse_sens C hmono x7 hx7 i u hu_f hu_t with ⟨v', hcv', hv'_t⟩
      have hv'_kids : v' ∈ orKids C x7 v :=
        mem_orKids_of_mem C hmono x7 v u v' hv1 hv2 hor hu_mem hu_lt hcv'
      rcases orKids_valid C x7 v v' hv'_kids with ⟨hv'_lt, hv'_val⟩
      have hi_mem := ih v' hv'_lt hv'_val hv'_t
      rw [reach_unfold]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v', hv'_kids, hi_mem⟩)

private theorem sum_le_two_mul (D : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ D, f x ≤ 2) :
    (∑ x ∈ D, f x) ≤ 2 * D.card := by
  have h1 : (∑ x ∈ D, f x) ≤ ∑ _x ∈ D, 2 := Finset.sum_le_sum hf
  have h2 : (∑ _x ∈ D, 2) = 2 * D.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

private theorem pointLine_le_set_pt (X Y : Finset (Fin 13)) (p l : Fin 13) (hl : l ∈ Y) :
    ListLe (pointLineInput 13 13 p l) ((incidenceInput X Y).set p.val true) := by
  have hlen1 : (pointLineInput 13 13 p l).length = 26 := by
    simp [pointLineInput, restrictInput]
  have hlen2 : (incidenceInput X Y).length = 26 := by
    simp [incidenceInput]
  refine ⟨by simp [hlen1, hlen2], fun k hk => ?_⟩
  by_cases hk13 : k < 13
  · have hkp : (pointLineInput 13 13 p l).getD k false = decide ((⟨k, hk13⟩ : Fin 13) = p) := by
      unfold pointLineInput restrictInput
      rw [getD_append_left _ _ false k (by simp [hk13])]
      exact getD_ofFn 13 _ k hk13
    rw [hkp, decide_eq_true_eq] at hk
    have hkeq : k = p.val := by simpa [Fin.ext_iff] using hk
    subst hkeq
    exact getD_set_eq (incidenceInput X Y) p.val true (by omega)
  · by_cases hk26 : k < 26
    · have hkl : (pointLineInput 13 13 p l).getD k false =
          decide ((⟨k - 13, by omega⟩ : Fin 13) = l) := by
        unfold pointLineInput restrictInput
        rw [getD_append_right _ _ false k (by simp; omega)]
        have hlen_fn : (List.ofFn (fun q : Fin 13 => decide (q = p))).length = 13 := by simp
        simpa [hlen_fn] using getD_ofFn 13 (fun v : Fin 13 => decide (v = l)) (k - 13) (by omega)
      rw [hkl, decide_eq_true_eq] at hk
      have hne : p.val ≠ k := by omega
      rw [getD_set_ne (incidenceInput X Y) p.val k true hne]
      unfold incidenceInput
      rw [getD_append_right _ _ false k (by simp; omega)]
      have hlen_fn : (List.ofFn (fun q : Fin 13 => decide (q ∈ X))).length = 13 := by simp
      rw [hlen_fn, getD_ofFn 13 (fun v : Fin 13 => decide (v ∈ Y)) (k - 13) (by omega)]
      rw [hk]
      exact decide_eq_true hl
    · have hf := getD_ge_len (pointLineInput 13 13 p l) false k (by omega)
      rw [hf] at hk
      cases hk

private theorem pointLine_le_set_ln (X Y : Finset (Fin 13)) (p l : Fin 13) (hp : p ∈ X) :
    ListLe (pointLineInput 13 13 p l) ((incidenceInput X Y).set (13 + l.val) true) := by
  have hlen1 : (pointLineInput 13 13 p l).length = 26 := by
    simp [pointLineInput, restrictInput]
  have hlen2 : (incidenceInput X Y).length = 26 := by
    simp [incidenceInput]
  refine ⟨by simp [hlen1, hlen2], fun k hk => ?_⟩
  by_cases hk13 : k < 13
  · have hkp : (pointLineInput 13 13 p l).getD k false = decide ((⟨k, hk13⟩ : Fin 13) = p) := by
      unfold pointLineInput restrictInput
      rw [getD_append_left _ _ false k (by simp [hk13])]
      exact getD_ofFn 13 _ k hk13
    rw [hkp, decide_eq_true_eq] at hk
    have hne : 13 + l.val ≠ k := by omega
    rw [getD_set_ne (incidenceInput X Y) (13 + l.val) k true hne]
    unfold incidenceInput
    rw [getD_append_left _ _ false k (by simp [hk13])]
    rw [getD_ofFn 13 (fun q : Fin 13 => decide (q ∈ X)) k hk13, hk]
    exact decide_eq_true hp
  · by_cases hk26 : k < 26
    · have hkl : (pointLineInput 13 13 p l).getD k false =
          decide ((⟨k - 13, by omega⟩ : Fin 13) = l) := by
        unfold pointLineInput restrictInput
        rw [getD_append_right _ _ false k (by simp; omega)]
        have hlen_fn : (List.ofFn (fun q : Fin 13 => decide (q = p))).length = 13 := by simp
        simpa [hlen_fn] using getD_ofFn 13 (fun v : Fin 13 => decide (v = l)) (k - 13) (by omega)
      rw [hkl, decide_eq_true_eq] at hk
      have hkeq : k = 13 + l.val := by
        have hv : k - 13 = l.val := congrArg Fin.val hk
        omega
      subst hkeq
      exact getD_set_eq (incidenceInput X Y) (13 + l.val) true (by omega)
    · have hf := getD_ge_len (pointLineInput 13 13 p l) false k (by omega)
      rw [hf] at hk
      cases hk

theorem main :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
        ∀ (x3 : ℕ),
          (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ PEqualNP.HeptadCover.singerLines3 x5 →
            PEqualNP.LowMerge.wireVal x1 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x4 x5) x3 = Bool.true) →
          ∀ (x5 : Finset (Fin (13 : ℕ))),
            have x6 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x5;
            have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x5 x6;
            x5 = PEqualNP.GenericRejection.zeroSet PEqualNP.HeptadCover.singerLines3 x6 →
            PEqualNP.LowMerge.wireVal x1 x7 x3 = Bool.false →
            ∃ (x10 : Finset ℕ), List.count Bool.false x7 ≤ x10.card + (1 : ℕ) ∧
              ∀ x11 ∈ x10, (26 : ℕ) ≤ x11 ∧ x11 ≤ x3 ∧
                (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x11 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                PEqualNP.LowMerge.wireVal x1 x7 x11 = Bool.false := by
  intro C hmono x3 hinc X
  let Y : Finset (Fin 13) := missLines singerLines3 X
  let x7 : List Bool := incidenceInput X Y
  change X = zeroSet singerLines3 Y → wireVal C x7 x3 = false →
    ∃ x10 : Finset ℕ, List.count false x7 ≤ x10.card + 1 ∧
      ∀ w ∈ x10, 26 ≤ w ∧ w ≤ x3 ∧ (gateAt C (w - 26)).op = GateOp.or ∧ wireVal C x7 w = false
  intro hX hfalse
  have hx7_len : x7.length = 26 := by simp [x7, incidenceInput]
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hmono g hg).1
  let L : Finset ℕ := (Finset.range 26).filter (fun i => x7.getD i false = false)
  have hcnt_le : List.count false x7 ≤ L.card := by
    have hc := count_false_le_card x7
    simpa [hx7_len, L] using hc
  have hL_flip : ∀ i ∈ L, wireVal C (x7.set i true) x3 = true := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rcases hi with ⟨hi26, hif⟩
    by_cases hi13 : i < 13
    · let p : Fin 13 := ⟨i, hi13⟩
      have hp_get : x7.getD i false = decide (p ∈ X) := by
        dsimp only [x7, incidenceInput]
        rw [getD_append_left _ _ false i (by simp [hi13])]
        exact getD_ofFn 13 _ i hi13
      rw [hp_get, decide_eq_false_iff_not] at hif
      have hp_not_zero : p ∉ zeroSet singerLines3 Y := by rwa [← hX]
      simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
        Classical.not_not] at hp_not_zero
      rcases hp_not_zero with ⟨l, hlY, hpl⟩
      have hle := pointLine_le_set_pt X Y p l hlY
      exact (foldl_mono C.gates hgs _ _ hle).2 x3 (hinc p l hpl)
    · let l : Fin 13 := ⟨i - 13, by omega⟩
      have hl_get : x7.getD i false = decide (l ∈ Y) := by
        dsimp only [x7, incidenceInput]
        rw [getD_append_right _ _ false i (by simp; omega)]
        have hlen_fn : (List.ofFn (fun q : Fin 13 => decide (q ∈ X))).length = 13 := by simp
        simpa [hlen_fn] using getD_ofFn 13 (fun v : Fin 13 => decide (v ∈ Y)) (i - 13) (by omega)
      rw [hl_get, decide_eq_false_iff_not] at hif
      have hl_not_miss : l ∉ missLines singerLines3 X := hif
      simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.not_disjoint_iff] at hl_not_miss
      rcases hl_not_miss with ⟨p, hpl, hpX⟩
      have hle := pointLine_le_set_ln X Y p l hpX
      have hieq : 13 + l.val = i := by dsimp only [l]; omega
      rw [← hieq]
      exact (foldl_mono C.gates hgs _ _ hle).2 x3 (hinc p l hpl)
  by_cases hLemp : L = ∅
  · refine ⟨∅, ?_, by simp⟩
    rw [hLemp] at hcnt_le
    simp only [Finset.card_empty] at hcnt_le ⊢
    omega
  · rcases Finset.nonempty_iff_ne_empty.mpr hLemp with ⟨i0, hi0⟩
    rcases collapse_sens C hmono x7 hx7_len i0 x3 hfalse (hL_flip i0 hi0) with ⟨r, hcr, _⟩
    rcases collapse_valid C x7 x3 r hcr with ⟨hr_le, hr_val⟩
    let R : Finset ℕ := reach C x7 r
    let Lr : Finset ℕ := R.filter (fun z => decide (z < 26))
    let x10 : Finset ℕ := R.filter (fun z => decide (26 ≤ z))
    have hL_sub : L ⊆ Lr := by
      intro i hi
      have hi26 : i < 26 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      rcases collapse_sens C hmono x7 hx7_len i x3 hfalse (hL_flip i hi) with ⟨ri, hcri, hri_t⟩
      have hri_eq : ri = r := Option.some.inj (hcri.symm.trans hcr)
      rw [hri_eq] at hri_t
      have hiR : i ∈ R := reach_sens C hmono x7 hx7_len i r hr_val hri_t
      rw [Finset.mem_filter]
      exact ⟨hiR, decide_eq_true hi26⟩
    have hdisj : Disjoint Lr x10 := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      have h1 : z < 26 := of_decide_eq_true (Finset.mem_filter.mp hz1).2
      have h2 : 26 ≤ z := of_decide_eq_true (Finset.mem_filter.mp hz2).2
      omega
    have hunion : Lr ∪ x10 = R := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Lr, x10, decide_eq_true_eq]
      constructor
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
      · intro hz
        by_cases h26 : z < 26
        · exact Or.inl ⟨hz, h26⟩
        · exact Or.inr ⟨hz, by omega⟩
    have hR_card : R.card = Lr.card + x10.card := by
      rw [← hunion]
      exact Finset.card_union_of_disjoint hdisj
    have herase_sub : R.erase r ⊆ x10.biUnion (orKids C x7) := by
      intro z hz
      rw [Finset.mem_erase] at hz
      rcases reach_parent C x7 r z hz.2 hz.1 with ⟨p, hpR, hp26, hzp⟩
      rw [Finset.mem_biUnion]
      refine ⟨p, ?_, hzp⟩
      rw [Finset.mem_filter]
      exact ⟨hpR, decide_eq_true hp26⟩
    have hbi_le : (R.erase r).card ≤ 2 * x10.card := by
      have h1 : (R.erase r).card ≤ (x10.biUnion (orKids C x7)).card :=
        Finset.card_le_card herase_sub
      have h2 : (x10.biUnion (orKids C x7)).card ≤ ∑ p ∈ x10, (orKids C x7 p).card :=
        Finset.card_biUnion_le
      have h3 : (∑ p ∈ x10, (orKids C x7 p).card) ≤ 2 * x10.card :=
        sum_le_two_mul x10 (fun p => (orKids C x7 p).card) (fun p _ => orKids_card_le_two C x7 p)
      omega
    have hr_in_R : r ∈ R := by
      dsimp only [R]
      rw [reach_unfold]
      exact Finset.mem_insert_self r _
    have herase_add : (R.erase r).card + 1 = R.card := Finset.card_erase_add_one hr_in_R
    have hLr_le : L.card ≤ Lr.card := Finset.card_le_card hL_sub
    refine ⟨x10, by omega, ?_⟩
    intro w hw
    rw [Finset.mem_filter, decide_eq_true_eq] at hw
    rcases hw with ⟨hwR, hw26⟩
    rcases reach_valid C x7 r hr_val w hwR with ⟨hw_le_r, hw_val⟩
    rcases hw_val with ⟨hwlt, _⟩ | ⟨_, _, hwor, hwf⟩
    · omega
    · exact ⟨hw26, by omega, hwor, hwf⟩

end PEqualNP.Outside.L_meta_5865_aux

theorem PEqualNP.Outside.L_meta_5865 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     ∀ (x3 : ℕ),       (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ PEqualNP.HeptadCover.singerLines3 x5 → PEqualNP.LowMerge.wireVal x1 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x4 x5) x3 = Bool.true) →         ∀ (x5 : Finset (Fin (13 : ℕ))),           have x6 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x5;           have x7 : List Bool := PEqualNP.GenericRejection.incidenceInput x5 x6;           x5 = PEqualNP.GenericRejection.zeroSet PEqualNP.HeptadCover.singerLines3 x6 → PEqualNP.LowMerge.wireVal x1 x7 x3 = Bool.false → ∃ (x10 : Finset ℕ), List.count Bool.false x7 ≤ x10.card + (1 : ℕ) ∧ ∀ x11 ∈ x10, (26 : ℕ) ≤ x11 ∧ x11 ≤ x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x11 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.LowMerge.wireVal x1 x7 x11 = Bool.false :=
  PEqualNP.Outside.L_meta_5865_aux.main
