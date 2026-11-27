import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4616

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepList {α : Type} (f : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun acc g => acc ++ [f acc g]) init

lemma stepList_length {α : Type} (f : List α → Gate → α) (init : List α) (gs : List Gate) :
    (stepList f init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [stepList]
  | cons g gs ih =>
    simp only [stepList, List.foldl_cons]
    change (stepList f (init ++ [f init g]) gs).length = init.length + (gs.length + 1)
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_self {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _)]
  simp

lemma stepList_getD_lt {α : Type} (f : List α → Gate → α) (init : List α) (gs : List Gate)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (stepList f init gs).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [stepList, List.foldl_cons]
    change (stepList f (init ++ [f init g]) gs).getD i d = init.getD i d
    have hi' : i < (init ++ [f init g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (init ++ [f init g]) hi']
    exact getD_append_left init [f init g] i d hi

lemma stepList_append {α : Type} (f : List α → Gate → α) (init : List α) (gs1 gs2 : List Gate) :
    stepList f init (gs1 ++ gs2) = stepList f (stepList f init gs1) gs2 := by
  simp [stepList, List.foldl_append]

lemma stepList_getD_prefix {α : Type} (f : List α → Gate → α) (init : List α) (gs : List Gate)
    (k i : ℕ) (d : α) (hk : k ≤ gs.length) (hi : i < init.length + k) :
    (stepList f init gs).getD i d = (stepList f init (gs.take k)).getD i d := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsplit, stepList_append]
  refine stepList_getD_lt f (stepList f init (gs.take k)) (gs.drop k) i d ?_
  rw [stepList_length, List.length_take]
  omega

lemma stepList_getD_gate {α : Type} (f : List α → Gate → α) (init : List α) (gs : List Gate)
    (j : ℕ) (g : Gate) (d : α) (hj : gs[j]? = some g) :
    (stepList f init gs).getD (init.length + j) d = f (stepList f init (gs.take j)) g := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons hd tl ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [stepList, List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
      change (stepList f (init ++ [f init hd]) tl).getD init.length d = f init hd
      have hi : init.length < (init ++ [f init hd]).length := by simp
      rw [stepList_getD_lt f (init ++ [f init hd]) tl init.length d hi]
      exact getD_append_right_self init (f init hd) d
    | succ k =>
      simp only [List.getElem?_cons_succ] at hj
      simp only [stepList, List.foldl_cons, List.take_succ_cons]
      change (stepList f (init ++ [f init hd]) tl).getD (init.length + (k + 1)) d =
        f (stepList f (init ++ [f init hd]) (tl.take k)) g
      have hlen : init.length + (k + 1) = (init ++ [f init hd]).length + k := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hlen]
      exact ih (init ++ [f init hd]) k hj

def leafStep (acc : List ℕ) (g : Gate) : ℕ :=
  (g.inputs.map (fun i => acc.getD i 0)).sum

def leafList (n : ℕ) (C : Circuit) : List ℕ :=
  stepList leafStep (List.replicate n 1) C.gates

def pathStep (n : ℕ) (target : ℕ) (acc : List ℕ) (g : Gate) : ℕ :=
  (if acc.length = n + target then 1 else 0) + (g.inputs.map (fun i => acc.getD i 0)).sum

def pathList (n : ℕ) (C : Circuit) (target : ℕ) : List ℕ :=
  stepList (pathStep n target) (List.replicate n 0) C.gates

lemma leaf_eq_one_add_sum_path (n : ℕ) (C : Circuit)
    (hfan : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) :
    ∀ w : ℕ, w < n + C.size →
      (leafList n C).getD w 0 =
        1 + ∑ g0 : Fin C.size, (pathList n C g0.1).getD w 0 := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · have hL : (leafList n C).getD w 0 = 1 := by
        unfold leafList
        rw [stepList_getD_lt _ _ _ w 0 (by simp [hlt])]
        simp [List.getD_eq_getElem?_getD, hlt]
      have hP : ∀ g0 : Fin C.size, (pathList n C g0.1).getD w 0 = 0 := by
        intro g0
        unfold pathList
        rw [stepList_getD_lt _ _ _ w 0 (by simp [hlt])]
        simp [List.getD_eq_getElem?_getD, hlt]
      rw [hL]
      simp_rw [hP]
      simp
    · have hj : w - n < C.gates.length := by
        change w < n + C.gates.length at hw
        omega
      let j := w - n
      have hwj : w = n + j := by omega
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨a, b, hinp, hab, hbj⟩ := hfan j C.gates[j] hget
      have haw : a < w := by omega
      have hbw : b < w := by omega
      have ha_le : a < n + j := by omega
      have hb_le : b < n + j := by omega
      have hj_le : j ≤ C.gates.length := Nat.le_of_lt hj
      have hL : (leafList n C).getD w 0 =
          (leafList n C).getD a 0 + (leafList n C).getD b 0 := by
        rw [hwj]
        unfold leafList
        have h1 := stepList_getD_gate leafStep (List.replicate n 1) C.gates j C.gates[j] 0 hget
        simp only [List.length_replicate] at h1
        rw [h1]
        simp only [leafStep, hinp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero]
        have ha' := stepList_getD_prefix leafStep (List.replicate n 1) C.gates j a 0 hj_le (by simp [ha_le])
        have hb' := stepList_getD_prefix leafStep (List.replicate n 1) C.gates j b 0 hj_le (by simp [hb_le])
        rw [ha', hb']
      have hP : ∀ g0 : Fin C.size, (pathList n C g0.1).getD w 0 =
          (if j = g0.1 then 1 else 0) +
            ((pathList n C g0.1).getD a 0 + (pathList n C g0.1).getD b 0) := by
        intro g0
        rw [hwj]
        unfold pathList
        have h1 := stepList_getD_gate (pathStep n g0.1) (List.replicate n 0) C.gates j C.gates[j] 0 hget
        simp only [List.length_replicate] at h1
        rw [h1]
        simp only [pathStep, hinp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero, stepList_length, List.length_replicate, List.length_take,
          Nat.min_eq_left hj_le]
        have hiff : (n + j = n + g0.1) ↔ (j = g0.1) := by omega
        simp only [hiff]
        have ha' := stepList_getD_prefix (pathStep n g0.1) (List.replicate n 0) C.gates j a 0 hj_le (by simp [ha_le])
        have hb' := stepList_getD_prefix (pathStep n g0.1) (List.replicate n 0) C.gates j b 0 hj_le (by simp [hb_le])
        rw [ha', hb']
      have hiha := ih a haw (by omega)
      have hihb := ih b hbw (by omega)
      have hsum_ind : ∑ g0 : Fin C.size, (if j = g0.1 then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin C.size)]
        · simp
        · intro g0 _ hne
          have hne' : j ≠ g0.1 := fun h => hne (Fin.ext h.symm)
          simp [hne']
        · intro hmem
          exact absurd (Finset.mem_univ _) hmem
      rw [hL, hiha, hihb]
      simp_rw [hP]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_ind]
      omega

lemma wire_eval_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (a b : ℕ) (hget : C.gates[j]? = some g)
    (hinp : g.inputs = [a, b]) (hab : a < b) (hbj : b < n + j) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have hj_le : j ≤ C.gates.length := Nat.le_of_lt hj
  let f : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map (fun i => w.getD i false))
  have h1 := stepList_getD_gate f (List.ofFn x) C.gates j g false hget
  simp only [List.length_ofFn] at h1
  change (stepList f (List.ofFn x) C.gates).getD (n + j) false = _
  rw [h1]
  simp only [f, hinp, List.map_cons, List.map_nil]
  have ha' := stepList_getD_prefix f (List.ofFn x) C.gates j a false hj_le (by simp; omega)
  have hb' := stepList_getD_prefix f (List.ofFn x) C.gates j b false hj_le (by simp; omega)
  rw [← ha', ← hb']
  rfl

lemma wire_eval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  let f : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map (fun i => w.getD i false))
  change (stepList f (List.ofFn x) C.gates).getD w false = x ⟨w, hw⟩
  rw [stepList_getD_lt f (List.ofFn x) C.gates w false (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

lemma leafList_gate {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate) (a b : ℕ)
    (hget : C.gates[j]? = some g) (hinp : g.inputs = [a, b]) (hab : a < b) (hbj : b < n + j) :
    (leafList n C).getD (n + j) 0 = (leafList n C).getD a 0 + (leafList n C).getD b 0 := by
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have hj_le : j ≤ C.gates.length := Nat.le_of_lt hj
  unfold leafList
  have h1 := stepList_getD_gate leafStep (List.replicate n 1) C.gates j g 0 hget
  simp only [List.length_replicate] at h1
  rw [h1]
  simp only [leafStep, hinp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  have ha' := stepList_getD_prefix leafStep (List.replicate n 1) C.gates j a 0 hj_le (by simp; omega)
  have hb' := stepList_getD_prefix leafStep (List.replicate n 1) C.gates j b 0 hj_le (by simp; omega)
  rw [ha', hb']

lemma kw_partition {n : ℕ} (C : Circuit)
    (hmono : Monotone2 C)
    (hfan : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) :
    ∀ (w : ℕ), w < n + C.size →
      ∀ (A B : Set (Fin n → Bool)),
        (∀ x ∈ A, (C.wires (List.ofFn x)).getD w false = true) →
        (∀ y ∈ B, (C.wires (List.ofFn y)).getD w false = false) →
        ∃ (P Q : Fin ((leafList n C).getD w 0) → (Fin n → Bool) → Prop)
          (v : Fin ((leafList n C).getD w 0) → Fin n),
          ∀ x ∈ A, ∀ y ∈ B,
            (∃! r : Fin ((leafList n C).getD w 0), P r x ∧ Q r y) ∧
            ∀ r, P r x → Q r y → x (v r) = true ∧ y (v r) = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw A B hA hB
    by_cases hlt : w < n
    · have hL : (leafList n C).getD w 0 = 1 := by
        unfold leafList
        rw [stepList_getD_lt _ _ _ w 0 (by simp [hlt])]
        simp [List.getD_eq_getElem?_getD, hlt]
      refine ⟨fun _ _ => True, fun _ _ => True, fun _ => ⟨w, hlt⟩, ?_⟩
      intro x hx y hy
      refine ⟨?_, ?_⟩
      · refine ⟨⟨0, by omega⟩, ⟨trivial, trivial⟩, ?_⟩
        intro r _
        exact Fin.ext (by omega)
      · intro _ _ _
        have hx' := hA x hx
        have hy' := hB y hy
        rw [wire_eval_input C x w hlt] at hx'
        rw [wire_eval_input C y w hlt] at hy'
        exact ⟨hx', hy'⟩
    · have hj : w - n < C.gates.length := by
        change w < n + C.gates.length at hw
        omega
      let j := w - n
      have hwj : w = n + j := by omega
      have hget : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨a, b, hinp, hab, hbj⟩ := hfan j C.gates[j] hget
      have hL : (leafList n C).getD w 0 =
          (leafList n C).getD a 0 + (leafList n C).getD b 0 := by
        rw [hwj]
        exact leafList_gate C j C.gates[j] a b hget hinp hab hbj
      have hgmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
      have hop := (hmono C.gates[j] hgmem).1
      have hwire : ∀ z : Fin n → Bool,
          (C.wires (List.ofFn z)).getD w false =
            C.gates[j].op.eval [(C.wires (List.ofFn z)).getD a false,
              (C.wires (List.ofFn z)).getD b false] := by
        intro z
        rw [hwj]
        exact wire_eval_gate C z j C.gates[j] a b hget hinp hab hbj
      let e : Fin ((leafList n C).getD w 0) ≃
          Fin ((leafList n C).getD a 0) ⊕ Fin ((leafList n C).getD b 0) :=
        (finCongr hL).trans finSumFinEquiv.symm
      rcases hop with hand | hor
      · let B1 : Set (Fin n → Bool) :=
          {y | y ∈ B ∧ (C.wires (List.ofFn y)).getD a false = false}
        let B2 : Set (Fin n → Bool) :=
          {y | y ∈ B ∧ (C.wires (List.ofFn y)).getD a false = true ∧
            (C.wires (List.ofFn y)).getD b false = false}
        have hAa : ∀ x ∈ A, (C.wires (List.ofFn x)).getD a false = true := by
          intro x hx
          have hxw := hA x hx
          rw [hwire x, hand] at hxw
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true] at hxw
          exact hxw.1
        have hAb : ∀ x ∈ A, (C.wires (List.ofFn x)).getD b false = true := by
          intro x hx
          have hxw := hA x hx
          rw [hwire x, hand] at hxw
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true] at hxw
          exact hxw.2
        obtain ⟨Pa, Qa, va, hrecA⟩ := ih a (by omega) (by omega) A B1 hAa (fun y hy => hy.2)
        obtain ⟨Pb, Qb, vb, hrecB⟩ := ih b (by omega) (by omega) A B2 hAb (fun y hy => hy.2.2)
        refine ⟨fun r x => match e r with | Sum.inl r1 => Pa r1 x | Sum.inr r2 => Pb r2 x,
          fun r y => match e r with | Sum.inl r1 => y ∈ B1 ∧ Qa r1 y | Sum.inr r2 => y ∈ B2 ∧ Qb r2 y,
          fun r => match e r with | Sum.inl r1 => va r1 | Sum.inr r2 => vb r2, ?_⟩
        intro x hx y hy
        have hyw := hB y hy
        rw [hwire y, hand] at hyw
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_false_iff] at hyw
        cases hya : (C.wires (List.ofFn y)).getD a false
        · have hy1 : y ∈ B1 := ⟨hy, hya⟩
          have hy2 : y ∉ B2 := fun h => by
            have h' := h.2.1
            rw [hya] at h'
            exact Bool.noConfusion h'
          obtain ⟨⟨r1, ⟨hP1, hQ1⟩, hr1u⟩, hprop1⟩ := hrecA x hx y hy1
          refine ⟨?_, ?_⟩
          · refine ⟨e.symm (Sum.inl r1), ?_, ?_⟩
            · simp [hP1, hy1, hQ1]
            · intro r hr
              rcases hr with ⟨hPr, hQr⟩
              cases her : e r with
              | inl r1' =>
                rw [her] at hPr hQr
                have hreq : r1' = r1 := hr1u r1' ⟨hPr, hQr.2⟩
                apply e.injective
                simp [her, hreq]
              | inr r2' =>
                rw [her] at hQr
                exact absurd hQr.1 hy2
          · intro r hPr hQr
            dsimp only
            cases her : e r with
            | inl r1' =>
              rw [her] at hPr hQr
              exact hprop1 r1' hPr hQr.2
            | inr r2' =>
              rw [her] at hQr
              exact absurd hQr.1 hy2
        · have hyb : (C.wires (List.ofFn y)).getD b false = false := by
            rcases hyw with h1 | h2
            · rw [hya] at h1; exact Bool.noConfusion h1
            · exact h2
          have hy2 : y ∈ B2 := ⟨hy, hya, hyb⟩
          have hy1 : y ∉ B1 := fun h => by
            have h' := h.2
            rw [hya] at h'
            exact Bool.noConfusion h'
          obtain ⟨⟨r2, ⟨hP2, hQ2⟩, hr2u⟩, hprop2⟩ := hrecB x hx y hy2
          refine ⟨?_, ?_⟩
          · refine ⟨e.symm (Sum.inr r2), ?_, ?_⟩
            · simp [hP2, hy2, hQ2]
            · intro r hr
              rcases hr with ⟨hPr, hQr⟩
              cases her : e r with
              | inl r1' =>
                rw [her] at hQr
                exact absurd hQr.1 hy1
              | inr r2' =>
                rw [her] at hPr hQr
                have hreq : r2' = r2 := hr2u r2' ⟨hPr, hQr.2⟩
                apply e.injective
                simp [her, hreq]
          · intro r hPr hQr
            dsimp only
            cases her : e r with
            | inl r1' =>
              rw [her] at hQr
              exact absurd hQr.1 hy1
            | inr r2' =>
              rw [her] at hPr hQr
              exact hprop2 r2' hPr hQr.2
      · let A1 : Set (Fin n → Bool) :=
          {x | x ∈ A ∧ (C.wires (List.ofFn x)).getD a false = true}
        let A2 : Set (Fin n → Bool) :=
          {x | x ∈ A ∧ (C.wires (List.ofFn x)).getD a false = false ∧
            (C.wires (List.ofFn x)).getD b false = true}
        have hBa : ∀ y ∈ B, (C.wires (List.ofFn y)).getD a false = false := by
          intro y hy
          have hyw := hB y hy
          rw [hwire y, hor] at hyw
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            Bool.or_eq_false_iff] at hyw
          exact hyw.1
        have hBb : ∀ y ∈ B, (C.wires (List.ofFn y)).getD b false = false := by
          intro y hy
          have hyw := hB y hy
          rw [hwire y, hor] at hyw
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            Bool.or_eq_false_iff] at hyw
          exact hyw.2
        obtain ⟨Pa, Qa, va, hrecA⟩ := ih a (by omega) (by omega) A1 B (fun x hx => hx.2) hBa
        obtain ⟨Pb, Qb, vb, hrecB⟩ := ih b (by omega) (by omega) A2 B (fun x hx => hx.2.2) hBb
        refine ⟨fun r x => match e r with | Sum.inl r1 => x ∈ A1 ∧ Pa r1 x | Sum.inr r2 => x ∈ A2 ∧ Pb r2 x,
          fun r y => match e r with | Sum.inl r1 => Qa r1 y | Sum.inr r2 => Qb r2 y,
          fun r => match e r with | Sum.inl r1 => va r1 | Sum.inr r2 => vb r2, ?_⟩
        intro x hx y hy
        have hxw := hA x hx
        rw [hwire x, hor] at hxw
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true] at hxw
        cases hxa : (C.wires (List.ofFn x)).getD a false
        · have hxb : (C.wires (List.ofFn x)).getD b false = true := by
            rcases hxw with h1 | h2
            · rw [hxa] at h1; exact Bool.noConfusion h1
            · exact h2
          have hx2 : x ∈ A2 := ⟨hx, hxa, hxb⟩
          have hx1 : x ∉ A1 := fun h => by
            have h' := h.2
            rw [hxa] at h'
            exact Bool.noConfusion h'
          obtain ⟨⟨r2, ⟨hP2, hQ2⟩, hr2u⟩, hprop2⟩ := hrecB x hx2 y hy
          refine ⟨?_, ?_⟩
          · refine ⟨e.symm (Sum.inr r2), ?_, ?_⟩
            · simp [hx2, hP2, hQ2]
            · intro r hr
              rcases hr with ⟨hPr, hQr⟩
              cases her : e r with
              | inl r1' =>
                rw [her] at hPr
                exact absurd hPr.1 hx1
              | inr r2' =>
                rw [her] at hPr hQr
                have hreq : r2' = r2 := hr2u r2' ⟨hPr.2, hQr⟩
                apply e.injective
                simp [her, hreq]
          · intro r hPr hQr
            dsimp only
            cases her : e r with
            | inl r1' =>
              rw [her] at hPr
              exact absurd hPr.1 hx1
            | inr r2' =>
              rw [her] at hPr hQr
              exact hprop2 r2' hPr.2 hQr
        · have hx1 : x ∈ A1 := ⟨hx, hxa⟩
          have hx2 : x ∉ A2 := fun h => by
            have h' := h.2.1
            rw [hxa] at h'
            exact Bool.noConfusion h'
          obtain ⟨⟨r1, ⟨hP1, hQ1⟩, hr1u⟩, hprop1⟩ := hrecA x hx1 y hy
          refine ⟨?_, ?_⟩
          · refine ⟨e.symm (Sum.inl r1), ?_, ?_⟩
            · simp [hx1, hP1, hQ1]
            · intro r hr
              rcases hr with ⟨hPr, hQr⟩
              cases her : e r with
              | inl r1' =>
                rw [her] at hPr hQr
                have hreq : r1' = r1 := hr1u r1' ⟨hPr.2, hQr⟩
                apply e.injective
                simp [her, hreq]
              | inr r2' =>
                rw [her] at hPr
                exact absurd hPr.1 hx2
          · intro r hPr hQr
            dsimp only
            cases her : e r with
            | inl r1' =>
              rw [her] at hPr hQr
              exact hprop1 r1' hPr.2 hQr
            | inr r2' =>
              rw [her] at hPr
              exact absurd hPr.1 hx2

lemma line_card {q m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1) (l : Fin m) :
    (Finset.univ.filter (fun p : Fin m => inc p l)).card = q + 1 := by
  rw [← Fintype.card_subtype]
  exact hline l

lemma point_card {q m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hq : 300 ≤ q) (hm : m = q ^ 2 + q + 1)
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l)
    (p : Fin m) :
    (Finset.univ.filter (fun l : Fin m => inc p l)).card = q + 1 := by
  have h1 : ∑ l : Fin m, ∑ p' : Fin m, (if inc p l ∧ inc p' l ∧ p' ≠ p then 1 else 0) =
      (Finset.univ.filter (fun l : Fin m => inc p l)).card * q := by
    have hinner : ∀ l : Fin m,
        ∑ p' : Fin m, (if inc p l ∧ inc p' l ∧ p' ≠ p then 1 else 0) =
          if inc p l then q else 0 := by
      intro l
      by_cases hpl : inc p l
      · simp only [hpl, true_and, ↓reduceIte]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hfilt : Finset.univ.filter (fun p' : Fin m => inc p' l ∧ p' ≠ p) =
            (Finset.univ.filter (fun p' : Fin m => inc p' l)).erase p := by
          ext p'
          simp [and_comm]
        rw [hfilt, Finset.card_erase_of_mem (by simp [hpl]), line_card inc hline l]
        omega
      · simp [hpl]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ l : Fin m, ∑ p' : Fin m, (if inc p l ∧ inc p' l ∧ p' ≠ p then 1 else 0) =
      (q + 1) * q := by
    rw [Finset.sum_comm]
    have hinner : ∀ p' : Fin m,
        ∑ l : Fin m, (if inc p l ∧ inc p' l ∧ p' ≠ p then 1 else 0) =
          if p' ≠ p then 1 else 0 := by
      intro p'
      by_cases hne : p' ≠ p
      · simp only [ne_eq, hne, not_false_eq_true, and_true, ↓reduceIte]
        obtain ⟨l0, hl0, hl0u⟩ := huniq p p' hne.symm
        rw [Finset.sum_eq_single l0]
        · simp [hl0]
        · intro l _ hlne
          have hnot : ¬(inc p l ∧ inc p' l) := fun hl => hlne (hl0u l hl)
          simp [hnot]
        · intro hmem
          exact absurd (Finset.mem_univ l0) hmem
      · simp only [hne, and_false, ↓reduceIte, Finset.sum_const_zero]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have hfilt : Finset.univ.filter (fun p' : Fin m => p' ≠ p) = Finset.univ.erase p := by
      ext p'
      simp
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin, hm,
      Nat.add_sub_cancel]
    ring
  have hmul : (Finset.univ.filter (fun l : Fin m => inc p l)).card * q = (q + 1) * q :=
    h1.symm.trans h2
  exact Nat.eq_of_mul_eq_mul_right (by omega) hmul

def INC {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc] : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => inc e.1 e.2)

lemma INC_card {q m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hq : 300 ≤ q) (hm : m = q ^ 2 + q + 1)
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l) :
    (INC inc).card = m * (q + 1) := by
  unfold INC
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hrow : ∀ p : Fin m, (∑ l : Fin m, if inc p l then 1 else 0) = q + 1 := by
    intro p
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    exact point_card inc hq hm hline huniq p
  simp [hrow]

def posInput {m : ℕ} (p l : Fin m) : Fin (m + m) → Bool :=
  fun z => decide (z = Fin.castAdd m p ∨ z = Fin.natAdd m l)

def negInput {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc] (p l : Fin m) :
    Fin (m + m) → Bool :=
  fun z => Fin.addCases (fun p' => decide (inc p' l ∧ p' ≠ p))
    (fun l' => decide (inc p l' ∧ l' ≠ l)) z

lemma negInput_castAdd {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (p l p' : Fin m) :
    negInput inc p l (Fin.castAdd m p') = decide (inc p' l ∧ p' ≠ p) :=
  Fin.addCases_left p'

lemma negInput_natAdd {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (p l l' : Fin m) :
    negInput inc p l (Fin.natAdd m l') = decide (inc p l' ∧ l' ≠ l) :=
  Fin.addCases_right l'

lemma negInput_line_card {q m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hq : 300 ≤ q) (hm : m = q ^ 2 + q + 1)
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l)
    {p l : Fin m} (hpl : inc p l) :
    Fintype.card { l' : Fin m // negInput inc p l (Fin.natAdd m l') = true } ≤ q := by
  rw [Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun l' : Fin m => negInput inc p l (Fin.natAdd m l') = true) =
      (Finset.univ.filter (fun l' : Fin m => inc p l')).erase l := by
    ext l'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, negInput_natAdd,
      decide_eq_true_eq, and_comm]
  rw [hfilt, Finset.card_erase_of_mem (by simp [hpl]), point_card inc hq hm hline huniq p]
  omega

lemma negInput_no_inc {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l)
    {p l : Fin m} (hpl : inc p l) :
    ¬∃ p' l' : Fin m, inc p' l' ∧
      negInput inc p l (Fin.castAdd m p') = true ∧
      negInput inc p l (Fin.natAdd m l') = true := by
  rintro ⟨p', l', hp'l', hp', hl'⟩
  rw [negInput_castAdd, decide_eq_true_eq] at hp'
  rw [negInput_natAdd, decide_eq_true_eq] at hl'
  obtain ⟨_, _, hlu⟩ := huniq p p' hp'.2.symm
  have heq : l = l' := (hlu l ⟨hpl, hp'.1⟩).trans (hlu l' ⟨hl'.1, hp'l'⟩).symm
  exact hl'.2 heq.symm

section RankEngine

open scoped Classical

def Ku {m L : ℕ} (v : Fin L → Fin (m + m)) (u : Fin (m + m)) : Finset (Fin L) :=
  Finset.univ.filter (fun r => v r = u)

def Eu {m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc] (u : Fin (m + m)) :
    Finset (Fin m × Fin m) :=
  (INC inc).filter (fun e => Fin.castAdd m e.1 = u ∨ Fin.natAdd m e.2 = u)

noncomputable def Du {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (u : Fin (m + m)) : Finset (Fin m × Fin m) :=
  (Eu inc u).filter (fun e => ∃ r ∈ Ku v u, P r (posInput e.1 e.2) ∧ Q r (negInput inc e.1 e.2))

noncomputable def Mu {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (u : Fin (m + m)) : Finset (Fin m × Fin m) :=
  (Eu inc u) \ (Du inc P Q v u)

noncomputable def rowVec {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (u : Fin (m + m)) (e : Fin m × Fin m) : (Fin m × Fin m) → ℚ :=
  fun e' => ∑ r ∈ Ku v u,
    if P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2) then (1 : ℚ) else 0

lemma castAdd_ne_natAdd {m : ℕ} (p l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd m l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma Eu_card {q m : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hq : 300 ≤ q) (hm : m = q ^ 2 + q + 1)
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l)
    (u : Fin (m + m)) :
    (Eu inc u).card = q + 1 := by
  by_cases hu : u.1 < m
  · let p : Fin m := ⟨u.1, hu⟩
    have hup : u = Fin.castAdd m p := Fin.ext rfl
    rw [hup]
    have hbij : (Eu inc (Fin.castAdd m p)).card =
        (Finset.univ.filter (fun l : Fin m => inc p l)).card := by
      refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
      · intro e he
        simp only [Eu, INC, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rcases he.2 with h1 | h2
        · have hp : e.1 = p := Fin.castAdd_injective m m h1
          rw [← hp]; exact he.1
        · exact absurd h2.symm (castAdd_ne_natAdd p e.2)
      · intro e1 he1 e2 he2 hEq
        simp only [Eu, INC, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
        have h1 : e1.1 = p := by
          rcases he1.2 with h | h
          · exact Fin.castAdd_injective m m h
          · exact absurd h.symm (castAdd_ne_natAdd p e1.2)
        have h2 : e2.1 = p := by
          rcases he2.2 with h | h
          · exact Fin.castAdd_injective m m h
          · exact absurd h.symm (castAdd_ne_natAdd p e2.2)
        exact Prod.ext (h1.trans h2.symm) hEq
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        refine ⟨(p, l), ?_, rfl⟩
        simp [Eu, INC, hl]
    rw [hbij]
    exact point_card inc hq hm hline huniq p
  · let l : Fin m := ⟨u.1 - m, by omega⟩
    have hul : u = Fin.natAdd m l := Fin.ext (by simp [l]; omega)
    rw [hul]
    have hbij : (Eu inc (Fin.natAdd m l)).card =
        (Finset.univ.filter (fun p : Fin m => inc p l)).card := by
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        simp only [Eu, INC, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rcases he.2 with h1 | h2
        · exact absurd h1 (castAdd_ne_natAdd e.1 l)
        · have hl : e.2 = l := Fin.natAdd_injective m m h2
          rw [← hl]; exact he.1
      · intro e1 he1 e2 he2 hEq
        simp only [Eu, INC, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
        have h1 : e1.2 = l := by
          rcases he1.2 with h | h
          · exact absurd h (castAdd_ne_natAdd e1.1 l)
          · exact Fin.natAdd_injective m m h
        have h2 : e2.2 = l := by
          rcases he2.2 with h | h
          · exact absurd h (castAdd_ne_natAdd e2.1 l)
          · exact Fin.natAdd_injective m m h
        exact Prod.ext hEq (h1.trans h2.symm)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨(p, l), ?_, rfl⟩
        simp [Eu, INC, hp]
    rw [hbij]
    exact line_card inc hline l

lemma sum_Ku_card {m L : ℕ} (v : Fin L → Fin (m + m)) :
    ∑ u : Fin (m + m), (Ku v u).card = L := by
  have h1 := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin L)))
    (t := (Finset.univ : Finset (Fin (m + m))))
    (f := v)
    (fun r _ => Finset.mem_univ (v r))
  simpa [Ku] using h1.symm

lemma existsUnique_mem_Mu {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false)
    {e : Fin m × Fin m} (he : e ∈ INC inc) :
    ∃! u : Fin (m + m), e ∈ Mu inc P Q v u := by
  obtain ⟨⟨r0, ⟨hr0P, hr0Q⟩, hr0u⟩, hprop⟩ := hrect e e he he
  have hpos := (hprop r0 hr0P hr0Q).1
  simp only [posInput, decide_eq_true_eq] at hpos
  have hne : Fin.castAdd m e.1 ≠ Fin.natAdd m e.2 := castAdd_ne_natAdd e.1 e.2
  rcases hpos with h1 | h2
  · refine ⟨Fin.natAdd m e.2, ?_, ?_⟩
    · simp only [Mu, Du, Eu, Ku, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨he, Or.inr trivial⟩, ?_⟩
      rintro ⟨_, r, hrv, hrP, hrQ⟩
      have hreq : r = r0 := hr0u r ⟨hrP, hrQ⟩
      rw [hreq, h1] at hrv
      exact hne hrv
    · intro u hu
      simp only [Mu, Du, Eu, Ku, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu.1.2 with rfl | rfl
      · exfalso
        exact hu.2 ⟨⟨he, Or.inl rfl⟩, r0, h1, hr0P, hr0Q⟩
      · rfl
  · refine ⟨Fin.castAdd m e.1, ?_, ?_⟩
    · simp only [Mu, Du, Eu, Ku, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨he, Or.inl trivial⟩, ?_⟩
      rintro ⟨_, r, hrv, hrP, hrQ⟩
      have hreq : r = r0 := hr0u r ⟨hrP, hrQ⟩
      rw [hreq, h2] at hrv
      exact hne hrv.symm
    · intro u hu
      simp only [Mu, Du, Eu, Ku, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu.1.2 with rfl | rfl
      · rfl
      · exfalso
        exact hu.2 ⟨⟨he, Or.inr rfl⟩, r0, h2, hr0P, hr0Q⟩

lemma sum_Mu_card {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false) :
    ∑ u : Fin (m + m), (Mu inc P Q v u).card = (INC inc).card := by
  have hsub : ∀ u, Mu inc P Q v u ⊆ INC inc := by
    intro u e he
    simp only [Mu, Eu, Finset.mem_sdiff, Finset.mem_filter] at he
    exact he.1.1
  calc
    ∑ u : Fin (m + m), (Mu inc P Q v u).card
        = ∑ u : Fin (m + m), ∑ e ∈ INC inc, if e ∈ Mu inc P Q v u then 1 else 0 := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
          congr 1
          ext e
          simp only [Finset.mem_filter]
          exact ⟨fun he => ⟨hsub u he, he⟩, fun h => h.2⟩
    _ = ∑ e ∈ INC inc, ∑ u : Fin (m + m), if e ∈ Mu inc P Q v u then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ _e ∈ INC inc, 1 := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          obtain ⟨u0, hu0, hu0u⟩ := existsUnique_mem_Mu inc P Q v hrect he
          rw [Finset.sum_eq_single u0]
          · simp [hu0]
          · intro u _ hune
            have : e ∉ Mu inc P Q v u := fun hmem => hune (hu0u u hmem)
            simp [this]
          · intro hmem
            exact absurd (Finset.mem_univ u0) hmem
    _ = (INC inc).card := by
          simp

lemma off_diag_owner {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false)
    (u : Fin (m + m)) {e e' : Fin m × Fin m}
    (he : e ∈ Eu inc u) (he' : e' ∈ Eu inc u) (hne : e ≠ e')
    {r : Fin L} (hrP : P r (posInput e.1 e.2)) (hrQ : Q r (negInput inc e'.1 e'.2)) :
    v r = u := by
  simp only [Eu, INC, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
  have hprop := (hrect e e' (by simp [INC, he.1]) (by simp [INC, he'.1])).2 r hrP hrQ
  obtain ⟨hpos, hneg⟩ := hprop
  simp only [posInput, decide_eq_true_eq] at hpos
  by_cases hu : u.1 < m
  · let p : Fin m := ⟨u.1, hu⟩
    have hup : u = Fin.castAdd m p := Fin.ext rfl
    rw [hup] at he he' ⊢
    have he1 : e.1 = p := by
      rcases he.2 with h | h
      · exact Fin.castAdd_injective m m h
      · exact absurd h.symm (castAdd_ne_natAdd p e.2)
    have he'1 : e'.1 = p := by
      rcases he'.2 with h | h
      · exact Fin.castAdd_injective m m h
      · exact absurd h.symm (castAdd_ne_natAdd p e'.2)
    have hne2 : e.2 ≠ e'.2 := fun h => hne (Prod.ext (he1.trans he'1.symm) h)
    rcases hpos with h1 | h2
    · rw [h1, he1]
    · exfalso
      rw [h2, he'1, negInput_natAdd] at hneg
      have hinc : inc p e.2 := by rw [← he1]; exact he.1
      have htrue : decide (inc p e.2 ∧ e.2 ≠ e'.2) = true := decide_eq_true ⟨hinc, hne2⟩
      rw [htrue] at hneg
      exact Bool.noConfusion hneg
  · let l : Fin m := ⟨u.1 - m, by omega⟩
    have hul : u = Fin.natAdd m l := Fin.ext (by simp [l]; omega)
    rw [hul] at he he' ⊢
    have he2 : e.2 = l := by
      rcases he.2 with h | h
      · exact absurd h (castAdd_ne_natAdd e.1 l)
      · exact Fin.natAdd_injective m m h
    have he'2 : e'.2 = l := by
      rcases he'.2 with h | h
      · exact absurd h (castAdd_ne_natAdd e'.1 l)
      · exact Fin.natAdd_injective m m h
    have hne1 : e.1 ≠ e'.1 := fun h => hne (Prod.ext h (he2.trans he'2.symm))
    rcases hpos with h1 | h2
    · exfalso
      rw [h1, he'2, negInput_castAdd] at hneg
      have hinc : inc e.1 l := by rw [← he2]; exact he.1
      have htrue : decide (inc e.1 l ∧ e.1 ≠ e'.1) = true := decide_eq_true ⟨hinc, hne1⟩
      rw [htrue] at hneg
      exact Bool.noConfusion hneg
    · rw [h2, he2]

lemma rowVec_off_diag {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false)
    (u : Fin (m + m)) {e e' : Fin m × Fin m}
    (he : e ∈ Eu inc u) (he' : e' ∈ Eu inc u) (hne : e ≠ e') :
    rowVec inc P Q v u e e' = 1 := by
  have heI : e ∈ INC inc := (Finset.mem_filter.mp he).1
  have he'I : e' ∈ INC inc := (Finset.mem_filter.mp he').1
  obtain ⟨⟨r0, ⟨hr0P, hr0Q⟩, hr0u⟩, _⟩ := hrect e e' heI he'I
  have hr0u' : r0 ∈ Ku v u := by
    simp only [Ku, Finset.mem_filter, Finset.mem_univ, true_and]
    exact off_diag_owner inc P Q v hrect u he he' hne hr0P hr0Q
  unfold rowVec
  rw [Finset.sum_eq_single r0]
  · simp [hr0P, hr0Q]
  · intro r _ hrne
    have hnot : ¬(P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) :=
      fun hr => hrne (hr0u r hr)
    simp [hnot]
  · intro hmem
    exact absurd hr0u' hmem

lemma rowVec_diag_Du {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false)
    (u : Fin (m + m)) {e : Fin m × Fin m} (he : e ∈ Du inc P Q v u) :
    rowVec inc P Q v u e e = 1 := by
  simp only [Du, Finset.mem_filter] at he
  obtain ⟨heE, r0, hr0u, hr0P, hr0Q⟩ := he
  have heI : e ∈ INC inc := (Finset.mem_filter.mp heE).1
  obtain ⟨⟨_, _, hru⟩, _⟩ := hrect e e heI heI
  unfold rowVec
  rw [Finset.sum_eq_single r0]
  · simp [hr0P, hr0Q]
  · intro r _ hrne
    have hnot : ¬(P r (posInput e.1 e.2) ∧ Q r (negInput inc e.1 e.2)) := fun hr =>
      hrne ((hru r hr).trans (hru r0 ⟨hr0P, hr0Q⟩).symm)
    simp [hnot]
  · intro hmem
    exact absurd hr0u hmem

lemma rowVec_diag_Mu {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (u : Fin (m + m)) {e : Fin m × Fin m} (he : e ∈ Mu inc P Q v u) :
    rowVec inc P Q v u e e = 0 := by
  simp only [Mu, Du, Finset.mem_sdiff, Finset.mem_filter] at he
  unfold rowVec
  refine Finset.sum_eq_zero (fun r hr => ?_)
  have hnot : ¬(P r (posInput e.1 e.2) ∧ Q r (negInput inc e.1 e.2)) := by
    rintro ⟨hrP, hrQ⟩
    exact he.2 ⟨he.1, r, hr, hrP, hrQ⟩
  simp [hnot]

lemma card_le_Ku_of_rows_indep {m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (u : Fin (m + m)) (I : Finset (Fin m × Fin m))
    (hind : ∀ a : I → ℚ,
      (∀ e' : Fin m × Fin m, ∑ e : I, a e * rowVec inc P Q v u e.1 e' = 0) → a = 0) :
    I.card ≤ (Ku v u).card := by
  let T : (I → ℚ) →ₗ[ℚ] (Ku v u → ℚ) :=
    { toFun := fun a r => ∑ e : I, a e * (if P r.1 (posInput e.1.1 e.1.2) then (1 : ℚ) else 0)
      map_add' := by
        intro a b
        ext r
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext r
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine hind a (fun e' => ?_)
    have hcalc : ∑ e : I, a e * rowVec inc P Q v u e.1 e' =
        ∑ r : Ku v u, T a r * (if Q r.1 (negInput inc e'.1 e'.2) then (1 : ℚ) else 0) := by
      calc
        ∑ e : I, a e * rowVec inc P Q v u e.1 e'
            = ∑ e : I, ∑ r : Ku v u,
                a e * (if P r.1 (posInput e.1.1 e.1.2) then (1 : ℚ) else 0) *
                  (if Q r.1 (negInput inc e'.1 e'.2) then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl (fun e _ => ?_)
              unfold rowVec
              rw [← Finset.sum_coe_sort (Ku v u), Finset.mul_sum]
              refine Finset.sum_congr rfl (fun r _ => ?_)
              by_cases hP : P r.1 (posInput e.1.1 e.1.2) <;>
                by_cases hQ : Q r.1 (negInput inc e'.1 e'.2) <;>
                simp [hP, hQ]
        _ = ∑ r : Ku v u, ∑ e : I,
              a e * (if P r.1 (posInput e.1.1 e.1.2) then (1 : ℚ) else 0) *
                (if Q r.1 (negInput inc e'.1 e'.2) then (1 : ℚ) else 0) := by
              rw [Finset.sum_comm]
        _ = ∑ r : Ku v u, T a r * (if Q r.1 (negInput inc e'.1 e'.2) then (1 : ℚ) else 0) := by
              refine Finset.sum_congr rfl (fun r _ => ?_)
              rw [← Finset.sum_mul]
              rfl
    rw [hcalc, ha]
    simp
  have hle := LinearMap.finrank_le_finrank_of_injective hTinj
  simpa [Module.finrank_pi, Fintype.card_coe] using hle

lemma per_vertex_bound {q m L : ℕ} (inc : Fin m → Fin m → Prop) [DecidableRel inc]
    (hq : 300 ≤ q) (hm : m = q ^ 2 + q + 1)
    (hline : ∀ l : Fin m, Fintype.card { p : Fin m // inc p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin m, p1 ≠ p2 → ∃! l : Fin m, inc p1 l ∧ inc p2 l)
    (P Q : Fin L → (Fin (m + m) → Bool) → Prop) (v : Fin L → Fin (m + m))
    (hrect : ∀ e e' : Fin m × Fin m, e ∈ INC inc → e' ∈ INC inc →
      (∃! r : Fin L, P r (posInput e.1 e.2) ∧ Q r (negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (posInput e.1 e.2) → Q r (negInput inc e'.1 e'.2) →
        posInput e.1 e.2 (v r) = true ∧ negInput inc e'.1 e'.2 (v r) = false)
    (u : Fin (m + m)) :
    (Mu inc P Q v u).card ≤ (Ku v u).card := by
  by_cases hne : (Du inc P Q v u).Nonempty
  · obtain ⟨e0, he0Du⟩ := hne
    have he0Eu : e0 ∈ Eu inc u := (Finset.mem_filter.mp he0Du).1
    have he0nMu : e0 ∉ Mu inc P Q v u := by
      simp [Mu, he0Du]
    let I := insert e0 (Mu inc P Q v u)
    have hIcard : I.card = (Mu inc P Q v u).card + 1 := Finset.card_insert_of_notMem he0nMu
    have hle : I.card ≤ (Ku v u).card := by
      refine card_le_Ku_of_rows_indep inc P Q v u I (fun a ha => ?_)
      have hIsub : ∀ e : I, e.1 ∈ Eu inc u := by
        intro e
        rcases Finset.mem_insert.mp e.2 with h1 | h2
        · rw [h1]; exact he0Eu
        · exact (Finset.mem_sdiff.mp h2).1
      let tot : ℚ := ∑ e : I, a e
      have htot : tot = 0 := by
        have h0 := ha e0
        have hrow : ∀ e : I, rowVec inc P Q v u e.1 e0 = 1 := by
          intro e
          by_cases heq : e.1 = e0
          · rw [heq]; exact rowVec_diag_Du inc P Q v hrect u he0Du
          · exact rowVec_off_diag inc P Q v hrect u (hIsub e) he0Eu heq
        have h0' : ∑ e : I, a e * 1 = 0 := by
          simpa [hrow] using h0
        simpa [tot] using h0'
      have ha_other : ∀ e : I, e.1 ≠ e0 → a e = 0 := by
        intro e hne'
        have heMu : e.1 ∈ Mu inc P Q v u := by
          rcases Finset.mem_insert.mp e.2 with h1 | h2
          · exact absurd h1 hne'
          · exact h2
        have hev := ha e.1
        have hsplit : ∑ f : I, a f * rowVec inc P Q v u f.1 e.1 = tot - a e := by
          have hsum : ∑ f : I, a f * rowVec inc P Q v u f.1 e.1 =
              ∑ f : I, (if f = e then 0 else a f) := by
            refine Finset.sum_congr rfl (fun f _ => ?_)
            by_cases hfe : f = e
            · subst hfe
              simp [rowVec_diag_Mu inc P Q v u heMu]
            · have hfe' : f.1 ≠ e.1 := fun hval => hfe (Subtype.ext hval)
              simp [hfe, rowVec_off_diag inc P Q v hrect u (hIsub f) (hIsub e) hfe']
          rw [hsum]
          have hadd : (∑ f : I, if f = e then 0 else a f) + a e = tot := by
            have : ∑ f : I, (if f = e then a f else 0) = a e := by
              simp
            rw [← this, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun f _ => ?_)
            by_cases hfe : f = e <;> simp [hfe]
          linarith
        rw [hsplit, htot] at hev
        linarith
      funext e
      by_cases heq : e.1 = e0
      · have he_eq : e = ⟨e0, Finset.mem_insert_self e0 _⟩ := Subtype.ext heq
        have hsum : tot = a e + ∑ f ∈ Finset.univ.erase e, a f :=
          (Finset.add_sum_erase Finset.univ a (Finset.mem_univ e)).symm
        have hrest : ∑ f ∈ Finset.univ.erase e, a f = 0 := by
          refine Finset.sum_eq_zero (fun f hf => ?_)
          have hne' : f ≠ e := (Finset.mem_erase.mp hf).1
          have hne'' : f.1 ≠ e0 := by
            intro hval
            apply hne'
            rw [he_eq]
            exact Subtype.ext hval
          exact ha_other f hne''
        rw [htot, hrest, add_zero] at hsum
        exact hsum.symm
      · exact ha_other e heq
    omega
  · have hDu_empty : Du inc P Q v u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hMu_eq : Mu inc P Q v u = Eu inc u := by
      simp [Mu, hDu_empty]
    have hge2 : 2 ≤ (Mu inc P Q v u).card := by
      rw [hMu_eq, Eu_card inc hq hm hline huniq u]
      omega
    let I := Mu inc P Q v u
    refine card_le_Ku_of_rows_indep inc P Q v u I (fun a ha => ?_)
    have hIsub : ∀ e : I, e.1 ∈ Eu inc u := fun e => (Finset.mem_sdiff.mp e.2).1
    let tot : ℚ := ∑ e : I, a e
    have ha_eq : ∀ e : I, a e = tot := by
      intro e
      have hev := ha e.1
      have hsplit : ∑ f : I, a f * rowVec inc P Q v u f.1 e.1 = tot - a e := by
        have hsum : ∑ f : I, a f * rowVec inc P Q v u f.1 e.1 =
            ∑ f : I, (if f = e then 0 else a f) := by
          refine Finset.sum_congr rfl (fun f _ => ?_)
          by_cases hfe : f = e
          · subst hfe
            simp [rowVec_diag_Mu inc P Q v u f.2]
          · have hfe' : f.1 ≠ e.1 := fun hval => hfe (Subtype.ext hval)
            simp [hfe, rowVec_off_diag inc P Q v hrect u (hIsub f) (hIsub e) hfe']
        rw [hsum]
        have hadd : (∑ f : I, if f = e then 0 else a f) + a e = tot := by
          have : ∑ f : I, (if f = e then a f else 0) = a e := by
            simp
          rw [← this, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun f _ => ?_)
          by_cases hfe : f = e <;> simp [hfe]
        linarith
      rw [hsplit] at hev
      linarith
    have hsum_tot : (I.card : ℚ) * tot = tot := by
      calc
        (I.card : ℚ) * tot = ∑ _e : I, tot := by
          simp
        _ = ∑ e : I, a e := by
          refine Finset.sum_congr rfl (fun e _ => (ha_eq e).symm)
        _ = tot := rfl
    have hcard_ge : (2 : ℚ) ≤ (I.card : ℚ) := by exact_mod_cast hge2
    have htot : tot = 0 := by nlinarith
    funext e
    rw [ha_eq e, htot]
    rfl

end RankEngine

end PEqualNP.Outside.L_meta_4616

theorem PEqualNP.Outside.L_meta_4616 :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             x5.output < x2 + x2 + x5.size →               (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →                 (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →                   (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →                     have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);                     x2 * (x1 + (1 : ℕ)) ≤ (1 : ℕ) + ∑ x16 : Fin x5.size, x15 x16 := by
  intro q m inc hdec C hq hm hline huniq hmono hout hfan hpos hneg
  dsimp only
  have hleaf_id : (PEqualNP.Outside.L_meta_4616.leafList (m + m) C).getD C.output 0 =
      1 + ∑ g0 : Fin C.size,
        (List.foldl (fun (acc : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
          acc ++ [(if acc.length = m + m + g0.1 then 1 else 0) +
            (List.map (fun i => acc.getD i 0) g.inputs).sum])
          (List.replicate (m + m) 0) C.gates).getD C.output 0 :=
    PEqualNP.Outside.L_meta_4616.leaf_eq_one_add_sum_path (m + m) C hfan C.output hout
  rw [← hleaf_id]
  let A : Set (Fin (m + m) → Bool) :=
    {x | ∃ p l : Fin m, inc p l ∧ x = PEqualNP.Outside.L_meta_4616.posInput p l}
  let B : Set (Fin (m + m) → Bool) :=
    {y | ∃ p l : Fin m, inc p l ∧ y = PEqualNP.Outside.L_meta_4616.negInput inc p l}
  have hA : ∀ x ∈ A, (C.wires (List.ofFn x)).getD C.output false = true := by
    rintro x ⟨p, l, hpl, rfl⟩
    exact hpos p l hpl
  have hB : ∀ y ∈ B, (C.wires (List.ofFn y)).getD C.output false = false := by
    rintro y ⟨p, l, hpl, rfl⟩
    exact hneg (PEqualNP.Outside.L_meta_4616.negInput inc p l)
      (PEqualNP.Outside.L_meta_4616.negInput_line_card inc hq hm hline huniq hpl)
      (PEqualNP.Outside.L_meta_4616.negInput_no_inc inc huniq hpl)
  obtain ⟨P, Q, v, hkw⟩ :=
    PEqualNP.Outside.L_meta_4616.kw_partition C hmono hfan C.output hout A B hA hB
  have hrect : ∀ e e' : Fin m × Fin m,
      e ∈ PEqualNP.Outside.L_meta_4616.INC inc →
      e' ∈ PEqualNP.Outside.L_meta_4616.INC inc →
      (∃! r : Fin ((PEqualNP.Outside.L_meta_4616.leafList (m + m) C).getD C.output 0),
        P r (PEqualNP.Outside.L_meta_4616.posInput e.1 e.2) ∧
        Q r (PEqualNP.Outside.L_meta_4616.negInput inc e'.1 e'.2)) ∧
      ∀ r, P r (PEqualNP.Outside.L_meta_4616.posInput e.1 e.2) →
        Q r (PEqualNP.Outside.L_meta_4616.negInput inc e'.1 e'.2) →
        PEqualNP.Outside.L_meta_4616.posInput e.1 e.2 (v r) = true ∧
        PEqualNP.Outside.L_meta_4616.negInput inc e'.1 e'.2 (v r) = false := by
    intro e e' he he'
    simp only [PEqualNP.Outside.L_meta_4616.INC, Finset.mem_filter, Finset.mem_univ,
      true_and] at he he'
    exact hkw (PEqualNP.Outside.L_meta_4616.posInput e.1 e.2) ⟨e.1, e.2, he, rfl⟩
      (PEqualNP.Outside.L_meta_4616.negInput inc e'.1 e'.2) ⟨e'.1, e'.2, he', rfl⟩
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin (m + m)))) =>
    PEqualNP.Outside.L_meta_4616.per_vertex_bound inc hq hm hline huniq P Q v hrect u)
  rw [PEqualNP.Outside.L_meta_4616.sum_Mu_card inc P Q v hrect,
    PEqualNP.Outside.L_meta_4616.sum_Ku_card v,
    PEqualNP.Outside.L_meta_4616.INC_card inc hq hm hline huniq] at hsum
  exact hsum
