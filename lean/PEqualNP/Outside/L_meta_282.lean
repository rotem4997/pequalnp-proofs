import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]
    simp

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht, List.length_append, hl]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ hi

private lemma wiresFrom_getD_take (gs : List Gate) (w : List Bool) (j i : ℕ)
    (hi : i < w.length + j) (hj : j ≤ gs.length) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  have h1 : wiresFrom gs w = wiresFrom (gs.drop j) (wiresFrom (gs.take j) w) := by
    rw [← wiresFrom_append, List.take_append_drop]
  rw [h1]
  symm
  exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_take, Nat.min_eq_left hj]; exact hi)

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (wiresFrom gs w).getD i false else false) := by
  have hsp : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ (h := hj), List.take_append_drop]
  have h1 : (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
    conv_lhs => rw [hsp, wiresFrom_append, wiresFrom_cons]
    set pre := wiresFrom (gs.take j) w with hpre
    have hlen : pre.length = w.length + j := by
      rw [hpre, wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [wiresFrom_getD_lt _ _ _ (by rw [List.length_append, hlen]; simp)]
    rw [← hlen]
    simp
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hilt
  · exact wiresFrom_getD_take gs w j i hilt (Nat.le_of_lt hj)
  · exact List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega)

private lemma getD_ofFn_fin {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-! ### The 8 maximal independent sets of two triangles joined by edge (2, 3) -/

private def mis : Fin 8 → Fin 6 → Bool
  | 0 => fun i => decide (i = 0 ∨ i = 3)
  | 1 => fun i => decide (i = 0 ∨ i = 4)
  | 2 => fun i => decide (i = 0 ∨ i = 5)
  | 3 => fun i => decide (i = 1 ∨ i = 3)
  | 4 => fun i => decide (i = 1 ∨ i = 4)
  | 5 => fun i => decide (i = 1 ∨ i = 5)
  | 6 => fun i => decide (i = 2 ∨ i = 4)
  | 7 => fun i => decide (i = 2 ∨ i = 5)

private def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)]

private def hasEdge (x : Fin 6 → Bool) : Prop :=
  ∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

private instance (x : Fin 6 → Bool) : Decidable (hasEdge x) := by
  unfold hasEdge; infer_instance

private lemma mis_indep : ∀ r : Fin 8, ¬ hasEdge (mis r) := by
  decide

private lemma mis_union_edge : ∀ r s : Fin 8, r ≠ s → hasEdge (fun i => mis r i || mis s i) := by
  decide

private def evalMask (m : Fin 64) (x : Fin 6 → Bool) : Bool :=
  (Finset.univ.filter (fun i : Fin 6 => m.val.testBit i.val && x i)).Nonempty

private lemma evalMask_no_partition :
    ∀ u v : Fin 64,
      ¬ ((Finset.univ.filter (fun r : Fin 8 => evalMask u (mis r) = true → evalMask v (mis r) = true)).card ≤ 4 ∧
         (Finset.univ.filter (fun r : Fin 8 => evalMask v (mis r) = true → evalMask u (mis r) = true)).card ≤ 4) := by
  decide

private lemma mask_of_or_only (C : Circuit) (hmono : Monotone2 C) (j0 : ℕ)
    (hnoAnd : ∀ j < j0, ∀ g, C.gates[j]? = some g → g.op = GateOp.or) :
    ∀ w < 6 + j0, ∃ m : Fin 64, ∀ x : Fin 6 → Bool,
      (C.wires (List.ofFn x)).getD w false = evalMask m x := by
  have hmk_lt : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
      (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) < 64 := by
    decide
  have hmk_bit : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ i : Fin 6,
      ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
       (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)).testBit i.val =
      (![b0, b1, b2, b3, b4, b5] i) := by
    decide
  have mk_mask : ∀ f : Fin 6 → Bool, ∃ m : Fin 64, ∀ i : Fin 6, m.val.testBit i.val = f i := by
    intro f
    refine ⟨⟨_, hmk_lt (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)⟩, fun i => ?_⟩
    rw [hmk_bit]
    fin_cases i <;> rfl
  have eval_of_f : ∀ (f : Fin 6 → Bool), ∃ m : Fin 64, ∀ x : Fin 6 → Bool,
      evalMask m x = decide (∃ i : Fin 6, f i = true ∧ x i = true) := by
    intro f
    obtain ⟨m, hm⟩ := mk_mask f
    refine ⟨m, fun x => ?_⟩
    apply Bool.eq_iff_iff.2
    simp only [evalMask, decide_eq_true_eq, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, hm]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt6 : w < 6
    · obtain ⟨m, hm⟩ := eval_of_f (fun i => decide (i.val = w))
      refine ⟨m, fun x => ?_⟩
      rw [hm]
      change (wiresFrom C.gates (List.ofFn x)).getD w false = _
      rw [wiresFrom_getD_lt _ _ _ (by simp [hlt6])]
      apply Bool.eq_iff_iff.2
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt6, ↓reduceDIte,
        Option.getD_some, decide_eq_true_eq]
      constructor
      · intro h; exact ⟨⟨w, hlt6⟩, rfl, h⟩
      · rintro ⟨i, hi, hx⟩
        have : i = ⟨w, hlt6⟩ := Fin.ext hi
        rwa [← this]
    · by_cases hltC : w < 6 + C.gates.length
      · set j := w - 6
        have hjlt : j < C.gates.length := by omega
        have hj0 : j < j0 := by omega
        have hwj : w = 6 + j := by omega
        set g := C.gates[j]'hjlt
        have hg_get : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hg_or : g.op = GateOp.or := hnoAnd j hj0 g hg_get
        have hg_len : g.inputs.length ≤ 2 := (hmono g (List.getElem_mem hjlt)).2
        have hstep_val : ∀ x : Fin 6 → Bool,
            (C.wires (List.ofFn x)).getD (6 + j) false =
              g.op.eval (g.inputs.map fun u =>
                if u < 6 + j then (C.wires (List.ofFn x)).getD u false else false) := by
          intro x
          have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hjlt
          rw [List.length_ofFn] at h1
          exact h1
        have hchild_mask : ∀ u : ℕ, ∃ m : Fin 64, ∀ x : Fin 6 → Bool,
            (if u < 6 + j then (C.wires (List.ofFn x)).getD u false else false) = evalMask m x := by
          intro u
          by_cases hu : u < 6 + j
          · obtain ⟨m, hm⟩ := ih u (by omega) (by omega)
            exact ⟨m, fun x => by rw [if_pos hu, hm]⟩
          · obtain ⟨m, hm⟩ := eval_of_f (fun _ => false)
            exact ⟨m, fun x => by rw [if_neg hu, hm]; simp⟩
        rw [hwj]
        cases hgin : g.inputs with
        | nil =>
          obtain ⟨m, hm⟩ := eval_of_f (fun _ => false)
          refine ⟨m, fun x => ?_⟩
          rw [hstep_val, hg_or, hgin, hm]; simp [GateOp.eval]
        | cons a t =>
          cases t with
          | nil =>
            obtain ⟨ma, hma⟩ := hchild_mask a
            refine ⟨ma, fun x => ?_⟩
            rw [hstep_val, hg_or, hgin]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hma]
          | cons b t2 =>
            have ht2 : t2 = [] := by
              rw [hgin] at hg_len
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hg_len
            subst ht2
            obtain ⟨ma, hma⟩ := hchild_mask a
            obtain ⟨mb, hmb⟩ := hchild_mask b
            obtain ⟨m, hm⟩ := eval_of_f (fun i => ma.val.testBit i.val || mb.val.testBit i.val)
            refine ⟨m, fun x => ?_⟩
            rw [hstep_val, hg_or, hgin, hm]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hma, hmb]
            apply Bool.eq_iff_iff.2
            simp only [evalMask, decide_eq_true_eq, Bool.or_eq_true, Finset.Nonempty,
              Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true]
            constructor
            · rintro (⟨i, ha, hx⟩ | ⟨i, hb, hx⟩)
              · exact ⟨i, Or.inl ha, hx⟩
              · exact ⟨i, Or.inr hb, hx⟩
            · rintro ⟨i, ha | hb, hx⟩
              · exact Or.inl ⟨i, ha, hx⟩
              · exact Or.inr ⟨i, hb, hx⟩
      · obtain ⟨m, hm⟩ := eval_of_f (fun _ => false)
        refine ⟨m, fun x => ?_⟩
        rw [hm]
        change (wiresFrom C.gates (List.ofFn x)).getD w false = _
        rw [List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)]
        simp

/-! ### Key OR-preservation lemma on subsets of MIS -/

private lemma wire_or_of_choice (C : Circuit) (hmono : Monotone2 C)
    (R : Finset ℕ) (r s : Fin 8)
    (hspec : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → g.inputs.length = 2 →
      j ∉ R →
      ∀ a b : ℕ, g.inputs = [a, b] →
        let va (x : Fin 6 → Bool) := if a < 6 + j then (C.wires (List.ofFn x)).getD a false else false
        let vb (x : Fin 6 → Bool) := if b < 6 + j then (C.wires (List.ofFn x)).getD b false else false
        (va (mis r) = false ∧ va (mis s) = false) ∨
        (vb (mis r) = false ∧ vb (mis s) = false) ∨
        (va (mis r) = true ∧ vb (mis r) = true) ∨
        (va (mis s) = true ∧ vb (mis s) = true))
    (hagree : ∀ j ∈ R, ∀ (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
      ∀ a b : ℕ, g.inputs = [a, b] →
        (if a < 6 + j then (C.wires (List.ofFn (mis r))).getD a false else false) =
        (if a < 6 + j then (C.wires (List.ofFn (mis s))).getD a false else false)) :
    ∀ w : ℕ, (C.wires (List.ofFn (fun i => mis r i || mis s i))).getD w false =
      ((C.wires (List.ofFn (mis r))).getD w false || (C.wires (List.ofFn (mis s))).getD w false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · change (wiresFrom C.gates _).getD w false =
        ((wiresFrom C.gates _).getD w false || (wiresFrom C.gates _).getD w false)
      rw [wiresFrom_getD_lt _ _ _ (by simp [hw6]),
        wiresFrom_getD_lt _ _ _ (by simp [hw6]),
        wiresFrom_getD_lt _ _ _ (by simp [hw6]),
        getD_ofFn_fin _ w hw6, getD_ofFn_fin _ w hw6, getD_ofFn_fin _ w hw6]
    · by_cases hwC : w < 6 + C.gates.length
      · set j := w - 6
        have hjlt : j < C.gates.length := by omega
        have hwj : w = 6 + j := by omega
        set g := C.gates[j]'hjlt
        have hg_get : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        obtain ⟨hg_op, hg_len⟩ := hmono g (List.getElem_mem hjlt)
        have hstep : ∀ x : Fin 6 → Bool,
            (C.wires (List.ofFn x)).getD (6 + j) false =
              g.op.eval (g.inputs.map fun u =>
                if u < 6 + j then (C.wires (List.ofFn x)).getD u false else false) := by
          intro x
          have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hjlt
          rw [List.length_ofFn] at h1
          exact h1
        have hih_in : ∀ u : ℕ,
            (if u < 6 + j then (C.wires (List.ofFn (fun i => mis r i || mis s i))).getD u false else false) =
            ((if u < 6 + j then (C.wires (List.ofFn (mis r))).getD u false else false) ||
             (if u < 6 + j then (C.wires (List.ofFn (mis s))).getD u false else false)) := by
          intro u
          split_ifs with hu
          · exact ih u (by omega)
          · rfl
        rw [hwj, hstep, hstep, hstep]
        rcases hg_op with hop_and | hop_or
        · rw [hop_and]
          cases hgin : g.inputs with
          | nil => simp [GateOp.eval]
          | cons a t =>
            cases t with
            | nil =>
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                id_eq, Bool.and_true]
              exact hih_in a
            | cons b t2 =>
              have ht2 : t2 = [] := by
                rw [hgin] at hg_len
                cases t2 with
                | nil => rfl
                | cons _ _ => simp at hg_len
              subst ht2
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                id_eq, Bool.and_true]
              rw [hih_in a, hih_in b]
              by_cases hjR : j ∈ R
              · have ha := hagree j hjR g hg_get hop_and a b hgin
                rw [ha]
                cases (if a < 6 + j then (C.wires (List.ofFn (mis s))).getD a false else false) <;>
                  cases (if b < 6 + j then (C.wires (List.ofFn (mis r))).getD b false else false) <;>
                  cases (if b < 6 + j then (C.wires (List.ofFn (mis s))).getD b false else false) <;>
                  rfl
              · have hs := hspec j g hg_get hop_and (by rw [hgin]; rfl) hjR a b hgin
                rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  dsimp only at h1 h2 <;> rw [h1, h2] <;> simp
        · rw [hop_or]
          cases hgin : g.inputs with
          | nil => simp [GateOp.eval]
          | cons a t =>
            cases t with
            | nil =>
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
              exact hih_in a
            | cons b t2 =>
              have ht2 : t2 = [] := by
                rw [hgin] at hg_len
                cases t2 with
                | nil => rfl
                | cons _ _ => simp at hg_len
              subst ht2
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                id_eq, Bool.or_false]
              rw [hih_in a, hih_in b]
              cases (if a < 6 + j then (C.wires (List.ofFn (mis r))).getD a false else false) <;>
                cases (if a < 6 + j then (C.wires (List.ofFn (mis s))).getD a false else false) <;>
                cases (if b < 6 + j then (C.wires (List.ofFn (mis r))).getD b false else false) <;>
                cases (if b < 6 + j then (C.wires (List.ofFn (mis s))).getD b false else false) <;>
                rfl
      · change (wiresFrom C.gates _).getD w false =
          ((wiresFrom C.gates _).getD w false || (wiresFrom C.gates _).getD w false)
        rw [List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega),
          List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega),
          List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)]
        rfl

theorem main :
    ¬ ∃ C : Circuit,
      (Monotone2 C ∧
        (∃ A : Finset ℕ, A.card ≤ 3 ∧
          ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)) ∧
      (∀ x : Fin 6 → Bool,
        (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) := by
  classical
  rintro ⟨C, ⟨hmono, ⟨A, hAcard, hAmem⟩⟩, heval⟩
  have hmis_false : ∀ r : Fin 8, C.eval (List.ofFn (mis r)) = false := by
    intro r
    cases h : C.eval (List.ofFn (mis r))
    · rfl
    · exact absurd ((heval (mis r)).1 h) (mis_indep r)
  have hmis_union_true : ∀ r s : Fin 8, r ≠ s →
      C.eval (List.ofFn (fun i => mis r i || mis s i)) = true := by
    intro r s hrs
    exact (heval _).2 (mis_union_edge r s hrs)
  -- Helper: injectivity bound on any subset `Sub : Finset (Fin 8)` using choice bits on `R`
  let choiceBit (j : ℕ) (r : Fin 8) : Bool :=
    match C.gates[j]? with
    | some g =>
      match g.inputs with
      | a :: _ => if a < 6 + j then (C.wires (List.ofFn (mis r))).getD a false else false
      | [] => false
    | none => false
  have hinj_bound : ∀ (R : Finset ℕ) (Sub : Finset (Fin 8)),
      (∀ r ∈ Sub, ∀ s ∈ Sub,
        ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → g.inputs.length = 2 →
          j ∉ R →
          ∀ a b : ℕ, g.inputs = [a, b] →
            let va (x : Fin 6 → Bool) := if a < 6 + j then (C.wires (List.ofFn x)).getD a false else false
            let vb (x : Fin 6 → Bool) := if b < 6 + j then (C.wires (List.ofFn x)).getD b false else false
            (va (mis r) = false ∧ va (mis s) = false) ∨
            (vb (mis r) = false ∧ vb (mis s) = false) ∨
            (va (mis r) = true ∧ vb (mis r) = true) ∨
            (va (mis s) = true ∧ vb (mis s) = true)) →
      Sub.card ≤ 2 ^ R.card := by
    intro R Sub hspec
    let sig : Sub → (R → Bool) := fun r j => choiceBit j.val r.val
    have hsig_inj : Function.Injective sig := by
      intro ⟨r, hr⟩ ⟨s, hs⟩ hEq
      apply Subtype.ext
      by_contra hrs
      have hagree : ∀ j ∈ R, ∀ (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
          ∀ a b : ℕ, g.inputs = [a, b] →
            (if a < 6 + j then (C.wires (List.ofFn (mis r))).getD a false else false) =
            (if a < 6 + j then (C.wires (List.ofFn (mis s))).getD a false else false) := by
        intro j hjR g hg_get _ a b hab
        have h := congrFun hEq ⟨j, hjR⟩
        simpa [sig, choiceBit, hg_get, hab] using h
      have hor := wire_or_of_choice C hmono R r s (hspec r hr s hs) hagree C.output
      have ht := hmis_union_true r s hrs
      have hfr := hmis_false r
      have hfs := hmis_false s
      change C.eval (List.ofFn (fun i => mis r i || mis s i)) =
        (C.eval (List.ofFn (mis r)) || C.eval (List.ofFn (mis s))) at hor
      rw [ht, hfr, hfs] at hor
      cases hor
    have hcard := Fintype.card_le_of_injective sig hsig_inj
    simpa [Fintype.card_coe] using hcard
  -- Filter to actual 2-input AND gates inside `C.gates`
  set A2 : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs.length = 2) with hA2
  have hA2_sub : A2 ⊆ A := by
    intro j hj
    obtain ⟨_, g, hg, hop, _⟩ := Finset.mem_filter.1 hj
    exact hAmem j g hg hop
  have hA2_card_le : A2.card ≤ 3 := (Finset.card_le_card hA2_sub).trans hAcard
  have hA2_card_ge : 8 ≤ 2 ^ A2.card := by
    have h := hinj_bound A2 Finset.univ (by
      intro r _ s _ j g hg hop hlen hjnot
      exfalso
      apply hjnot
      have hjlt : j < C.gates.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hg
        cases hg
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hjlt, g, hg, hop, hlen⟩)
    simpa using h
  have hA2_card_eq : A2.card = 3 := by
    have : ¬ (A2.card ≤ 2) := by
      intro h2
      have : 2 ^ A2.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) h2
      omega
    omega
  have hA2_eq_A : A2 = A := Finset.eq_of_subset_of_card_le hA2_sub (by omega)
  have hA2_ne : A2.Nonempty := Finset.card_pos.1 (by omega)
  set j0 := A2.min' hA2_ne with hj0_def
  have hj0_mem : j0 ∈ A2 := Finset.min'_mem A2 hA2_ne
  obtain ⟨hj0_range, g0, hg0_get, hg0_op, hg0_len⟩ := Finset.mem_filter.1 hj0_mem
  have hnoAnd : ∀ j < j0, ∀ g : Gate, C.gates[j]? = some g → g.op = GateOp.or := by
    intro j hjj0 g hg_get
    have hjlt : j < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hg_get
      cases hg_get
    have hg_mem : g ∈ C.gates := by
      rw [List.getElem?_eq_getElem hjlt] at hg_get
      cases hg_get
      exact List.getElem_mem hjlt
    rcases (hmono g hg_mem).1 with hand | hor
    · exfalso
      have hjA : j ∈ A := hAmem j g hg_get hand
      rw [← hA2_eq_A] at hjA
      have := Finset.min'_le A2 j hjA
      omega
    · exact hor
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g0.inputs = [a, b] := by
    cases h : g0.inputs with
    | nil => rw [h] at hg0_len; simp at hg0_len
    | cons a t =>
      cases t with
      | nil => rw [h] at hg0_len; simp at hg0_len
      | cons b t2 =>
        cases t2 with
        | nil => exact ⟨a, b, rfl⟩
        | cons _ _ => rw [h] at hg0_len; simp at hg0_len
  have hmask_in : ∀ u : ℕ, ∃ m : Fin 64, ∀ x : Fin 6 → Bool,
      (if u < 6 + j0 then (C.wires (List.ofFn x)).getD u false else false) = evalMask m x := by
    intro u
    by_cases hu : u < 6 + j0
    · obtain ⟨m, hm⟩ := mask_of_or_only C hmono j0 hnoAnd u hu
      exact ⟨m, fun x => by rw [if_pos hu, hm]⟩
    · refine ⟨0, fun x => ?_⟩
      rw [if_neg hu]; simp [evalMask]
  obtain ⟨mu, hmu⟩ := hmask_in a
  obtain ⟨mv, hmv⟩ := hmask_in b
  set R := A2.erase j0 with hR_def
  have hR_card : R.card = 2 := by
    have h := Finset.card_erase_add_one hj0_mem
    rw [← hR_def, hA2_card_eq] at h
    omega
  set Su : Finset (Fin 8) :=
    Finset.univ.filter (fun r : Fin 8 => evalMask mu (mis r) = true → evalMask mv (mis r) = true)
  set Sv : Finset (Fin 8) :=
    Finset.univ.filter (fun r : Fin 8 => evalMask mv (mis r) = true → evalMask mu (mis r) = true)
  have hSu : Su.card ≤ 4 := by
    have h := hinj_bound R Su (by
      intro r hr s hs j g hg hop hlen hjnot a' b' hab'
      have hjA2 : j ∈ A2 := by
        have hjlt : j < C.gates.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hg
          cases hg
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hjlt, g, hg, hop, hlen⟩
      have hjeq : j = j0 := by
        by_contra hne
        exact hjnot (Finset.mem_erase.2 ⟨hne, hjA2⟩)
      subst hjeq
      rw [hg0_get] at hg
      cases hg
      rw [hab] at hab'
      cases hab'
      have hrm : evalMask mu (mis r) = true → evalMask mv (mis r) = true := (Finset.mem_filter.1 hr).2
      have hsm : evalMask mu (mis s) = true → evalMask mv (mis s) = true := (Finset.mem_filter.1 hs).2
      dsimp only
      rw [hmu, hmu, hmv, hmv]
      cases har : evalMask mu (mis r)
      · cases has : evalMask mu (mis s)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, hsm has⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hrm har⟩)))
    rw [hR_card] at h
    exact h
  have hSv : Sv.card ≤ 4 := by
    have h := hinj_bound R Sv (by
      intro r hr s hs j g hg hop hlen hjnot a' b' hab'
      have hjA2 : j ∈ A2 := by
        have hjlt : j < C.gates.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hg
          cases hg
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hjlt, g, hg, hop, hlen⟩
      have hjeq : j = j0 := by
        by_contra hne
        exact hjnot (Finset.mem_erase.2 ⟨hne, hjA2⟩)
      subst hjeq
      rw [hg0_get] at hg
      cases hg
      rw [hab] at hab'
      cases hab'
      have hrm : evalMask mv (mis r) = true → evalMask mu (mis r) = true := (Finset.mem_filter.1 hr).2
      have hsm : evalMask mv (mis s) = true → evalMask mu (mis s) = true := (Finset.mem_filter.1 hs).2
      dsimp only
      rw [hmu, hmu, hmv, hmv]
      cases hbr : evalMask mv (mis r)
      · cases hbs : evalMask mv (mis s)
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨hsm hbs, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hrm hbr, rfl⟩)))
    rw [hR_card] at h
    exact h
  exact evalMask_no_partition mu mv ⟨hSu, hSv⟩

end PEqualNP.Outside.L_meta_282_aux

theorem PEqualNP.Outside.L_meta_282 :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (PEqualNP.MetaComplexity.Monotone2 C ∧
        (∃ A : Finset ℕ, A.card ≤ 3 ∧
          ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧
      (∀ x : Fin 6 → Bool,
        (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :=
  PEqualNP.Outside.L_meta_282_aux.main
