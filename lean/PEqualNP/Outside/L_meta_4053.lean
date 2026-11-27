import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4053

open PEqualNP.CircuitLowerBounds

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def ev (w : List Bool) (A : Finset ℕ) : Bool := decide (∀ i ∈ A, w.getD i false = true)

def NW (x : List Bool) (Ls : List (Finset ℕ × Finset ℕ)) : List Bool :=
  Ls.foldl (fun w p => w ++ [ev w p.1 || ev w p.2]) (x ++ [false])

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def rep (n : ℕ) (S : List (Finset ℕ)) (u : ℕ) : Finset ℕ :=
  if u < n then {u} else S.getD (u - n) {n}

def lineOf (n : ℕ) (S : List (Finset ℕ)) : List ℕ → Finset ℕ × Finset ℕ
  | [] => ({n}, {n})
  | [a] => (rep n S a, rep n S a)
  | a :: b :: _ => (rep n S a, rep n S b)

def step (n : ℕ) (st : List (Finset ℕ) × List (Finset ℕ × Finset ℕ)) (g : Gate) :
    List (Finset ℕ) × List (Finset ℕ × Finset ℕ) :=
  if isOr g.op then (st.1 ++ [{n + 1 + st.2.length}], st.2 ++ [lineOf n st.1 g.inputs])
  else (st.1 ++ [g.inputs.toFinset.biUnion (rep n st.1)], st.2)

theorem getD_snoc (w : List Bool) (v : Bool) (u : ℕ) :
    (w ++ [v]).getD u false = if u = w.length then v else w.getD u false := by
  rcases lt_trichotomy u w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have h1 : w.length ≤ u := by omega
    have h2 : (w ++ [v]).length ≤ u := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2, h.ne']

theorem rep_append (n : ℕ) (S : List (Finset ℕ)) (T : Finset ℕ) (u : ℕ) :
    rep n (S ++ [T]) u = if u = n + S.length then T else rep n S u := by
  unfold rep
  by_cases h : u < n
  · have : u ≠ n + S.length := by omega
    simp [h, this]
  · rcases lt_trichotomy (u - n) S.length with h1 | h1 | h1
    · have : u ≠ n + S.length := by omega
      simp [h, this, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · have : u = n + S.length := by omega
      simp [h, this, List.getD_eq_getElem?_getD]
    · have : u ≠ n + S.length := by omega
      have h2 : S.length ≤ u - n := by omega
      have h3 : (S ++ [T]).length ≤ u - n := by simp; omega
      simp [h, this, List.getD_eq_getElem?_getD, List.getElem?_eq_none h2,
        List.getElem?_eq_none h3]

theorem ev_singleton (w : List Bool) (i : ℕ) : ev w {i} = w.getD i false := by
  simp [ev]

theorem ev_append (w : List Bool) (b : Bool) (A : Finset ℕ) (h : ∀ i ∈ A, i < w.length) :
    ev (w ++ [b]) A = ev w A := by
  unfold ev
  congr 1
  apply propext
  constructor
  · intro H i hi
    have := H i hi
    rw [getD_snoc, if_neg (by have := h i hi; omega)] at this
    exact this
  · intro H i hi
    rw [getD_snoc, if_neg (by have := h i hi; omega)]
    exact H i hi

theorem NW_snoc (x : List Bool) (Ls : List (Finset ℕ × Finset ℕ)) (p : Finset ℕ × Finset ℕ) :
    NW x (Ls ++ [p]) = NW x Ls ++ [ev (NW x Ls) p.1 || ev (NW x Ls) p.2] := by
  simp [NW, List.foldl_append]

theorem NW_length (x : List Bool) (Ls : List (Finset ℕ × Finset ℕ)) :
    (NW x Ls).length = x.length + 1 + Ls.length := by
  induction Ls using List.reverseRecOn with
  | nil => simp [NW]
  | append_singleton l a ih => rw [NW_snoc]; simp [ih]; omega

theorem NW_getD (x : List Bool) (Ls : List (Finset ℕ × Finset ℕ)) (i : ℕ)
    (hi : i < x.length + 1) : (NW x Ls).getD i false = (x ++ [false]).getD i false := by
  induction Ls using List.reverseRecOn with
  | nil => simp [NW]
  | append_singleton l a ih =>
    rw [NW_snoc, getD_snoc, if_neg (by rw [NW_length]; omega), ih]

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

def Inv (n : ℕ) (gs : List Gate) (st : List (Finset ℕ) × List (Finset ℕ × Finset ℕ)) : Prop :=
  st.2.length = gs.countP (fun g => isOr g.op) ∧
  (∀ u, ∀ i ∈ rep n st.1 u, i < n + 1 + st.2.length) ∧
  (∀ k (h : k < st.2.length), ∀ i ∈ st.2[k].1 ∪ st.2[k].2, i < n + 1 + k) ∧
  ∀ x : List Bool, x.length = n → (W gs x).length = n + st.1.length ∧
    ∀ u, (W gs x).getD u false = ev (NW x st.2) (rep n st.1 u)

theorem inv_nil (n : ℕ) : Inv n [] ([], []) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro u i hi
    unfold rep at hi
    split_ifs at hi with h
    · simp at hi; omega
    · simp at hi; omega
  · intro k h
    simp at h
  · intro x hx
    refine ⟨by simp [W, hx], ?_⟩
    intro u
    unfold rep
    split_ifs with h
    · rw [ev_singleton, NW_getD _ _ _ (by omega), getD_snoc, if_neg (by omega)]
      rfl
    · have : ([] : List (Finset ℕ)).getD (u - n) {n} = {n} := by simp
      rw [this, ev_singleton, NW_getD _ _ _ (by omega), getD_snoc, if_pos hx.symm]
      have h1 : x.length ≤ u := by omega
      simp [W, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]

theorem inv_step (n : ℕ) (gs : List Gate) (st : List (Finset ℕ) × List (Finset ℕ × Finset ℕ))
    (g : Gate) (hI : Inv n gs st) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) : Inv n (gs ++ [g]) (step n st g) := by
  obtain ⟨S, Ls⟩ := st
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hc, hb, hl, hx⟩ := hI
  simp only at hc hb hl hx hop hlen
  rcases hop with rfl | rfl
  · have hs : step n (S, Ls) ⟨GateOp.and, inputs⟩ =
        (S ++ [inputs.toFinset.biUnion (rep n S)], Ls) := by simp [step, isOr]
    rw [hs]
    refine ⟨by simp [List.countP_append, isOr, hc], ?_, hl, ?_⟩
    · intro u i hi
      simp only at hi ⊢
      rw [rep_append] at hi
      split_ifs at hi with h
      · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 hi
        exact hb a i ha
      · exact hb u i hi
    · intro x hxl
      obtain ⟨hwl, hr⟩ := hx x hxl
      refine ⟨by rw [W_snoc]; simp [hwl]; omega, ?_⟩
      intro u
      simp only
      rw [W_snoc, getD_snoc, rep_append, hwl]
      split_ifs with h
      · rw [Bool.eq_iff_iff]
        simp only [GateOp.eval, List.all_eq_true, ev, decide_eq_true_eq]
        constructor
        · intro H i hi
          obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.1 hi
          have h1 := H _ (List.mem_map.2 ⟨a, List.mem_toFinset.1 ha, rfl⟩)
          simp only [id] at h1
          rw [hr a] at h1
          simp only [ev, decide_eq_true_eq] at h1
          exact h1 i hia
        · intro H b hb'
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb'
          simp only [id]
          rw [hr a]
          simp only [ev, decide_eq_true_eq]
          intro i hi
          exact H i (Finset.mem_biUnion.2 ⟨a, List.mem_toFinset.2 ha, hi⟩)
      · exact hr u
  · have hs : step n (S, Ls) ⟨GateOp.or, inputs⟩ =
        (S ++ [{n + 1 + Ls.length}], Ls ++ [lineOf n S inputs]) := by simp [step, isOr]
    rw [hs]
    have hline : ∀ i ∈ (lineOf n S inputs).1 ∪ (lineOf n S inputs).2, i < n + 1 + Ls.length := by
      intro i hi
      match inputs, hi with
      | [], hi => simp [lineOf] at hi; omega
      | [a], hi =>
        simp only [lineOf, Finset.union_self] at hi
        exact hb a i hi
      | a :: b :: _, hi =>
        simp only [lineOf, Finset.mem_union] at hi
        rcases hi with hi | hi
        · exact hb a i hi
        · exact hb b i hi
    refine ⟨by simp [List.countP_append, isOr, hc], ?_, ?_, ?_⟩
    · intro u i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      rw [rep_append] at hi
      split_ifs at hi with h
      · simp at hi; omega
      · have := hb u i hi
        omega
    · intro k hk i hi
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk' : k < Ls.length
      · simp only [List.getElem_append_left hk'] at hi
        exact hl k hk' i hi
      · have hk2 : k = Ls.length := by omega
        subst hk2
        simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_singleton] at hi
        exact hline i hi
    · intro x hxl
      obtain ⟨hwl, hr⟩ := hx x hxl
      refine ⟨by rw [W_snoc]; simp [hwl]; omega, ?_⟩
      intro u
      simp only
      have hnl : (NW x Ls).length = n + 1 + Ls.length := by rw [NW_length, hxl]
      have hfalse : ev (NW x Ls) {n} = false := by
        rw [ev_singleton, NW_getD _ _ _ (by omega), getD_snoc, if_pos hxl.symm]
      rw [W_snoc, getD_snoc, rep_append, hwl, NW_snoc]
      split_ifs with h
      · rw [ev_singleton, getD_snoc, if_pos hnl.symm]
        match inputs, hlen with
        | [], _ => simp [GateOp.eval, lineOf, hfalse]
        | [a], _ => simp [GateOp.eval, lineOf, ← hr]
        | [a, b], _ => simp [GateOp.eval, lineOf, ← hr]
        | _ :: _ :: _ :: _, hlen => simp at hlen
      · rw [ev_append _ _ _ (by intro i hi; rw [hnl]; exact hb u i hi)]
        exact hr u

theorem inv_all (n : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv n gs (gs.foldl (step n) ([], [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact inv_nil n
  | append_singleton l a ih =>
    rw [List.foldl_append]
    have ha := h a (by simp)
    exact inv_step n l _ a (ih (fun g hg => h g (by simp [hg]))) ha.1 ha.2

theorem cnt0 (l : List Gate) :
    (Finset.univ.filter (fun i : Fin l.length => isOr (l.get i).op = true)).card =
      l.countP (fun g => isOr g.op) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    show (Finset.univ.filter
      (fun i : Fin (l.length + 1) => isOr ((a :: l).get i).op = true)).card = _
    rw [Fin.card_filter_univ_succ]
    simp only [List.countP_cons]
    split_ifs with h1 h2 h2
    · simpa using ih
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simpa using ih

theorem cnt (l : List Gate) :
    {i : Fin l.length | (l.get i).op = GateOp.or}.ncard = l.countP (fun g => isOr g.op) := by
  have e : {i : Fin l.length | (l.get i).op = GateOp.or} =
      ↑(Finset.univ.filter (fun i : Fin l.length => isOr (l.get i).op = true)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    cases (l.get i).op <;> simp [isOr]
  rw [e, Set.ncard_coe_finset, cnt0]

end PEqualNP.Outside.L_meta_4053

theorem PEqualNP.Outside.L_meta_4053 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     ∃ (x4 : List (Finset ℕ × Finset ℕ)) (x5 : Finset ℕ),       x4.length = {x6 : Fin x2.gates.length | (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧         (∀ (x6 : ℕ) (x7 : x6 < x4.length), ∀ x8 ∈ x4[x6].1 ∪ x4[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, x6 < x1 + (1 : ℕ) + x4.length) ∧             ∀ (x6 : Fin x1 → Bool),               x2.eval (List.ofFn x6) =                 have x7 : List Bool := List.foldl (fun (x7 : List Bool) (x8 : Finset ℕ × Finset ℕ) => x7 ++ [Decidable.decide (∀ x9 ∈ x8.1, x7.getD x9 Bool.false = Bool.true) || Decidable.decide (∀ x9 ∈ x8.2, x7.getD x9 Bool.false = Bool.true)]) (List.ofFn x6 ++ [Bool.false]) x4;                 Decidable.decide (∀ x8 ∈ x5, x7.getD x8 Bool.false = Bool.true) := by
  intro n C hC
  have hI := PEqualNP.Outside.L_meta_4053.inv_all n C.gates (fun g hg => by
    have := hC g hg
    exact ⟨by simpa using this.1, this.2⟩)
  obtain ⟨hc, hb, hl, hx⟩ := hI
  refine ⟨(C.gates.foldl (PEqualNP.Outside.L_meta_4053.step n) ([], [])).2,
    PEqualNP.Outside.L_meta_4053.rep n
      (C.gates.foldl (PEqualNP.Outside.L_meta_4053.step n) ([], [])).1 C.output, ?_, hl, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_4053.cnt]
    exact hc
  · exact hb C.output
  · intro x
    exact (hx (List.ofFn x) (List.length_ofFn)).2 C.output
