import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8901

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




open PEqualNP.MetaComplexity.NestedCover

theorem orS (n : ℕ) (gs : List Gate) :
    (gs.foldl (CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD j [] ↔
      (d = j ∨ (gs[j].op = GateOp.or ∧ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
        d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (CleanedNonEdge.orStep n) [] with hr
    have hold : ∀ i, i < gs.length → (CleanedNonEdge.orStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [CleanedNonEdge.orStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hw => ?_)
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (CleanedNonEdge.orStep n r g).getD gs.length [] = r.length ::
          (@ite _ (g.op = GateOp.or) (Classical.dec _)
            ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => r.getD (w - n) [])) []) := by
        rw [← h1]
        unfold CleanedNonEdge.orStep
        rw [getD_at']
        congr 1
        split_ifs <;> rfl
      rw [e2, List.mem_cons, h1]
      refine or_congr_right ?_
      split_ifs with ho
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, ho, true_and]
        refine exists_congr fun w => ?_
        constructor
        · rintro ⟨⟨q1, q2, q3⟩, q4⟩
          exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
        · rintro ⟨q1, q2, q3, q4⟩
          rw [hold _ (by omega)] at q4
          exact ⟨⟨q1, q2, q3⟩, q4⟩
      · simp [ho]

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩


theorem inI {N : ℕ} (C : Circuit) (i j : Fin N) : j ∈ TopForm.orIn N C i ↔ j = i := by
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, _, hr, _⟩)
    · exact Fin.ext h
    · have := hr.1; have := i.isLt; omega
  · intro h; left; rw [h]

theorem inO {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) (i : Fin N) :
    i ∈ TopForm.orIn N C (N + j) ↔ ∃ t : Fin 2, i ∈ TopForm.orIn N C (TopForm.opnd C j t) := by
  obtain ⟨e, hin, h0, h1, _⟩ := gate2 h hj
  obtain ⟨l1, l2⟩ := orS N C.gates
  have mem : ∀ k, CleanedNonEdge.OrReaches N C (N + j) k ↔ k = j ∨ ∃ t : Fin 2, CleanedNonEdge.OrReaches N C (TopForm.opnd C j t) k := by
    intro k
    unfold CleanedNonEdge.OrReaches CleanedNonEdge.orSets
    rw [Nat.add_sub_cancel_left, l2 j hj k, e, hin]
    constructor
    · rintro ⟨_, h | ⟨_, w, hw, h2, h3, h4⟩⟩
      · exact Or.inl h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inr ⟨0, h2, h4⟩
        · exact Or.inr ⟨1, h2, h4⟩
    · rintro (h | ⟨t, h2, h4⟩)
      · exact ⟨by omega, Or.inl h⟩
      · refine ⟨by omega, Or.inr ⟨ho, TopForm.opnd C j t, ?_, h2, ?_, h4⟩⟩
        · fin_cases t <;> simp
        · fin_cases t <;> assumption
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and, mem]
  constructor
  · rintro (h | ⟨k, hk, rfl | ⟨t, ht⟩, hko, hi⟩)
    · have := i.isLt; omega
    · rw [hin] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · exact ⟨0, Or.inl hi⟩
      · exact ⟨1, Or.inl hi⟩
    · exact ⟨t, Or.inr ⟨k, hk, ht, hko, hi⟩⟩
  · rintro ⟨t, h | ⟨k, hk, hr, hko, hi⟩⟩
    · refine Or.inr ⟨j, hj, Or.inl rfl, ho, ?_⟩
      rw [hin, h]
      fin_cases t <;> simp
    · exact Or.inr ⟨k, hk, Or.inr ⟨t, hr⟩, hko, hi⟩

theorem inA {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.and) (i : Fin N) :
    i ∉ TopForm.orIn N C (N + j) := by
  obtain ⟨e, _⟩ := gate2 h hj
  obtain ⟨l1, l2⟩ := orS N C.gates
  intro hi
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, ⟨_, hr⟩, hko, _⟩
  · have := i.isLt; omega
  · unfold CleanedNonEdge.orSets at hr
    rw [Nat.add_sub_cancel_left, l2 j hj k, e] at hr
    rcases hr with rfl | ⟨h2, _⟩
    · rw [ho] at hko; cases hko
    · rw [ho] at h2; cases h2

theorem opl {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (t : Fin 2) : TopForm.opnd C j t < N + j := by
  obtain ⟨_, _, h0, h1, _⟩ := gate2 h hj
  fin_cases t <;> assumption

theorem gval {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CircuitLowerBounds.wireValue C x (N + j) = (gateAt C j).op.eval [PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 0), PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 1)] := by
  obtain ⟨e, hin, h0, h1, _⟩ := gate2 h hj
  have := run_gate C.gates x j hj
  rw [hx, e, hin] at this
  simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1] at this
  exact this

theorem or_val {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) (i : Fin N) (hi : x.getD i false = true) :
    ∀ w, w < N + C.gates.length → i ∈ TopForm.orIn N C w → PEqualNP.CircuitLowerBounds.wireValue C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm
    by_cases hwN : w < N
    · have : i = ⟨w, hwN⟩ := (inI C ⟨w, hwN⟩ i).1 hm
      subst this
      exact (run_input C.gates x w (by omega)).trans hi
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwN)
      have hj : j < C.gates.length := by omega
      obtain ⟨_, _, _, _, ho⟩ := gate2 h hj
      rcases ho with ho | ho
      · exact absurd hm (inA h j hj ho i)
      · obtain ⟨t, ht⟩ := (inO h j hj ho i).1 hm
        have h2 := ih _ (opl h j hj t) (by have := opl h j hj t; omega) ht
        rw [gval h x hx j hj, ho]
        fin_cases t
        · have h2 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 0) = true := h2
          simp [GateOp.eval, h2]
        · have h2 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 1) = true := h2
          simp [GateOp.eval, h2]

/-- Merging letters inside `D` along the OR gates. -/
theorem merge {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (D : Finset (Fin N)) : ∀ k, k ≤ C.gates.length →
    ∃ (Q : Finset ℕ) (f : Fin N → Fin N), (∀ j ∈ Q, j < k) ∧ (∀ S : Finset (Fin N), S.card ≤ Q.card + (S.image f).card) ∧
      (∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧ TopForm.orIn N C (N + j) ⊆ D ∧ ∃ x ∈ TopForm.orIn N C (N + j), ∃ y ∈ TopForm.orIn N C (N + j), x ≠ y) ∧
      ∀ w < N + k, TopForm.orIn N C w ⊆ D → ∀ x ∈ TopForm.orIn N C w, ∀ y ∈ TopForm.orIn N C w, f x = f y := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨∅, id, by simp, by simp, by simp, ?_⟩
    intro w hw _ x hx y hy
    have hw : w < N := by omega
    rw [(inI C ⟨w, hw⟩ x).1 hx, (inI C ⟨w, hw⟩ y).1 hy]
  | succ k ih =>
    intro hk
    obtain ⟨Q, f, hQ, hc, hg, hf⟩ := ih (by omega)
    have hk' : k < C.gates.length := by omega
    have keep : (TopForm.orIn N C (N + k) ⊆ D → ∀ x ∈ TopForm.orIn N C (N + k), ∀ y ∈ TopForm.orIn N C (N + k), f x = f y) →
        ∃ (Q : Finset ℕ) (f : Fin N → Fin N), (∀ j ∈ Q, j < k + 1) ∧ (∀ S : Finset (Fin N), S.card ≤ Q.card + (S.image f).card) ∧
        (∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧ TopForm.orIn N C (N + j) ⊆ D ∧ ∃ x ∈ TopForm.orIn N C (N + j), ∃ y ∈ TopForm.orIn N C (N + j), x ≠ y) ∧
        ∀ w < N + (k + 1), TopForm.orIn N C w ⊆ D → ∀ x ∈ TopForm.orIn N C w, ∀ y ∈ TopForm.orIn N C w, f x = f y := fun h' =>
      ⟨Q, f, fun j hj => Nat.lt_succ_of_lt (hQ j hj), hc, hg, fun w hw => by
        by_cases e : w = N + k
        · rw [e]; exact h'
        · exact hf w (by omega)⟩
    obtain ⟨_, _, _, _, ho⟩ := gate2 h hk'
    rcases ho with ho | ho
    · exact keep fun _ x hx => absurd hx (inA h k hk' ho x)
    by_cases hD : TopForm.orIn N C (N + k) ⊆ D
    swap
    · exact keep fun h' => absurd h' hD
    have sub : ∀ t : Fin 2, TopForm.orIn N C (TopForm.opnd C k t) ⊆ D := fun t i hi => hD ((inO h k hk' ho i).2 ⟨t, hi⟩)
    have ch : ∀ t : Fin 2, ∀ x ∈ TopForm.orIn N C (TopForm.opnd C k t), ∀ y ∈ TopForm.orIn N C (TopForm.opnd C k t), f x = f y := fun t => hf _ (opl h k hk' t) (sub t)
    have two : ∀ x ∈ TopForm.orIn N C (N + k), x ∈ TopForm.orIn N C (TopForm.opnd C k 0) ∨ x ∈ TopForm.orIn N C (TopForm.opnd C k 1) := by
      intro x hx
      obtain ⟨t, ht⟩ := (inO h k hk' ho x).1 hx
      fin_cases t
      · exact Or.inl ht
      · exact Or.inr ht
    by_cases hE : ∃ x0 ∈ TopForm.orIn N C (TopForm.opnd C k 0), ∃ y0 ∈ TopForm.orIn N C (TopForm.opnd C k 1), f x0 ≠ f y0
    · obtain ⟨x0, hx0, y0, hy0, hne⟩ := hE
      refine ⟨insert k Q, fun z => if f z = f y0 then f x0 else f z, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · omega
        · have := hQ j hj; omega
      · intro S
        rw [Finset.card_insert_of_notMem (fun h' => by have := hQ k h'; omega)]
        have hsub : S.image f ⊆ insert (f y0) (S.image fun z => if f z = f y0 then f x0 else f z) := by
          intro v hv
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
          by_cases e : f z = f y0
          · rw [e]; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨z, hz, if_neg e⟩)
        have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have := hc S
        omega
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact ⟨ho, hD, x0, (inO h _ hk' ho x0).2 ⟨0, hx0⟩, y0, (inO h _ hk' ho y0).2 ⟨1, hy0⟩, fun e => hne (by rw [e])⟩
        · exact hg j hj
      · intro w hw hwD x hx y hy
        by_cases e : w = N + k
        · subst e
          have one : ∀ x ∈ TopForm.orIn N C (N + k), (if f x = f y0 then f x0 else f x) = f x0 := by
            intro x hx
            rcases two x hx with h' | h'
            · have := ch 0 x h' x0 hx0
              split_ifs
              · rfl
              · exact this
            · rw [if_pos (ch 1 x h' y0 hy0)]
          simp only [one x hx, one y hy]
        · simp only [hf w (by omega) hwD x hx y hy]
    · push Not at hE
      refine keep fun _ x hx y hy => ?_
      rcases two x hx with h1 | h1 <;> rcases two y hy with h2 | h2
      · exact ch 0 x h1 y h2
      · exact hE x h1 y h2
      · exact (hE y h2 x h1).symm
      · exact ch 1 x h1 y h2

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8901

theorem PEqualNP.Outside.L_meta_8901 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)), (2 : ℕ) ≤ x1 → (∀ (x7 x8 x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x7 ∈ x3 x9 ∧ x8 ∈ x3 x9 ∧ x7 ∈ x3 x10 ∧ x8 ∈ x3 x10)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → (∀ x9 ∈ x5, x9.1 ∈ x3 x9.2 ∧ ∃ x11 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x12 x13) (x2 + x2 + x11) = Bool.false) ∧ (Fin.castAdd x2 x9.1 ∈ PEqualNP.TopForm.orIn (x2 + x2) x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) ∧ Fin.natAdd x2 x9.2 ∈ PEqualNP.TopForm.orIn (x2 + x2) x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) ∨ Fin.natAdd x2 x9.2 ∈ PEqualNP.TopForm.orIn (x2 + x2) x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) ∧ Fin.castAdd x2 x9.1 ∈ PEqualNP.TopForm.orIn (x2 + x2) x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))))) → x5.card ≤ x4.size := by
  intro q n S C E hq hC4 hAO hE
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨e0, he0⟩
  · simp
  have : Nonempty (Fin (n + n)) := ⟨Fin.castAdd n e0.1⟩
  let Ad : Fin (n + n) → Fin (n + n) → Prop := fun a b => ∃ p l, p ∈ S l ∧ ((a = Fin.castAdd n p ∧ b = Fin.natAdd n l) ∨ (a = Fin.natAdd n l ∧ b = Fin.castAdd n p))
  let L : ℕ → Finset (Fin (n + n)) := fun w => PEqualNP.TopForm.orIn (n + n) C w
  have hcn : ∀ (p l : Fin n), Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro p l e
    have := congrArg Fin.val e
    simp at this
    omega
  have hci : ∀ p p' : Fin n, Fin.castAdd n p = Fin.castAdd n p' → p = p' := fun p p' e => Fin.ext (by simpa using congrArg Fin.val e)
  have hni : ∀ p p' : Fin n, Fin.natAdd n p = Fin.natAdd n p' → p = p' := fun p p' e => Fin.ext (by simpa using congrArg Fin.val e)
  have hAs : ∀ a b, Ad a b → Ad b a := by
    rintro a b ⟨p, l, h, h' | h'⟩
    · exact ⟨p, l, h, Or.inr ⟨h'.2, h'.1⟩⟩
    · exact ⟨p, l, h, Or.inl ⟨h'.2, h'.1⟩⟩
  have hA4 : ∀ z z' b b', Ad z b → Ad z b' → Ad z' b → Ad z' b' → b ≠ b' → z = z' := by
    rintro z z' b b' ⟨p1, l1, m1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ ⟨p2, l2, m2, ⟨e2, rfl⟩ | ⟨e2, rfl⟩⟩ ⟨p3, l3, m3, ⟨rfl, e3⟩ | ⟨rfl, e3⟩⟩ ⟨p4, l4, m4, ⟨e4, e4'⟩ | ⟨e4, e4'⟩⟩ hne
    all_goals first
      | exact absurd e2 (hcn _ _)
      | exact absurd e2.symm (hcn _ _)
      | exact absurd e3 (hcn _ _)
      | exact absurd e3.symm (hcn _ _)
      | exact absurd e4 (hcn _ _)
      | exact absurd e4.symm (hcn _ _)
      | exact absurd e4' (hcn _ _)
      | exact absurd e4'.symm (hcn _ _)
      | skip
    · have e2 := hci _ _ e2
      have e3 := hni _ _ e3
      have e4 := hci _ _ e4
      have e4' := hni _ _ e4'
      subst e2; subst e3; subst e4; subst e4'
      by_contra hz
      exact hC4 p1 p3 l1 l2 (fun e => hz (by rw [e])) (fun e => hne (by rw [e])) ⟨m1, m3, m2, m4⟩
    · have e2 := hni _ _ e2
      have e3 := hci _ _ e3
      have e4 := hni _ _ e4
      have e4' := hci _ _ e4'
      subst e2; subst e3; subst e4; subst e4'
      by_contra hz
      exact hC4 p1 p2 l1 l3 (fun e => hne (by rw [e])) (fun e => hz (by rw [e])) ⟨m1, m2, m3, m4⟩
  have len : ∀ (X Y : Finset (Fin n)), (PEqualNP.GenericRejection.incidenceInput X Y).length = n + n := by
    intro X Y; simp [PEqualNP.GenericRejection.incidenceInput]
  have gP : ∀ (X Y : Finset (Fin n)) (p : Fin n), (PEqualNP.GenericRejection.incidenceInput X Y).getD (Fin.castAdd n p : Fin (n + n)) false = decide (p ∈ X) := by
    intro X Y p
    unfold PEqualNP.GenericRejection.incidenceInput
    rw [Fin.val_castAdd, List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have gL : ∀ (X Y : Finset (Fin n)) (l : Fin n), (PEqualNP.GenericRejection.incidenceInput X Y).getD (Fin.natAdd n l : Fin (n + n)) false = decide (l ∈ Y) := by
    intro X Y l
    unfold PEqualNP.GenericRejection.incidenceInput
    rw [Fin.val_natAdd, List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have sp : ∀ a : Fin (n + n), (∃ p, a = Fin.castAdd n p) ∨ ∃ l, a = Fin.natAdd n l := by
    intro a
    by_cases h : (a : ℕ) < n
    · exact Or.inl ⟨⟨a, h⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨a - n, by omega⟩, Fin.ext (by simp; omega)⟩
  -- a top AND accepts only adjacent letters
  let Top : ℕ → Prop := fun g => g < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ a ∈ L (PEqualNP.TopForm.opnd C g 0), ∀ b ∈ L (PEqualNP.TopForm.opnd C g 1), Ad a b
  have hTop : ∀ g, g < C.size → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (X Y : Finset (Fin n)), Y.card ≤ q → PEqualNP.GenericRejection.IsFalseInput S X Y →
      PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + g) = false) → Top g := by
    intro g hg ho hrej
    have hg : g < C.gates.length := hg
    refine ⟨hg, ho, fun a ha b hb => ?_⟩
    have val : ∀ X Y : Finset (Fin n), (PEqualNP.GenericRejection.incidenceInput X Y).getD a false = true → (PEqualNP.GenericRejection.incidenceInput X Y).getD b false = true →
        PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + g) = true := by
      intro X Y h1 h2
      have k1 := PEqualNP.Outside.L_meta_8901.or_val hAO _ (len X Y) a h1 _ (by have := PEqualNP.Outside.L_meta_8901.opl hAO g hg 0; omega) ha
      have k2 := PEqualNP.Outside.L_meta_8901.or_val hAO _ (len X Y) b h2 _ (by have := PEqualNP.Outside.L_meta_8901.opl hAO g hg 1; omega) hb
      rw [PEqualNP.Outside.L_meta_8901.gval hAO _ (len X Y) g hg, ho, k1, k2]
      rfl
    have pl : ∀ p l, (∀ X Y : Finset (Fin n), p ∈ X → l ∈ Y → PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + g) = true) → p ∈ S l := by
      intro p l h
      by_contra hno
      have h1 := hrej {p} {l} (by simp; omega) (by
        intro l' hl'
        rw [Finset.mem_singleton] at hl'
        subst hl'
        rw [Finset.disjoint_singleton_right]
        exact hno)
      rw [h {p} {l} (by simp) (by simp)] at h1
      cases h1
    rcases sp a with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;> rcases sp b with ⟨p', rfl⟩ | ⟨l', rfl⟩
    · exfalso
      have h1 := hrej {p, p'} ∅ (by simp) (by intro l hl; simp at hl)
      rw [val {p, p'} ∅ (by rw [gP]; simp) (by rw [gP]; simp)] at h1
      cases h1
    · exact ⟨p, l', pl p l' fun X Y h1 h2 => val X Y (by rw [gP]; simpa using h1) (by rw [gL]; simpa using h2), Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨p', l, pl p' l fun X Y h1 h2 => val X Y (by rw [gL]; simpa using h2) (by rw [gP]; simpa using h1), Or.inr ⟨rfl, rfl⟩⟩
    · exfalso
      have h1 := hrej ∅ {l, l'} ((Finset.card_le_two).trans hq) (by intro x _; simp)
      rw [val ∅ {l, l'} (by rw [gL]; simp) (by rw [gL]; simp)] at h1
      cases h1
  let K : ℕ → Fin (n + n) → Fin 2 → Prop := fun g z t => L (PEqualNP.TopForm.opnd C g (1 - t)) = {z} ∧ ∀ a ∈ L (PEqualNP.TopForm.opnd C g t), Ad z a
  -- each edge has a top, and the top is a star
  have hedge : ∀ e ∈ E, ∃ g, Top g ∧ ∃ t : Fin 2, Fin.castAdd n e.1 ∈ L (PEqualNP.TopForm.opnd C g t) ∧ Fin.natAdd n e.2 ∈ L (PEqualNP.TopForm.opnd C g (1 - t)) := by
    intro e he
    obtain ⟨_, g, hg, ho, hrej, h | h⟩ := hE e he
    · exact ⟨g, hTop g hg ho hrej, 0, h.1, h.2⟩
    · exact ⟨g, hTop g hg ho hrej, 1, h.2, h.1⟩
  have flip : ∀ t : Fin 2, (1 : Fin 2) - (1 - t) = t := by decide
  have prod : ∀ g, Top g → ∀ t : Fin 2, ∀ a ∈ L (PEqualNP.TopForm.opnd C g t), ∀ b ∈ L (PEqualNP.TopForm.opnd C g (1 - t)), Ad a b := by
    intro g hg t a ha b hb
    fin_cases t
    · exact hg.2.2 a ha b hb
    · exact hAs _ _ (hg.2.2 b hb a ha)
  have hstar : ∀ g, Top g → ∀ t : Fin 2, (L (PEqualNP.TopForm.opnd C g t)).Nonempty → (L (PEqualNP.TopForm.opnd C g (1 - t))).Nonempty → ∃ z s, K g z s := by
    intro g hg t ⟨a, ha⟩ ⟨b, hb⟩
    by_cases h : ∃ b' ∈ L (PEqualNP.TopForm.opnd C g (1 - t)), b' ≠ b
    · obtain ⟨b', hb', hne⟩ := h
      refine ⟨a, 1 - t, ?_, fun c hc => prod g hg t a ha c hc⟩
      rw [flip]
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun a' ha' => ?_⟩
      exact hA4 a' a b' b (prod g hg t a' ha' b' hb') (prod g hg t a' ha' b hb) (prod g hg t a ha b' hb') (prod g hg t a ha b hb) hne
    · push Not at h
      exact ⟨b, t, Finset.eq_singleton_iff_unique_mem.2 ⟨hb, h⟩, fun c hc => hAs _ _ (prod g hg t c hc b hb)⟩
  choose! top htop htop2 using hedge
  choose! side hside1 hside2 using htop2
  have hK : ∀ e ∈ E, ∃ z s, K (top e) z s := fun e he => hstar _ (htop e he) (side e) ⟨_, hside1 e he⟩ ⟨_, hside2 e he⟩
  -- one centre per top
  let cen : ℕ → Option (Fin (n + n) × Fin 2) := fun g => if h : ∃ p : Fin (n + n) × Fin 2, K g p.1 p.2 then some h.choose else none
  have hcen : ∀ g p, cen g = some p → K g p.1 p.2 := by
    intro g p h
    by_cases hx : ∃ p : Fin (n + n) × Fin 2, K g p.1 p.2
    · simp only [cen, dif_pos hx, Option.some.injEq] at h
      rw [← h]; exact hx.choose_spec
    · simp only [cen, dif_neg hx] at h
      cases h
  have hcenE : ∀ e ∈ E, ∃ p, cen (top e) = some p := by
    intro e he
    obtain ⟨z, s, h⟩ := hK e he
    have hx : ∃ p : Fin (n + n) × Fin 2, K (top e) p.1 p.2 := ⟨(z, s), h⟩
    exact ⟨hx.choose, by simp only [cen, dif_pos hx]⟩
  choose! cz hcz using hcenE
  -- the leaf of an edge at its centre
  have hleaf : ∀ e ∈ E, ∃ a, a ∈ L (PEqualNP.TopForm.opnd C (top e) (cz e).2) ∧ Ad (cz e).1 a ∧
      (((cz e).1 = Fin.natAdd n e.2 ∧ a = Fin.castAdd n e.1) ∨ ((cz e).1 = Fin.castAdd n e.1 ∧ a = Fin.natAdd n e.2)) := by
    intro e he
    obtain ⟨k1, k2⟩ := hcen _ _ (hcz e he)
    have h1 := hside1 e he
    have h2 := hside2 e he
    have ts : side e = (cz e).2 ∨ side e = 1 - (cz e).2 := by
      generalize side e = s
      generalize (cz e).2 = s'
      revert s s'; decide
    rcases ts with ts | ts
    · rw [ts] at h1 h2
      rw [k1, Finset.mem_singleton] at h2
      exact ⟨_, h1, k2 _ h1, Or.inl ⟨h2.symm, rfl⟩⟩
    · rw [ts] at h1 h2
      rw [flip] at h2
      rw [k1, Finset.mem_singleton] at h1
      exact ⟨_, h2, k2 _ h2, Or.inr ⟨h1.symm, rfl⟩⟩
  choose! lf hlf1 hlf2 hlf3 using hleaf
  have m := fun z : Fin (n + n) => PEqualNP.Outside.L_meta_8901.merge hAO (Finset.univ.filter fun a => Ad z a) C.gates.length le_rfl
  choose Q f hQ hc hg hf using m
  let A : Fin (n + n) → Finset ℕ := fun z => (Finset.range C.gates.length).filter fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ s, cen g = some (z, s)
  -- edges at one centre
  have one : ∀ z, (E.filter fun e => (cz e).1 = z).card ≤ (Q z).card + (A z).card := by
    intro z
    let S' := (E.filter fun e => (cz e).1 = z).image lf
    have hcard : S'.card = (E.filter fun e => (cz e).1 = z).card := by
      refine Finset.card_image_of_injOn ?_
      intro e he e' he' h
      obtain ⟨he, hz⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 he)
      obtain ⟨he', hz'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 he')
      have h : lf e = lf e' := h
      rcases hlf3 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hlf3 e' he' with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact Prod.ext (hci _ _ (a2.symm.trans (h.trans b2))) (hni _ _ (a1.symm.trans (hz.trans (hz'.symm.trans b1))))
      · exact absurd (a2.symm.trans (h.trans b2)) (hcn _ _)
      · exact absurd (b2.symm.trans (h.symm.trans a2)) (hcn _ _)
      · exact Prod.ext (hci _ _ (a1.symm.trans (hz.trans (hz'.symm.trans b1)))) (hni _ _ (a2.symm.trans (h.trans b2)))
    have himg : (S'.image (f z)).card ≤ (A z).card := by
      have hne : ∀ v ∈ S'.image (f z), ∃ g ∈ A z, ∃ s, cen g = some (z, s) ∧ ∃ a ∈ L (PEqualNP.TopForm.opnd C g s), f z a = v := by
        intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨he, hz⟩ := Finset.mem_filter.1 he
        have hT := htop e he
        have hc' : cen (top e) = some (z, (cz e).2) := by rw [hcz e he, ← hz]
        exact ⟨top e, Finset.mem_filter.2 ⟨Finset.mem_range.2 hT.1, hT.2.1, _, hc'⟩, (cz e).2, hc', _, hlf1 e he, rfl⟩
      choose! gg hg1 ss hg2 aa hg3 hg4 using hne
      refine Finset.card_le_card_of_injOn gg (fun v hv => hg1 v hv) ?_
      intro v hv v' hv' h
      have hv := Finset.mem_coe.1 hv
      have hv' := Finset.mem_coe.1 hv'
      have e1 := hg2 v hv
      have e2 := hg2 v' hv'
      have h : gg v = gg v' := h
      rw [h, e2] at e1
      have es : ss v = ss v' := (Prod.ext_iff.1 (Option.some.inj e1)).2.symm
      have k := (hcen _ _ e2).2
      have hw : PEqualNP.TopForm.opnd C (gg v') (ss v') < n + n + C.gates.length := by
        have hr := (Finset.mem_filter.1 (hg1 v' hv')).1
        have := PEqualNP.Outside.L_meta_8901.opl hAO (gg v') (Finset.mem_range.1 hr) (ss v')
        have := Finset.mem_range.1 hr
        omega
      have a1 := hg3 v hv
      rw [h, es] at a1
      rw [← hg4 v hv, ← hg4 v' hv']
      exact hf z _ hw (fun a ha => Finset.mem_filter.2 ⟨Finset.mem_univ _, k a ha⟩) _ a1 _ (hg3 v' hv')
    have := hc z S'
    omega
  -- the gates of different centres are different
  have hdis : ∀ z ∈ (Finset.univ : Finset (Fin (n + n))), ∀ z' ∈ (Finset.univ : Finset (Fin (n + n))), z ≠ z' → Disjoint (Q z ∪ A z) (Q z' ∪ A z') := by
    intro z _ z' _ hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    have opA : ∀ z, j ∈ A z → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and := fun z h => (Finset.mem_filter.1 h).2.1
    rcases Finset.mem_union.1 hj with h | h <;> rcases Finset.mem_union.1 hj' with h' | h'
    · obtain ⟨_, s1, x, hx, y, hy, hxy⟩ := hg z j h
      obtain ⟨_, s2, _⟩ := hg z' j h'
      have q := fun a ha => (Finset.mem_filter.1 (s1 ha) : a ∈ _ ∧ Ad z a).2
      have q' := fun a ha => (Finset.mem_filter.1 (s2 ha) : a ∈ _ ∧ Ad z' a).2
      exact hne (hA4 z z' x y (q x hx) (q y hy) (q' x hx) (q' y hy) hxy)
    · have := (hg z j h).1; rw [opA _ h'] at this; cases this
    · have := (hg z' j h').1; rw [opA _ h] at this; cases this
    · obtain ⟨_, _, s, e⟩ := Finset.mem_filter.1 h
      obtain ⟨_, _, s', e'⟩ := Finset.mem_filter.1 h'
      rw [e] at e'
      exact hne (Prod.ext_iff.1 (Option.some.inj e')).1
  have hd2 : ∀ z, Disjoint (Q z) (A z) := by
    intro z
    rw [Finset.disjoint_left]
    intro j h h'
    have h1 := (hg z j h).1
    rw [(Finset.mem_filter.1 h').2.1] at h1
    cases h1
  have hsum : E.card = ∑ z : Fin (n + n), (E.filter fun e => (cz e).1 = z).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  have h5 : C.size = C.gates.length := rfl
  calc E.card = ∑ z : Fin (n + n), (E.filter fun e => (cz e).1 = z).card := hsum
    _ ≤ ∑ z : Fin (n + n), (Q z ∪ A z).card := Finset.sum_le_sum fun z _ => by rw [Finset.card_union_of_disjoint (hd2 z)]; exact one z
    _ = (Finset.univ.biUnion fun z => Q z ∪ A z).card := (Finset.card_biUnion hdis).symm
    _ ≤ (Finset.range C.gates.length).card := by
        refine Finset.card_le_card (Finset.biUnion_subset.2 fun z _ => Finset.union_subset ?_ (Finset.filter_subset _ _))
        exact fun j hj => Finset.mem_range.2 (hQ z j hj)
    _ = C.size := by rw [Finset.card_range, h5]
