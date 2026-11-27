import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8213

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



def cn (n : ℕ) (gs : List Gate) : List (List ℕ) := gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []

theorem cn_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    cn n (gs ++ [g]) = PEqualNP.EdgeOwnership.coneStep n (cn n gs) g := by
  simp [cn, List.foldl_append]

theorem cn_length (n : ℕ) (gs : List Gate) : (cn n gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [cn_snoc]; simp [PEqualNP.EdgeOwnership.coneStep, ih]

theorem cn_iff (n : ℕ) (gs : List Gate) : ∀ (j : ℕ) (hj : j < gs.length) (b : ℕ),
    b ∈ (cn n gs).getD j [] ↔ ∃ w ∈ gs[j].inputs, (n ≤ w ∧ w < n + j) ∧
      (b = w - n ∨ b ∈ (cn n gs).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj b
    have hlen := cn_length n gs
    have low : ∀ i, i < gs.length → (cn n (gs ++ [g])).getD i [] = (cn n gs).getD i [] := by
      intro i hi
      rw [cn_snoc]
      exact getD_ltz _ _ _ _ (by rw [hlen]; exact hi)
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [low j h, List.getElem_append_left h, ih j h b]
      constructor
      · rintro ⟨w, h1, h2, h3⟩
        exact ⟨w, h1, h2, by rw [low _ (by omega)]; exact h3⟩
      · rintro ⟨w, h1, h2, h3⟩
        exact ⟨w, h1, h2, by rwa [low _ (by omega)] at h3⟩
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      have hv : (cn n (gs ++ [g])).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cn n gs).length))).flatMap
            (fun w => (w - n) :: (cn n gs).getD (w - n) []) := by
        rw [cn_snoc]
        unfold PEqualNP.EdgeOwnership.coneStep
        rw [← hlen, getD_at']
      rw [hg, hv, List.mem_flatMap]
      constructor
      · rintro ⟨w, h1, h2⟩
        obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
        have h5 := of_decide_eq_true h4
        rw [hlen] at h5
        exact ⟨w, h3, h5, by rw [low _ (by omega)]; exact List.mem_cons.1 h2⟩
      · rintro ⟨w, h1, h2, h3⟩
        rw [low _ (by omega)] at h3
        exact ⟨w, List.mem_filter.2 ⟨h1, decide_eq_true (by rw [hlen]; exact h2)⟩,
          List.mem_cons.2 h3⟩


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8213

theorem PEqualNP.Outside.L_meta_8213 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1;   have x3 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;   have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;   have x5 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x7 x8 x9 : Fin (26 : ℕ) → Bool), (∀ (x10 : Fin (26 : ℕ)), x9 x10 = Bool.true → x7 x10 = Bool.true ∨ x8 x10 = Bool.true) → x1.eval (List.ofFn x9) = Bool.true → x1.eval (List.ofFn x7) = Bool.false → x1.eval (List.ofFn x8) = Bool.false → ∀ (x14 x15 : ℕ), (x14 < x1.size ∧ (x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3 x14 x9 = Bool.true ∧ ∀ x16 ∈ (x2 x14).inputs, x4 x16 x7 = Bool.false) → (x15 < x1.size ∧ (x2 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3 x15 x9 = Bool.true ∧ ∀ x17 ∈ (x2 x15).inputs, x4 x17 x8 = Bool.false) → ¬x5 x14 x15 → ¬x5 x15 x14 → ∃ x20 < x1.size, (x2 x20).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3 x20 x9 = Bool.true ∧ x20 ≠ x14 ∧ x20 ≠ x15 := by
  intro C G V WV K hC x7 x8 x9 hsub h9 h7 h8 p q hp hq hnpq hnqp
  classical
  let W : (Fin 26 → Bool) → ℕ → Bool := fun x w => (PEqualNP.Outside.L_meta_8213.run C.gates (List.ofFn x)).getD w false
  have gA : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := fun j hj => List.getD_eq_getElem _ _ hj
  have hback : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < 26 + j := by
    intro j hj i hi
    exact hC.2.1 j hj i (by rw [gA j hj]; exact hi)
  have Wg : ∀ x j (hj : j < C.gates.length), W x (26 + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => W x i) := by
    intro x j hj
    have := PEqualNP.Outside.L_meta_8213.run_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at this
    refine this.trans ?_
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [if_pos (hback j hj i hi)]
  have Wi : ∀ x (i : Fin 26), W x i = x i := by
    intro x i
    simp only [W]
    rw [PEqualNP.Outside.L_meta_8213.run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hand : ∀ x j (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and → (W x (26 + j) = true ↔ ∀ i ∈ C.gates[j].inputs, W x i = true) := by
    intro x j hj ho
    rw [Wg x j hj, ho]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hor : ∀ x j (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or → (W x (26 + j) = true ↔ ∃ i ∈ C.gates[j].inputs, W x i = true) := by
    intro x j hj ho
    rw [Wg x j hj, ho]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  let cone : ℕ → List ℕ := fun j => (PEqualNP.Outside.L_meta_8213.cn 26 C.gates).getD j []
  have hcone : ∀ j (hj : j < C.gates.length) b, b ∈ cone j ↔ ∃ w ∈ C.gates[j].inputs, (26 ≤ w ∧ w < 26 + j) ∧ (b = w - 26 ∨ b ∈ cone (w - 26)) :=
    fun j hj b => PEqualNP.Outside.L_meta_8213.cn_iff 26 C.gates j hj b
  have hlt : ∀ j, j < C.gates.length → ∀ b ∈ cone j, b < j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj b hb
      obtain ⟨w, _, hw2, h | h⟩ := (hcone j hj b).1 hb
      · omega
      · have := ih (w - 26) (by omega) (by omega) b h
        omega
  have leaf : ∀ w, W x9 w = true → (∃ i : Fin 26, x9 i = true ∧ ∀ z : Fin 26 → Bool, z i = true → W z w = true) ∨
      ∃ j, ∃ hj : j < C.gates.length, C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ W x9 (26 + j) = true ∧ (∀ z, W z (26 + j) = true → W z w = true) ∧ 26 ≤ w ∧ (j = w - 26 ∨ j ∈ cone (w - 26)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      by_cases h1 : w < 26
      · left
        have e := fun z => Wi z ⟨w, h1⟩
        exact ⟨⟨w, h1⟩, (e x9).symm.trans h, fun z hz => (e z).trans hz⟩
      · by_cases h2 : w < 26 + C.gates.length
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
          have hj : j < C.gates.length := by omega
          rcases hC.1 _ (List.getElem_mem hj) with ho | ho
          · right
            exact ⟨j, hj, ho, h, fun z hz => hz, by omega, Or.inl (by omega)⟩
          · obtain ⟨u, hu, hut⟩ := (hor x9 j hj ho).1 h
            rcases ih u (hback j hj u hu) hut with ⟨i, hi, hz⟩ | ⟨k, hk, ok, hk9, hz, hu26, hc⟩
            · exact Or.inl ⟨i, hi, fun z hzi => (hor z j hj ho).2 ⟨u, hu, hz z hzi⟩⟩
            · refine Or.inr ⟨k, hk, ok, hk9, fun z hzk => (hor z j hj ho).2 ⟨u, hu, hz z hzk⟩, by omega, Or.inr ?_⟩
              rw [Nat.add_sub_cancel_left]
              exact (hcone j hj k).2 ⟨u, hu, ⟨hu26, hback j hj u hu⟩, hc⟩
        · simp only [W] at h
          rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_8213.run_length]; simp; omega)] at h
          cases h
  by_contra hcon
  have honly : ∀ j (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and → W x9 (26 + j) = true → j = p ∨ j = q := by
    intro j hj ho hw
    by_contra hne
    rw [not_or] at hne
    exact hcon ⟨j, hj, by simp only [G]; rw [gA j hj]; exact ho, hw, hne.1, hne.2⟩
  -- an AND whose operands are false at y is true at y'
  have step : ∀ (a b : ℕ) (y y' : Fin 26 → Bool), (∀ i, x9 i = true → y i = true ∨ y' i = true) → (∀ j (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and → W x9 (26 + j) = true → j = a ∨ j = b) →
      ∀ ha : a < C.gates.length, C.gates[a].op = PEqualNP.CircuitLowerBounds.GateOp.and → W x9 (26 + a) = true → (∀ u ∈ C.gates[a].inputs, W y u = false) → b ∉ cone a → W y' (26 + a) = true := by
    intro a b y y' hs ho ha oa h9a hf hbc
    refine (hand y' a ha oa).2 fun u hu => ?_
    have hu9 := (hand x9 a ha oa).1 h9a u hu
    rcases leaf u hu9 with ⟨i, hi, hz⟩ | ⟨k, hk, ok, hk9, _, hu26, hc⟩
    · rcases hs i hi with h | h
      · have := hz y h
        rw [hf u hu] at this; cases this
      · exact hz y' h
    · exfalso
      have hkc : k ∈ cone a := (hcone a ha k).2 ⟨u, hu, ⟨hu26, hback a ha u hu⟩, hc⟩
      rcases ho k hk ok hk9 with e | e
      · have := hlt a ha k hkc
        omega
      · exact hbc (by rw [← e]; exact hkc)
  have hpl : p < C.gates.length := hp.1
  have hql : q < C.gates.length := hq.1
  have op : C.gates[p].op = PEqualNP.CircuitLowerBounds.GateOp.and := by have := hp.2.1; simp only [G] at this; rw [gA p hpl] at this; exact this
  have oq : C.gates[q].op = PEqualNP.CircuitLowerBounds.GateOp.and := by have := hq.2.1; simp only [G] at this; rw [gA q hql] at this; exact this
  have fp : ∀ u ∈ C.gates[p].inputs, W x7 u = false := fun u hu => hp.2.2.2 u (by simp only [G]; rw [gA p hpl]; exact hu)
  have fq : ∀ u ∈ C.gates[q].inputs, W x8 u = false := fun u hu => hq.2.2.2 u (by simp only [G]; rw [gA q hql]; exact hu)
  have e7 : W x7 C.output = false := h7
  have e8 : W x8 C.output = false := h8
  rcases leaf C.output h9 with ⟨i, hi, hz⟩ | ⟨k, hk, ok, hk9, hz, _⟩
  · rcases hsub i hi with h | h
    · rw [hz x7 h] at e7; cases e7
    · rw [hz x8 h] at e8; cases e8
  · rcases honly k hk ok hk9 with rfl | rfl
    · have := step k q x7 x8 hsub honly hk ok hk9 fp hnqp
      rw [hz x8 this] at e8; cases e8
    · have := step k p x8 x7 (fun i hi => (hsub i hi).symm) (fun j hj o1 o2 => (honly j hj o1 o2).symm) hk ok hk9 fq hnpq
      rw [hz x7 this] at e7; cases e7
