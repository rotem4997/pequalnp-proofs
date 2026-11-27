import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358_aux

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem len (gs : List Gate) : ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepF]
    omega

theorem snoc_ne (l : List Bool) (v : Bool) (w : ℕ) (h : w ≠ l.length) :
    (l ++ [v]).getD w false = l.getD w false := by
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem snoc_eq (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem supp (n : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    ∀ W : Finset ℕ, ∃ S : Finset ℕ,
      S.card ≤ W.card + List.countP (fun g : Gate => !g.op.eval [false]) gs ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ w ∈ W, (gs.foldl stepF x).getD w false = (gs.foldl stepF y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ W
    exact ⟨W, by simp, fun x y _ _ h w hw => by simpa using h w hw⟩
  | append_singleton gs g ih =>
    intro hf W
    have ih' := ih (fun g hg => hf g (List.mem_append_left _ hg))
    obtain ⟨hop, hlen⟩ := hf g (by simp)
    haveI := Classical.dec (g.op = GateOp.not)
    by_cases hm : n + gs.length ∈ W
    · obtain ⟨R, hRdef⟩ : ∃ R : List ℕ, R = if g.op = GateOp.not then g.inputs.take 1 else g.inputs :=
        ⟨_, rfl⟩
      obtain ⟨S, hSc, hSa⟩ := ih' (W.erase (n + gs.length) ∪ R.toFinset)
      refine ⟨S, ?_, ?_⟩
      · have c1 := Finset.card_union_le (W.erase (n + gs.length)) R.toFinset
        have c2 := Finset.card_erase_of_mem hm
        have c3 := List.toFinset_card_le R
        have c4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hm⟩
        have c5 : R.length ≤ 1 + List.countP (fun g : Gate => !g.op.eval [false]) [g] := by
          rcases hop with h | h | h <;> simp [hRdef, h, GateOp.eval, List.countP_cons] <;> omega
        rw [List.countP_append]
        omega
      · intro x y hx hy hS w hw
        rw [List.foldl_append, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, stepF]
        by_cases hwm : w = n + gs.length
        · subst hwm
          have ex : ∀ v, (gs.foldl stepF x ++ [v]).getD (n + gs.length) false = v := by
            intro v
            have := snoc_eq (gs.foldl stepF x) v
            rwa [len, hx] at this
          have ey : ∀ v, (gs.foldl stepF y ++ [v]).getD (n + gs.length) false = v := by
            intro v
            have := snoc_eq (gs.foldl stepF y) v
            rwa [len, hy] at this
          rw [ex, ey]
          have hR : ∀ i ∈ R, (gs.foldl stepF x).getD i false = (gs.foldl stepF y).getD i false :=
            fun i hi => hSa x y hx hy hS i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
          rcases hop with h | h | h
          · have e : (g.inputs.map fun i => (gs.foldl stepF x).getD i false) =
                (g.inputs.map fun i => (gs.foldl stepF y).getD i false) :=
              List.map_congr_left (fun i hi => hR i (by simp [hRdef, h, hi]))
            rw [e]
          · have e : (g.inputs.map fun i => (gs.foldl stepF x).getD i false) =
                (g.inputs.map fun i => (gs.foldl stepF y).getD i false) :=
              List.map_congr_left (fun i hi => hR i (by simp [hRdef, h, hi]))
            rw [e]
          · rw [h]
            cases hin : g.inputs with
            | nil => simp [GateOp.eval]
            | cons a t =>
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              rw [hR a (by simp [hRdef, h, hin])]
        · rw [snoc_ne _ _ _ (by rw [len, hx]; exact hwm), snoc_ne _ _ _ (by rw [len, hy]; exact hwm)]
          exact hSa x y hx hy hS w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩))
    · obtain ⟨S, hSc, hSa⟩ := ih' W
      refine ⟨S, by rw [List.countP_append]; omega, ?_⟩
      intro x y hx hy hS w hw
      have hwm : w ≠ n + gs.length := fun e => hm (e ▸ hw)
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, stepF]
      rw [snoc_ne _ _ _ (by rw [len, hx]; exact hwm), snoc_ne _ _ _ (by rw [len, hy]; exact hwm)]
      exact hSa x y hx hy hS w hw

theorem one {α : Type} (p : α → Bool) : ∀ (l : List α) (j : ℕ) (hj : j < l.length),
    p (l[j]) = false → l.countP p + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro j hj; simp at hj
  | cons a t ih =>
    intro j hj hp
    cases j with
    | zero =>
      simp at hp
      have := List.countP_le_length (p := p) (l := t)
      simp [List.countP_cons, hp]
      omega
    | succ j =>
      simp at hj hp
      have := ih j hj hp
      simp [List.countP_cons]
      split <;> omega

theorem two {α : Type} (p : α → Bool) : ∀ (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length),
    p (l[i]'(by omega)) = false → p (l[j]) = false → l.countP p + 2 ≤ l.length := by
  intro l
  induction l with
  | nil => intro i j _ hj; simp at hj
  | cons a t ih =>
    intro i j hij hj hpi hpj
    cases j with
    | zero => omega
    | succ j =>
      simp at hj hpj
      cases i with
      | zero =>
        simp at hpi
        have := one p t j hj hpj
        rw [List.countP_cons, List.length_cons, hpi]
        simp only [Bool.false_eq_true, if_false]
        omega
      | succ i =>
        simp at hpi
        have := ih i j (by omega) hj hpi hpj
        simp [List.countP_cons]
        split <;> omega

end PEqualNP.Outside.L_meta_3358_aux

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  intro x2 hF hs x4 x5 h45 h4 h5
  obtain ⟨S, hSc, hSa⟩ := PEqualNP.Outside.L_meta_3358_aux.supp 17 x2.gates
    (fun g hg => by
      have := hF g hg
      simpa using this) {x2.output}
  have hc := PEqualNP.Outside.L_meta_3358_aux.two (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [Bool.false])
    x2.gates x4.val x5.val h45 x5.isLt
    (by simp only [List.get_eq_getElem] at h4; simp [h4, PEqualNP.CircuitLowerBounds.GateOp.eval])
    (by simp only [List.get_eq_getElem] at h5; simp [h5, PEqualNP.CircuitLowerBounds.GateOp.eval])
  have hsz : x2.gates.length ≤ 7 := hs
  rw [Finset.card_singleton] at hSc
  refine ⟨S ∩ Finset.range 17, Finset.inter_subset_right, ?_, ?_⟩
  · have := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := Finset.range 17))
    omega
  · intro x y hx hy h
    refine hSa x y hx hy ?_ x2.output (Finset.mem_singleton_self _)
    intro i hi
    by_cases hlt : i < 17
    · exact h i (Finset.mem_inter.mpr ⟨hi, Finset.mem_range.mpr hlt⟩)
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
