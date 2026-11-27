import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2861_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem at_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) ∧
    ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  constructor
  · rw [← hQ]
    simp [step, List.getD_eq_getElem?_getD]
  · intro i hi
    rw [← hQ] at hi
    have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi2]
    simp only [step]
    rw [List.getElem?_append_left hi]

theorem fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := ext gs w
  rw [hs]; exact List.getD_append _ _ _ _ h

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := ext gs w
  rw [hs]; simp [hl]

theorem recur (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (hrb : ∀ m ∈ gs[k].inputs, m < w.length + k) :
    (gs.foldl step w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun m => (gs.foldl step w).getD m false) := by
  obtain ⟨h1, h2⟩ := at_gate gs w k hk
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro m hm
  exact (h2 m (hrb m hm)).symm

end PEqualNP.Outside.L_meta_2861_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2861_aux in
theorem PEqualNP.Outside.L_meta_2861 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  rintro n ⟨gs, out⟩ i j a b c hRB hj hij hopi hini hopj hinj hc hno hout
  simp only at hj hno hout
  have hi : i < gs.length := by omega
  have hga : ∀ (l : List Gate) (o k : ℕ) (hk : k < l.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt ⟨l, o⟩ k = l[k] := by
    intro l o k hk
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hk]
  have hgi : gs[i] = ⟨GateOp.and, [a, b]⟩ := by
    have e1 := hopi
    have e2 := hini
    rw [hga _ _ _ hi] at e1 e2
    rcases hh : gs[i] with ⟨o, l⟩
    rw [hh] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  have hgj : gs[j] = ⟨GateOp.and, [n + i, c]⟩ := by
    have e1 := hopj
    have e2 := hinj
    rw [hga _ _ _ hj] at e1 e2
    rcases hh : gs[j] with ⟨o, l⟩
    rw [hh] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  have hrb : ∀ k (hk : k < gs.length), ∀ m ∈ gs[k].inputs, m < n + k := by
    intro k hk m hm
    exact hRB k hk m (by rw [hga _ _ _ hk]; exact hm)
  have ha : a < n + i := hrb i hi a (by rw [hgi]; simp)
  have hb : b < n + i := hrb i hi b (by rw [hgi]; simp)
  have hlen : ((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩).length = gs.length := by
    simp
  have hnj : ((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩)[j]'(by rw [hlen]; exact hj)
      = ⟨GateOp.and, [n + i, b]⟩ := by
    simp
  have hni : ((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩)[i]'(by rw [hlen]; exact hi)
      = ⟨GateOp.and, [a, c]⟩ := by
    simp [List.getElem_set, Nat.ne_of_gt hij]
  have hnk : ∀ k (hk : k < gs.length), k ≠ i → k ≠ j →
      ((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩)[k]'(by rw [hlen]; exact hk)
      = gs[k] := by
    intro k hk h1 h2
    simp [List.getElem_set, Ne.symm h1, Ne.symm h2]
  have hrb2 : ∀ k (hk : k < gs.length),
      ∀ m ∈ (((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩)[k]'(by rw [hlen]; exact hk)).inputs,
      m < n + k := by
    intro k hk m hm
    by_cases h2 : k = j
    · subst h2
      rw [hnj] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega
    · by_cases h1 : k = i
      · subst h1
        rw [hni] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
      · rw [hnk k hk h1 h2] at hm
        exact hrb k hk m hm
  refine ⟨?_, ?_, ?_⟩
  · intro k hk m hm
    simp only [List.length_set] at hk
    rw [hga _ _ _ (by rw [hlen]; exact hk)] at hm
    exact hrb2 k hk m hm
  · simp [Circuit.size]
  · intro x
    have hmain : ∀ p, p ≠ n + i →
        (((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩).foldl step (List.ofFn x)).getD p false
        = (gs.foldl step (List.ofFn x)).getD p false := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ih =>
      intro hp
      rcases lt_or_ge p n with h | h
      · rw [fold_get _ _ _ (by simpa using h), fold_get _ _ _ (by simpa using h)]
      · rcases lt_or_ge p (n + gs.length) with h2 | h2
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
          have hk : k < gs.length := by omega
          have hki : k ≠ i := by omega
          have r1 := recur gs (List.ofFn x) k hk (by simpa using hrb k hk)
          have r2 := recur ((gs.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩)
            (List.ofFn x) k (by rw [hlen]; exact hk) (by simpa using hrb2 k hk)
          simp only [List.length_ofFn] at r1 r2
          by_cases hkj : k = j
          · subst hkj
            have s1 := recur gs (List.ofFn x) i hi (by simpa using hrb i hi)
            have s2 := recur ((gs.set i ⟨GateOp.and, [a, c]⟩).set k ⟨GateOp.and, [n + i, b]⟩)
              (List.ofFn x) i (by rw [hlen]; exact hi) (by simpa using hrb2 i hi)
            simp only [List.length_ofFn] at s1 s2
            rw [hgj] at r1
            rw [hnj] at r2
            rw [hgi] at s1
            rw [hni] at s2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
              Bool.and_true] at r1 r2 s1 s2
            rw [r1, r2, s1, s2, ih a (by omega) (by omega), ih b (by omega) (by omega),
              ih c (by omega) (by omega)]
            simp only [Bool.and_assoc]
            congr 1
            exact Bool.and_comm _ _
          · rw [r1, r2, hnk k hk hki hkj]
            congr 1
            apply List.map_congr_left
            intro m hm
            apply ih m (hrb k hk m hm)
            intro hmi
            apply hno k hk hkj
            rw [hga _ _ _ hk, ← hmi]
            exact hm
        · rw [List.getD_eq_default _ _ (by rw [fold_len, hlen]; simpa using h2),
            List.getD_eq_default _ _ (by rw [fold_len]; simpa using h2)]
    exact hmain out hout
