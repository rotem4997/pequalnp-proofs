import Mathlib
import PEqualNP.Defs

namespace Gap564

open PEqualNP.AndCount

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

def removeGate {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) : AndCountCircuit n where
  size := m
  leftVars j := lv (i₀.succAbove j)
  leftGates j := Finset.univ.filter (fun k => i₀.succAbove k ∈ lg (i₀.succAbove j))
  rightVars j := rv (i₀.succAbove j)
  rightGates j := Finset.univ.filter (fun k => i₀.succAbove k ∈ rg (i₀.succAbove j))
  outVars := ov
  outGates := Finset.univ.filter (fun k => i₀.succAbove k ∈ og)

theorem mem_leftGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (j k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).leftGates j ↔
      i₀.succAbove k ∈ lg (i₀.succAbove j) := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ lg (i₀.succAbove j)) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem mem_rightGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (j k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).rightGates j ↔
      i₀.succAbove k ∈ rg (i₀.succAbove j) := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ rg (i₀.succAbove j)) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem mem_outGates {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (k : Fin m) :
    k ∈ (removeGate lv lg rv rg ov og i₀).outGates ↔ i₀.succAbove k ∈ og := by
  show k ∈ Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ og) ↔ _
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

theorem side_corr {n m : ℕ} (i₀ : Fin (m + 1)) (U B : Finset (Fin n))
    (F : Finset (Fin (m + 1))) (hF : i₀ ∉ F) (j : Fin m) (val₁ : Fin m → Bool)
    (val : Fin (m + 1) → Bool) (h : ∀ k : Fin m, k < j → val₁ k = val (i₀.succAbove k)) :
    AndCountCircuit.sideTrue U B (Finset.univ.filter (fun k => i₀.succAbove k ∈ F)) j val₁ =
      AndCountCircuit.sideTrue U B F (i₀.succAbove j) val := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨k, hk, hlt, hv⟩)
    · exact Or.inl h1
    · refine Or.inr ⟨i₀.succAbove k, (Finset.mem_filter.mp hk).2,
        Fin.succAbove_lt_succAbove_iff.mpr hlt, ?_⟩
      rw [← h k hlt]
      exact hv
  · rintro (h1 | ⟨k', hk', hlt, hv⟩)
    · exact Or.inl h1
    · have hne : k' ≠ i₀ := by
        intro e
        rw [e] at hk'
        exact hF hk'
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
      have hkj : k < j := Fin.succAbove_lt_succAbove_iff.mp hlt
      refine Or.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, hkj, ?_⟩
      rw [h k hkj]
      exact hv

theorem remove_val {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1))
    (hl : ∀ k, i₀ ∉ lg k) (hr : ∀ k, i₀ ∉ rg k) (U : Finset (Fin n)) :
    ∀ (b : ℕ) (j : Fin m), j.val < b →
      (removeGate lv lg rv rg ov og i₀).gateVal U j =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove j) := by
  intro b
  induction b with
  | zero =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ b ih =>
    intro j hj
    have key : ∀ k : Fin m, k < j → (removeGate lv lg rv rg ov og i₀).gateVal U k =
        (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U (i₀.succAbove k) := by
      intro k hk
      have hkj : k.val < j.val := hk
      exact ih k (by omega)
    rw [gateVal_eq (removeGate lv lg rv rg ov og i₀) U j,
      gateVal_eq (AndCountCircuit.mk (m + 1) lv lg rv rg ov og) U (i₀.succAbove j)]
    have e1 := side_corr i₀ U (lv (i₀.succAbove j)) (lg (i₀.succAbove j)) (hl _) j
      ((removeGate lv lg rv rg ov og i₀).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key
    have e2 := side_corr i₀ U (rv (i₀.succAbove j)) (rg (i₀.succAbove j)) (hr _) j
      ((removeGate lv lg rv rg ov og i₀).gateVal U)
      ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U) key
    exact congrArg₂ (fun a c => a && c) e1 e2

theorem remove_eval {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1)) (hout : i₀ ∉ og)
    (hl : ∀ k, i₀ ∉ lg k) (hr : ∀ k, i₀ ∉ rg k) (U : Finset (Fin n)) :
    (removeGate lv lg rv rg ov og i₀).eval U =
      (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).eval U := by
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hv⟩)
    · exact Or.inl h1
    · refine Or.inr ⟨i₀.succAbove j, (mem_outGates lv lg rv rg ov og i₀ j).mp hj, ?_⟩
      rw [← remove_val lv lg rv rg ov og i₀ hl hr U (j.val + 1) j (Nat.lt_succ_self _)]
      exact hv
  · rintro (h1 | ⟨j', hj', hv⟩)
    · exact Or.inl h1
    · have hne : j' ≠ i₀ := by
        intro e
        rw [e] at hj'
        exact hout hj'
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      refine Or.inr ⟨j, (mem_outGates lv lg rv rg ov og i₀ j).mpr hj', ?_⟩
      rw [remove_val lv lg rv rg ov og i₀ hl hr U (j.val + 1) j (Nat.lt_succ_self _)]
      exact hv

theorem remove_wf {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1))
    (hwf : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) :
    (removeGate lv lg rv rg ov og i₀).WellFormed := by
  intro j
  constructor
  · intro k hk
    have h1 : i₀.succAbove k ∈ lg (i₀.succAbove j) :=
      (mem_leftGates lv lg rv rg ov og i₀ j k).mp hk
    exact Fin.succAbove_lt_succAbove_iff.mp ((hwf (i₀.succAbove j)).1 _ h1)
  · intro k hk
    have h1 : i₀.succAbove k ∈ rg (i₀.succAbove j) :=
      (mem_rightGates lv lg rv rg ov og i₀ j k).mp hk
    exact Fin.succAbove_lt_succAbove_iff.mp ((hwf (i₀.succAbove j)).2 _ h1)

theorem filter_nonempty {m : ℕ} (i₀ : Fin (m + 1)) (F : Finset (Fin (m + 1))) (hF : i₀ ∉ F)
    (h : F.Nonempty) : (Finset.univ.filter (fun k : Fin m => i₀.succAbove k ∈ F)).Nonempty := by
  obtain ⟨k', hk'⟩ := h
  have hne : k' ≠ i₀ := by
    intro e
    rw [e] at hk'
    exact hF hk'
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩⟩

theorem remove_sides {n m : ℕ} (lv : Fin (m + 1) → Finset (Fin n))
    (lg : Fin (m + 1) → Finset (Fin (m + 1))) (rv : Fin (m + 1) → Finset (Fin n))
    (rg : Fin (m + 1) → Finset (Fin (m + 1))) (ov : Finset (Fin n))
    (og : Finset (Fin (m + 1))) (i₀ : Fin (m + 1))
    (hl : ∀ k, i₀ ∉ lg k) (hr : ∀ k, i₀ ∉ rg k)
    (h : ∀ i : Fin (m + 1), ((lv i).Nonempty ∨ (lg i).Nonempty) ∧
      ((rv i).Nonempty ∨ (rg i).Nonempty)) :
    ∀ j : Fin m,
      (((removeGate lv lg rv rg ov og i₀).leftVars j).Nonempty ∨
        ((removeGate lv lg rv rg ov og i₀).leftGates j).Nonempty) ∧
      (((removeGate lv lg rv rg ov og i₀).rightVars j).Nonempty ∨
        ((removeGate lv lg rv rg ov og i₀).rightGates j).Nonempty) := by
  intro j
  obtain ⟨h1, h2⟩ := h (i₀.succAbove j)
  constructor
  · rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (filter_nonempty i₀ _ (hl _) h1)
  · rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (filter_nonempty i₀ _ (hr _) h2)

theorem aux : ∀ (s n : ℕ) (C : AndCountCircuit n), C.size = s → C.WellFormed →
    ∃ C' : AndCountCircuit n,
      C'.WellFormed ∧ C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
      (∀ i : Fin C'.size, i ∈ C'.outGates ∨
        ∃ k : Fin C'.size, i ∈ C'.leftGates k ∨ i ∈ C'.rightGates k) ∧
      ((∀ i : Fin C.size, ((C.leftVars i).Nonempty ∨ (C.leftGates i).Nonempty) ∧
          ((C.rightVars i).Nonempty ∨ (C.rightGates i).Nonempty)) →
        ∀ i : Fin C'.size, ((C'.leftVars i).Nonempty ∨ (C'.leftGates i).Nonempty) ∧
          ((C'.rightVars i).Nonempty ∨ (C'.rightGates i).Nonempty)) ∧
      ((∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false) →
        ∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) := by
  intro s
  induction s with
  | zero =>
    intro n C hs hwf
    refine ⟨C, hwf, le_refl _, fun _ => rfl, ?_, fun h => h, fun h => h⟩
    intro i
    have hi : i.val < C.size := i.2
    omega
  | succ m ih =>
    intro n C hs hwf
    by_cases hused : ∀ i : Fin C.size, i ∈ C.outGates ∨
        ∃ k : Fin C.size, i ∈ C.leftGates k ∨ i ∈ C.rightGates k
    · exact ⟨C, hwf, le_refl _, fun _ => rfl, hused, fun h => h, fun h => h⟩
    · obtain ⟨i₀, hi₀⟩ := not_forall.mp hused
      have hout : i₀ ∉ C.outGates := fun h => hi₀ (Or.inl h)
      have hk : ∀ k : Fin C.size, i₀ ∉ C.leftGates k ∧ i₀ ∉ C.rightGates k :=
        fun k => ⟨fun h => hi₀ (Or.inr ⟨k, Or.inl h⟩), fun h => hi₀ (Or.inr ⟨k, Or.inr h⟩)⟩
      clear hi₀ hused
      obtain ⟨size, lv, lg, rv, rg, ov, og⟩ := C
      have hs' : size = m + 1 := hs
      subst hs'
      have hl : ∀ k, i₀ ∉ lg k := fun k => (hk k).1
      have hr : ∀ k, i₀ ∉ rg k := fun k => (hk k).2
      obtain ⟨C', hwf', hsz', hev', hused', hp1', hp2'⟩ :=
        ih n (removeGate lv lg rv rg ov og i₀) rfl (remove_wf lv lg rv rg ov og i₀ hwf)
      have hsz2 : C'.size ≤ m := hsz'
      refine ⟨C', hwf', Nat.le_succ_of_le hsz2, ?_, hused', ?_, ?_⟩
      · intro U
        rw [hev' U]
        exact remove_eval lv lg rv rg ov og i₀ hout hl hr U
      · intro h
        exact hp1' (remove_sides lv lg rv rg ov og i₀ hl hr h)
      · intro h
        refine hp2' ?_
        intro j v
        rw [remove_val lv lg rv rg ov og i₀ hl hr {v} (j.val + 1) j (Nat.lt_succ_self _)]
        exact h _ v

end Gap564

theorem PEqualNP.Outside.L_meta_564 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    C.WellFormed →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧ C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
        (∀ i : Fin C'.size, i ∈ C'.outGates ∨
          ∃ k : Fin C'.size, i ∈ C'.leftGates k ∨ i ∈ C'.rightGates k) ∧
        ((∀ i : Fin C.size, ((C.leftVars i).Nonempty ∨ (C.leftGates i).Nonempty) ∧
            ((C.rightVars i).Nonempty ∨ (C.rightGates i).Nonempty)) →
          ∀ i : Fin C'.size, ((C'.leftVars i).Nonempty ∨ (C'.leftGates i).Nonempty) ∧
            ((C'.rightVars i).Nonempty ∨ (C'.rightGates i).Nonempty)) ∧
        ((∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false) →
          ∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) := by
  intro n C hwf
  exact Gap564.aux C.size n C rfl hwf
