import PEqualNP.MetaComplexity.Helpers.LiftFixMain

/-!
# Helpers for L-meta-2925: the lift step of L-meta-2715 inside the model `IsAO2`

`lift_step_AO` is `LiftFix.lift_step` (same proof) with one more conclusion: if every gate of
`D` reads exactly two wires, so does every gate of the new circuit (the copy `OR [u]` is the
deleted gate, the new output `OR [old output, t]` reads two). `main_AO` iterates it inside
`IsAO2`, keeping the size.
-/

namespace PEqualNP.MetaComplexity.LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Lift
open PEqualNP.MetaComplexity.NestedCover

theorem lift_step_AO (n : ℕ) (D : Circuit) (T : Finset ℕ) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL2 : ∀ g ∈ D.gates, g.inputs.length = 2)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
      (∀ g ∈ D1.gates, g.inputs.length = 2) ∧
      D1.gates.length = D.gates.length ∧ circuitFun n D1 = circuitFun n D ∧
      PA D1 T1 ∧ PB n D1 T1 ∧ T1.card = T.card + 1 := by
  have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
  have hrk := readsBack_get n D hR k g hkg
  have htk : t < n + k := hrk t ht
  have hgl : g.inputs.length ≤ 2 := (hM g (List.mem_of_getElem? hkg)).2
  obtain ⟨u, hu, hequ⟩ := pick_u g hor hgl t ht
  have huk : u < n + k := hrk u hu
  obtain ⟨x0, hx0⟩ := hsat
  have hout : D.output < n + D.gates.length := by
    by_contra hcon
    have h1 := himp x0 hx0
    unfold circuitFun Circuit.eval at h1
    rw [getD_oob] at h1
    · exact absurd h1 (by simp)
    · rw [wires_eq, foldl_step_length]; simp; omega
  have hTlt : ∀ j ∈ T, j < D.gates.length := fun j hj => by
    obtain ⟨g', hg', _⟩ := hA j hj
    exact (List.getElem?_eq_some_iff.mp hg').1
  -- the circuit with operands ordered
  have hE0w : ∀ w, (D.gates.set k ⟨GateOp.or, [u, t]⟩).foldl step w = D.gates.foldl step w :=
    fun w => foldl_set_equiv D.gates k g _ hkg hequ w
  have hE0f : circuitFun n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ = circuitFun n D := by
    funext x
    simp only [circuitFun, Circuit.eval, wires_eq, hE0w]
  have hE0M : Monotone2 ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ := by
    intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hM g' h
    · subst h; simp
  have hE0k : (D.gates.set k ⟨GateOp.or, [u, t]⟩)[k]? = some ⟨GateOp.or, [u, t]⟩ := by
    simp [List.getElem?_set, hk]
  have hL := L2604 n ⟨D.gates.set k ⟨GateOp.or, [u, t]⟩, D.output⟩ k u t hE0M
    (by simpa using hk) hE0k htk (by
      intro x hx
      rw [hE0f]
      apply himp
      simpa [wires_eq, hE0w] using hx)
  simp only [List.set_set, List.length_set] at hL
  rw [hE0f] at hL
  -- the lifted circuit E
  set E : Circuit := ⟨D.gates.set k ⟨GateOp.or, [u]⟩ ++ [⟨GateOp.or, [D.output, t]⟩], n + D.gates.length⟩
    with hE
  have hElen : E.gates.length = D.gates.length + 1 := by simp [hE]
  have hEget : ∀ j, j ≠ k → j < D.gates.length → E.gates[j]? = D.gates[j]? := by
    intro j hjk hj
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hj), List.getElem?_set_ne (Ne.symm hjk)]
  have hEk : E.gates[k]? = some ⟨GateOp.or, [u]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_left (by simpa using hk)]
    simp [List.getElem?_set, hk]
  have hEN : E.gates[D.gates.length]? = some ⟨GateOp.or, [D.output, t]⟩ := by
    simp only [hE]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hEM : Monotone2 E := by
    intro g' hg'
    simp only [hE, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rcases List.mem_or_eq_of_mem_set hg' with h | h
      · exact hM g' h
      · subst h; simp
    · simp
  have hER : ReadsBack n E := by
    apply readsBack_of_get
    intro j g' hg' i hi
    rcases Nat.lt_trichotomy j D.gates.length with hj | hj | hj
    · by_cases hjk : j = k
      · subst hjk
        rw [hEk] at hg'
        cases hg'
        simp at hi
        omega
      · rw [hEget j hjk hj] at hg'
        exact readsBack_get n D hR j g' hg' i hi
    · subst hj
      rw [hEN] at hg'
      cases hg'
      simp at hi
      omega
    · have : E.gates[j]? = none := List.getElem?_eq_none (by omega)
      rw [this] at hg'
      cases hg'
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false := by
    intro x
    have := wires_copy E k u hEk (List.ofFn x) (by simp; omega)
    simpa using this
  have hEf : circuitFun n E = circuitFun n D := by
    rw [← hL]
  -- delete the copy
  refine ⟨del n k u E, (insert D.gates.length T).image (sg k), del_mono n k u E hEM,
    del_readsBack n k u E hER huk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg'
    obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g' hj
    have hne : (if j < k then j else j + 1) ≠ k := by split_ifs <;> omega
    simp only [rd, List.length_map]
    set j' := (if j < k then j else j + 1) with hj'
    rcases Nat.lt_trichotomy j' D.gates.length with h1 | h1 | h1
    · rw [hEget j' hne h1] at hg0
      exact hL2 g0 (List.mem_of_getElem? hg0)
    · rw [h1, hEN] at hg0
      cases hg0
      rfl
    · rw [List.getElem?_eq_none (by omega)] at hg0
      cases hg0
  · have := del_length n k u E (by omega)
    omega
  · rw [del_fun n k u E (by omega) huk (readsBack_take n E hER k) hcopy, hEf]
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · exact ⟨_, del_get n k u E _ _ (by omega) hEN, rfl⟩
    · obtain ⟨g', hg', hor'⟩ := hA j hj
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      rw [← hEget j hjk (hTlt j hj)] at hg'
      exact ⟨_, del_get n k u E _ _ hjk hg', hor'⟩
  · intro j' hj'
    simp only [Finset.mem_image, Finset.mem_insert] at hj'
    obtain ⟨j, hj, rfl⟩ := hj'
    rcases hj with rfl | hj
    · left
      simp only [del, hE]
      exact sig_gate n k u _ (by omega)
    · right
      have hjk : j ≠ k := fun h => hkT (h ▸ hj)
      have hread : ∃ k'' ∈ insert D.gates.length T, k'' ≠ k ∧ ∃ g' : Gate, E.gates[k'']? = some g' ∧
          n + j ∈ g'.inputs := by
        rcases hB j hj with h | ⟨k', hk', g', hg', hin⟩
        · exact ⟨D.gates.length, Finset.mem_insert_self _ _, by omega, _, hEN, by simp [h]⟩
        · have hk'k : k' ≠ k := fun h => hkT (h ▸ hk')
          rw [← hEget k' hk'k (hTlt k' hk')] at hg'
          exact ⟨k', Finset.mem_insert_of_mem hk', hk'k, g', hg', hin⟩
      obtain ⟨k'', hk'', hk''k, g', hg', hin⟩ := hread
      refine ⟨sg k k'', Finset.mem_image_of_mem _ hk'', _, del_get n k u E _ _ hk''k hg', ?_⟩
      simp only [rd, List.mem_map]
      exact ⟨n + j, hin, sig_gate n k u j hjk⟩
  · have hNT : D.gates.length ∉ T := fun h => by have := hTlt D.gates.length h; omega
    rw [Finset.card_image_of_injOn (sg_injOn k _ (by
      simp only [Finset.mem_insert, not_or]
      exact ⟨by omega, hkT⟩)), Finset.card_insert_of_notMem hNT]

theorem mono_of_AO2 (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) : Monotone2 D := by
  intro g hg
  refine ⟨?_, by rw [h.2.2 g hg]⟩
  rcases h.1 g hg with h1 | h1 <;> simp [h1]

theorem AO2_of (n : ℕ) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hL : ∀ g ∈ D.gates, g.inputs.length = 2) : PEqualNP.TopForm.IsAO2 n D := by
  refine ⟨fun g hg => ?_, hR, hL⟩
  have := (hM g hg).1
  simpa using this

theorem main_AO (n : ℕ) : ∀ m (D : Circuit) (T : Finset ℕ), 2 * D.gates.length - T.card = m →
    PEqualNP.TopForm.IsAO2 n D → PA D T → PB n D T →
    ∃ D' : Circuit, PEqualNP.TopForm.IsAO2 n D' ∧ D'.gates.length = D.gates.length ∧
      circuitFun n D' = circuitFun n D ∧ ∃ T' : Finset ℕ, PA D' T' ∧ PB n D' T' ∧ PC n D' T' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D T hm hAO hA hB
  by_cases hC : PC n D T
  · exact ⟨D, hAO, rfl, rfl, T, hA, hB, hC⟩
  · unfold PC at hC
    push Not at hC
    obtain ⟨k, g, hkg, hor, t, ht, hsat, himp, hkT⟩ := hC
    obtain ⟨D1, T1, hM1, hR1, hL1, hl1, hf1, hA1, hB1, hc1⟩ :=
      lift_step_AO n D T (mono_of_AO2 n D hAO) hAO.2.1 hAO.2.2 hA hB k g hkg hor t ht hsat
        himp hkT
    have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
    have hTc : T.card ≤ D.gates.length := by
      have hsub : T ⊆ Finset.range D.gates.length := fun j hj => by
        obtain ⟨g', hg', _⟩ := hA j hj
        simpa using (List.getElem?_eq_some_iff.mp hg').1
      simpa using Finset.card_le_card hsub
    obtain ⟨D', hAO', hs', hf', T', hT'⟩ :=
      ih (2 * D1.gates.length - T1.card) (by omega) D1 T1 rfl (AO2_of n D1 hM1 hR1 hL1) hA1 hB1
    exact ⟨D', hAO', hs'.trans hl1, hf'.trans hf1, T', hT'⟩

end PEqualNP.MetaComplexity.LiftFix
