import PEqualNP.MetaComplexity.L2604
import PEqualNP.MetaComplexity.Helpers.LiftFix

/-!
# Helpers for L-meta-2715: one lift step and the iteration

`lift_step`: an OR gate `k` outside a closed OR set `T` reading a satisfiable wire `t` that
implies the output is removed: gate `k` is set to `OR [u, t]`, the lift L2604 makes it `OR [u]`
and adds the output `OR [old output, t]`, and the copy `OR [u]` is deleted. Same size, same
function, and `T` (renamed) plus the new output is again closed, one larger. `main` iterates on
`2 * size - |T|`.
-/

namespace PEqualNP.MetaComplexity.LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Lift
open PEqualNP.MetaComplexity.NestedCover

/-- Every element of `T` is an OR gate of `D`. -/
def PA (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ j ∈ T, ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or

/-- Every element of `T` is the output or is read by a gate of `T`. -/
def PB (n : ℕ) (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ j ∈ T, D.output = n + j ∨ ∃ k ∈ T, ∃ g : Gate, D.gates[k]? = some g ∧ n + j ∈ g.inputs

/-- Every OR gate reading a satisfiable wire that implies the output lies in `T`. -/
def PC (n : ℕ) (D : Circuit) (T : Finset ℕ) : Prop :=
  ∀ (k : ℕ) (g : Gate), D.gates[k]? = some g → g.op = GateOp.or → ∀ t ∈ g.inputs,
    (∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true) →
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true → circuitFun n D x = true) →
    k ∈ T

theorem pick_u (g : Gate) (hor : g.op = GateOp.or) (hl : g.inputs.length ≤ 2) (t : ℕ)
    (ht : t ∈ g.inputs) : ∃ u ∈ g.inputs, ∀ w : List Bool,
      GateOp.or.eval ([u, t].map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only at hor hl ht ⊢
  subst hor
  match ins, hl, ht with
  | [], _, ht => simp at ht
  | [a], _, ht =>
    simp at ht; subst ht
    exact ⟨t, by simp, fun w => by simp [GateOp.eval]⟩
  | [a, b], _, ht =>
    simp at ht
    rcases ht with rfl | rfl
    · exact ⟨b, by simp, fun w => by simp [GateOp.eval, Bool.or_comm]⟩
    · exact ⟨a, by simp, fun w => by simp [GateOp.eval]⟩
  | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem sg_injOn (k : ℕ) (S : Finset ℕ) (hS : k ∉ S) : Set.InjOn (sg k) (S : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ≠ k := fun h => hS (h ▸ ha)
  have hb' : b ≠ k := fun h => hS (h ▸ hb)
  unfold sg at hab
  split_ifs at hab <;> omega

theorem lift_step (n : ℕ) (D : Circuit) (T : Finset ℕ) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hA : PA D T) (hB : PB n D T) (k : ℕ) (g : Gate) (hkg : D.gates[k]? = some g)
    (hor : g.op = GateOp.or) (t : ℕ) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true)
    (himp : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD t false = true →
      circuitFun n D x = true)
    (hkT : k ∉ T) :
    ∃ D1 : Circuit, ∃ T1 : Finset ℕ, Monotone2 D1 ∧ ReadsBack n D1 ∧
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
    del_readsBack n k u E hER huk, ?_, ?_, ?_, ?_, ?_⟩
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

theorem main (n : ℕ) : ∀ m (D : Circuit) (T : Finset ℕ), 2 * D.gates.length - T.card = m →
    Monotone2 D → ReadsBack n D → PA D T → PB n D T →
    ∃ D' : Circuit, Monotone2 D' ∧ ReadsBack n D' ∧ D'.size ≤ D.size ∧
      circuitFun n D' = circuitFun n D ∧ ∃ T' : Finset ℕ, PA D' T' ∧ PB n D' T' ∧ PC n D' T' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D T hm hM hR hA hB
  by_cases hC : PC n D T
  · exact ⟨D, hM, hR, le_rfl, rfl, T, hA, hB, hC⟩
  · unfold PC at hC
    push Not at hC
    obtain ⟨k, g, hkg, hor, t, ht, hsat, himp, hkT⟩ := hC
    obtain ⟨D1, T1, hM1, hR1, hl1, hf1, hA1, hB1, hc1⟩ :=
      lift_step n D T hM hR hA hB k g hkg hor t ht hsat himp hkT
    have hk : k < D.gates.length := (List.getElem?_eq_some_iff.mp hkg).1
    have hTc : T.card ≤ D.gates.length := by
      have hsub : T ⊆ Finset.range D.gates.length := fun j hj => by
        obtain ⟨g', hg', _⟩ := hA j hj
        simpa using (List.getElem?_eq_some_iff.mp hg').1
      simpa using Finset.card_le_card hsub
    obtain ⟨D', hM', hR', hs', hf', T', hT'⟩ :=
      ih (2 * D1.gates.length - T1.card) (by omega) D1 T1 rfl hM1 hR1 hA1 hB1
    refine ⟨D', hM', hR', ?_, hf'.trans hf1, T', hT'⟩
    simp only [Circuit.size] at hs' ⊢
    omega

end PEqualNP.MetaComplexity.LiftFix
