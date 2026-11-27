import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4045_1
    (wireFamilies : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ j (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j) →
      let trim := fun A : Finset (Finset (Fin n)) => A.filter fun S => ∀ T ∈ A, T ⊆ S → S ⊆ T
      ∃ A : ℕ → Finset (Finset (Fin n)),
        (∀ i : Fin n, A i.val = {{i}}) ∧
        (∀ (x : Fin n → Bool) w, (C.wires (List.ofFn x)).getD w false = true ↔
          ∃ T ∈ A w, ∀ i ∈ T, x i = true) ∧
        ∀ j < C.size, ∃ a < n+j, ∃ b < n+j, a ≠ b ∧
          (A (n+j) = trim (A a ∪ A b) ∨ A (n+j) = trim (((A a) ×ˢ (A b)).image fun p => p.1∪p.2)))
    (deletedSupports :
      let trim := fun A : Finset (Finset (Fin 26)) => A.filter fun S => ∀ T ∈ A, T ⊆ S → S ⊆ T
      let I := (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun p =>
        p.1 = p.2 ∨ p.1 = p.2+1 ∨ p.1 = p.2+3 ∨ p.1 = p.2+9
      let E := I.image fun p : Fin 13 × Fin 13 => ({Fin.castAdd 13 p.1,Fin.natAdd 13 p.2} : Finset (Fin 26))
      ∀ (m o : ℕ) (A : ℕ → Finset (Finset (Fin 26))), m ≤ 62 → o < 26+m →
        (∀ i : Fin 26, A i.val = {{i}}) →
        (∀ j < m, ∃ a < 26+j, ∃ b < 26+j, a ≠ b ∧
          (A (26+j) = trim (A a ∪ A b) ∨ A (26+j) = trim (((A a) ×ˢ (A b)).image fun p => p.1∪p.2))) →
        (∀ S ∈ A o, ∃ e ∈ E, e ⊆ S) → (∀ e ∈ E, ∃ S ∈ A o, S ⊆ e) →
        ∃ v : Fin 26, let s := fun k => (A k).filter (fun T => v ∉ T)
                      ((Finset.range (26+m)).image s).card + 5 ≤ ((Finset.range 26).image s).card + m) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  intro C W legal budget values computes
  obtain ⟨A,inputs,wire,gate⟩ := wireFamilies 26 C legal
  let I := (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun p =>
    p.1 = p.2 ∨ p.1 = p.2+1 ∨ p.1 = p.2+3 ∨ p.1 = p.2+9
  let E := I.image fun p : Fin 13 × Fin 13 => ({Fin.castAdd 13 p.1, Fin.natAdd 13 p.2} : Finset (Fin 26))
  have mark (T : Finset (Fin 26)) :
      W (fun i => decide (i∈T)) C.output = true ↔ ∃ e ∈ E, e ⊆ T := by
    rw [computes]
    constructor
    · rintro ⟨a,b,he,ha,hb⟩
      refine ⟨{Fin.castAdd 13 a,Fin.natAdd 13 b}, Finset.mem_image.mpr
        ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩,?_⟩
      simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using
        And.intro (of_decide_eq_true ha) (of_decide_eq_true hb)
    · rintro ⟨_,mem,sub⟩
      obtain ⟨⟨a,b⟩,h,rfl⟩ := Finset.mem_image.mp mem
      exact ⟨a,b,(Finset.mem_filter.mp h).2,
        decide_eq_true (sub (by simp)),decide_eq_true (sub (by simp))⟩
  have signature (T : Finset (Fin 26)) (k : ℕ) :
      W (fun i => decide (i∈T)) k = true ↔ ∃ S ∈ A k, S ⊆ T := by
    rw [values,wire]
    simp only [decide_eq_true_eq]
    rfl
  have contains (S : Finset (Fin 26)) (h : S ∈ A C.output) : ∃ e ∈ E, e ⊆ S :=
    (mark S).mp ((signature S _).mpr ⟨S,h,Finset.Subset.rfl⟩)
  have included (e : Finset (Fin 26)) (h : e ∈ E) : ∃ S ∈ A C.output, S ⊆ e :=
    (signature e _).mp ((mark e).mpr ⟨e,h,Finset.Subset.rfl⟩)
  have goodOut : C.output < 26+C.size := by
    have existsEdge : E.Nonempty := by decide
    have yes := (mark Finset.univ).mpr ⟨_,existsEdge.choose_spec,Finset.subset_univ _⟩
    rw [values] at yes
    have len (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
        ((⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).length = x.length + gs.length := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        change ((⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (x ++ [_])).length = _
        rw [ih]; simp; omega
    by_contra! late
    rw [List.getD_eq_default _ _ (by
      change ((⟨C.gates,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires _).length ≤ _
      rw [len,List.length_ofFn]; exact late)] at yes
    contradiction
  obtain ⟨v,bound⟩ := deletedSupports C.size C.output A budget goodOut inputs gate contains included
  let s := fun k => (A k).filter (fun T => v ∉ T)
  let old := fun j => ∃ k < 26+j, s (26+j) = s k
  have counted (m : ℕ) : ((Finset.range (26+m)).image s).card +
      ((Finset.range m).filter old).card = ((Finset.range 26).image s).card + m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have seen : s (26+m) ∈ (Finset.range (26+m)).image s ↔ old m := by
        simp only [old,Finset.mem_image,Finset.mem_range]
        constructor <;> rintro ⟨k,lt,eq⟩ <;> exact ⟨k,lt,eq.symm⟩
      rw [show 26+(m+1) = (26+m)+1 by omega,Finset.range_add_one,Finset.image_insert,Finset.range_add_one]
      by_cases h : old m
      · rw [Finset.insert_eq_of_mem (seen.mpr h),Finset.filter_insert]
        simp only [ite_eq_left h,Finset.card_insert_of_notMem (by simp : m ∉ (Finset.range m).filter old)]
        omega
      · rw [Finset.card_insert_of_notMem (fun z => h (seen.mp z)),Finset.filter_insert]
        simp only [ite_eq_right h]; omega
  have count := counted C.size
  change ((Finset.range (26+C.size)).image s).card + 5 ≤ ((Finset.range 26).image s).card + C.size at bound
  refine ⟨v,(Finset.range C.size).filter old,by omega,?_⟩
  intro j mem
  obtain ⟨ltJ,k,ltK,eq⟩ := Finset.mem_filter.mp mem
  refine ⟨Finset.mem_range.mp ltJ,true,false,k,ltK,?_⟩
  intro x off
  simp only [Bool.true_and,Bool.or_false]
  apply Bool.eq_iff_iff.mpr
  have slice (a : ℕ) : W x a = true ↔ ∃ T ∈ s a, ∀ i ∈ T, x i = true := by
    rw [values,wire]
    constructor
    · rintro ⟨T,ht,yes⟩
      exact ⟨T,Finset.mem_filter.mpr ⟨ht,fun hv => Bool.noConfusion ((yes v hv).symm.trans off)⟩,yes⟩
    · rintro ⟨T,ht,yes⟩
      exact ⟨T,(Finset.mem_filter.mp ht).1,yes⟩
  rw [slice,slice,eq]
