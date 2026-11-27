import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8615

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem snoc_ne (w : List Bool) (v : Bool) (i : Nat) (hi : i ≠ w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  rcases Nat.lt_or_ge i w.length with h | h
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h]

theorem snoc_at (w : List Bool) (v : Bool) :
    (w ++ [v]).getD w.length false = v := by simp

def Agree (S : Finset Nat) (x y : List Bool) : Prop :=
  ∀ i ∈ S, x.getD i false = y.getD i false

theorem support (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (n : Nat) (S : Finset Nat) :
    ∃ A : Finset Nat, A.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n → Agree A x y →
        Agree S (run gs x) (run gs y) := by
  induction gs generalizing n S with
  | nil => exact ⟨S, by simp, fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨B, hB, hrun⟩ := ih (fun h hh => hgs h (List.mem_cons_of_mem _ hh)) (n+1) S
    have hg : g.inputs.toFinset.card ≤ 2 :=
      (List.toFinset_card_le _).trans (hgs g (by simp))
    by_cases hn : n ∈ B
    · refine ⟨B.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
      · have hc := Finset.card_union_le (B.erase n) g.inputs.toFinset
        have he := Finset.card_erase_add_one hn
        simp only [List.length_cons]
        omega
      · intro x y hx hy h
        have hv : (g.inputs.map fun i => x.getD i false) =
            (g.inputs.map fun i => y.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
        apply hrun _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        by_cases e : i = n
        · subst i
          change (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD n false =
            (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD n false
          have hread (w : List Bool) (hw : w.length = n) (v : Bool) :
              (w ++ [v]).getD n false = v := by
            rw [← hw, snoc_at]
          rw [hread _ hx, hread _ hy, hv]
        · rw [snoc_ne _ _ _ (by simpa [hx]), snoc_ne _ _ _ (by simpa [hy])]
          exact h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hi⟩))
    · refine ⟨B, by simp only [List.length_cons]; omega, ?_⟩
      intro x y hx hy h
      apply hrun _ _ (by simp [hx]) (by simp [hy])
      intro i hi
      have e : i ≠ n := fun he => hn (he ▸ hi)
      rw [snoc_ne _ _ _ (by simpa [hx]), snoc_ne _ _ _ (by simpa [hy])]
      exact h i hi

def table (T : Nat) (x : Fin 5 → Bool) : Bool :=
  T.testBit (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)

def row (m : Nat) (i : Fin 5) : Bool := m.testBit i.val

theorem row_all (x : Fin 5 → Bool) :
    row (⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x⟩ : Fin 32).val = x := by
  funext i
  exact Nat.testBit_ofBits_lt x i.val i.isLt

theorem row_read (m j : Nat) (h : j < 5) :
    (List.ofFn (row m)).getD j false = row m ⟨j,h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

def Essential (T k : Nat) : Prop :=
  ∀ i : Fin k, ∃ m : Fin 32,
    let q := m.val ^^^ 2 ^ i.val
    table T (row m.val) ≠ table T (row q) ∧
      ∀ j : Fin 5, j.val ≠ i.val → row m.val j = row q j

theorem size_bound {T k s : Nat} (ess : Essential T k)
    (h : HasCircuitSize 5 (table T) s) : k ≤ s + 1 := by
  obtain ⟨C, hC, hs, heval⟩ := h
  obtain ⟨A, hA, ha⟩ := support C.gates (fun g hg => (hC g hg).2) 5 {C.output}
  have incl : Finset.range k ⊆ A := by
    intro i hi
    by_contra hni
    obtain ⟨m, hm, hsame⟩ := ess ⟨i, Finset.mem_range.mp hi⟩
    let q := m.val ^^^ 2 ^ i
    have agree : Agree A (List.ofFn (row m.val)) (List.ofFn (row q)) := by
      intro j hj
      by_cases hlt : j < 5
      · rw [row_read _ _ hlt, row_read _ _ hlt]
        exact hsame ⟨j,hlt⟩ (by
          intro hji
          change j = i at hji
          exact hni (hji ▸ hj))
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have equal := ha _ _ (by simp) (by simp) agree C.output (by simp)
    change C.eval (List.ofFn (row m.val)) = C.eval (List.ofFn (row q)) at equal
    exact hm ((heval _).symm.trans (equal.trans (heval _)))
  have hh := Finset.card_le_card incl
  simp only [Finset.card_range, Finset.card_singleton] at hh hA
  change C.gates.length ≤ s at hs
  omega

def mchk (gs : List Gate) : Bool :=
  gs.all (fun g => (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length ≤ 2))

theorem mchk_spec (C : Circuit) (h : mchk C.gates = true) : Monotone2 C := by
  intro g hg
  simp only [mchk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all

theorem solve {T k s : Nat} (D : Circuit) (hsz : D.size ≤ k - 1)
    (hm : mchk D.gates = true) (he : Essential T k)
    (hd : ∀ m : Fin 32, D.eval (List.ofFn (row m.val)) = table T (row m.val))
    (h : HasCircuitSize 5 (table T) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = table T x := by
  refine ⟨D, mchk_spec D hm, ?_, ?_⟩
  · have := size_bound he h
    omega
  · intro x
    simpa only [row_all x] using hd ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x⟩

def witness0 : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [5, 6]⟩], 7⟩

theorem essential0 : Essential 0x88808880 4 := by
  unfold Essential
  decide +kernel

theorem correct0 : ∀ m : Fin 32,
    witness0.eval (List.ofFn (row m.val)) = table 0x88808880 (row m.val) := by
  decide +kernel

def witness1 : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩], 7⟩

theorem essential1 : Essential 0xa888a888 4 := by
  unfold Essential
  decide +kernel

theorem correct1 : ∀ m : Fin 32,
    witness1.eval (List.ofFn (row m.val)) = table 0xa888a888 (row m.val) := by
  decide +kernel

def witness2 : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩], 7⟩

theorem essential2 : Essential 0xaaa8aaa8 4 := by
  unfold Essential
  decide +kernel

theorem correct2 : ∀ m : Fin 32,
    witness2.eval (List.ofFn (row m.val)) = table 0xaaa8aaa8 (row m.val) := by
  decide +kernel

def witness3 : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 6]⟩], 7⟩

theorem essential3 : Essential 0xeaaaeaaa 4 := by
  unfold Essential
  decide +kernel

theorem correct3 : ∀ m : Fin 32,
    witness3.eval (List.ofFn (row m.val)) = table 0xeaaaeaaa (row m.val) := by
  decide +kernel

def witness4 : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

theorem essential4 : Essential 0xeac0eac0 4 := by
  unfold Essential
  decide +kernel

theorem correct4 : ∀ m : Fin 32,
    witness4.eval (List.ofFn (row m.val)) = table 0xeac0eac0 (row m.val) := by
  decide +kernel

def witness5 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩], 7⟩

theorem essential5 : Essential 0xeee0eee0 4 := by
  unfold Essential
  decide +kernel

theorem correct5 : ∀ m : Fin 32,
    witness5.eval (List.ofFn (row m.val)) = table 0xeee0eee0 (row m.val) := by
  decide +kernel

def witness6 : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 6]⟩], 7⟩

theorem essential6 : Essential 0xeeeaeeea 4 := by
  unfold Essential
  decide +kernel

theorem correct6 : ∀ m : Fin 32,
    witness6.eval (List.ofFn (row m.val)) = table 0xeeeaeeea (row m.val) := by
  decide +kernel

def witness7 : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩], 7⟩

theorem essential7 : Essential 0xfeeefeee 4 := by
  unfold Essential
  decide +kernel

theorem correct7 : ∀ m : Fin 32,
    witness7.eval (List.ofFn (row m.val)) = table 0xfeeefeee (row m.val) := by
  decide +kernel

def witness8 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

theorem essential8 : Essential 0xfffefffe 4 := by
  unfold Essential
  decide +kernel

theorem correct8 : ∀ m : Fin 32,
    witness8.eval (List.ofFn (row m.val)) = table 0xfffefffe (row m.val) := by
  decide +kernel

def witness9 : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [4, 7]⟩], 8⟩

theorem essential9 : Essential 0x80000000 5 := by
  unfold Essential
  decide +kernel

theorem correct9 : ∀ m : Fin 32,
    witness9.eval (List.ofFn (row m.val)) = table 0x80000000 (row m.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_8615

theorem PEqualNP.Outside.L_meta_8615 : ∀ T ∈ ({0x88808880, 0xa888a888, 0xaaa8aaa8, 0xeaaaeaaa, 0xeac0eac0, 0xeee0eee0, 0xeeeaeeea, 0xfeeefeee, 0xfffefffe, 0x80000000} : Finset ℕ), ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  open PEqualNP.Outside.L_meta_8615 in
  intro T hT s h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact solve witness0 (by decide) (by decide) essential0 correct0 h
  · exact solve witness1 (by decide) (by decide) essential1 correct1 h
  · exact solve witness2 (by decide) (by decide) essential2 correct2 h
  · exact solve witness3 (by decide) (by decide) essential3 correct3 h
  · exact solve witness4 (by decide) (by decide) essential4 correct4 h
  · exact solve witness5 (by decide) (by decide) essential5 correct5 h
  · exact solve witness6 (by decide) (by decide) essential6 correct6 h
  · exact solve witness7 (by decide) (by decide) essential7 correct7 h
  · exact solve witness8 (by decide) (by decide) essential8 correct8 h
  · exact solve witness9 (by decide) (by decide) essential9 correct9 h
