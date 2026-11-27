import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3100
open PEqualNP.CircuitLowerBounds

def assignment (i : Fin 4) (v : Fin 9) : Bool :=
  decide (v.val = i.val ∨ v.val = i.val + 5)

def sample (i : Fin 4) : List Bool :=
  List.ofFn (assignment i) ++ [assignment i 0 || assignment i 4]

def zero : List Bool := List.replicate 10 false

theorem sample_len (i : Fin 4) : (sample i).length = 10 := by
  simp [sample]

theorem zero_len : zero.length = 10 := rfl

theorem zero_get (k : ℕ) : zero.getD k false = false := by
  by_cases hk : k < 10
  · interval_cases k <;> rfl
  · apply List.getD_eq_default
    rw [zero_len]
    omega

theorem sample_disjoint (i j : Fin 4) (h : i ≠ j) (k : ℕ) :
    ¬ ((sample i).getD k false = true ∧ (sample j).getD k false = true) := by
  by_cases hk : k < 10
  · have hf : ∀ a b : Fin 4, a ≠ b → ∀ w : Fin 10,
        ¬ ((sample a).getD w.val false = true ∧ (sample b).getD w.val false = true) := by
      decide
    exact hf i j h ⟨k,hk⟩
  · have he : (sample i).getD k false = false :=
      List.getD_eq_default _ _ (by rw [sample_len]; omega)
    intro hh
    rw [he] at hh
    exact Bool.noConfusion hh.1

theorem impossible (C : Circuit) (S : Finset ℕ) (hcard : S.card ≤ 3)
    (hzero : C.eval zero = false) (hpos : ∀ i : Fin 4, C.eval (sample i) = true)
    (hdep : ∀ i : Fin 4, (∀ k ∈ S, (sample i).getD k false = false) →
      C.eval (sample i) = C.eval zero) : False := by
  classical
  have hit : ∀ i : Fin 4, ∃ k ∈ S, (sample i).getD k false = true := by
    intro i
    by_contra h
    have hs : ∀ k ∈ S, (sample i).getD k false = false := by
      intro k hk
      cases hv : (sample i).getD k false with
      | false => rfl
      | true => exact False.elim (h ⟨k,hk,hv⟩)
    have he := hdep i hs
    rw [hpos i, hzero] at he
    exact Bool.noConfusion he
  let f : Fin 4 → ℕ := fun i => Classical.choose (hit i)
  have hf : ∀ i, f i ∈ S ∧ (sample i).getD (f i) false = true :=
    fun i => Classical.choose_spec (hit i)
  have hle : (Finset.univ : Finset (Fin 4)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn f
    · intro i _
      exact Finset.mem_coe.mpr (hf i).1
    · intro i _ j _ he
      by_contra hne
      apply sample_disjoint i j hne (f i)
      refine ⟨(hf i).2, ?_⟩
      rw [he]
      exact (hf j).2
  simp at hle
  omega

-- The following list facts also occur in the checked proof of L-meta-1624.
theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) :
    (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem snoc_congr (xs ys : List Bool) (v : Bool) (o : ℕ)
    (hlen : xs.length = ys.length) (hv : xs.getD o false = ys.getD o false) :
    (xs ++ [v]).getD o false = (ys ++ [v]).getD o false := by
  by_cases h : o < xs.length
  · rw [getD_snoc_lt xs v o h, getD_snoc_lt ys v o (by omega)]
    exact hv
  · by_cases he : o = xs.length
    · have he' : o = ys.length := he.trans hlen
      calc
        _ = v := by simpa only [he] using getD_snoc_eq xs v
        _ = _ := by simpa only [he'] using (getD_snoc_eq ys v).symm
    · rw [getD_snoc_gt xs v o (by omega), getD_snoc_gt ys v o (by omega)]

theorem one_dep (g : Gate) (o : ℕ) (i : Fin 4)
    (h : ∀ k ∈ (o :: g.inputs).toFinset, (sample i).getD k false = false) :
    (⟨[g],o⟩ : Circuit).eval (sample i) = (⟨[g],o⟩ : Circuit).eval zero := by
  have hm : g.inputs.map (fun k => (sample i).getD k false) =
      g.inputs.map (fun k => zero.getD k false) := by
    apply List.map_congr_left
    intro k hk
    rw [zero_get]
    exact h k (by simp [hk])
  change ((sample i) ++ [g.op.eval (g.inputs.map fun k => (sample i).getD k false)]).getD o false =
      (zero ++ [g.op.eval (g.inputs.map fun k => zero.getD k false)]).getD o false
  rw [hm]
  apply snoc_congr
  · rw [sample_len,zero_len]
  · rw [zero_get]
    exact h o (by simp)

end PEqualNP.Outside.L_meta_3100

theorem PEqualNP.Outside.L_meta_3100 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) x3) → (¬∃ (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x4) → (15 : ℕ) ≤ x1.size := by
  intro C hm hf hn
  have hzero : C.eval PEqualNP.Outside.L_meta_3100.zero = false :=
    hf (fun _ => false)
  have hpos : ∀ i : Fin 4, C.eval (PEqualNP.Outside.L_meta_3100.sample i) = true := by
    intro i
    fin_cases i <;> exact hf (PEqualNP.Outside.L_meta_3100.assignment _)
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil =>
    exfalso
    apply PEqualNP.Outside.L_meta_3100.impossible ⟨[],o⟩ {o} (by simp) hzero hpos
    intro i hi
    change (PEqualNP.Outside.L_meta_3100.sample i).getD o false =
      PEqualNP.Outside.L_meta_3100.zero.getD o false
    rw [PEqualNP.Outside.L_meta_3100.zero_get]
    exact hi o (by simp)
  | cons g gs =>
    cases gs with
    | nil =>
      exfalso
      have hg : g.inputs.length ≤ 2 := (hm g (by simp)).2
      have hs : ((o :: g.inputs).toFinset).card ≤ 3 := by
        calc
          _ ≤ (o :: g.inputs).length := List.toFinset_card_le _
          _ ≤ 3 := by simp; omega
      exact PEqualNP.Outside.L_meta_3100.impossible ⟨[g],o⟩ (o :: g.inputs).toFinset hs
        hzero hpos (fun i hi => PEqualNP.Outside.L_meta_3100.one_dep g o i hi)
    | cons g' gs =>
      exact False.elim (hn ⟨g',rfl⟩)
