import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7596

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


theorem det : ∀ (gs : List Gate) (N : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ S : Finset ℕ, ∃ S' : Finset ℕ, S'.card ≤ S.card + gs.length ∧
    ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ S', x.getD w false = y.getD w false) → ∀ w ∈ S, (run gs x).getD w false = (run gs y).getD w false := by
  intro gs
  induction gs with
  | nil => intro N _ S; exact ⟨S, by simp, fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro N hg S
    obtain ⟨T, hT, hd⟩ := ih (N + 1) (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) S
    have step : ∀ x y : List Bool, x.length = N → y.length = N → (∀ w ∈ T, w ≠ N → x.getD w false = y.getD w false) →
        (N ∈ T → ∀ w ∈ g.inputs, x.getD w false = y.getD w false) → ∀ w ∈ S, (run (g :: gs) x).getD w false = (run (g :: gs) y).getD w false := by
      intro x y hx hy h1 h2
      refine hd (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hx]) (by simp [hy]) ?_
      intro w hw
      rcases Nat.lt_trichotomy w N with h | h | h
      · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
        exact h1 w hw (by omega)
      · subst h
        have e1 : (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
          rw [← hx]; exact getD_at _ _
        have e2 : (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD w false = g.op.eval (g.inputs.map fun i => y.getD i false) := by
          rw [← hy]; exact getD_at _ _
        rw [e1, e2, List.map_congr_left fun i hi => h2 hw i hi]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    by_cases hN : N ∈ T
    · refine ⟨T.erase N ∪ g.inputs.toFinset, ?_, fun x y hx hy h => step x y hx hy (fun w hw hne => h w ?_) (fun _ w hw => h w ?_)⟩
      · have e1 := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have e2 := Finset.card_erase_add_one hN
        have e3 := List.toFinset_card_le g.inputs
        have e4 := hg g List.mem_cons_self
        simp only [List.length_cons]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 hw)
    · refine ⟨T, by simp only [List.length_cons]; omega, fun x y hx hy h => step x y hx hy (fun w hw _ => h w hw) (fun h' => absurd h' hN)⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7596

theorem PEqualNP.Outside.L_meta_7596 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 × Fin x1)), (∀ x4 ∈ x2.gates, x4.inputs.length ≤ (2 : ℕ)) → (∀ (x5 : Fin (x1 + x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x6 : Fin (x1 + x1)) => Decidable.decide (x6 = x5)) = Bool.false) → (∀ x6 ∈ x3, (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x6.1 ∨ x8 = Fin.natAdd x1 x6.2)) = Bool.true) → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ x2.size + (1 : ℕ) := by
  intro n C E hC h1 h2
  classical
  obtain ⟨S, hS, hdet⟩ := PEqualNP.Outside.L_meta_7596.det C.gates (n + n) hC {C.output}
  have ess : ∀ (x y : Fin (n + n) → Bool) (i : Fin (n + n)), (∀ k, k ≠ i → x k = y k) → PEqualNP.MetaComplexity.circuitFun (n + n) C x ≠ PEqualNP.MetaComplexity.circuitFun (n + n) C y → (i : ℕ) ∈ S := by
    intro x y i hxy hne
    by_contra hi
    refine hne (hdet (List.ofFn x) (List.ofFn y) (by simp) (by simp) (fun w hw => ?_) C.output (by simp))
    by_cases hwn : w < n + n
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hwn, dif_pos hwn]
      rw [hxy ⟨w, hwn⟩ (by rintro rfl; exact hi hw)]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have ne1 : ∀ p l : Fin n, (Fin.castAdd n p : Fin (n + n)) ≠ Fin.natAdd n l := by
    intro p l h
    have := congrArg Fin.val h
    simp at this; omega
  have A : ((E.image Prod.fst).image fun p => ((Fin.castAdd n p : Fin (n + n)) : ℕ)) ∪ ((E.image Prod.snd).image fun l => ((Fin.natAdd n l : Fin (n + n)) : ℕ)) ⊆ S := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_image] at hw
    rcases hw with ⟨p, ⟨e, he, rfl⟩, rfl⟩ | ⟨l, ⟨e, he, rfl⟩, rfl⟩
    · refine ess (fun k => decide (k = Fin.natAdd n e.2)) (fun k => decide (k = Fin.castAdd n e.1 ∨ k = Fin.natAdd n e.2)) (Fin.castAdd n e.1) ?_ ?_
      · intro k hk
        simp [hk]
      · rw [h1 (Fin.natAdd n e.2), h2 e he]; simp
    · refine ess (fun k => decide (k = Fin.castAdd n e.1)) (fun k => decide (k = Fin.castAdd n e.1 ∨ k = Fin.natAdd n e.2)) (Fin.natAdd n e.2) ?_ ?_
      · intro k hk
        simp only [eq_false hk, or_false]
      · rw [h1 (Fin.castAdd n e.1), h2 e he]; simp
  have c := Finset.card_le_card A
  have c1 : ((E.image Prod.fst).image fun p => ((Fin.castAdd n p : Fin (n + n)) : ℕ)).card = (E.image Prod.fst).card :=
    Finset.card_image_of_injective _ fun a b h => Fin.ext h
  have c2 : ((E.image Prod.snd).image fun l => ((Fin.natAdd n l : Fin (n + n)) : ℕ)).card = (E.image Prod.snd).card :=
    Finset.card_image_of_injective _ fun a b h => by
      have h' : n + (a : ℕ) = n + (b : ℕ) := h
      exact Fin.ext (by omega)
  rw [Finset.card_union_of_disjoint, c1, c2] at c
  · have h3 : C.size = C.gates.length := rfl
    rw [Finset.card_singleton] at hS
    omega
  · refine Finset.disjoint_left.2 fun w h3 h4 => ?_
    simp only [Finset.mem_image] at h3 h4
    obtain ⟨p, _, rfl⟩ := h3
    obtain ⟨l, _, hl⟩ := h4
    have hl' : n + (l : ℕ) = (p : ℕ) := hl
    have := p.isLt
    omega
