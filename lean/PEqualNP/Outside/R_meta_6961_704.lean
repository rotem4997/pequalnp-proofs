import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each empty rectangle has at most three points or at most three lines.
-- Test the maximal extension of each small side, and the individual flags.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6961_704
    (geometry : let U : Finset (Fin 13) := Finset.univ
      let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l + d
      ∀ S : Finset (Fin 13), S.card = 4 →
        (U.filter fun l : Fin 13 => ∀ p ∈ S, ¬ I p l).card ≤ 3)
    (search :
      let U : Finset (Fin 13) := Finset.univ
      let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l + d
      let row := fun (P L : Finset (Fin 13)) => Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ p l, I p l → circuitFun 26 C (row {p} {l}) = true) ∧
        (∀ P : Finset (Fin 13), P.card ≤ 3 → circuitFun 26 C
          (row P (U.filter fun l => ∀ p ∈ P, ¬ I p l)) = false) ∧
        (∀ L : Finset (Fin 13), L.card ≤ 3 → circuitFun 26 C
          (row (U.filter fun p => ∀ l ∈ L, ¬ I p l) L) = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (63 : ℕ) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x2 = Decidable.decide (∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (∃ x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x3 = x4 + x5) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := by
  let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l + d
  let row := fun (P L : Finset (Fin 13)) => Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
  obtain ⟨C, hm, hs, yes, noP, noL⟩ := search
  -- Wire monotonicity follows the gate induction used in L-meta-10586.
  let W (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
      W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
    simp [W, List.foldl_append]
  have W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [W]
    | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
  have getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
      (l ++ [a]).getD t d =
        if t < l.length then l.getD t d else if t = l.length then a else d := by
    simp only [List.getD_eq_getElem?_getD]
    by_cases h1 : t < l.length
    · rw [ite_eq_left h1, List.getElem?_append_left h1]
    · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
      by_cases h2 : t = l.length
      · subst h2; simp
      · rw [ite_eq_right h2]
        have : t - l.length ≠ 0 := by omega
        simp [this]
  let Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true
  have eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
      (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
      (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
    rcases hg with hg | hg <;> rw [hg] at he ⊢
    · change List.all _ id = true at he ⊢
      simp at he ⊢
      intro i hi; exact h i hi (he i hi)
    · change List.any _ id = true at he ⊢
      simp at he ⊢
      obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩
  have W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
    induction gs using List.reverseRecOn with
    | nil => simpa [W] using hxy
    | append_singleton gs g ih =>
      have ih := ih (fun g' hg' => hm g' (by simp [hg']))
      intro t ht
      have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
      rw [W_snoc, getD_snoc] at ht ⊢
      rw [← hlen]
      by_cases h1 : t < (W gs x).length
      · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
      · rw [ite_eq_right h1] at ht ⊢
        by_cases h2 : t = (W gs x).length
        · rw [ite_eq_left h2] at ht ⊢
          exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
        · rw [ite_eq_right h2] at ht; simp at ht
  have ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
      (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases h : k < n <;> simp [h]
  have mono : Monotone (circuitFun 26 C) := by
    intro x y xy
    apply Bool.le_iff_imp.mpr
    apply W_mono C.gates (fun g hg => (hm g hg).1) (List.ofFn x) (List.ofFn y) (by simp) _ C.output
    intro i h
    rw [ofFn_getD] at h ⊢
    split at h <;> rename_i hi
    · rw [dite_eq_left hi]
      exact Bool.le_iff_imp.mp (xy _) h
    · rw [dite_eq_right hi]
      exact h
  have row_le {P Q L K : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ K) :
      row P L ≤ row Q K := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      simp only [row,Fin.append_left,Bool.le_iff_imp,decide_eq_true_eq]
      exact fun h => hp h
    · intro l
      simp only [row,Fin.append_right,Bool.le_iff_imp,decide_eq_true_eq]
      exact fun h => hl h
  refine ⟨C,hm,hs,?_⟩
  intro x
  let P := Finset.univ.filter fun p : Fin 13 => x (Fin.castAdd 13 p) = true
  let L := Finset.univ.filter fun l : Fin 13 => x (Fin.natAdd 13 l) = true
  have rowEq : row P L = x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [row,P]
    · intro j
      change Fin.append _ _ (Fin.natAdd 13 j) = _
      rw [Fin.append_right]
      simp [L]
  change circuitFun 26 C x = decide (∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  by_cases e : ∃ p l : Fin 13, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  · rw [decide_eq_true e]
    obtain ⟨p,l,hi,hp,hl⟩ := e
    have le := mono (row_le (P := {p}) (L := {l}) (Q := P) (K := L)
      (by simpa [P] using hp) (by simpa [L] using hl))
    rw [rowEq,yes p l hi] at le
    exact Bool.eq_true_of_true_le le
  · rw [decide_eq_false e]
    have dis (p) (hp : p ∈ P) (l) (hl : l ∈ L) : ¬ I p l := by
      intro hit
      exact e ⟨p,l,hit,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
    by_cases small : P.card ≤ 3
    · have sub : L ⊆ Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l) := by
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => dis p hp l hl⟩
      have le := mono (row_le (Finset.Subset.refl P) sub)
      rw [rowEq,noP P small] at le
      exact le_antisymm le (Bool.false_le _)
    · obtain ⟨S,sub,card⟩ := Finset.exists_subset_card_eq (show 4 ≤ P.card by omega)
      have smallL : L.card ≤ 3 := by
        apply le_trans (Finset.card_le_card (t := Finset.univ.filter fun l => ∀ p ∈ S, ¬ I p l) ?_)
          (geometry S card)
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => dis p (sub hp) l hl⟩
      have subP : P ⊆ Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l) := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis p hp⟩
      have le := mono (row_le subP (Finset.Subset.refl L))
      rw [rowEq,noL L smallL] at le
      exact le_antisymm le (Bool.false_le _)
