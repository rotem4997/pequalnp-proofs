import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2982_aux

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl stepF w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (stepF w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [stepF]

theorem getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepF x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := pre gs x
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (gs.foldl stepF x).getD i false = false := by
  obtain ⟨t, ht, hl⟩ := pre gs x
  rw [ht]
  apply List.getD_eq_default
  simp
  omega

theorem gate_val (gs : List Gate) : ∀ (x : List Bool) (j : ℕ), j < gs.length →
    (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < x.length + j) →
    (gs.foldl stepF x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (gs.foldl stepF x).getD i false) := by
  induction gs with
  | nil => intro x j hj; simp at hj
  | cons g gs ih =>
    intro x j hj hr
    rcases j with _ | j
    · simp only [List.getD_cons_zero, List.foldl_cons] at hr ⊢
      obtain ⟨t, ht, _⟩ := pre gs (stepF x g)
      rw [ht]
      have e1 : (stepF x g ++ t).getD (x.length + 0) false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [stepF, List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hr i hi
      simp only [Nat.add_zero] at hi'
      simp [stepF, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
    · simp only [List.getD_cons_succ, List.foldl_cons, List.length_cons] at hr hj ⊢
      have hl : (stepF x g).length = x.length + 1 := by simp [stepF]
      have := ih (stepF x g) j (by omega) (by
        intro i hi
        have := hr i hi
        omega)
      rw [hl] at this
      rw [show x.length + (j + 1) = x.length + 1 + j by omega]
      exact this

theorem supp (gs : List Gate) (n : ℕ) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hr : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) :
    ∀ j, ∀ W : Finset ℕ, (∀ w ∈ W, w < n + j ∨ n + gs.length ≤ w) →
      ∃ S : Finset ℕ, S.card ≤ W.card + j ∧ (∀ s ∈ S, s < n) ∧
        ∀ x y : List Bool, x.length = n → y.length = n → (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ w ∈ W, (gs.foldl stepF x).getD w false = (gs.foldl stepF y).getD w false := by
  intro j
  induction j with
  | zero =>
    intro W hW
    refine ⟨W.filter (fun w => w < n), by simpa using Finset.card_filter_le W _, ?_, ?_⟩
    · intro s hs
      exact (Finset.mem_filter.mp hs).2
    · intro x y hx hy hS w hw
      rcases hW w hw with h1 | h1
      · rw [getD_lt gs x w (by omega), getD_lt gs y w (by omega)]
        exact hS w (Finset.mem_filter.mpr ⟨hw, by omega⟩)
      · rw [getD_ge gs x w (by omega), getD_ge gs y w (by omega)]
  | succ j ih =>
    intro W hW
    by_cases hc : j < gs.length ∧ n + j ∈ W
    · obtain ⟨hj, hjW⟩ := hc
      have hg : gs.getD j ⟨GateOp.or, []⟩ ∈ gs := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hlen := hfan _ hg
      obtain ⟨S, hSc, hSn, hSa⟩ := ih (W.erase (n + j) ∪ (gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset) (by
        intro w hw
        rcases Finset.mem_union.mp hw with h1 | h1
        · obtain ⟨h2, h3⟩ := Finset.mem_erase.mp h1
          rcases hW w h3 with h4 | h4
          · left; omega
          · right; exact h4
        · left
          exact hr j hj w (List.mem_toFinset.mp h1))
      refine ⟨S, ?_, hSn, ?_⟩
      · have c1 := Finset.card_union_le (W.erase (n + j)) (gs.getD j ⟨GateOp.or, []⟩).inputs.toFinset
        have c2 := Finset.card_erase_of_mem hjW
        have c3 := List.toFinset_card_le (gs.getD j ⟨GateOp.or, []⟩).inputs
        have c4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hjW⟩
        omega
      · intro x y hx hy hS w hw
        by_cases hwj : w = n + j
        · subst hwj
          have gx := gate_val gs x j hj (by rw [hx]; exact hr j hj)
          have gy := gate_val gs y j hj (by rw [hy]; exact hr j hj)
          rw [hx] at gx
          rw [hy] at gy
          rw [gx, gy]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hSa x y hx hy hS i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
        · exact hSa x y hx hy hS w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwj, hw⟩))
    · obtain ⟨S, hSc, hSn, hSa⟩ := ih W (by
        intro w hw
        rcases hW w hw with h1 | h1
        · by_cases h2 : w = n + j
          · subst h2
            right
            have : ¬ j < gs.length := fun h3 => hc ⟨h3, hw⟩
            omega
          · left; omega
        · right; exact h1)
      exact ⟨S, by omega, hSn, hSa⟩

theorem main (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hp : ∀ i : Fin n, ∃ q : Fin n → Bool, f (Function.update q i true) ≠ f (Function.update q i false))
    (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (h : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) : n ≤ C.size + 1 := by
  obtain ⟨S, hSc, hSn, hSa⟩ := supp C.gates n (fun g hg => (hM g hg).2)
    (by
      intro j hj i hi
      exact hR j hj i hi) C.gates.length {C.output} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      subst hw
      omega)
  by_contra hlt
  have hex : ∃ i, i < n ∧ i ∉ S := by
    by_contra hno
    push Not at hno
    have hsub : Finset.range n ⊆ S := by
      intro i hi
      exact hno i (Finset.mem_range.mp hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    simp [Circuit.size] at hSc hlt
    omega
  obtain ⟨i, hin, hiS⟩ := hex
  obtain ⟨q, hq⟩ := hp ⟨i, hin⟩
  apply hq
  rw [← h, ← h]
  simp only [Circuit.eval, wires_eq]
  apply hSa _ _ (by simp) (by simp) _ C.output (Finset.mem_singleton_self _)
  intro k hk
  have hkn := hSn k hk
  have hki : k ≠ i := fun e => hiS (e ▸ hk)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨i, hin⟩ := fun e => hki (Fin.mk.inj e)
  simp [hkn, Function.update_of_ne hne]

theorem updL (n m : ℕ) (a : Fin n → Bool) (b : Fin m → Bool) (p : Fin n) (v : Bool) :
    Function.update (Fin.append a b) (Fin.castAdd m p) v = Fin.append (Function.update a p v) b := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · by_cases e : k = p
    · subst e
      simp
    · have : Fin.castAdd m k ≠ Fin.castAdd m p := fun h => e (Fin.castAdd_injective _ _ h)
      simp [Function.update_of_ne this, Function.update_of_ne e]
  · have : Fin.natAdd n k ≠ Fin.castAdd m p := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Function.update_of_ne this]

theorem updR (n m : ℕ) (a : Fin n → Bool) (b : Fin m → Bool) (p : Fin m) (v : Bool) :
    Function.update (Fin.append a b) (Fin.natAdd n p) v = Fin.append a (Function.update b p v) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · have : Fin.castAdd m k ≠ Fin.natAdd n p := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Function.update_of_ne this]
  · by_cases e : k = p
    · subst e
      simp
    · have : Fin.natAdd n k ≠ Fin.natAdd n p := fun h => e (Fin.natAdd_injective _ _ h)
      simp [Function.update_of_ne this, Function.update_of_ne e]

theorem inc (n m : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    PEqualNP.GenericRejection.incidenceInput X Y =
      List.ofFn (Fin.append (fun p : Fin n => decide (p ∈ X)) (fun l : Fin m => decide (l ∈ Y))) := by
  rw [List.ofFn_fin_append]
  rfl

theorem updS (n : ℕ) (p : Fin n) (v : Bool) :
    Function.update (fun k : Fin n => decide (k ∈ (∅ : Finset (Fin n)))) p v =
      fun k : Fin n => decide (k ∈ (if v then ({p} : Finset (Fin n)) else ∅)) := by
  funext k
  by_cases e : k = p
  · subst e
    cases v <;> simp
  · cases v <;> simp [Function.update_of_ne e, e]

end PEqualNP.Outside.L_meta_2982_aux

theorem PEqualNP.Outside.L_meta_2982 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), (x2 x4).Nonempty) → (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x5 ∈ x2 x6) → PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 x9 : Finset (Fin x1)), x8.card + x9.card = (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 x9) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) := by
  intro x1 x2 x3 hne hcov hA hR hW
  obtain ⟨hao, hrb, hfan⟩ := hA
  refine PEqualNP.Outside.L_meta_2982_aux.main (x1 + x1) (fun x => x3.eval (List.ofFn x)) ?_ x3 ?_ hrb (fun _ => rfl)
  · intro i
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · obtain ⟨l, hl⟩ := hcov p
      refine ⟨Fin.append (fun k : Fin x1 => decide (k ∈ (∅ : Finset (Fin x1)))) (fun k : Fin x1 => decide (k ∈ ({l} : Finset (Fin x1)))), ?_⟩
      have h1 := hR l p hl
      have h2 := hW ∅ {l} (by simp)
      rw [PEqualNP.Outside.L_meta_2982_aux.inc] at h1 h2
      simp only [PEqualNP.Outside.L_meta_2982_aux.updL, PEqualNP.Outside.L_meta_2982_aux.updS]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [h1, h2]
      simp
    · obtain ⟨p, hp⟩ := hne l
      refine ⟨Fin.append (fun k : Fin x1 => decide (k ∈ ({p} : Finset (Fin x1)))) (fun k : Fin x1 => decide (k ∈ (∅ : Finset (Fin x1)))), ?_⟩
      have h1 := hR l p hp
      have h2 := hW {p} ∅ (by simp)
      rw [PEqualNP.Outside.L_meta_2982_aux.inc] at h1 h2
      simp only [PEqualNP.Outside.L_meta_2982_aux.updR, PEqualNP.Outside.L_meta_2982_aux.updS]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [h1, h2]
      simp
  · intro g hg
    refine ⟨?_, le_of_eq (hfan g hg)⟩
    rcases hao g hg with h | h <;> simp [h]
