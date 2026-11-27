import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18407
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def cov (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
  ∀ j, a.getD j false = true → b.getD j false = true ∨ c.getD j false = true

lemma add_end (s : List Bool) (x : Bool) (i : Nat) :
    (s ++ [x]).getD i false = if i = s.length then x else s.getD i false := by
  by_cases hi : i < s.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
  · by_cases he : i = s.length
    · subst i; simp
    · have h1 : s.length ≤ i := by omega
      have h2 : (s ++ [x]).length ≤ i := by simp; omega
      rw [ite_eq_right he, List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

lemma cover_step (a b c : List Bool) (g : Gate) (ho : g.op = .or) (h : cov a b c) :
    cov (step a g) (step b g) (step c g) := by
  obtain ⟨hAB,hAC,h⟩ := h
  refine ⟨by simp [step,hAB],by simp [step,hAC],?_⟩
  intro j hj
  unfold step at hj ⊢
  rw [add_end] at hj
  rw [add_end,add_end,← hAB,← hAC]
  by_cases hh : j = a.length
  · simp only [ite_eq_left hh, ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hj ⊢
    obtain ⟨_,⟨i,hi,rfl⟩,hA⟩ := hj
    rcases h i hA with hB|hC
    · exact Or.inl ⟨_,⟨i,hi,rfl⟩,hB⟩
    · exact Or.inr ⟨_,⟨i,hi,rfl⟩,hC⟩
  · simp only [ite_eq_right hh] at hj ⊢
    exact h j hj

lemma cover_fold (gs : List Gate) (h : ∀ g ∈ gs,g.op = .or)
    (a b c : List Bool) (hh : cov a b c) :
    cov (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact hh
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) _ _ _ (cover_step a b c g (h g List.mem_cons_self) hh)

def inc (p l : Fin 13) : Prop := p-l=0 ∨ p-l=1 ∨ p-l=3 ∨ p-l=9
instance (p l : Fin 13) : Decidable (inc p l) := by unfold inc; infer_instance
def Q₁ : Finset (Fin 13) := {0,1,2,5}
def Q₂ : Finset (Fin 13) := {2,4,5,6}
def qr (q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (i ∈ q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ q, ¬inc p l)
def e : List Bool := (List.ofFn fun i : Fin 13 => decide (i=0)) ++
  List.ofFn fun l : Fin 13 => decide (l=0)

lemma small_cover : cov e (qr Q₁) (qr Q₂) := by
  refine ⟨by simp [e,qr],by simp [e,qr],?_⟩
  have h : ∀ i : Fin 26, e.getD i.val false = true →
      (qr Q₁).getD i.val false = true ∨ (qr Q₂).getD i.val false = true := by decide
  intro i hi
  by_cases hn : i<26
  · exact h ⟨i,hn⟩ hi
  · rw [List.getD_eq_default] at hi
    · contradiction
    · simp [e]; omega

end PEqualNP.Outside.L_meta_18407

open PEqualNP.Outside.L_meta_18407 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_18407 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) → (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x6, ¬(x10 - x9 = (0 : Fin (13 : ℕ)) ∨ x10 - x9 = (1 : Fin (13 : ℕ)) ∨ x10 - x9 = (3 : Fin (13 : ℕ)) ∨ x10 - x9 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C hm ha _ hp hq
  have hor (g : Gate) (hg : g ∈ C.gates) : g.op = .or := by
    have hh : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
    rcases hh with eh|eh
    · obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      exact False.elim (ha ⟨⟨j,hj⟩,eh⟩)
    · exact eh
  have he : C.eval e = true := hp 0 0 (Or.inl rfl)
  have h₁ : C.eval (qr Q₁) = false := hq Q₁ (by decide) (by decide)
  have h₂ : C.eval (qr Q₂) = false := hq Q₂ (by decide) (by decide)
  have h := (cover_fold C.gates hor e (qr Q₁) (qr Q₂) small_cover).2.2 C.output
  change C.eval e = true → C.eval (qr Q₁) = true ∨ C.eval (qr Q₂) = true at h
  simp [he,h₁,h₂] at h
