import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612_aux

def Step (A : List ℕ) (w : ℕ) := ∃ a ∈ A, ∃ b ∈ A, w = a &&& b ∨ w = a ||| b

def Legal (A U : List ℕ) := ∀ i : Fin U.length, Step (A ++ U.take i.val) (U.get i)

private theorem step_mono {A B : List ℕ} {w} (sub : A ⊆ B) (ok : Step A w) : Step B w := by
  obtain ⟨a,ha,b,hb,op⟩ := ok
  exact ⟨a,sub ha,b,sub hb,op⟩

private theorem snoc_iff (A U : List ℕ) (w : ℕ) :
    Legal A (U ++ [w]) ↔ Legal A U ∧ Step (A ++ U) w := by
  constructor
  · intro h
    constructor
    · intro i
      have j : i.val < (U ++ [w]).length := by simp
      have hj := h ⟨i.val,j⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
        List.take_append_of_le_length (Nat.le_of_lt i.isLt)] using hj
    · have last : U.length < (U ++ [w]).length := by simp
      simpa [List.get_eq_getElem] using h ⟨U.length,last⟩
  · rintro ⟨ok,step⟩ i
    by_cases early : i.val < U.length
    · simpa only [List.get_eq_getElem,List.getElem_append_left early,
        List.take_append_of_le_length (Nat.le_of_lt early)] using ok ⟨_,early⟩
    · have h : i.val = U.length := by have := i.isLt; simp at this; omega
      simpa [List.get_eq_getElem,h] using step

private theorem extend (A W B V : List ℕ) (initial : B ⊆ A ++ W)
    (nodup : W.Nodup) (fresh : ∀ w ∈ W, w ∉ A) (valid : Legal A W) (alg : Legal B V) :
    ∃ U : List ℕ, U.length ≤ W.length + V.length ∧ U.Nodup ∧ (∀ w ∈ U, w ∉ A) ∧
      Legal A U ∧ B ++ V ⊆ A ++ U := by
  induction V using List.reverseRecOn with
  | nil => exact ⟨W,by simp,nodup,fresh,valid,by simpa using initial⟩
  | append_singleton V v ih =>
    obtain ⟨previous,step⟩ := (snoc_iff B V v).mp alg
    obtain ⟨U,len,distinct,disjoint,good,sub⟩ := ih previous
    by_cases present : v ∈ A ++ U
    · refine ⟨U,by simp; omega,distinct,disjoint,good,?_⟩
      intro w hw
      simp only [← List.append_assoc,List.mem_append,List.mem_singleton] at hw
      rcases hw with left | rfl
      · exact sub (List.mem_append.mpr left)
      · exact present
    · refine ⟨U ++ [v],by simp; omega,?_,?_,(snoc_iff A U v).mpr ⟨good,step_mono sub step⟩,?_⟩
      · simp only [List.nodup_append,distinct,List.nodup_cons,List.not_mem_nil,not_false_eq_true,List.nodup_nil,and_self,true_and,List.mem_singleton]
        rintro a ha _ rfl rfl
        exact present (List.mem_append_right _ ha)
      · intro w hw
        simp only [List.mem_append,List.mem_singleton] at hw
        rcases hw with old | rfl
        · exact disjoint w old
        · exact fun h => present (List.mem_append_left _ h)
      · intro w hw
        simp only [← List.append_assoc,List.mem_append,List.mem_singleton] at hw ⊢
        rcases hw with old | h
        · exact Or.inl (by simpa using sub (by simpa using old))
        · exact Or.inr h

theorem assemble (A F K V : List ℕ) (t : ℕ) (newTarget : t ∉ A) (front : Legal A F)
    (ports : ∀ k ∈ K, k ∈ A ++ F) (back : Legal K V) (goal : t ∈ K ++ V) :
    ∃ W : List ℕ, W.length ≤ F.length + V.length ∧ W.Nodup ∧ (∀ w ∈ W, w ∉ A) ∧ t ∈ W ∧ Legal A W := by
  have empty : Legal A [] := fun i => Fin.elim0 i
  obtain ⟨U,len,unique,fresh,alg,contains⟩ := extend A [] A F (by simp) (by simp) (by simp) empty front
  obtain ⟨W,budget,nd,disj,valid,all⟩ := extend A U K V (fun _ h => contains (ports _ h)) unique fresh alg back
  have hit := List.mem_append.mp (all goal)
  exact ⟨W,by simp at len; omega,nd,disj,hit.resolve_left newTarget,valid⟩

end PEqualNP.Outside.L_meta_4612_aux

theorem PEqualNP.Outside.L_meta_4612 :
  have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 :=
  PEqualNP.Outside.L_meta_4612_aux.assemble
