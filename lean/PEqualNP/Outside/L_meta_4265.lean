import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4265

open PEqualNP.CircuitLowerBounds

lemma getD_append_singleton (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hk : k < l.length
  · rw [if_pos hk, List.getElem?_append_left hk]
  · rw [if_neg hk, List.getElem?_append_right (Nat.le_of_not_lt hk)]
    by_cases hkeq : k = l.length
    · subst hkeq; simp
    · rw [if_neg hkeq]
      have hnone : ([b] : List Bool)[k - l.length]? = none := by
        rw [List.getElem?_eq_none]; simp; omega
      rw [hnone]; rfl

lemma forall2_mem_corresp {x3 x4 : ℕ} {us vs : List ℕ}
    (h : List.Forall₂ (fun u v => v = u + 1 ∨ v = 0 ∧ (u = x3 ∨ u = x4)) us vs)
    {u0 : ℕ} (hu0 : u0 ∈ us) :
    ∃ v ∈ vs, v = u0 + 1 ∨ v = 0 := by
  induction h with
  | nil => cases hu0
  | cons hr _ ih =>
    rcases List.mem_cons.mp hu0 with rfl | htail
    · rcases hr with rfl | ⟨rfl, _⟩
      · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
      · exact ⟨0, List.mem_cons_self, Or.inr rfl⟩
    · obtain ⟨w, hw, hcases⟩ := ih htail
      exact ⟨w, List.mem_cons_of_mem _ hw, hcases⟩

lemma forall2_map_eq {x3 x4 : ℕ} {x5 : Fin 7} {acc1 acc2 : List Bool}
    (h01 : acc1.getD 0 false = true) (h02 : acc2.getD 0 false = true)
    (heq : ∀ w : ℕ, w ≠ (x5 : ℕ) → acc1.getD (w + 1) false = acc2.getD (w + 1) false) :
    ∀ {us vs : List ℕ},
    List.Forall₂ (fun u v => v = u + 1 ∨ v = 0 ∧ (u = x3 ∨ u = x4)) us vs →
    (x5 : ℕ) ∉ us →
    (vs.map fun i => acc1.getD i false) = (vs.map fun i => acc2.getD i false)
  | [], [], .nil, _ => rfl
  | u :: us', v :: vs', .cons hr ht, hx5 => by
    have hne : u ≠ (x5 : ℕ) := by
      intro hu; apply hx5; subst hu; exact List.mem_cons_self
    have hx5' : (x5 : ℕ) ∉ us' := fun hm => hx5 (List.mem_cons_of_mem u hm)
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · rcases hr with rfl | ⟨rfl, _⟩
      · exact heq u hne
      · rw [h01, h02]
    · exact forall2_map_eq h01 h02 heq ht hx5'

lemma or_eval_of_mem_true (l : List Bool) (hl : true ∈ l) : GateOp.or.eval l = true := by
  simp only [GateOp.eval, List.any_eq_true]
  exact ⟨true, hl, rfl⟩

lemma foldl_wires_eq
    (x3 x4 : ℕ) (x5 : Fin 7) (x6 x7 : Fin 7 → Bool)
    (hagree : ∀ i : Fin 7, i ≠ x5 → x6 i = x7 i) :
    ∀ (gs1 gs2 : List Gate) (acc1 acc2 : List Bool),
      List.Forall₂
        (fun g1 g2 => g1.op = g2.op ∧
          List.Forall₂ (fun u v => v = u + 1 ∨ v = 0 ∧ (u = x3 ∨ u = x4)) g1.inputs g2.inputs)
        gs1 gs2 →
      (∀ g1 ∈ gs1, (x5 : ℕ) ∈ g1.inputs →
        g1.op = GateOp.or ∧ ∃ j : Fin 7, j ≠ x5 ∧ (j : ℕ) ∈ g1.inputs ∧ x6 j = true) →
      8 ≤ acc1.length →
      acc1.length = acc2.length →
      acc1.getD 0 false = true →
      acc2.getD 0 false = true →
      (∀ j : Fin 7, j ≠ x5 → acc1.getD ((j : ℕ) + 1) false = x6 j) →
      (∀ j : Fin 7, j ≠ x5 → acc2.getD ((j : ℕ) + 1) false = x7 j) →
      (∀ w : ℕ, w ≠ (x5 : ℕ) → acc1.getD (w + 1) false = acc2.getD (w + 1) false) →
      let r1 := gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc1
      let r2 := gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc2
      ∀ w : ℕ, w ≠ (x5 : ℕ) → r1.getD (w + 1) false = r2.getD (w + 1) false := by
  intro gs1
  induction gs1 with
  | nil =>
    intro gs2 acc1 acc2 hrel _ _ _ _ _ _ _ heq
    cases hrel
    exact heq
  | cons g1 rest1 ih =>
    intro gs2 acc1 acc2 hrel hor hlen8 hlen h01 h02 hj1 hj2 heq
    cases hrel with
    | cons hg hrest =>
      rename_i g2 rest2
      obtain ⟨hop, hinp⟩ := hg
      have hor_g1 : (x5 : ℕ) ∈ g1.inputs →
          g1.op = GateOp.or ∧ ∃ j : Fin 7, j ≠ x5 ∧ (j : ℕ) ∈ g1.inputs ∧ x6 j = true :=
        hor g1 List.mem_cons_self
      have hor_rest : ∀ g ∈ rest1, (x5 : ℕ) ∈ g.inputs →
          g.op = GateOp.or ∧ ∃ j : Fin 7, j ≠ x5 ∧ (j : ℕ) ∈ g.inputs ∧ x6 j = true :=
        fun g hg' => hor g (List.mem_cons_of_mem _ hg')
      have hval : g2.op.eval (g2.inputs.map fun i => acc1.getD i false) =
                  g2.op.eval (g2.inputs.map fun i => acc2.getD i false) := by
        by_cases hx5 : (x5 : ℕ) ∈ g1.inputs
        · obtain ⟨hg1or, j, hjne, hjmem, hjtrue⟩ := hor_g1 hx5
          have hg2or : g2.op = GateOp.or := hop.symm.trans hg1or
          obtain ⟨v, hvmem, hvcases⟩ := forall2_mem_corresp hinp hjmem
          have hv1 : acc1.getD v false = true := by
            rcases hvcases with rfl | rfl
            · rw [hj1 j hjne, hjtrue]
            · exact h01
          have hv2 : acc2.getD v false = true := by
            rcases hvcases with rfl | rfl
            · rw [hj2 j hjne, ← hagree j hjne, hjtrue]
            · exact h02
          rw [hg2or]
          rw [or_eval_of_mem_true _ (List.mem_map.mpr ⟨v, hvmem, hv1⟩)]
          rw [or_eval_of_mem_true _ (List.mem_map.mpr ⟨v, hvmem, hv2⟩)]
        · rw [forall2_map_eq h01 h02 heq hinp hx5]
      simp only [List.foldl_cons]
      apply ih rest2
        (acc1 ++ [g2.op.eval (g2.inputs.map fun i => acc1.getD i false)])
        (acc2 ++ [g2.op.eval (g2.inputs.map fun i => acc2.getD i false)])
        hrest hor_rest
      · simp; omega
      · simp [hlen]
      · rw [getD_append_singleton, if_pos (by omega)]; exact h01
      · rw [getD_append_singleton, if_pos (by omega)]; exact h02
      · intro j hjne
        rw [getD_append_singleton, if_pos (by omega)]
        exact hj1 j hjne
      · intro j hjne
        rw [getD_append_singleton, if_pos (by omega)]
        exact hj2 j hjne
      · intro w hw
        rw [getD_append_singleton, getD_append_singleton, hlen]
        split_ifs
        · exact heq w hw
        · exact hval
        · rfl

lemma getD_cons_ofFn (f : Fin 7 → Bool) (j : Fin 7) :
    (true :: List.ofFn f).getD ((j : ℕ) + 1) false = f j := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_ofFn, j.isLt,
    ↓reduceDIte, Option.getD_some, Fin.eta]

lemma main_proof
    (x1 x2 : Circuit) (x3 x4 : ℕ) (x5 : Fin 7) (x6 x7 : Fin 7 → Bool)
    (hrel : List.Forall₂
      (fun g1 g2 => g1.op = g2.op ∧
        List.Forall₂ (fun u v => v = u + 1 ∨ v = 0 ∧ (u = x3 ∨ u = x4)) g1.inputs g2.inputs)
      x1.gates x2.gates)
    (hagree : ∀ i : Fin 7, i ≠ x5 → x6 i = x7 i)
    (hor : ∀ g1 ∈ x1.gates, (x5 : ℕ) ∈ g1.inputs →
      g1.op = GateOp.or ∧ ∃ j : Fin 7, j ≠ x5 ∧ (j : ℕ) ∈ g1.inputs ∧ x6 j = true)
    (hout : x1.output ≠ (x5 : ℕ)) :
    (x2.wires (true :: List.ofFn x6)).getD (x1.output + 1) false =
    (x2.wires (true :: List.ofFn x7)).getD (x1.output + 1) false := by
  have h1 := foldl_wires_eq x3 x4 x5 x6 x7 hagree x1.gates x2.gates
    (true :: List.ofFn x6) (true :: List.ofFn x7) hrel hor
    (by simp) (by simp) (by simp) (by simp)
    (fun j _ => getD_cons_ofFn x6 j)
    (fun j _ => getD_cons_ofFn x7 j)
    (fun w hw => by
      by_cases hw7 : w < 7
      · let j : Fin 7 := ⟨w, hw7⟩
        have hne : j ≠ x5 := by intro h; apply hw; exact congrArg Fin.val h
        have h6 := getD_cons_ofFn x6 j
        have h7 := getD_cons_ofFn x7 j
        change (true :: List.ofFn x6).getD ((j : ℕ) + 1) false =
          (true :: List.ofFn x7).getD ((j : ℕ) + 1) false
        rw [h6, h7, hagree j hne]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
  exact h1 x1.output hout

end PEqualNP.Outside.L_meta_4265

theorem PEqualNP.Outside.L_meta_4265 :
  ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin (7 : ℕ)) (x6 x7 : Fin (7 : ℕ) → Bool), List.Forall₂ (fun (x8 x9 : PEqualNP.CircuitLowerBounds.Gate) => x8.op = x9.op ∧ List.Forall₂ (fun (x10 x11 : ℕ) => x11 = x10 + (1 : ℕ) ∨ x11 = (0 : ℕ) ∧ (x10 = x3 ∨ x10 = x4)) x8.inputs x9.inputs) x1.gates x2.gates → (∀ (x9 : Fin (7 : ℕ)), x9 ≠ x5 → x6 x9 = x7 x9) → (∀ x10 ∈ x1.gates, ↑x5 ∈ x10.inputs → x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x13 : Fin (7 : ℕ)), x13 ≠ x5 ∧ ↑x13 ∈ x10.inputs ∧ x6 x13 = Bool.true) → x1.output ≠ ↑x5 → (x2.wires (Bool.true :: List.ofFn x6)).getD (x1.output + (1 : ℕ)) Bool.false = (x2.wires (Bool.true :: List.ofFn x7)).getD (x1.output + (1 : ℕ)) Bool.false := by
  intro x1 x2 x3 x4 x5 x6 x7 hrel hagree hor hout
  exact PEqualNP.Outside.L_meta_4265.main_proof x1 x2 x3 x4 x5 x6 x7 hrel hagree hor hout
