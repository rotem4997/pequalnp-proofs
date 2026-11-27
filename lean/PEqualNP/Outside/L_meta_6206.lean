import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6206

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.HeptadCover PEqualNP.GenericRejection

private def BitsLE (xs ys : List Bool) : Prop :=
  ∀ i, xs.getD i false = true → ys.getD i false = true

private lemma append_mono {xs ys as bs : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (hab : BitsLE as bs) :
    BitsLE (xs ++ as) (ys ++ bs) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hab _ hi

private lemma gate_mono {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (hxy : BitsLE xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨i, hi, rfl⟩
    exact hxy i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hxy i h⟩

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) :
    BitsLE (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · apply append_mono hlen hxy
      intro i hi
      cases i with
      | zero => exact gate_mono (hgs g List.mem_cons_self) hxy hi
      | succ i => simp at hi

private lemma wire_true_mono {C : Circuit} (hC : Monotone2 C) {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (i : ℕ) :
    wireVal C xs i = true → wireVal C ys i = true := by
  apply fold_mono C.gates _ xs ys hlen hxy i
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

private lemma ofFn_mono {n : ℕ} {f g : Fin n → Bool}
    (hfg : ∀ i, f i = true → g i = true) : BitsLE (List.ofFn f) (List.ofFn g) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    exact hfg ⟨i, h⟩ hi
  · have h' : (List.ofFn f).length ≤ i := by simpa using Nat.le_of_not_gt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hi
    cases hi

private lemma wire_incidence_mono {C : Circuit} (hC : Monotone2 C)
    {n m : ℕ} {X X' : Finset (Fin n)} {Y Y' : Finset (Fin m)}
    (hX : X ⊆ X') (hY : Y ⊆ Y') (i : ℕ) :
    wireVal C (incidenceInput X Y) i = true →
      wireVal C (incidenceInput X' Y') i = true := by
  apply wire_true_mono hC _ _ i
  · simp [incidenceInput]
  · unfold incidenceInput
    apply append_mono (by simp)
    · exact ofFn_mono (fun p hp => decide_eq_true (hX (of_decide_eq_true hp)))
    · exact ofFn_mono (fun l hl => decide_eq_true (hY (of_decide_eq_true hl)))

-- Each entry covers the point pairs off line zero and the indexed line.
private def quadrangleCatalog (l : Fin 13) : List (Finset (Fin 13)) :=
  match l.val with
  | 0 => [{2, 4, 5, 6}, {8, 10, 11, 12}, {2, 4, 7, 8}, {5, 6, 7, 10},
          {2, 4, 11, 12}, {5, 6, 11, 12}, {2, 5, 8, 10}, {4, 6, 8, 10},
          {2, 4, 7, 11}, {2, 4, 7, 12}]
  | 1 => [{5, 6, 7, 11}, {5, 7, 8, 12}, {6, 8, 11, 12}]
  | 2 => [{4, 6, 7, 8}, {4, 7, 10, 12}, {6, 8, 10, 12}]
  | 3 => [{2, 5, 7, 8}, {2, 7, 10, 11}, {5, 8, 10, 11}]
  | 4 => [{2, 6, 8, 10}, {2, 6, 11, 12}, {8, 10, 11, 12}]
  | 5 => [{2, 4, 7, 11}, {2, 7, 10, 12}, {4, 10, 11, 12}]
  | 6 => [{4, 5, 8, 10}, {4, 5, 11, 12}, {8, 10, 11, 12}]
  | 7 => [{2, 4, 5, 6}, {2, 4, 11, 12}, {5, 6, 11, 12}]
  | 8 => [{2, 5, 6, 10}, {2, 5, 7, 12}, {6, 7, 10, 12}]
  | 9 => [{2, 4, 6, 8}, {2, 4, 7, 11}, {6, 7, 8, 11}]
  | 10 => [{2, 4, 5, 8}, {2, 4, 7, 12}, {5, 7, 8, 12}]
  | 11 => [{2, 4, 5, 6}, {2, 5, 8, 10}, {4, 6, 8, 10}]
  | _ => [{4, 5, 6, 10}, {4, 6, 7, 11}, {5, 7, 10, 11}]

set_option maxRecDepth 2048 in
private lemma catalog_valid (l : Fin 13) (Q : Finset (Fin 13))
    (hQ : Q ∈ quadrangleCatalog l) :
    IsQuadrangle singerLines3 Q ∧
      0 ∈ missLines singerLines3 Q ∧ l ∈ missLines singerLines3 Q := by
  have h : (quadrangleCatalog l).all (fun R =>
      decide (IsQuadrangle singerLines3 R ∧
        0 ∈ missLines singerLines3 R ∧ l ∈ missLines singerLines3 R)) = true := by
    fin_cases l <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h Q hQ)

private def offLines (l : Fin 13) : List (Fin 13) :=
  (List.finRange 13).filter fun p => !(decide (p ∈ singerLines3 0 ∨ p ∈ singerLines3 l))

private def covers (l : Fin 13) : Bool :=
  (offLines l).all fun p =>
    (offLines l).all fun q =>
      (quadrangleCatalog l).any fun Q => decide (p ∈ Q ∧ q ∈ Q)

set_option maxRecDepth 2048 in
private lemma covers_true (l : Fin 13) : covers l = true := by
  fin_cases l <;> decide +kernel

private lemma mem_offLines {l p : Fin 13}
    (h0 : p ∉ singerLines3 0) (hl : p ∉ singerLines3 l) : p ∈ offLines l := by
  simp [offLines, h0, hl]

private lemma catalog_covers (l p q : Fin 13)
    (hp0 : p ∉ singerLines3 0) (hq0 : q ∉ singerLines3 0)
    (hpl : p ∉ singerLines3 l) (hql : q ∉ singerLines3 l) :
    ∃ Q ∈ quadrangleCatalog l, p ∈ Q ∧ q ∈ Q := by
  have h := List.all_eq_true.mp (covers_true l) p (mem_offLines hp0 hpl)
  have h' := List.all_eq_true.mp h q (mem_offLines hq0 hql)
  obtain ⟨Q, hQ, hpq⟩ := List.any_eq_true.mp h'
  exact ⟨Q, hQ, of_decide_eq_true hpq⟩

private def shift (c : Fin 13) : Equiv.Perm (Fin 13) where
  toFun p := ⟨(p.val + 13 - c.val) % 13, Nat.mod_lt _ (by decide)⟩
  invFun p := ⟨(p.val + c.val) % 13, Nat.mod_lt _ (by decide)⟩
  left_inv p := by
    apply Fin.ext
    change ((p.val + 13 - c.val) % 13 + c.val) % 13 = p.val
    omega
  right_inv p := by
    apply Fin.ext
    change ((p.val + c.val) % 13 + 13 - c.val) % 13 = p.val
    omega

private lemma shift_self (c : Fin 13) : shift c c = 0 := by
  apply Fin.ext
  change (c.val + 13 - c.val) % 13 = 0
  omega

private lemma shift_incidence (c p l : Fin 13) :
    shift c p ∈ singerLines3 (shift c l) ↔ p ∈ singerLines3 l := by
  have hmod :
      ((shift c p).val + 13 - (shift c l).val) % 13 = (p.val + 13 - l.val) % 13 := by
    change ((p.val + 13 - c.val) % 13 + 13 - (l.val + 13 - c.val) % 13) % 13 =
      (p.val + 13 - l.val) % 13
    omega
  simp only [singerLines3, Finset.mem_filter, Finset.mem_univ, true_and, hmod]

private lemma unshift_inter (c l : Fin 13) (Q : Finset (Fin 13)) :
    Q.image (shift c).symm ∩ singerLines3 l =
      (Q ∩ singerLines3 (shift c l)).image (shift c).symm := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    have h := (shift_incidence c ((shift c).symm q) l).mpr hp
    rw [Equiv.apply_symm_apply] at h
    exact ⟨q, ⟨hq, h⟩, rfl⟩
  · rintro ⟨q, ⟨hq, hql⟩, rfl⟩
    refine ⟨⟨q, hq, rfl⟩, (shift_incidence c _ l).mp ?_⟩
    simpa only [Equiv.apply_symm_apply] using hql

private lemma unshift_quad (c : Fin 13) {Q : Finset (Fin 13)}
    (hQ : IsQuadrangle singerLines3 Q) :
    IsQuadrangle singerLines3 (Q.image (shift c).symm) := by
  constructor
  · rw [Finset.card_image_of_injective _ (shift c).symm.injective]
    exact hQ.1
  · intro l
    rw [unshift_inter, Finset.card_image_of_injective _ (shift c).symm.injective]
    exact hQ.2 (shift c l)

private lemma unshift_miss (c l : Fin 13) {Q : Finset (Fin 13)}
    (h : shift c l ∈ missLines singerLines3 Q) :
    l ∈ missLines singerLines3 (Q.image (shift c).symm) := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left] at h ⊢
  intro p hp himage
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp himage
  apply h _ hq
  simpa only [Equiv.apply_symm_apply] using (shift_incidence c ((shift c).symm q) l).mpr hp

private lemma common_quadrangle {p q a b : Fin 13}
    (hpa : p ∉ singerLines3 a) (hqb : q ∉ singerLines3 b)
    (hpb : p ∉ singerLines3 b) (hqa : q ∉ singerLines3 a) :
    ∃ Q, IsQuadrangle singerLines3 Q ∧ p ∈ Q ∧ q ∈ Q ∧
      a ∈ missLines singerLines3 Q ∧ b ∈ missLines singerLines3 Q := by
  let e := shift a
  have hp0 : e p ∉ singerLines3 0 := by
    rw [← shift_self a]
    exact fun h => hpa ((shift_incidence a p a).mp h)
  have hq0 : e q ∉ singerLines3 0 := by
    rw [← shift_self a]
    exact fun h => hqa ((shift_incidence a q a).mp h)
  obtain ⟨Q, hQ, hp, hq⟩ := catalog_covers (e b) (e p) (e q) hp0 hq0
    (fun h => hpb ((shift_incidence a p b).mp h))
    (fun h => hqb ((shift_incidence a q b).mp h))
  obtain ⟨hquad, ha, hb⟩ := catalog_valid (e b) Q hQ
  refine ⟨Q.image e.symm, unshift_quad a hquad, ?_, ?_, ?_, unshift_miss a b hb⟩
  · exact Finset.mem_image.mpr ⟨e p, hp, e.symm_apply_apply p⟩
  · exact Finset.mem_image.mpr ⟨e q, hq, e.symm_apply_apply q⟩
  · exact unshift_miss a a (shift_self a ▸ ha)

end PEqualNP.Outside.L_meta_6206

open PEqualNP.Outside.L_meta_6206

theorem PEqualNP.Outside.L_meta_6206 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     have x5 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x5 : ℕ) (x6 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x6 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x6)) x5;     have x6 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x6 : ℕ) => {x7 : Fin (13 : ℕ) × Fin (13 : ℕ) | x7.1 ∉ PEqualNP.HeptadCover.singerLines3 x7.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x7.1} {x7.2}) x6 = Bool.true};     (∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → x5 x2 x7 = Bool.false ∨ x5 x3 x7 = Bool.false) → ∀ x8 ∈ x6 x2, ∀ x10 ∈ x6 x3, x8.1 ∈ PEqualNP.HeptadCover.singerLines3 x10.2 ∨ x10.1 ∈ PEqualNP.HeptadCover.singerLines3 x8.2 := by
  intro C i j hC
  dsimp only
  intro hsep a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hcross
  push Not at hcross
  obtain ⟨Q, hQ, hap, hbp, hal, hbl⟩ :=
    common_quadrangle ha.1 hb.1 hcross.1 hcross.2
  have hi := wire_incidence_mono hC (Finset.singleton_subset_iff.mpr hap)
    (Finset.singleton_subset_iff.mpr hal) i ha.2
  have hj := wire_incidence_mono hC (Finset.singleton_subset_iff.mpr hbp)
    (Finset.singleton_subset_iff.mpr hbl) j hb.2
  rcases hsep Q hQ with h | h
  · rw [hi] at h
    cases h
  · rw [hj] at h
    cases h
