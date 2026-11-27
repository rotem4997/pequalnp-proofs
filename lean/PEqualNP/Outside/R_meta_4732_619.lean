import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_4732_619 :
    (∀ (C : Circuit) (b : Bool) (σ τ : Equiv.Perm (Fin 13)), Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      C.output ≠ 26 →
      ∃ B : Circuit, Monotone2 B ∧
        (∀ j : Fin B.gates.length, ∀ i ∈ (B.gates.get j).inputs, i < 26 + j.val) ∧
        B.size ≤ C.size ∧
        ∀ x y : Fin 13 → Bool, B.eval (List.ofFn x ++ List.ofFn y) =
          C.eval ((List.ofFn (x ∘ σ.symm) ++ List.ofFn (y ∘ τ.symm)) ++ [b])) →
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     let pos := fun (p l : Fin 13) =>
       (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
     let neg := fun Q : Finset (Fin 13) =>
       (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
         List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ D)
     let quad := fun Q : Finset (Fin 13) =>
       Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p - l ∈ D).card ≤ 2
     ∀ C : Circuit, Monotone2 C →
       (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 26 + j.val) →
       (∀ p l, p - l ∈ D → p ≠ 0 ∨ l ≠ 0 → C.eval (pos p l) = true) →
       (∀ Q, quad Q → C.eval (neg Q) = false) → 63 ≤ C.size) →
    (have x1 : Finset (Fin (13 : ℕ)) :=
       {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
     have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool :=
       fun (x2 x3 : Fin (13 : ℕ)) =>
         (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++
         List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
     have x3 : Finset (Fin (13 : ℕ)) → List Bool :=
       fun (x3 : Finset (Fin (13 : ℕ))) =>
         (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++
         List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1);
     have x4 : Finset (Fin (13 : ℕ)) → Prop :=
       fun (x4 : Finset (Fin (13 : ℕ))) =>
         x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ);
     ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool),
       PEqualNP.MetaComplexity.Monotone2 x5 →
       (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) →
       (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 →
         x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) →
       (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) →
       (63 : ℕ) ≤ x5.size) := by
  intro normalize canon
  dsimp only at canon ⊢
  intro C droppedLine b hm hr hp hn
  let S : Finset (Fin 13) := {0, 1, 3, 9}
  let pos := fun (p l : Fin 13) =>
    (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
  let neg := fun Q : Finset (Fin 13) =>
    (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ S)
  let quad := fun Q : Finset (Fin 13) =>
    Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p - l ∈ S).card ≤ 2
  change (∀ p l, p - l ∈ S → p ≠ 0 ∨ l ≠ droppedLine → C.eval (pos p l ++ [b]) = true) at hp
  change (∀ Q, quad Q → C.eval (neg Q ++ [b]) = false) at hn
  have hout : C.output ≠ 26 := by
    intro ho
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have gen (w : List Bool) (hw : w.length = 26) : C.eval (w ++ [b]) = b := by
      unfold Circuit.eval Circuit.wires
      rw [ho]
      change (C.gates.foldl step (w ++ [b])).getD 26 false = b
      rw [keep _ _ _ (by simp [hw])]
      rw [← hw]
      simp
    have h1 := hp 1 1 (by decide) (Or.inl (by decide))
    have h2 := hn ({0, 1, 2, 5} : Finset (Fin 13)) (by decide)
    rw [gen _ (by simp [pos])] at h1
    rw [gen _ (by simp [neg])] at h2
    rw [h2] at h1
    exact Bool.noConfusion h1
  let a : Fin 13 := if 0 - droppedLine ∈ S then droppedLine else 0
  have ha : 0 - a ∈ S := by
    dsimp only [a]
    split <;> rename_i h
    · exact h
    · decide
  let pf : Fin 13 → Fin 13 → Fin 13 := fun t =>
    if t = 4 then ![0, 4, 1, 5, 2, 8, 11, 12, 9, 7, 10, 6, 3] else
    if t = 10 then ![0, 6, 1, 10, 5, 4, 12, 7, 3, 11, 8, 2, 9] else
    if t = 12 then ![0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9] else id
  let pb : Fin 13 → Fin 13 → Fin 13 := fun t =>
    if t = 4 then ![0, 2, 4, 12, 1, 3, 11, 9, 5, 8, 10, 6, 7] else
    if t = 10 then ![0, 2, 11, 8, 5, 4, 1, 7, 10, 12, 3, 9, 6] else
    if t = 12 then ![0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9] else id
  let lf : Fin 13 → Fin 13 → Fin 13 := fun t =>
    if t = 4 then ![4, 1, 5, 2, 12, 8, 11, 9, 6, 7, 10, 3, 0] else
    if t = 10 then ![10, 5, 1, 9, 4, 3, 11, 7, 2, 8, 12, 6, 0] else
    if t = 12 then ![12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0] else id
  let lb : Fin 13 → Fin 13 → Fin 13 := fun t =>
    if t = 4 then ![12, 1, 3, 11, 0, 2, 8, 9, 5, 7, 10, 6, 4] else
    if t = 10 then ![12, 2, 8, 5, 4, 1, 11, 7, 9, 3, 0, 6, 10] else
    if t = 12 then ![12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0] else id
  have pleft : ∀ t i, pb t (pf t i) = i := by decide
  have pright : ∀ t i, pf t (pb t i) = i := by decide
  have lleft : ∀ t i, lb t (lf t i) = i := by decide
  have lright : ∀ t i, lf t (lb t i) = i := by decide
  let σ : Equiv.Perm (Fin 13) := ⟨pf a, pb a, pleft a, pright a⟩
  let τ : Equiv.Perm (Fin 13) := ⟨lf a, lb a, lleft a, lright a⟩
  have pzero : σ 0 = 0 := (show ∀ t, pf t 0 = 0 by decide) a
  have lzero : τ 0 = a := (show ∀ t, 0 - t ∈ S → lf t 0 = t by decide) a ha
  have aut : ∀ p l, σ p - τ l ∈ S ↔ p - l ∈ S := by
    have all_t (t : Fin 13) : ∀ p l, pf t p - lf t l ∈ S ↔ p - l ∈ S := by
      by_cases h4 : t = 4
      · subst t; decide
      by_cases h10 : t = 10
      · subst t; decide
      by_cases h12 : t = 12
      · subst t; decide
      simp [pf, lf, h4, h10, h12]
    exact all_t a
  obtain ⟨B, Bm, Br, Bsz, Bfun⟩ := normalize C b σ τ hm hr hout
  apply (canon B Bm Br ?_ ?_).trans Bsz
  · intro p l hi hne
    change B.eval (pos p l) = true
    have e (s t : Fin 13) (e : Equiv.Perm (Fin 13)) (h : t = e s) :
        ((fun i : Fin 13 => decide (i = s)) ∘ e.symm) = (fun i : Fin 13 => decide (i = t)) := by
      subst t
      funext i
      simp [Function.comp_apply, Equiv.symm_apply_eq]
    dsimp only [pos]
    rw [Bfun, e p (σ p) σ rfl, e l (τ l) τ rfl]
    apply hp (σ p) (τ l) ((aut p l).mpr hi)
    by_cases he : 0 - droppedLine ∈ S
    · rcases hne with h | h
      · exact Or.inl (fun eq => h (σ.injective (eq.trans pzero.symm)))
      · right
        intro eq
        have hA : a = droppedLine := if_pos he
        exact h (τ.injective (eq.trans (lzero.trans hA).symm))
    · by_cases h' : σ p = 0
      · right
        intro hq
        exact he (by simpa only [h', hq] using (aut p l).mpr hi)
      · exact Or.inl h'
  · intro Q hQ
    change B.eval (neg Q) = false
    let R : Finset (Fin 13) := Q.image σ
    have hR : quad R := by
      change R.card = 4 ∧ ∀ l : Fin 13, (R.filter fun p => p - l ∈ S).card ≤ 2
      refine ⟨(Finset.card_image_of_injective Q σ.injective).trans hQ.1, ?_⟩
      intro v
      obtain ⟨l, rfl⟩ := τ.surjective v
      rw [show R = Q.image σ from rfl, Finset.filter_image,
        Finset.card_image_of_injective _ σ.injective]
      have eql : (Q.filter fun t => σ t - τ l ∈ S) = Q.filter (fun t => t - l ∈ S) := by
        ext p
        simp only [Finset.mem_filter, aut]
      rw [eql]
      exact hQ.2 l
    have f1 : ((fun i : Fin 13 => decide (i ∈ Q)) ∘ σ.symm) =
        (fun i : Fin 13 => decide (i ∈ R)) := by
      funext i
      simp only [Function.comp_apply, decide_eq_decide, R, Finset.mem_image]
      constructor
      · exact fun h => ⟨σ.symm i, h, σ.apply_symm_apply i⟩
      · rintro ⟨j, hj, rfl⟩
        simpa only [σ.symm_apply_apply] using hj
    have f2 : ((fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ S)) ∘ τ.symm) =
        (fun i : Fin 13 => decide (∀ p ∈ R, p - i ∉ S)) := by
      funext i
      simp only [Function.comp_apply, decide_eq_decide]
      constructor
      · intro h q hq
        obtain ⟨p, hpQ, rfl⟩ := Finset.mem_image.mp hq
        have ha := (aut p (τ.symm i)).mp
        rw [τ.apply_symm_apply] at ha
        exact fun hc => h p hpQ (ha hc)
      · intro h p hpQ hi
        apply h (σ p) (Finset.mem_image.mpr ⟨p, hpQ, rfl⟩)
        have ha := (aut p (τ.symm i)).mpr hi
        rwa [τ.apply_symm_apply] at ha
    dsimp only [neg]
    rw [Bfun, f1, f2]
    exact hn R hR
