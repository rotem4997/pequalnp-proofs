import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1843

open PEqualNP.CircuitLowerBounds

abbrev AOx (n : ℕ) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C

abbrev CrP (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
    ¬ ((∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
      (∀ h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
        (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))

abbrev Ins (N K : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (S W : Finset (Fin N)) : Prop :=
  (0 < C.gates.length ∧
    (∀ j < C.gates.length, ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      (C.lineDegrees (N + N) (Finset.image (fun p : Fin N => (p : ℕ)) (S)ᶜ ∪
        Finset.image (fun l : Fin N => N + (l : ℕ)) (W)ᶜ)).getD i 0 = 0) ∧
    (C.lineDegrees (N + N) (Finset.image (fun p : Fin N => (p : ℕ)) (S)ᶜ ∪
        Finset.image (fun l : Fin N => N + (l : ℕ)) (W)ᶜ)).getD C.output 0 = 0) ∧
  (∀ p ∈ S, ∀ l ∈ W, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
    (Fin.append (fun a : Fin N => decide (a ∈ ({p} : Finset (Fin N))))
      (fun b : Fin N => decide (b ∈ ({l} : Finset (Fin N))))) = true) ∧
  (∀ X Y : Finset (Fin N), X ⊆ S → Y ⊆ W → Y.card ≤ K → (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
    PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a : Fin N => decide (a ∈ X)) (fun b : Fin N => decide (b ∈ Y))) = false)

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem inc_ge {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (S W : Finset (Fin N)) (c : ℕ)
    (h : ∀ l ∈ W, c ≤ (S.filter (fun u => I u l)).card) :
    W.card * c ≤ ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card := by
  have h1 : ((S ×ˢ W).filter (fun pl => I pl.1 pl.2)).card =
      ∑ l ∈ W, (S.filter (fun u => I u l)).card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.card_filter]
  rw [h1]
  calc W.card * c = ∑ _l ∈ W, c := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum h

theorem zl (l : List ℕ) (h : ∀ x ∈ l, x = 0) : l.sum = 0 ∧ l.foldr max 0 = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons a t ih =>
    have ha : a = 0 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    subst ha
    refine ⟨?_, ?_⟩
    · simp [h2.1]
    · simp [h2.2]

theorem getD_zero (L : List ℕ) (h : ∀ x ∈ L, x = 0) (i : ℕ) : L.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i L.length with hi | hi
  · rw [List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none hi]
    rfl

theorem ld_step (g : Gate) (d : List ℕ) (hd : ∀ x ∈ d, x = 0) : g.lineDegree d = 0 := by
  have h := zl (g.inputs.map fun i => d.getD i 0) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact getD_zero d hd i)
  unfold Gate.lineDegree
  split_ifs
  · exact h.1
  · exact h.2

theorem ld_fold : ∀ (gs : List Gate) (d : List ℕ), (∀ x ∈ d, x = 0) →
    ∀ x ∈ gs.foldl (fun d g => d ++ [g.lineDegree d]) d, x = 0 := by
  intro gs
  induction gs with
  | nil =>
    intro d hd x hx
    exact hd x hx
  | cons g t ih =>
    intro d hd x hx
    rw [List.foldl_cons] at hx
    refine ih (d ++ [g.lineDegree d]) ?_ x hx
    intro y hy
    rcases List.mem_append.mp hy with h1 | h1
    · exact hd y h1
    · rw [List.mem_singleton.mp h1]
      exact ld_step g d hd

theorem ld_zero (C : Circuit) (n i : ℕ) : (C.lineDegrees n ∅).getD i 0 = 0 := by
  refine getD_zero _ ?_ i
  unfold Circuit.lineDegrees
  refine ld_fold _ _ ?_
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  simp

theorem none_of (n : ℕ) (Q : ℕ → Prop) (h : Set.ncard {j : ℕ | j < n ∧ Q j} ≤ 0) :
    ∀ j < n, ¬ Q j := by
  have hfin : {j : ℕ | j < n ∧ Q j}.Finite :=
    (Set.finite_lt_nat n).subset (fun j hj => hj.1)
  have h0 := (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp h)
  intro j hj hq
  have h1 : j ∈ ({j : ℕ | j < n ∧ Q j} : Set ℕ) := ⟨hj, hq⟩
  rw [h0] at h1
  exact h1

theorem view_eq (C : Circuit) (P : Fin C.gates.length → Prop) (f : Fin C.gates.length → Gate)
    (hP : ∀ j, ¬ P j) (n : ℕ) (z : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n (Circuit.mk (List.ofFn (fun j : Fin C.gates.length =>
      @ite Gate (P j) (Classical.propDecidable _) (f j)
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val))) C.output) z =
      PEqualNP.MetaComplexity.circuitFun n C z := by
  have h : (List.ofFn (fun j : Fin C.gates.length =>
      @ite Gate (P j) (Classical.propDecidable _) (f j)
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val))) = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      rw [if_neg (hP _)]
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
  exact congrArg (fun G => PEqualNP.MetaComplexity.circuitFun n (Circuit.mk G C.output) z) h

theorem acc_out {N : ℕ} (C : Circuit) (hg : C.gates = []) (p l : Fin N)
    (h : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) :
    C.output = p.val ∨ C.output = N + l.val := by
  have h1 : (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))).getD C.output false = true := by
    have h2 : PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD C.output false := rfl
    rw [h2, hg] at h
    exact h
  rw [ofFn_getD] at h1
  by_cases ho : C.output < N + N
  · rw [dif_pos ho] at h1
    rcases of_decide_eq_true h1 with e | e
    · left
      exact congrArg Fin.val e
    · right
      exact congrArg Fin.val e
  · rw [dif_neg ho] at h1
    cases h1

theorem ind_eq (N : ℕ) (p l : Fin N) :
    (Fin.append (fun a : Fin N => decide (a ∈ ({p} : Finset (Fin N))))
      (fun b : Fin N => decide (b ∈ ({l} : Finset (Fin N))))) =
    fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]
    have h1 : ¬ (Fin.castAdd N i = Fin.natAdd N l) := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      have := i.isLt
      omega
    have h2 : (Fin.castAdd N i = Fin.castAdd N p) ↔ i = p := by
      constructor
      · intro h
        have h2 := congrArg Fin.val h
        simp only [Fin.val_castAdd] at h2
        exact Fin.ext h2
      · intro h
        rw [h]
    apply decide_eq_decide.mpr
    rw [Finset.mem_singleton]
    constructor
    · intro h
      left
      rw [h]
    · rintro (h | h)
      · exact h2.mp h
      · exact absurd h h1
  · rw [Fin.append_right]
    have h1 : ¬ (Fin.natAdd N i = Fin.castAdd N p) := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      have := p.isLt
      omega
    have h2 : (Fin.natAdd N i = Fin.natAdd N l) ↔ i = l := by
      constructor
      · intro h
        have h2 := congrArg Fin.val h
        simp only [Fin.val_natAdd] at h2
        exact Fin.ext (by omega)
      · intro h
        rw [h]
    apply decide_eq_decide.mpr
    rw [Finset.mem_singleton]
    constructor
    · intro h
      right
      rw [h]
    · rintro (h | h)
      · exact absurd h h1
      · exact h2.mp h

theorem arith (a c R D w q d inc s s0 T N : ℕ) (Dz Tz : ℤ)
    (h3 : R * D * inc ≤ R * D * w + max (R * max (2 * D) (q + 1)) (3 * q * D) * s)
    (hinc : w * (q + 1 - d) ≤ inc) (hd : d ≤ q) (hw : N ≤ w + T) (hs : s ≤ s0) (hR : 1 ≤ R)
    (hT : T ≤ N) (hDz : (D : ℤ) = Dz) (hTz : (T : ℤ) = Tz)
    (hyp : (a : ℤ) * max ((R : ℤ) * max (2 * Dz) ((q : ℤ) + 1)) (3 * (q : ℤ) * Dz) ≤
      (c : ℤ) * ((R : ℤ) * Dz * ((N : ℤ) - Tz) * ((q : ℤ) - (d : ℤ)))) : a ≤ c * s0 := by
  subst hDz hTz
  obtain ⟨M, hM⟩ : ∃ M, M = max (R * max (2 * D) (q + 1)) (3 * q * D) := ⟨_, rfl⟩
  have hMz : (M : ℤ) =
      max ((R : ℤ) * max (2 * (D : ℤ)) ((q : ℤ) + 1)) (3 * (q : ℤ) * (D : ℤ)) := by
    rw [hM]
    push_cast
    first | done | rfl
  rw [← hM] at h3
  rw [← hMz] at hyp
  have hMpos : 1 ≤ M := by
    have h1 : R * (q + 1) ≤ M := by
      rw [hM]
      exact le_trans (Nat.mul_le_mul_left R (le_max_right _ _)) (le_max_left _ _)
    have h2 : 1 * 1 ≤ R * (q + 1) := Nat.mul_le_mul hR (by omega)
    omega
  have e : w * (q + 1 - d) = w * (q - d) + w := by
    have e1 : q + 1 - d = (q - d) + 1 := by omega
    rw [e1, Nat.mul_add, Nat.mul_one]
  have h4 : R * D * (w * (q - d)) ≤ M * s := by
    have h5 := Nat.mul_le_mul_left (R * D) hinc
    rw [e, Nat.mul_add] at h5
    omega
  have h5 : R * D * ((N - T) * (q - d)) ≤ M * s0 :=
    calc R * D * ((N - T) * (q - d)) ≤ R * D * (w * (q - d)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ M * s := h4
      _ ≤ M * s0 := Nat.mul_le_mul_left _ hs
  have h5z : (R : ℤ) * (D : ℤ) * ((N : ℤ) - (T : ℤ)) * ((q : ℤ) - (d : ℤ)) ≤
      (M : ℤ) * (s0 : ℤ) := by
    have h6 : ((R * D * ((N - T) * (q - d)) : ℕ) : ℤ) ≤ ((M * s0 : ℕ) : ℤ) := Nat.cast_le.mpr h5
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hT,
      Nat.cast_sub hd] at h6
    have e2 : (R : ℤ) * (D : ℤ) * ((N : ℤ) - (T : ℤ)) * ((q : ℤ) - (d : ℤ)) =
        (R : ℤ) * (D : ℤ) * (((N : ℤ) - (T : ℤ)) * ((q : ℤ) - (d : ℤ))) := by ring
    rw [e2]
    exact h6
  have hMz0 : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  have h7 : (a : ℤ) * (M : ℤ) ≤ ((c * s0 : ℕ) : ℤ) * (M : ℤ) := by
    rw [Nat.cast_mul]
    calc (a : ℤ) * (M : ℤ)
        ≤ (c : ℤ) * ((R : ℤ) * (D : ℤ) * ((N : ℤ) - (T : ℤ)) * ((q : ℤ) - (d : ℤ))) := hyp
      _ ≤ (c : ℤ) * ((M : ℤ) * (s0 : ℤ)) := mul_le_mul_of_nonneg_left h5z (by positivity)
      _ = (c : ℤ) * (s0 : ℤ) * (M : ℤ) := by ring
  exact Nat.cast_le.mp (le_of_mul_le_mul_right h7 hMz0)

end PEqualNP.Outside.L_meta_1843

open PEqualNP.Outside.L_meta_1843

theorem PEqualNP.Outside.L_meta_1843 : (∀ (Nlv15b Klv15b mlv15b : ℕ) (Ilv15b : Fin Nlv15b → Fin Nlv15b → Prop) [DecidableRel Ilv15b] (Clv15b : PEqualNP.CircuitLowerBounds.Circuit) (Slv15b Wlv15b Xlv15b : Finset (Fin Nlv15b)) (wlv15b : Fin Nlv15b) (sglv15b : ℕ → Fin 2) (Splv15b Wplv15b : Finset (Fin Nlv15b)), ((∀ glv15b ∈ Clv15b.gates, (glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Clv15b) → Set.ncard {jlv15b : ℕ | jlv15b < Clv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15b 0 = 0) ∨ (∀ hlv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15b 0 = 0))} ≤ mlv15b + 1 → ((0 < Clv15b.gates.length ∧ (∀ jlv15bx1 < Clv15b.gates.length, ∀ ilv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx1).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx5 : Fin Nlv15b => (plv15bx5 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx4 : Fin Nlv15b => Nlv15b + (llv15bx4 : ℕ)) (Wlv15b)ᶜ)).getD ilv15bx1 0 = 0) ∧ (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx6 : Fin Nlv15b => (plv15bx6 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx5 : Fin Nlv15b => Nlv15b + (llv15bx5 : ℕ)) (Wlv15b)ᶜ)).getD Clv15b.output 0 = 0) ∧ (∀ plv15bx3 ∈ Slv15b, ∀ llv15bx2 ∈ Wlv15b, Ilv15b plv15bx3 llv15bx2 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx7 : Fin Nlv15b => decide (plv15bx7 ∈ ({plv15bx3} : Finset (Fin Nlv15b)))) (fun llv15bx6 : Fin Nlv15b => decide (llv15bx6 ∈ ({llv15bx2} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx1 Ylv15b : Finset (Fin Nlv15b), Xlv15bx1 ⊆ Slv15b → Ylv15b ⊆ Wlv15b → Ylv15b.card ≤ Klv15b + 1 → (∀ plv15bx4 ∈ Xlv15bx1, ∀ llv15bx3 ∈ Ylv15b, ¬ Ilv15b plv15bx4 llv15bx3) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx8 : Fin Nlv15b => decide (plv15bx8 ∈ Xlv15bx1)) (fun llv15bx7 : Fin Nlv15b => decide (llv15bx7 ∈ Ylv15b))) = false)) → wlv15b ∈ Wlv15b → Xlv15b ⊆ Slv15b → (∀ plv15bx1 ∈ Xlv15b, ¬ Ilv15b plv15bx1 wlv15b) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15bx2 : Fin Clv15b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx2 0 = 0) ∨ (∀ hlv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val))) Clv15b.output) (Fin.append (fun plv15bx9 : Fin Nlv15b => decide (plv15bx9 ∈ Xlv15b)) (fun llv15bx8 : Fin Nlv15b => decide (llv15bx8 ∈ ({wlv15b} : Finset (Fin Nlv15b))))) = true → Splv15b = Slv15b.filter (fun ulv15b : Fin Nlv15b => ¬ Ilv15b ulv15b wlv15b ∧ ulv15b ∉ Xlv15b) → Wplv15b = Wlv15b.filter (fun llv15bx1 : Fin Nlv15b => llv15bx1 ≠ wlv15b ∧ ∀ plv15bx2 ∈ Xlv15b, ¬ Ilv15b plv15bx2 llv15bx1) → (∃ plv15b ∈ Splv15b, ∃ llv15b ∈ Wplv15b, Ilv15b plv15b llv15b) → ∃ Dlv15b : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15bx1 ∈ Dlv15b.gates, (glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15bx1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Dlv15b) ∧ Set.ncard {jlv15bx3 : ℕ | jlv15bx3 < Dlv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx3 0 = 0) ∨ (∀ hlv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx2 0 = 0))} ≤ mlv15b ∧ Dlv15b.size ≤ Clv15b.size ∧ ((0 < Dlv15b.gates.length ∧ (∀ jlv15bx4 < Dlv15b.gates.length, ∀ ilv15bx4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx4).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx12 : Fin Nlv15b => (plv15bx12 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx11 : Fin Nlv15b => Nlv15b + (llv15bx11 : ℕ)) (Wplv15b)ᶜ)).getD ilv15bx4 0 = 0) ∧ (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx13 : Fin Nlv15b => (plv15bx13 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx12 : Fin Nlv15b => Nlv15b + (llv15bx12 : ℕ)) (Wplv15b)ᶜ)).getD Dlv15b.output 0 = 0) ∧ (∀ plv15bx10 ∈ Splv15b, ∀ llv15bx9 ∈ Wplv15b, Ilv15b plv15bx10 llv15bx9 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx14 : Fin Nlv15b => decide (plv15bx14 ∈ ({plv15bx10} : Finset (Fin Nlv15b)))) (fun llv15bx13 : Fin Nlv15b => decide (llv15bx13 ∈ ({llv15bx9} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx2 Ylv15bx1 : Finset (Fin Nlv15b), Xlv15bx2 ⊆ Splv15b → Ylv15bx1 ⊆ Wplv15b → Ylv15bx1.card ≤ Klv15b → (∀ plv15bx11 ∈ Xlv15bx2, ∀ llv15bx10 ∈ Ylv15bx1, ¬ Ilv15b plv15bx11 llv15bx10) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx15 : Fin Nlv15b => decide (plv15bx15 ∈ Xlv15bx2)) (fun llv15bx14 : Fin Nlv15b => decide (llv15bx14 ∈ Ylv15bx1))) = false))) → (∀ (Nlv16 : ℕ) (Clv16 : PEqualNP.CircuitLowerBounds.Circuit) (Vlv16 : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit), ((∀ glv16x2 ∈ Clv16.gates, (glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) Clv16) → Vlv16 = (fun sglv16x3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv16x2 : Fin Clv16.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv16x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16x1 0 = 0) ∨ (∀ hlv16x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val))) Clv16.output)) → (∀ zlv16 : Fin (Nlv16 + Nlv16) → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) Clv16 zlv16 = true ↔ ∀ sglv16 : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) (Vlv16 sglv16) zlv16 = true) ∧ (∀ sglv16x1 : ℕ → Fin 2, ((∀ glv16x1 ∈ (Vlv16 sglv16x1).gates, (glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) (Vlv16 sglv16x1)) ∧ (∀ jlv16 < (Vlv16 sglv16x1).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∃ ilv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16 0 = 0) ∨ (∀ hlv16x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x2 0 = 0))) ∧ (Vlv16 sglv16x1).size = Clv16.size ∧ ∀ (zlv16x1 : Fin (Nlv16 + Nlv16) → Bool) (wlv16 : ℕ), (Clv16.wires (List.ofFn zlv16x1)).getD wlv16 false = true → ((Vlv16 sglv16x1).wires (List.ofFn zlv16x1)).getD wlv16 false = true) ∧ (∀ (sglv16x2 : ℕ → Fin 2) (glv16 : ℕ), ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD glv16 0 = 0 → 0 < ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD glv16 0 → ∃ Elv16 : Finset ℕ, (∀ hlv16 ∈ Elv16, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16 0 = 0 ∧ (Relation.ReflTransGen (fun alv16 blv16 : ℕ => ∃ jlv16x1 < (Vlv16 sglv16x2).gates.length, blv16 = Nlv16 + Nlv16 + jlv16x1 ∧ alv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD blv16 0 ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD blv16 0) hlv16 glv16)) ∧ ∀ ylv16 : Fin Nlv16 → Bool, ((Vlv16 sglv16x2).wires (List.ofFn (Fin.append (fun ulv16 : Fin Nlv16 => false) ylv16))).getD glv16 false = decide (∃ hlv16x1 ∈ Elv16, (Clv16.wires (List.ofFn (Fin.append (fun ulv16x1 : Fin Nlv16 => false) ylv16))).getD hlv16x1 false = true))) → (∀ (qlv17 Nlv17 Klv17 mlv17 Rlv17 Dlv17 : ℕ) (Ilv17 : Fin Nlv17 → Fin Nlv17 → Prop) [DecidableRel Ilv17] (Clv17 : PEqualNP.CircuitLowerBounds.Circuit) (Slv17 Wlv17 : Finset (Fin Nlv17)), 2 ≤ qlv17 → Nlv17 = qlv17 ^ 2 + qlv17 + 1 → (∀ llv17 : Fin Nlv17, (Finset.univ.filter (fun plv17 => Ilv17 plv17 llv17)).card = qlv17 + 1) → (∀ palv17 pblv17 : Fin Nlv17, palv17 ≠ pblv17 → ∃! lblv17 : Fin Nlv17, Ilv17 palv17 lblv17 ∧ Ilv17 pblv17 lblv17) → ((∀ glv17 ∈ Clv17.gates, (glv17.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17 + Nlv17) Clv17) → Set.ncard {jlv17 : ℕ | jlv17 < Clv17.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17 0 = 0) ∨ (∀ hlv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17 0 = 0))} ≤ mlv17 → ((0 < Clv17.gates.length ∧ (∀ jlv17x1 < Clv17.gates.length, ∀ ilv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x1).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x3 : Fin Nlv17 => (plv17x3 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x3 : Fin Nlv17 => Nlv17 + (llv17x3 : ℕ)) (Wlv17)ᶜ)).getD ilv17x1 0 = 0) ∧ (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x4 : Fin Nlv17 => (plv17x4 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x4 : Fin Nlv17 => Nlv17 + (llv17x4 : ℕ)) (Wlv17)ᶜ)).getD Clv17.output 0 = 0) ∧ (∀ plv17x1 ∈ Slv17, ∀ llv17x1 ∈ Wlv17, Ilv17 plv17x1 llv17x1 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x5 : Fin Nlv17 => decide (plv17x5 ∈ ({plv17x1} : Finset (Fin Nlv17)))) (fun llv17x5 : Fin Nlv17 => decide (llv17x5 ∈ ({llv17x1} : Finset (Fin Nlv17))))) = true) ∧ (∀ Xlv17 Ylv17 : Finset (Fin Nlv17), Xlv17 ⊆ Slv17 → Ylv17 ⊆ Wlv17 → Ylv17.card ≤ Klv17 → (∀ plv17x2 ∈ Xlv17, ∀ llv17x2 ∈ Ylv17, ¬ Ilv17 plv17x2 llv17x2) → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x6 : Fin Nlv17 => decide (plv17x6 ∈ Xlv17)) (fun llv17x6 : Fin Nlv17 => decide (llv17x6 ∈ Ylv17))) = false)) → 2 ^ mlv17 + Dlv17 = Klv17 + 1 → 1 ≤ Dlv17 → 1 ≤ Rlv17 → Rlv17 ≤ qlv17 → (∀ sglv17 : ℕ → Fin 2, ∀ wlv17 ∈ Wlv17, ∀ Xlv17x1 : Finset (Fin Nlv17), Xlv17x1 ⊆ Slv17 → (∀ plv17x7 ∈ Xlv17x1, ¬ Ilv17 plv17x7 wlv17) → Xlv17x1.card ≤ Rlv17 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17x2 : Fin Clv17.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17x2 0 = 0) ∨ (∀ hlv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val))) Clv17.output) (Fin.append (fun plv17x8 : Fin Nlv17 => decide (plv17x8 ∈ Xlv17x1)) (fun llv17x7 : Fin Nlv17 => decide (llv17x7 ∈ ({wlv17} : Finset (Fin Nlv17))))) = false) → Rlv17 * Dlv17 * ((Slv17 ×ˢ Wlv17).filter (fun pllv17 => Ilv17 pllv17.1 pllv17.2)).card ≤ Rlv17 * Dlv17 * Wlv17.card + max (Rlv17 * max (2 * Dlv17) (qlv17 + 1)) (3 * qlv17 * Dlv17) * Clv17.size) → (∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1)) → ∀ (qlv18 Nlv18 klv18 mlv18 alv18 clv18 : ℕ) (Ilv18 : Fin Nlv18 → Fin Nlv18 → Prop) [DecidableRel Ilv18] (Clv18 : PEqualNP.CircuitLowerBounds.Circuit) (Rlv18 : ℕ → ℕ), 2 ≤ qlv18 → Nlv18 = qlv18 ^ 2 + qlv18 + 1 → (∀ llv18 : Fin Nlv18, (Finset.univ.filter (fun plv18 => Ilv18 plv18 llv18)).card = qlv18 + 1) → (∀ palv18 pblv18 : Fin Nlv18, palv18 ≠ pblv18 → ∃! lblv18 : Fin Nlv18, Ilv18 palv18 lblv18 ∧ Ilv18 pblv18 lblv18) → 1 ≤ klv18 → klv18 ≤ qlv18 → ((∀ glv18 ∈ Clv18.gates, (glv18.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv18.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv18.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18 + Nlv18) Clv18) → Set.ncard {jlv18 : ℕ | jlv18 < Clv18.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.Ico Nlv18 (Nlv18 + Nlv18))).getD ilv18x3 0 = 0) ∨ (∀ hlv18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.range Nlv18)).getD hlv18 0 = 0))} ≤ mlv18 → (∀ plv18x1 llv18x1 : Fin Nlv18, Ilv18 plv18x1 llv18x1 → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 (fun klv18x1 => decide (klv18x1 = Fin.castAdd Nlv18 plv18x1 ∨ klv18x1 = Fin.natAdd Nlv18 llv18x1)) = true) → (∀ zlv18 : Fin (Nlv18 + Nlv18) → Bool, (Finset.univ.filter (fun llv18x2 : Fin Nlv18 => zlv18 (Fin.natAdd Nlv18 llv18x2) = true)).card ≤ klv18 → (¬ ∃ plv18x2 llv18x3 : Fin Nlv18, Ilv18 plv18x2 llv18x3 ∧ zlv18 (Fin.castAdd Nlv18 plv18x2) = true ∧ zlv18 (Fin.natAdd Nlv18 llv18x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 zlv18 = false) → (∀ dlv18 < mlv18, 1 ≤ Rlv18 dlv18 ∧ Rlv18 dlv18 ≤ qlv18) → (∀ dlv18x1 elv18x1 : ℕ, dlv18x1 + elv18x1 = mlv18 → 2 ^ elv18x1 + dlv18x1 ≤ klv18 ∧ ∑ ilv18 ∈ Finset.range dlv18x1, (1 + Rlv18 ilv18 * (qlv18 + 1)) < Nlv18) → (∀ dlv18x2 elv18x2 : ℕ, dlv18x2 + elv18x2 + 1 = mlv18 → (alv18 : ℤ) * max ((Rlv18 dlv18x2 : ℤ) * max (2 * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ≤ (clv18 : ℤ) * ((Rlv18 dlv18x2 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1)) * ((Nlv18 : ℤ) - ∑ ilv18x1 ∈ Finset.range dlv18x2, (1 + (Rlv18 ilv18x1 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (dlv18x2 : ℤ)))) → (alv18 : ℤ) * max ((qlv18 : ℤ) * max (2 * ((klv18 : ℤ) - (mlv18 : ℤ))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ))) ≤ (clv18 : ℤ) * ((qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ)) * ((Nlv18 : ℤ) - ∑ ilv18x2 ∈ Finset.range mlv18, (1 + (Rlv18 ilv18x2 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (mlv18 : ℤ))) → alv18 ≤ clv18 * Clv18.size := by
  intro H1 _ H3 H4 q N k m a c I _ C R hq2 hN hline huniq hk1 hkq hAO hcross hacc hrej hR hbud hstage hfinal
  have hm0 := hbud m 0 (by omega)
  have hm1 : m + 1 ≤ k := by
    have h := hm0.1
    rw [pow_zero] at h
    omega
  have key : ∀ e d : ℕ, d + e = m →
      ∀ (Cd : PEqualNP.CircuitLowerBounds.Circuit) (S W : Finset (Fin N)),
      AOx (N + N) Cd →
      Set.ncard {j : ℕ | j < Cd.gates.length ∧ CrP N Cd j} ≤ e →
      Ins N (k - d) I Cd S W → Cd.size ≤ C.size →
      N ≤ W.card + ∑ i ∈ Finset.range d, (1 + R i * (q + 1)) →
      (∀ l ∈ W, q + 1 ≤ (S.filter (fun u => I u l)).card + d) → a ≤ c * C.size := by
    intro e
    induction e with
    | zero =>
      intro d hde Cd S W hA hcr hIn hsz hWc hSc
      have hdm : d = m := by omega
      rw [hdm] at hIn hWc hSc
      have hnc := none_of _ _ hcr
      obtain ⟨hI1, hI2, hI3⟩ := hIn
      have h3 := H3 q N (k - m) 0 q (k - m) I Cd S W hq2 hN hline huniq hA hcr ⟨hI1, hI2, hI3⟩
        (by rw [pow_zero, Nat.add_comm]) (by omega) (by omega) le_rfl
        (by
          intro sg w hw X hX hXI _
          refine (view_eq Cd _ _ (fun j hj => hnc j.val j.isLt hj) _ _).trans ?_
          exact hI3 X {w} hX (Finset.singleton_subset_iff.mpr hw)
            (by
              rw [Finset.card_singleton]
              omega)
            (fun p hp l hl => by
              rw [Finset.mem_singleton.mp hl]
              exact hXI p hp))
      have hinc := inc_ge I S W (q + 1 - m) (fun l hl => by
        have h := hSc l hl
        omega)
      exact arith a c q (k - m) W.card q m _ Cd.size C.size _ N _ _ h3 hinc (by omega) hWc hsz
        (by omega) (le_of_lt hm0.2) (Nat.cast_sub (by omega))
        (by
          push_cast
          first | done | rfl) hfinal
    | succ e ih =>
      intro d hde Cd S W hA hcr hIn hsz hWc hSc
      have hk := hbud d (e + 1) hde
      have hk2 := hbud (d + 1) e (by omega)
      have hRd := hR d (by omega)
      rw [Finset.sum_range_succ] at hk2
      obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 2 ^ (e + 1) := ⟨_, rfl⟩
      have hkP : P + d ≤ k := by
        rw [hP]
        exact hk.1
      have hPz : (2 : ℤ) ^ (e + 1) = (P : ℤ) := by
        rw [hP]
        norm_num
      obtain ⟨D, hD⟩ : ∃ D : ℕ, D = k + 1 - d - P := ⟨_, rfl⟩
      by_contra hgoal
      have h3 := H3 q N (k - d) (e + 1) (R d) D I Cd S W hq2 hN hline huniq hA hcr hIn
        (by
          rw [← hP]
          omega) (by omega) hRd.1 hRd.2
        (by
          intro sg w hw X hX hXI hXc
          by_contra hne
          have htrue := Bool.eq_true_of_not_eq_false hne
          apply hgoal
          obtain ⟨hcW, hcS⟩ := (H4 q N (R d) I S W hq2 hN hline huniq).2 w X hXc
          have hsub := Finset.card_sdiff_add_card_eq_card
            (Finset.filter_subset (fun l => l ≠ w ∧ ∀ p ∈ X, ¬ I p l) W)
          have hex : ∃ p ∈ S.filter (fun u => ¬ I u w ∧ u ∉ X),
              ∃ l ∈ W.filter (fun l => l ≠ w ∧ ∀ p ∈ X, ¬ I p l), I p l := by
            have hpos : 0 < (W.filter (fun l => l ≠ w ∧ ∀ p ∈ X, ¬ I p l)).card := by omega
            obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
            have h1 := hcS l hl
            have h2 := hSc l (Finset.mem_filter.mp hl).1
            have hpos2 : 0 < ((S.filter (fun u => ¬ I u w ∧ u ∉ X)).filter
                (fun u => I u l)).card := by omega
            obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos2
            exact ⟨p, (Finset.mem_filter.mp hp).1, l, hl, (Finset.mem_filter.mp hp).2⟩
          have hkd : k - d = (k - d - 1) + 1 := by omega
          rw [hkd] at hIn
          obtain ⟨D2, hD2a, hD2c, hD2s, hD2i⟩ :=
            H1 N (k - d - 1) e I Cd S W X w sg _ _ hA hcr hIn hw hX hXI htrue rfl rfl hex
          have hkd2 : k - (d + 1) = k - d - 1 := by omega
          refine ih (d + 1) (by omega) D2 (S.filter (fun u => ¬ I u w ∧ u ∉ X))
            (W.filter (fun l => l ≠ w ∧ ∀ p ∈ X, ¬ I p l)) hD2a hD2c ?_ (le_trans hD2s hsz) ?_ ?_
          · rw [hkd2]
            exact hD2i
          · rw [Finset.sum_range_succ]
            omega
          · intro l hl
            have h1 := hcS l hl
            have h2 := hSc l (Finset.mem_filter.mp hl).1
            omega)
      have hinc := inc_ge I S W (q + 1 - d) (fun l hl => by
        have h := hSc l hl
        omega)
      refine hgoal (arith a c (R d) D W.card q d _ Cd.size C.size _ N _ _ h3 hinc (by omega) hWc hsz
        hRd.1 (le_of_lt hk.2) ?_ ?_ (hstage d e (by omega)))
      · rw [hPz, hD]
        omega
      · push_cast
        first | done | rfl
  have hNpos : 7 ≤ N := by
    have h4 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq2 hq2
    rw [hN, pow_two]
    omega
  have hpos : 0 < C.gates.length := by
    by_contra h0
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨l1, hl1⟩ : ∃ l1 : Fin N, l1.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨l2, hl2⟩ : ∃ l2 : Fin N, l2.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
    obtain ⟨p1, hp1⟩ : (Finset.univ.filter (fun p => I p l1)).Nonempty :=
      Finset.card_pos.mp (by
        rw [hline]
        omega)
    obtain ⟨p2, hp2⟩ : ((Finset.univ.filter (fun p => I p l2)).erase p1).Nonempty :=
      Finset.card_pos.mp (by
        have h := Finset.pred_card_le_card_erase (s := Finset.univ.filter (fun p => I p l2)) (a := p1)
        rw [hline] at h
        omega)
    have hI1 := (Finset.mem_filter.mp hp1).2
    have hI2 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp2)).2
    have hne : p2 ≠ p1 := Finset.ne_of_mem_erase hp2
    have ho1 := acc_out C hg p1 l1 (hacc p1 l1 hI1)
    have ho2 := acc_out C hg p2 l2 (hacc p2 l2 hI2)
    have hv : p2.val ≠ p1.val := fun h => hne (Fin.ext h)
    have hb1 := p1.isLt
    have hb2 := p2.isLt
    omega
  refine key m 0 (by omega) C Finset.univ Finset.univ hAO hcross ?_ le_rfl (by simp) (fun l _ => by
    have h := hline l
    omega)
  refine ⟨⟨hpos, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj i hi
    simp only [Finset.compl_univ, Finset.image_empty, Finset.union_empty]
    exact ld_zero C (N + N) i
  · simp only [Finset.compl_univ, Finset.image_empty, Finset.union_empty]
    exact ld_zero C (N + N) C.output
  · intro p _ l _ hI
    rw [ind_eq N p l]
    exact hacc p l hI
  · intro X Y _ _ hYc hXY
    refine hrej _ ?_ ?_
    · have h1 : (Finset.univ.filter (fun l : Fin N =>
          Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y))
            (Fin.natAdd N l) = true)) = Y := by
        ext l
        rw [Finset.mem_filter, Fin.append_right]
        simp
      rw [h1]
      omega
    · rintro ⟨p, l, hI, hp, hl⟩
      rw [Fin.append_left] at hp
      rw [Fin.append_right] at hl
      exact hXY p (by simpa using hp) l (by simpa using hl) hI
