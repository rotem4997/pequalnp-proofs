import Mathlib

namespace PEqualNP.Outside.TwoRow

open Module

private abbrev Vec (I : Type) := I → ℂ
private abbrev Rows (I : Type) := Vec I × Vec I
private def total {I : Type} (w : Rows I) : Vec I := w.1 + w.2
private def crossTerm {I : Type} (w v : Rows I) : Vec I := w.1 * v.2 + v.1 * w.2

private def form {I : Type} [Fintype I] (c : Vec I) : LinearMap.BilinForm ℂ (Rows I) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ i, c i * (w.1 i * v.2 i + v.1 i * w.2 i))
    (by intro u v w; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
        intro i _; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intro a v w; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)
    (by intro u v w; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
        intro i _; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (by intro a v w; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring)

private theorem form_nondegenerate {I : Type} [Fintype I] (c : Vec I) (hc : ∀ i, c i ≠ 0) :
    (form c).Nondegenerate := by
  classical
  have symm (u v : Rows I) : form c u v = form c v u := by
    simp only [form, LinearMap.mk₂_apply]; apply Finset.sum_congr rfl; intro i _; ring
  have left : (form c).SeparatingLeft := by
    intro u hu
    apply Prod.ext <;> funext i
    · have h := hu (0, Pi.single i 1)
      simpa [form, Pi.single_apply, mul_ite, hc] using h
    · have h := hu (Pi.single i 1, 0)
      simpa [form, Pi.single_apply, ite_mul, mul_ite, hc] using h
  exact ⟨left, fun u hu => left u fun v => (symm u v).trans (hu v)⟩

-- A minimal set of coordinates on which the all-ones vector cannot be interpolated.
private theorem block_bound {I : Type} [Fintype I] [DecidableEq I]
    (U : Submodule ℂ (Vec I)) (P : Submodule ℂ (Rows I))
    (hone : (1 : Vec I) ∉ U)
    (hremove : ∀ i : I, ∃ u ∈ U, ∀ j ≠ i, u j = 1)
    (hs : ∀ w ∈ P, total w ∈ U)
    (hb : ∀ w ∈ P, ∀ v ∈ P, crossTerm w v ∈ U) :
    finrank ℂ P ≤ finrank ℂ U := by
  classical
  have hn : U.mkQ (1 : Vec I) ≠ 0 := by simpa using hone
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hn
  let f := l.comp U.mkQ
  have fone : f (1 : Vec I) = 1 := hl
  have fz {u : Vec I} (hu : u ∈ U) : f u = 0 := by simp [f, (Submodule.Quotient.mk_eq_zero _).mpr hu]
  let e (i : I) : Vec I := Pi.single i 1
  let c (i : I) := f (e i)
  let V := U ⊔ Submodule.span ℂ ({1} : Set (Vec I))
  have oneV : (1 : Vec I) ∈ V := (show Submodule.span ℂ ({1} : Set (Vec I)) ≤ V from le_sup_right) (Submodule.subset_span (by simp))
  have facts (i : I) : c i ≠ 0 ∧ e i ∈ V := by
    obtain ⟨u, hu, h⟩ := hremove i
    let d := 1 - u i
    have diff : d • e i = 1 - u := by
      funext j
      by_cases hj : j = i
      · subst j; simp [d,e]
      · simp [e,Pi.single_eq_of_ne hj, h j hj]
    have val : d * c i = 1 := by
      calc d * c i = f (d • e i) := (f.map_smul d (e i)).symm
           _ = 1 := by rw [diff, map_sub, fone, fz hu, sub_zero]
    have hd : d ≠ 0 := by intro he; simp [he] at val
    have hc : c i ≠ 0 := by intro he; simp [he] at val
    have hm : d • e i ∈ V := diff ▸ V.sub_mem oneV ((show U ≤ V from le_sup_left) hu)
    exact ⟨hc, by simpa [hd] using V.smul_mem d⁻¹ hm⟩
  have decomp (x : Vec I) : ∑ i, x i • e i = x := by
    funext j; simp [e, Finset.sum_apply, Pi.single_apply, mul_ite]
  have feval (x : Vec I) : f x = ∑ i, c i * x i := by
    calc f x = f (∑ i, x i • e i) := congrArg f (decomp x).symm
         _ = _ := by simp [c, mul_comm, smul_eq_mul]
  have Vtop : V = ⊤ := by
    apply top_unique; intro x _
    rw [← decomp x]; exact V.sum_mem fun i _ => V.smul_mem _ (facts i).2
  have hdim := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span ℂ ({1} : Set (Vec I)))
  have one_ne : (1 : Vec I) ≠ 0 := fun h => hone (h ▸ U.zero_mem)
  rw [show U ⊔ _ = ⊤ from Vtop, finrank_top, finrank_span_singleton one_ne] at hdim
  let B := form c
  have ev (u v : Rows I) : B u v = f (crossTerm u v) := (feval _).symm
  have iso : P ≤ B.orthogonal P := fun v hv w hw => (ev w v).trans (fz (hb w hw v hv))
  let t : Rows I := (1, 1)
  have et (w : Rows I) : B w t = f (total w) := by simp [ev, t, crossTerm, total]
  have ht : t ∈ B.orthogonal P := fun w hw => (et w).trans (fz (hs w hw))
  have hnP : t ∉ P := by
    intro h
    have h0 := fz (hs t h)
    simp [t, total, fone] at h0
  have strict := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne iso (fun h => hnP (h ▸ ht)))
  rw [LinearMap.BilinForm.finrank_orthogonal (form_nondegenerate c (fun i => (facts i).1)),
      Module.finrank_prod] at strict
  omega

private theorem split_rank {X Y : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (W : Submodule ℂ X) (p : X →ₗ[ℂ] Y) :
    finrank ℂ (W.map p) + finrank ℂ (W ⊓ p.ker : Submodule ℂ X) = finrank ℂ W := by
  have h := (p.domRestrict W).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, ← W.finrank_map_subtype_eq, LinearMap.ker_domRestrict,
    Submodule.map_comap_subtype] at h
  exact h

private def projectVec {I : Type} (S : Finset I) : Vec I →ₗ[ℂ] Vec S where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def projectRows {I : Type} (S : Finset I) : Rows I →ₗ[ℂ] Rows S :=
  (projectVec S).prodMap (projectVec S)

private theorem bound {I : Type} [Fintype I] [DecidableEq I]
    (A : Finset I) (R : Submodule ℂ (Rows I)) (W : Submodule ℂ (Vec I))
    (hr : ∀ w ∈ R, ∀ i ∉ A, w.1 i = 0 ∧ w.2 i = 0)
    (hw : ∀ x ∈ W, ∀ i ∉ A, x i = 0)
    (hz : ∀ x ∈ W, ∑ i, x i = 0)
    (hs : ∀ w ∈ R, total w ∈ W)
    (hb : ∀ w ∈ R, ∀ v ∈ R, crossTerm w v ∈ W) :
    finrank ℂ R ≤ finrank ℂ W := by
  classical
  induction A using Finset.strongInductionOn generalizing R W with | _ A ih
  by_cases he : A = ∅
  · have hbot : R = ⊥ := by
      apply le_antisymm _ bot_le
      intro w hw'
      apply Prod.ext <;> funext i
      · exact (hr w hw' i (by simp [he])).1
      · exact (hr w hw' i (by simp [he])).2
    rw [hbot, finrank_bot]; exact Nat.zero_le _
  let bad (S : Finset I) := ¬ ∃ x ∈ W, ∀ i ∈ S, x i = 1
  have badA : bad A := by
    rintro ⟨x, hx, h⟩
    have hsum := hz x hx
    rw [← Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => hw x hx i hi),
        Finset.sum_congr rfl h] at hsum
    exact he (by simpa using hsum)
  let candidates := A.powerset.filter bad
  have inC (T : Finset I) : T ∈ candidates ↔ T ⊆ A ∧ bad T := by simp [candidates]
  obtain ⟨S, hS, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, (inC A).2 ⟨by rfl, badA⟩⟩
  obtain ⟨hSA, hbad⟩ := (inC S).1 hS
  have nonempty : S.Nonempty := by
    by_contra! hn
    exact hbad ⟨0, W.zero_mem, by simp [hn]⟩
  let p := projectVec S
  let r := projectRows S
  have dim : finrank ℂ (R.map r) ≤ finrank ℂ (W.map p) := by
    apply block_bound
    · rintro ⟨x, hx, eq⟩
      exact hbad ⟨x, hx, fun i hi => congrFun eq ⟨i,hi⟩⟩
    · intro i
      have good : ¬ bad (S.erase i.val) := by
        intro h
        have hle := hmin _ ((inC _).2 ⟨(Finset.erase_subset _ _).trans hSA,h⟩)
        exact (Finset.card_erase_lt_of_mem i.property).not_ge hle
      obtain ⟨x, hx, agrees⟩ := Classical.byContradiction good
      refine ⟨p x, ⟨x,hx,rfl⟩, fun j hj => agrees j ?_⟩
      exact Finset.mem_erase.mpr ⟨fun eq => hj (Subtype.ext eq), j.property⟩
    · rintro _ ⟨w, hw', rfl⟩; exact ⟨total w, hs w hw', rfl⟩
    · rintro _ ⟨w, hw', rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨crossTerm w v, hb w hw' v hv, rfl⟩
  have ltA : A \ S ⊂ A := by
    obtain ⟨i, hi⟩ := nonempty
    exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => by
      have : i ∈ A \ S := by rw [h]; exact hSA hi
      exact (Finset.mem_sdiff.mp this).2 hi⟩
  have rz {w : Rows I} (h : w ∈ r.ker) (i : S) : w.1 i = 0 ∧ w.2 i = 0 :=
    ⟨congrFun (congrArg Prod.fst (show r w = 0 from h)) i,
     congrFun (congrArg Prod.snd (show r w = 0 from h)) i⟩
  have wz {x : Vec I} (h : x ∈ p.ker) (i : S) : x i = 0 := congrFun (show p x = 0 from h) i
  have rest : finrank ℂ (R ⊓ r.ker : Submodule ℂ (Rows I)) ≤
      finrank ℂ (W ⊓ p.ker : Submodule ℂ (Vec I)) := by
    apply ih (A \ S) ltA
    · intro w h i hi
      by_cases hS : i ∈ S
      · exact rz h.2 ⟨i,hS⟩
      · exact hr w h.1 i (fun ha => hi (Finset.mem_sdiff.mpr ⟨ha,hS⟩))
    · intro x h i hi
      by_cases hS : i ∈ S
      · exact wz h.2 ⟨i,hS⟩
      · exact hw x h.1 i (fun ha => hi (Finset.mem_sdiff.mpr ⟨ha,hS⟩))
    · intro x h; exact hz x h.1
    · intro w h
      refine ⟨hs w h.1, show p (total w) = 0 from ?_⟩
      funext i
      change w.1 i + w.2 i = 0
      simp [(rz h.2 i).1, (rz h.2 i).2]
    · intro w h v hv
      refine ⟨hb w h.1 v hv.1, show p (crossTerm w v) = 0 from ?_⟩
      funext i
      change w.1 i * v.2 i + v.1 i * w.2 i = 0
      simp [(rz h.2 i).1, (rz h.2 i).2]
  rw [← split_rank R r, ← split_rank W p]
  exact Nat.add_le_add dim rest

end PEqualNP.Outside.TwoRow

open PEqualNP.Outside.TwoRow

theorem PEqualNP.Outside.L_gct_153 : ∀ (q : ℕ) (R : Submodule ℂ ((Fin q → ℂ) × (Fin q → ℂ))), (∀ w ∈ R, ∀ w' ∈ R, (Finset.univ.sum fun j : Fin q => w.1 j * w'.2 j + w'.1 j * w.2 j) = 0) → (∀ w ∈ R, (Finset.univ.sum fun j : Fin q => w.1 j + w.2 j) = 0) → Module.finrank ℂ R ≤ Module.finrank ℂ (Submodule.span ℂ ({x : Fin q → ℂ | ∃ w ∈ R, x = fun j : Fin q => w.1 j + w.2 j} ∪ {x : Fin q → ℂ | ∃ w ∈ R, ∃ w' ∈ R, x = fun j : Fin q => w.1 j * w'.2 j + w'.1 j * w.2 j})) := by
  classical
  intro q R hb hs
  apply bound Finset.univ R
  · simp
  · simp
  · intro x hx
    let sumL : Vec (Fin q) →ₗ[ℂ] ℂ :=
      ∑ i : Fin q, LinearMap.proj (R := ℂ) (φ := fun _ : Fin q => ℂ) i
    suffices hle : _ ≤ sumL.ker by
      have hzero : x ∈ sumL.ker := hle hx
      simpa [sumL, LinearMap.mem_ker] using hzero
    apply Submodule.span_le.mpr
    rintro x (⟨w, hw, rfl⟩ | ⟨w, hw, v, hv, rfl⟩)
    · simpa [sumL, LinearMap.mem_ker] using hs w hw
    · simpa [sumL, LinearMap.mem_ker] using hb w hw v hv
  · intro w hw
    exact Submodule.subset_span (Or.inl ⟨w, hw, rfl⟩)
  · intro w hw v hv
    exact Submodule.subset_span (Or.inr ⟨w, hw, v, hv, rfl⟩)
