import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.NotPremium

theorem PEqualNP.Outside.R_meta_2001_829
  (clean : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ C : Circuit, Monotone2 C →
    (∀ u : Fin n, circuitFun n C (pairInput u u) = false) →
    (∀ j, j < C.size → (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, gateVal n C j (pairInput u v) = true → G.Adj u v) →
    ∃ D : Circuit, Monotone2 D ∧ D.output < n+n+D.size ∧ D.size+1 ≤ c*(C.size+1) ∧
      ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) = decide
        (∃ u v : Fin n, G.Adj u v ∧ circuitFun n C (pairInput u v) = true ∧
          x u = true ∧ y v = true))
  (price : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    let f := fun (C : Circuit) (u v : Fin n) => circuitFun n C (pairInput u v)
    let bad := fun (C : Circuit) j => j < C.size ∧ (gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
    ∀ C : Circuit, Monotone2 C → (∀ u v, f C u v = true → G.Adj u v) →
    (∃ j, bad C j) → ∃ j, bad C j ∧ ∃ D E : Circuit,
      Monotone2 D ∧ D.size < C.size ∧
      (∀ u v, f D u v = f ⟨replaceByConst C.gates j false,C.output⟩ u v) ∧
      (∀ u v, f D u v = true → f C u v = true) ∧
      Monotone2 E ∧ E.output < n+n+E.size ∧ E.size+1 ≤ k*(C.size-D.size) ∧
      ∀ x y : Fin n → Bool, E.eval (List.ofFn x ++ List.ofFn y) = decide
        (∃ u v : Fin n, f C u v = true ∧ f D u v = false ∧ x u = true ∧ y v = true))
  (join : ∀ (n : ℕ) (A B : Circuit), Monotone2 A → Monotone2 B →
    A.output < n+n+A.size → B.output < n+n+B.size →
    ∃ D : Circuit, Monotone2 D ∧ D.output < n+n+D.size ∧ D.size ≤ A.size+B.size+1 ∧
      ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) =
        (A.eval (List.ofFn x ++ List.ofFn y) || B.eval (List.ofFn x ++ List.ofFn y))) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  classical
  obtain ⟨a,hclean⟩ := clean
  obtain ⟨b,hprice⟩ := price
  let k := max a b
  refine ⟨k,?_⟩
  intro n G _ hd hg C hM hF
  let f := fun (C : Circuit) (u v : Fin n) => circuitFun n C (pairInput u v)
  have lift : ∀ s, ∀ C : Circuit, C.size = s → Monotone2 C →
      (∀ u v, f C u v = true → G.Adj u v) →
      ∃ D : Circuit, Monotone2 D ∧ D.output < n+n+D.size ∧ D.size+1 ≤ k*(C.size+1) ∧
        ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) = decide
          (∃ u v : Fin n, f C u v = true ∧ x u = true ∧ y v = true) := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro C hs hM hsafe
      by_cases hc : ∀ j, j < C.size → (gateAt C j).op = GateOp.and →
          ∀ u v : Fin n, gateVal n C j (pairInput u v) = true → G.Adj u v
      · have hsingle : ∀ u : Fin n, circuitFun n C (pairInput u u) = false := by
          intro u
          cases hh : f C u u with
          | false => exact hh
          | true => exact False.elim ((G.loopless.irrefl u) (hsafe u u hh))
        obtain ⟨D,hD,ho,hsize,he⟩ := hclean n G hg C hM hsingle hc
        refine ⟨D,hD,ho,hsize.trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)),?_⟩
        intro x y
        rw [he,decide_eq_decide]
        constructor
        · rintro ⟨u,v,_,hf,hx,hy⟩
          exact ⟨u,v,hf,hx,hy⟩
        · rintro ⟨u,v,hf,hx,hy⟩
          exact ⟨u,v,hsafe u v hf,hf,hx,hy⟩
      · have hbad : ∃ j, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
            ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
          push_neg at hc
          obtain ⟨j,hj,hop,u,v,hval,hn⟩ := hc
          exact ⟨j,hj,hop,u,v,hn,hval⟩
        obtain ⟨j,hj,D,E,hD,hsD,_,hsub,hE,hoE,hsE,heE⟩ :=
          hprice n G hd hg C hM hsafe hbad
        have hsafeD : ∀ u v, f D u v = true → G.Adj u v :=
          fun u v h => hsafe u v (hsub u v h)
        obtain ⟨B,hB,hoB,hsB,heB⟩ := ih D.size (by omega) D rfl hD hsafeD
        obtain ⟨F,hFM,hoF,hsF,heF⟩ := join n B E hB hE hoB hoE
        refine ⟨F,hFM,hoF,?_,?_⟩
        · have hEs : E.size+1 ≤ k*(C.size-D.size) :=
            hsE.trans (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
          have hcalc : k*(D.size+1)+k*(C.size-D.size) = k*(C.size+1) := by
            rw [← Nat.mul_add]
            congr 1
            omega
          omega
        · intro x y
          rw [heF,heB,heE,Bool.eq_iff_iff]
          simp only [Bool.or_eq_true,decide_eq_true_eq]
          constructor
          · rintro (⟨u,v,huv,hx,hy⟩ | ⟨u,v,huv,_,hx,hy⟩)
            · exact ⟨u,v,hsub u v huv,hx,hy⟩
            · exact ⟨u,v,huv,hx,hy⟩
          · rintro ⟨u,v,huv,hx,hy⟩
            cases hh : f D u v with
            | false => exact Or.inr ⟨u,v,huv,hh,hx,hy⟩
            | true => exact Or.inl ⟨u,v,hh,hx,hy⟩
  have hpair : ∀ u v : Fin n, f C u v = decide (G.Adj u v) := by
    intro u v
    change C.eval (List.ofFn (pairInput u v)) = _
    rw [hF,decide_eq_decide]
    change (∃ p q : Fin n, G.Adj p q ∧ decide (p = u ∨ p = v) = true ∧
      decide (q = u ∨ q = v) = true) ↔ G.Adj u v
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p,q,hpq,(rfl | rfl),(rfl | rfl)⟩
      · exact False.elim (G.loopless.irrefl _ hpq)
      · exact hpq
      · exact hpq.symm
      · exact False.elim (G.loopless.irrefl _ hpq)
    · intro huv
      exact ⟨u,v,huv,Or.inl rfl,Or.inr rfl⟩
  obtain ⟨D,hD,_,hs,he⟩ := lift C.size C rfl hM (fun u v h => by
    rw [hpair,decide_eq_true_eq] at h
    exact h)
  refine ⟨D,hD,hs,?_⟩
  intro x y
  rw [he]
  simp only [hpair,decide_eq_true_eq]
