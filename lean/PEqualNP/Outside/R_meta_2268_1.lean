import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Strip and restore each isolated OR input, charging one gate in each direction.
-- Reindex the remaining graph on its non-isolated vertices, then apply the small
-- circuit case or the explicit star bound, according to the remaining gate budget.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2268_1
    (bare : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (e : (Fin n → Bool) → Bool),
      30 ≤ n → Even n → G.Colorable 2 →
      (∀ i, (G.neighborSet i).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∃ i j, G.Adj i j) →
      (∀ x, e x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, s+1 < 2*n → HasCircuitSize n e s → ∃ u v : Fin n,
        u ≠ v ∧ ¬G.Adj u v ∧
        ∃ t, t + 8 ≤ s ∧ HasCircuitSize n
          (fun x => e (Function.update (Function.update x u false) v false)) t)
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (e : (Fin n → Bool) → Bool),
      G.Colorable 2 → (∀ i, (G.neighborSet i).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∃ i j, G.Adj i j) →
      (∀ x, e x = true ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      30 ≤ n ∧ Even n ∧ ∃ p q : Fin n, p ≠ q ∧ ¬G.Adj p q ∧ ∃ t, t+9 ≤ 2*n ∧
        HasCircuitSize n (fun x => e (Function.update (Function.update x p false) q false)) t)
    (rewire : ∀ (n m : ℕ) (r : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (k : ℕ),
      HasCircuitSize n h k → HasCircuitSize m (fun x => h (fun i => x (r i))) k)
    (orCost : (∀ (n : ℕ) (h : (Fin n → Bool) → Bool) (s : ℕ),
      HasCircuitSize n h s → ∀ p : Fin n, HasCircuitSize n (fun x => h x || x p) (s+1)) ∧
      ( ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (p : Fin n),
      HasCircuitSize n F s →
      (∃ x, F (Function.update x p false) ≠ F (Function.update x p true)) →
      (∃ x y, F (Function.update x p false) ≠ F (Function.update y p false)) →
      1 ≤ s ∧ HasCircuitSize n (fun x => F (Function.update x p false)) (s-1)))
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  obtain ⟨addOr,charge⟩ := orCost
  intro n G A f color deg girth isolated edge spec s size
  classical
  let E (x : Fin n → Bool) := decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
  let bits (T : Finset (Fin n)) (x : Fin n → Bool) := decide (∃ a ∈ T, x a = true)
  let F (T : Finset (Fin n)) (x : Fin n → Bool) := E x || bits T x
  have eqF : f = F A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simpa [F,E,bits,or_comm] using spec x
  have bitsIns (T : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool) :
      bits (insert p T) x = (bits T x || x p) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bits,Bool.or_eq_true,decide_eq_true_eq]
    rw [Finset.exists_mem_insert]
    exact or_comm
  have insertF (T : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool) :
      F (insert p T) x = (F T x || x p) := by
    simp only [F,bitsIns,Bool.or_assoc]
  have unchanged (T : Finset (Fin n)) (p : Fin n) (hp : p ∈ A) (outside : p ∉ T)
      (x : Fin n → Bool) (b : Bool) : F T (Function.update x p b) = F T x := by
    have sep {i j : Fin n} (h : G.Adj i j) : i ≠ p ∧ j ≠ p := by
      exact ⟨fun e => isolated i j h (e ▸ hp),fun e => isolated j i h.symm (e ▸ hp)⟩
    apply Bool.eq_iff_iff.mpr
    simp only [F,E,bits,Bool.or_eq_true,decide_eq_true_eq]
    apply or_congr
    · apply exists_congr; intro i
      apply exists_congr; intro j
      apply and_congr_right; intro adj
      rw [Function.update_of_ne (sep adj).1,Function.update_of_ne (sep adj).2]
    · apply exists_congr; intro i
      apply and_congr_right; intro mem
      rw [Function.update_of_ne (show i ≠ p from fun he => outside (he ▸ mem))]
  have zero (T : Finset (Fin n)) : F T (fun _ => false) = false := by simp [F,E,bits]
  have one (T : Finset (Fin n)) : F T (fun _ => true) = true := by simp [F,E,edge]
  have strip (T : Finset (Fin n)) : T ⊆ A → ∀ k, HasCircuitSize n (F T) k →
      T.card ≤ k ∧ HasCircuitSize n E (k-T.card) := by
    induction T using Finset.induction_on with
    | empty =>
      intro _ k hk
      have nilF : F ∅ = E := by funext x; simp [F,bits]
      simpa [nilF] using hk
    | @insert p T outside ih =>
      intro subset k hk
      have hp := subset (Finset.mem_insert_self p T)
      have hT : T ⊆ A := fun i hi => subset (Finset.mem_insert_of_mem hi)
      have off (x : Fin n → Bool) : F (insert p T) (Function.update x p false) = F T x := by
        rw [insertF,unchanged _ _ hp outside,Function.update_self,Bool.or_false]
      have on (x : Fin n → Bool) : F (insert p T) (Function.update x p true) = true := by
        rw [insertF,Function.update_self,Bool.or_true]
      obtain ⟨pos,hrest⟩ := charge n k (F (insert p T)) p hk
        ⟨fun _ => false,by rw [off,on,zero]; decide⟩
        ⟨fun _ => false,fun _ => true,by rw [off,off,zero,one]; decide⟩
      rw [show (fun x => F (insert p T) (Function.update x p false)) = F T from funext off] at hrest
      obtain ⟨le,core⟩ := ih hT (k-1) hrest
      rw [Finset.card_insert_of_notMem outside]
      exact ⟨by omega,by convert core using 1; omega⟩
  obtain ⟨card,core⟩ := strip A (Finset.Subset.refl A) s (eqF ▸ size)
  -- Index only the vertices outside A. On an unused input the map back
  -- may choose any active vertex because every edge avoids A.
  obtain ⟨a,b,ab⟩ := edge
  let U := {v : Fin n // v ∉ A}
  let m := Fintype.card U
  let e : Fin m ≃ U := (Fintype.equivFin U).symm
  let emb (v : Fin m) : Fin n := (e v).val
  have hinj : Function.Injective emb := fun _ _ h => e.injective (Subtype.ext h)
  let back (i : Fin n) : Fin m := if h : i ∉ A then e.symm ⟨i,h⟩ else e.symm ⟨a,isolated a b ab⟩
  have inU (v : Fin m) : emb v ∉ A := (e v).property
  have section_back (v : Fin m) : back (emb v) = v := by
    simp only [back,dite_eq_left (inU v)]
    exact e.symm_apply_apply v
  have section_emb (i : Fin n) (hi : i ∉ A) : emb (back i) = i := by
    simp [emb,back,hi]
  let H : SimpleGraph (Fin m) := G.comap emb
  let hom : H →g G := ⟨emb,fun h => h⟩
  have degH (v : Fin m) : (H.neighborSet v).ncard = 3 := by
    rw [← deg (emb v) (inU v)]
    apply Set.ncard_congr (fun q _ => emb q) (fun _ h => h) (fun _ _ _ _ h => hinj h)
    intro z hz
    change G.Adj (emb v) z at hz
    have rev := section_emb z (isolated _ _ hz.symm)
    refine ⟨back z,?_,rev⟩
    change G.Adj (emb v) (emb (back z))
    rwa [rev]
  have girthH (v : Fin m) (c : H.Walk v v) (cycle : c.IsCycle) : 7 ≤ c.length := by
    have injective : Function.Injective hom := hinj
    simpa using girth (emb v) (c.map hom) (cycle.map injective)
  have edgeH : ∃ i j, H.Adj i j := by
    refine ⟨back a,back b,?_⟩
    change G.Adj (emb (back a)) (emb (back b))
    rwa [section_emb _ (isolated _ _ ab),section_emb _ (isolated _ _ ab.symm)]
  let pure (y : Fin m → Bool) := E (fun i => y (back i))
  have pureSpec (y : Fin m → Bool) :
      pure y = true ↔ ∃ i j, H.Adj i j ∧ y i = true ∧ y j = true := by
    simp only [pure,E,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,oneI,oneJ⟩
      refine ⟨back i,back j,?_,oneI,oneJ⟩
      change G.Adj (emb (back i)) (emb (back j))
      rwa [section_emb _ (isolated _ _ ij),section_emb _ (isolated _ _ ij.symm)]
    · rintro ⟨i,j,ij,oneI,oneJ⟩
      exact ⟨emb i,emb j,ij,by rwa [section_back],by rwa [section_back]⟩
  have smallPure : HasCircuitSize m pure (s-A.card) := rewire n m back E _ core
  have colH := SimpleGraph.Colorable.of_hom hom color
  obtain ⟨order,even,p0,q0,neq0,far0,t0,bound0,small0⟩ := geometry m H pure colH degH girthH edgeH pureSpec
  have split : ∃ p q : Fin m, p ≠ q ∧ ¬H.Adj p q ∧ ∃ t, t+8 ≤ s-A.card ∧
      HasCircuitSize m (fun x => pure (Function.update (Function.update x p false) q false)) t := by
    by_cases below : (s-A.card)+1 < 2*m
    · exact bare m H pure order even colH degH girthH edgeH pureSpec _ below smallPure
    · exact ⟨p0,q0,neq0,far0,t0,by omega,small0⟩
  obtain ⟨p,q,pq,nonedge,t,save,short⟩ := split
  let u := emb p
  let v := emb q
  have hu : u ∉ A := inU p
  have hv : v ∉ A := inU q
  have ne : u ≠ v := fun eq => pq (hinj eq)
  have far : ¬G.Adj u v := nonedge
  let residual (x : Fin n → Bool) := E (Function.update (Function.update x u false) v false)
  have lifted := rewire m n emb _ t short
  have reduced : HasCircuitSize n residual t := by
    convert lifted using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [residual,pure,E,decide_eq_true_eq]
    have agrees (i : Fin n) (hi : i ∉ A) :
        (Function.update (Function.update x u false) v false) i =
        (Function.update (Function.update (fun j => x (emb j)) p false) q false) (back i) := by
      by_cases eq : i = emb q
      · subst i; simp [v,section_back]
      have neq : back i ≠ q := fun w => eq ((section_emb i hi).symm.trans (congrArg emb w))
      rw [Function.update_of_ne (show i ≠ v from eq),Function.update_of_ne neq]
      by_cases eq' : i = emb p
      · subst i; simp [u,section_back]
      have neq' : back i ≠ p := fun w => eq' ((section_emb i hi).symm.trans (congrArg emb w))
      rw [Function.update_of_ne (show i ≠ u from eq'),Function.update_of_ne neq',section_emb i hi]
    apply exists_congr; intro i
    apply exists_congr; intro j
    apply and_congr_right; intro ij
    rw [agrees i (isolated i j ij),agrees j (isolated j i ij.symm)]
  have restore (T : Finset (Fin n)) :
      HasCircuitSize n (fun x => residual x || bits T x) (t + T.card) := by
    induction T using Finset.induction_on with
    | empty => simpa [bits,residual] using reduced
    | @insert p T hp ih =>
      have next := addOr n _ _ ih p
      rw [Finset.card_insert_of_notMem hp]
      convert next using 1
      · funext x
        simp only [bitsIns,Bool.or_assoc]
  refine ⟨u,v,hu,hv,ne,far,t+A.card,by omega,?_⟩
  have restoreA := restore A
  have complete : (fun x => f (Function.update (Function.update x u false) v false)) =
      (fun x => residual x || bits A x) := by
    funext x
    rw [eqF]
    apply congrArg (fun b => residual x || b)
    apply Bool.eq_iff_iff.mpr
    simp only [bits,decide_eq_true_eq]
    apply exists_congr; intro a
    apply and_congr_right; intro ha
    rw [Function.update_of_ne (show a ≠ v from fun e => hv (e ▸ ha)),Function.update_of_ne (show a ≠ u from fun e => hu (e ▸ ha))]
  rw [complete]
  exact restoreA
