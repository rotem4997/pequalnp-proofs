import Mathlib.Combinatorics.Pigeonhole
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5365_619
    (support : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∃ V : Finset (Fin n), V.card ≤ C.size + 1 ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ V, x i = y i) → circuitFun n C x = circuitFun n C y)
    (core : ∃ r d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ →
      ∀ E ⊆ G.edgeFinset, (∀ v : Fin n, let s := (E.filter fun e => v ∈ e).card; s = 0 ∨ d < s) →
      (∀ u v : Fin n, s(u,v) ∈ E → ∀ j : Fin C.gates.length, Owns n C j.val u v →
        ∃ S : Finset (Fin n), (∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) ∧
        ∃ f : Fin (r+1) → Fin n × Fin n, ∃ K : Finset (Fin n), K.card ≤ 1 ∧ K ⊆ {u,v} ∧
          (∀ i, let p := f i
            p.1 ∈ S ∧ p.2 ∈ S ∧ gateVal n C j.val (pairInput p.1 p.2) = true) ∧
          (∀ i j, i ≠ j → ({(f i).1,(f i).2} : Finset _) ∩ {(f j).1,(f j).2} = K)) →
      E.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             ∃ (x21 : Finset (Fin x3)), Maximal (fun (x22 : Finset (Fin x3)) => ∀ x23 ∈ x22, ∀ x25 ∈ x22, ¬x4.Adj x23 x25) x21 ∧ ∀ (x22 : Finset (Fin x3)), x22.card ≤ x1 → x15 ∉ x22 → x16 ∉ x22 → ∃ x26 ∈ x21 \ x22, ∃ x27 ∈ x21 \ x22, x20 x26 x27) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  obtain ⟨r,d,c,core⟩ := core
  refine ⟨4*r+2,d+c,?_⟩
  intro n G dec deg girth C minimal computes E sub persists
  obtain ⟨V,Vcost,Vdep⟩ := support n C minimal.1
  have pairEval (a b i : Fin n) : pairInput a b i = decide (i=a ∨ i=b) := rfl
  have incident (a b : Fin n) (edge : G.Adj a b) : a ∈ V := by
    by_contra outside
    let x := pairInput a b
    let y := pairInput b b
    have eqv := Vdep x y (by
      intro i hi
      have ne : i ≠ a := fun e => outside (e ▸ hi)
      simp [x,y,pairEval,ne])
    rw [computes] at eqv
    have accept : NestedCover.graphFun G ∅ x = true := by
      change (decide (∃ i ∈ (∅ : Finset (Fin n)), x i = true) || decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
      have h : ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := ⟨a,b,edge,by simp [x,pairEval],by simp [x,pairEval]⟩
      simp [h]
    have reject : NestedCover.graphFun G ∅ y = false := by
      have h : ¬ ∃ i j, G.Adj i j ∧ y i = true ∧ y j = true := by
        rintro ⟨i,j,hij,hi,hj⟩
        have hi' : i = b := by simpa [y,pairEval] using hi
        have hj' : j = b := by simpa [y,pairEval] using hj
        exact G.loopless.irrefl b (by simpa only [hi',hj'] using hij)
      change (decide (∃ i ∈ (∅ : Finset (Fin n)), y i = true) || decide (∃ i j, G.Adj i j ∧ y i = true ∧ y j = true)) = false
      simp [h]
    rw [accept,reject] at eqv
    exact Bool.noConfusion eqv
  have endpoints (e : Sym2 (Fin n)) (he : e ∈ E) : ∀ a ∈ e, a ∈ V := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have uv := G.mem_edgeFinset.mp (sub he)
      intro a ha
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact incident _ _ uv
      · exact incident _ _ uv.symm
  have peel (W : Finset (Fin n)) : ∀ T ⊆ E, (∀ e ∈ T, ∀ a ∈ e, a ∈ W) →
      ∃ H ⊆ T, T.card ≤ d*W.card + H.card ∧
        ∀ v : Fin n, (H.filter fun e => v ∈ e).card = 0 ∨ d < (H.filter fun e => v ∈ e).card := by
    refine Finset.strongInductionOn W ?_
    intro W ih
    intro T hT hW
    by_cases done : ∀ v : Fin n, (T.filter fun e => v ∈ e).card = 0 ∨ d < (T.filter fun e => v ∈ e).card
    · exact ⟨T,Finset.Subset.rfl,by omega,done⟩
    push Not at done
    obtain ⟨v,hpos,hle⟩ := done
    let R := T.filter fun e => v ∈ e
    obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < R.card by dsimp [R]; omega)
    obtain ⟨et,ve⟩ := Finset.mem_filter.mp he
    have vw := hW e et v ve
    have small := ih (W.erase v) (Finset.erase_ssubset vw) (T \ R) (fun e h => hT (Finset.mem_sdiff.mp h).1) (by
      intro e he a ha
      obtain ⟨et,nr⟩ := Finset.mem_sdiff.mp he
      have ne : a ≠ v := fun q => nr (Finset.mem_filter.mpr ⟨et,q ▸ ha⟩)
      exact Finset.mem_erase.mpr ⟨ne,hW e et a ha⟩)
    obtain ⟨H,subH,cost,regular⟩ := small
    refine ⟨H,fun e he => (Finset.mem_sdiff.mp (subH he)).1,?_,regular⟩
    have rem := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun e => v ∈ e) T)
    have hd : R.card ≤ d := hle
    have lift := Finset.card_erase_add_one vw
    calc
      T.card = (T \ R).card + R.card := rem.symm
      _ ≤ (d*(W.erase v).card + H.card) + d := Nat.add_le_add cost hd
      _ = d * W.card + H.card := by rw [← lift,Nat.mul_add]; omega
  obtain ⟨H,subH,removed,dense⟩ := peel V E Finset.Subset.rfl endpoints
  have residual := core n G deg girth C minimal computes H (subH.trans sub) dense
  suffices bound : H.card ≤ c*(C.size+1) by
    have paid := Nat.mul_le_mul_left d Vcost
    rw [Nat.add_mul]; omega
  apply residual
  intro u v he j owner
  obtain ⟨S,maxS,avoid⟩ := persists s(u,v) (subH he) u v rfl j owner
  have independent := maxS.1
  refine ⟨S,independent,?_⟩
  let hit (t : Fin n × Fin n) := gateVal n C j.val (pairInput t.1 t.2) = true
  let pts (t : Fin n × Fin n) := ({t.1,t.2} : Finset (Fin n))
  let fixed := ({u,v} : Finset (Fin n))
  let freePts (t : Fin n × Fin n) := pts t \ fixed
  have build (m : ℕ) (hm : m ≤ 2*r+1) :
      ∃ f : Fin m → Fin n × Fin n,
        (∀ i, (f i).1 ∈ S ∧ (f i).2 ∈ S ∧ hit (f i)) ∧
        ∀ i j, i ≠ j → Disjoint (freePts (f i)) (freePts (f j)) := by
    induction m with
    | zero => exact ⟨Fin.elim0,by intro i; exact i.elim0,by intro i; exact i.elim0⟩
    | succ m ih =>
      obtain ⟨f,good,disj⟩ := ih (by omega)
      let B := Finset.univ.biUnion fun i : Fin m => freePts (f i)
      have each (i : Fin m) : (freePts (f i)).card ≤ 2 := by
        have h := Finset.card_le_card (Finset.sdiff_subset (s := pts (f i)) (t := fixed))
        have hp : (pts (f i)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
        exact h.trans hp
      have bsize : B.card ≤ 4*r+2 := by
        have h := (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := fun i => freePts (f i))).trans
          (Finset.sum_le_sum (fun i _ => each i))
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
        change B.card ≤ m*2 at h
        omega
      have bfree (a : Fin n) (ha : a ∈ fixed) : a ∉ B := by
        intro h; obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
        exact (Finset.mem_sdiff.mp hi).2 ha
      obtain ⟨a,ha,b,hb,on⟩ := avoid B bsize (bfree u (by simp [fixed])) (bfree v (by simp [fixed]))
      obtain ⟨as,ab⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨bs,bb⟩ := Finset.mem_sdiff.mp hb
      let t := (a,b)
      have fresh (i) : Disjoint (freePts t) (freePts (f i)) := by
        refine Finset.disjoint_left.mpr fun z hz hzi => ?_
        have zB : z ∈ B := Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hzi⟩
        have zz := (Finset.mem_sdiff.mp hz).1
        change z ∈ ({a,b} : Finset (Fin n)) at zz
        simp only [Finset.mem_insert,Finset.mem_singleton] at zz
        exact zz.elim (fun h => ab (h ▸ zB)) (fun h => bb (h ▸ zB))
      refine ⟨Fin.cons t f,Fin.cases ⟨as,bs,on⟩ good,?_⟩
      intro i l
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) l
      · exact fun h => (h rfl).elim
      · exact fun _ => fresh l
      · exact fun _ => (fresh i).symm
      · exact fun h => disj i l (fun e => h (congrArg Fin.succ e))
  have edge : G.Adj u v := G.mem_edgeFinset.mp (sub (subH he))
  obtain ⟨a,af,anchor⟩ : ∃ a ∈ fixed, ∀ b ∈ S, b ∈ fixed → b=a := by
    by_cases us : u ∈ S
    · refine ⟨u,by simp [fixed],fun b bs bf => ?_⟩
      rcases Finset.mem_insert.mp bf with h|h
      · exact h
      · have e := Finset.mem_singleton.mp h
        exact (independent u us v (e ▸ bs) edge).elim
    · refine ⟨v,by simp [fixed],fun b bs bf => ?_⟩
      rcases Finset.mem_insert.mp bf with h|h
      · exact (us (h ▸ bs)).elim
      · exact Finset.mem_singleton.mp h
  obtain ⟨f,good,disj⟩ := build (2*r+1) le_rfl
  let tag (i : Fin (2*r+1)) := decide (a ∈ pts (f i))
  obtain ⟨b,many⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card tag (n := r) (by simp)
  let I := Finset.univ.filter fun i => tag i = b
  obtain ⟨J,jsub,jcard⟩ := Finset.exists_subset_card_eq (s := I) (show r+1 ≤ I.card from many)
  let iso := Fintype.equivFinOfCardEq (α := ↥J) (show Fintype.card ↥J = r+1 by simpa using jcard)
  let idx (i : Fin (r+1)) := (iso.symm i).val
  have idxInj : Function.Injective idx := Subtype.val_injective.comp iso.symm.injective
  have color (i) : tag (idx i) = b := (Finset.mem_filter.mp (jsub (iso.symm i).property)).2
  let K := if b then {a} else (∅ : Finset (Fin n))
  refine ⟨fun i => f (idx i),K,?_,?_,fun i => good (idx i),?_⟩
  · by_cases h : b = true <;> simp [K,h]
  · by_cases bt : b = true
    · simpa only [K,if_pos bt,Finset.singleton_subset_iff] using af
    · simp [K,bt]
  intro i l ne
  change pts (f (idx i)) ∩ pts (f (idx l)) = K
  ext z
  have tagI := color i
  have tagL := color l
  constructor
  · intro h
    obtain ⟨zi,zl⟩ := Finset.mem_inter.mp h
    have zfixed : z ∈ fixed := by
      by_contra nz
      exact Finset.disjoint_left.mp (disj _ _ (fun eq => ne (idxInj eq))) (Finset.mem_sdiff.mpr ⟨zi,nz⟩) (Finset.mem_sdiff.mpr ⟨zl,nz⟩)
    have zS : z ∈ S := by
      rcases Finset.mem_insert.mp zi with e|e
      · exact e ▸ (good _).1
      · exact (Finset.mem_singleton.mp e) ▸ (good _).2.1
    have za := anchor z zS zfixed
    subst z
    have bt : b = true := tagI.symm.trans (by simpa [tag] using zi)
    simp [K,bt]
  · intro h
    have bt : b = true := by
      by_contra hn
      simp [K,hn] at h
    have za : z = a := by simpa [K,bt] using h
    subst z
    exact Finset.mem_inter.mpr ⟨by simpa [tag,bt] using tagI,by simpa [tag,bt] using tagL⟩
