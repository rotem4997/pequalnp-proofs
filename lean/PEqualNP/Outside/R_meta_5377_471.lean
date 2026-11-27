import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_5377_471
    (hPath : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ (j : ℕ) (a b c d : Fin n),
      Owns n C j a b → Owns n C j b c → Owns n C j c d →
      (∃ t : Fin n, (t=a ∨ t=b ∨ t=c ∨ t=d) ∧ gateVal n C j (pairInput t t) = true) ∨
        gateVal n C j (pairInput a d) = true)
    (hBlock : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ),
      0 < n → IsMinimalMonoCircuit n C → j < C.size →
      gateVal n C j x = true → circuitFun n C x = false →
      ∃ i k, j ≤ i ∧ i < k ∧ k < C.size ∧ n+i ∈ (gateAt C k).inputs ∧
        (gateAt C k).op = GateOp.and ∧ gateVal n C i x = true ∧ gateVal n C k x = false)
    (hExchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → PEqualNP.TopForm.NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      let edges (D : Circuit) (i : ℕ) := Finset.univ.filter (fun e : Fin n × Fin n =>
        G.Adj e.1 e.2 ∧ Owns n D i e.1 e.2)
      let centered (D : Circuit) (i : ℕ) := ∃ z : Fin n, ∀ e ∈ edges D i, e.1 = z ∨ e.2 = z
      ∀ (j : ℕ) (u v : Fin n), ¬centered C j → ¬G.Adj u v →
      let x := pairInput u v
      gateVal n C j x = true → ∀ i k, j ≤ i → i < k → k < C.size →
      n+i ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.and →
      gateVal n C i x = true → gateVal n C k x = false →
      ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = circuitFun n C ∧
        ∀ t, ¬centered D t → (t < j → ¬centered C t) ∧
          (t = j → (edges D t).card < (edges C t).card) ∧
          ∃ s, edges D t = edges C s ∧ ∀ z : Fin n,
            gateVal n C s (pairInput z z) = true → gateVal n D t (pairInput z z) = true) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ), (∀ (x9 x10 : Fin x1), ¬x6 x7 x8 x9 x10) ∨ (∃ (x9 : Fin x1) (x10 : Fin x1), x6 x7 x8 x9 x10 ∧ ∀ (x11 x12 : Fin x1), x6 x7 x8 x11 x12 → x11 = x9 ∨ x12 = x9 ∨ x11 = x10 ∨ x12 = x10) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x6 x7 x8 x9 x10 ∧ x6 x7 x8 x10 x11 ∧ x6 x7 x8 x11 x12 ∧ x6 x7 x8 x12 x13 ∧ x6 x7 x8 x13 x9 ∧ (∀ (x14 x15 : Fin x1), x6 x7 x8 x14 x15 → x14 = x9 ∨ x14 = x10 ∨ x14 = x11 ∨ x14 = x12 ∨ x14 = x13) ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x8 (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.true;       have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) => ∀ x10 < x9, (∀ (x12 x13 : Fin x1), ¬x6 x8 x10 x12 x13) ∨ ∃ (x12 : Fin x1), ∀ (x13 x14 : Fin x1), x6 x8 x10 x13 x14 → x13 = x12 ∨ x14 = x12;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x7 x9 → x10 < x9.size → x8 x9 x10 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), x7 x14 ∧ x8 x14 (x10 + (1 : ℕ)) := by
  classical
  intro n G _ htri hfour
  let r (D : Circuit) (j : ℕ) (u v : Fin n) := G.Adj u v ∧ Owns n D j u v
  let eligible (D : Circuit) := IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
    ∀ j, (∀ a b, ¬r D j a b) ∨
      (∃ b c, r D j b c ∧ ∀ u v, r D j u v → u = b ∨ v = b ∨ u = c ∨ v = c) ∨
      ∃ a b c d e, r D j a b ∧ r D j b c ∧ r D j c d ∧ r D j d e ∧ r D j e a ∧
        (∀ u v, r D j u v → u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = e) ∧
          gateVal n D j (pairInput a a) = true
  let star (D : Circuit) (j : ℕ) := (∀ a b, ¬r D j a b) ∨
    ∃ z, ∀ u v, r D j u v → u = z ∨ v = z
  let edges (D : Circuit) (i : ℕ) := Finset.univ.filter (fun e : Fin n × Fin n => r D i e.1 e.2)
  let centered (D : Circuit) (i : ℕ) := ∃ z : Fin n, ∀ e ∈ edges D i, e.1 = z ∨ e.2 = z
  have memE (D : Circuit) (i : ℕ) (u v : Fin n) :
      (u,v) ∈ edges D i ↔ r D i u v := by simp [edges]
  have cs (D : Circuit) (i : ℕ) (hc : centered D i) : star D i := by
    obtain ⟨z,hz⟩ := hc
    exact Or.inr ⟨z, fun a b hab => hz (a,b) ((memE D i a b).2 hab)⟩
  have sc (w : Fin n) (D : Circuit) (i : ℕ) (hs : star D i) : centered D i := by
    rcases hs with h | ⟨z,hz⟩
    · exact ⟨w, fun e he => (h e.1 e.2 ((memE D i e.1 e.2).1 he)).elim⟩
    · exact ⟨z, fun e he => hz e.1 e.2 ((memE D i e.1 e.2).1 he)⟩
  change ∀ (B : Circuit) (j : ℕ), eligible B → j < B.size → (∀ t < j, star B t) →
    ∃ T, eligible T ∧ ∀ t < j+1, star T t
  intro B j hB hj hp
  change eligible B at hB
  change ∀ t < j, star B t at hp
  change ∃ D, eligible D ∧ ∀ t < j+1, star D t
  have obstruction (D : Circuit) (j : ℕ) (hD : eligible D) (bad : ¬ star D j) :
      ∃ u v : Fin n, ¬G.Adj u v ∧ gateVal n D j (pairInput u v) = true := by
    have reverseEdge (x y : Fin n) (e : r D j x y) : r D j y x := by
      have eqpair : pairInput y x = pairInput x y := by
        funext z
        change decide (z = y ∨ z = x) = decide (z = x ∨ z = y)
        simp only [or_comm]
      refine ⟨e.1.symm, ?_⟩
      have old : Owns n D j x y := e.2
      delta Owns at old ⊢
      rw [eqpair]
      exact old
    have avoid (z : Fin n) : ∃ x y, r D j x y ∧ x ≠ z ∧ y ≠ z := by
      by_contra! no
      apply bad
      right
      refine ⟨z, ?_⟩
      intro x y e
      by_cases h : x = z
      · exact Or.inl h
      · exact Or.inr (no x y e h)
    rcases hD.2.2 j with empty | ⟨b,c,bc,cover⟩ | ⟨a,b,c,d,e,_,_,_,_,_,_,hs⟩
    · exact (bad (Or.inl empty)).elim
    · obtain ⟨x,y,xy,hxc,hyc⟩ := avoid c
      have leftArm : ∃ a, r D j a b ∧ a ≠ c := by
        rcases cover x y xy with h | h | h | h
        · subst x; exact ⟨y,reverseEdge b y xy,hyc⟩
        · subst y; exact ⟨x,xy,hxc⟩
        · exact (hxc h).elim
        · exact (hyc h).elim
      obtain ⟨a,ab,hac⟩ := leftArm
      obtain ⟨p,q,pq,hpb,hqb⟩ := avoid b
      have rightArm : ∃ d, r D j c d ∧ d ≠ b := by
        rcases cover p q pq with h | h | h | h
        · exact (hpb h).elim
        · exact (hqb h).elim
        · subst p; exact ⟨q,pq,hqb⟩
        · subst q; exact ⟨p,reverseEdge p c pq,hpb⟩
      obtain ⟨d,cd,hdb⟩ := rightArm
      rcases hPath n D hD.1.1 j a b c d ab.2 bc.2 cd.2 with ⟨t,_,ht⟩ | hfire
      · exact ⟨t,t,G.irrefl,ht⟩
      · refine ⟨a,d,?_,hfire⟩
        intro ad
        exact hdb ((Finset.card_le_one.mp (hfour a c hac)) b
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab.1,bc.1.symm⟩) d
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ad,cd.1⟩)).symm
    · exact ⟨a,a,G.irrefl,hs⟩
  let candidate (m : ℕ) := ∃ D : Circuit, eligible D ∧ (∀ t < j, star D t) ∧ (edges D j).card = m
  have someCount : ∃ m, candidate m := ⟨_, B, hB, hp, rfl⟩
  obtain ⟨D,hD,hpD,hd⟩ := Nat.find_spec someCount
  have lower (T : Circuit) (hT : eligible T) (hpT : ∀ t < j, star T t) :
      (edges D j).card ≤ (edges T j).card := by
    rw [hd]
    exact Nat.find_min' someCount (show candidate (edges T j).card from ⟨T,hT,hpT,rfl⟩)
  have finish (T : Circuit) (hT : eligible T) (ht : ∀ t < j, star T t) (hjT : star T j) :
      ∃ T, eligible T ∧ ∀ t < j+1, star T t := by
    refine ⟨T,hT,fun t h => ?_⟩
    rcases (show t < j ∨ t = j by omega) with hlt | rfl
    · exact ht t hlt
    · exact hjT
  by_cases good : star D j
  · exact finish D hD hpD good
  obtain ⟨u,v,huv,hfire⟩ := obstruction D j hD good
  have hn : 0 < n := by have := u.isLt; omega
  have hsize : B.size ≤ D.size := hB.1.2 D hD.1.1 (hD.2.1.trans hB.2.1.symm)
  have hgraph (s t : Fin n) : graphFun G ∅ (pairInput s t) = true → G.Adj s t := by
    have hp' (w : Fin n) : pairInput s t w = true ↔ w = s ∨ w = t := by
      change decide (w = s ∨ w = t) = true ↔ _
      exact decide_eq_true_iff
    delta graphFun
    simp only [ Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, hp']
    rintro ⟨a,b,hab,ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  have hout : circuitFun n D (pairInput u v) = false := by
    rw [hD.2.1]
    cases h : graphFun G ∅ (pairInput u v) with
    | false => rfl
    | true => exact (huv (hgraph u v h)).elim
  obtain ⟨i,k,hji,hik,hk,hin,hop,hfi,hfk⟩ :=
    hBlock n D (pairInput u v) j hn hD.1 (hj.trans_le hsize) hfire hout
  obtain ⟨T,hTmin,hTf,replace⟩ := hExchange n G D htri hfour hD.1 hD.2.1 j u v
    (fun h => good (cs D j h)) huv hfire i k hji hik hk hin hop hfi hfk
  have rep (t : ℕ) (bad : ¬centered T t) :
      (t < j → ¬centered D t) ∧ (t = j → (edges T t).card < (edges D t).card) ∧
      ∃ s, edges T t = edges D s ∧ ∀ z : Fin n,
        gateVal n D s (pairInput z z) = true → gateVal n T t (pairInput z z) = true := replace t bad
  have ht : ∀ t < j, star T t := by
    intro t hlt
    by_contra h
    exact (rep t (fun hc => h (cs T t hc))).1 hlt (sc u D t (hpD t hlt))
  have hT : eligible T := by
    refine ⟨hTmin,hTf.trans hD.2.1,fun t => ?_⟩
    by_cases cent : centered T t
    · by_cases anyEdge : ∃ a b, r T t a b
      · obtain ⟨a,b,ab⟩ := anyEdge
        obtain ⟨z,hz⟩ := cent
        have hz' (p q : Fin n) (pq : r T t p q) : p=z ∨ q=z := hz (p,q) ((memE T t p q).2 pq)
        refine Or.inr (Or.inl ⟨a,b,ab,fun p q pq => ?_⟩)
        have hab := hz' a b ab
        have hpq := hz' p q pq
        rcases hab with ha | hb
        · exact hpq.elim (fun h => Or.inl (h.trans ha.symm)) (fun h => Or.inr (Or.inl (h.trans ha.symm)))
        · exact hpq.elim (fun h => Or.inr (Or.inr (Or.inl (h.trans hb.symm))))
            (fun h => Or.inr (Or.inr (Or.inr (h.trans hb.symm))))
      · exact Or.inl (fun a b ab => anyEdge ⟨a,b,ab⟩)
    · obtain ⟨s,he,hsing⟩ := (rep t cent).2.2
      have same (a b : Fin n) : r T t a b ↔ r D s a b := by
        rw [← memE T t a b, ← memE D s a b, he]
      rcases hD.2.2 s with empty | ⟨a,b,ab,covers⟩ | ⟨a,b,c,d,e,ab,bc,cd,de,ea,covers,hs⟩
      · exact Or.inl (fun a b h => empty a b ((same a b).1 h))
      · exact Or.inr (Or.inl ⟨a,b,(same a b).2 ab,fun x y h => covers x y ((same x y).1 h)⟩)
      · exact Or.inr (Or.inr ⟨a,b,c,d,e,(same a b).2 ab,(same b c).2 bc,
          (same c d).2 cd,(same d e).2 de,(same e a).2 ea,fun x y h => covers x y ((same x y).1 h),
          hsing a hs⟩)
  by_cases after : centered T j
  · exact finish T hT ht (cs T j after)
  · exact (Nat.not_lt_of_ge (lower T hT ht) ((rep j after).2.1 rfl)).elim
