import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open scoped Classical

-- Select an inclusion-minimal family over capacity. Its excess is one and every
-- gate in its union is used by at least 45 pairs. Only orders at least 87 can occur.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_5220_418
    (core : ∀ (n k : ℕ) (S : Finset (Fin n × Fin n)) (A : Fin n × Fin n → Finset (Fin k)),
      44*(S.biUnion A).card < S.card →
      ∃ U ⊆ S, U.card = 44*(U.biUnion A).card+1 ∧
        ∀ j ∈ U.biUnion A, 45 ≤ (U.filter fun e => j ∈ A e).card)
    (light : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      87 ≤ q → N=q*q+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsMinimalMonoCircuit (N+N) C →
      (∀ s : Finset (Fin N), s.card ≤ q → C.eval (List.ofFn (Fin.addCases
        (fun p => decide (¬∃ l∈s, I p l)) (fun l => decide (l ∈ s)))) = false) →
      let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.2) (Fin.natAdd N e.1)
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N+N) (Ico N (N+N))).getD i 0)) = true
        then ⟨.or,[]⟩ else g), C.output⟩
      let A (e : Fin N × Fin N) := univ.filter (fun j : Fin C.size =>
        (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
        gateVal (N+N) C j.val (pair e) = true)
      ∀ U : Finset (Fin N × Fin N),
        (∀ e ∈ U, I e.2 e.1 ∧ C.eval (List.ofFn (pair e)) = true ∧ D.eval (List.ofFn (pair e)) = false) →
        U.card = 44*(U.biUnion A).card+1 →
        ∃ j ∈ U.biUnion A, (U.filter fun e => j ∈ A e).card ≤ 44) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = x1 * x1 + x1 + (1 : ℕ) →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           (∀ (x10 : Finset (Fin x2)), x10.card ≤ x1 → x5.eval (List.ofFn fun (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x10, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x10)) x12) = Bool.false) →             have x11 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x11 x12 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x11) (Fin.natAdd x2 x12);             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             ∀ (x13 : Fin x2 → Finset (Fin x2)), (∀ (x14 x15 : Fin x2), x15 ∈ x13 x14 → x3 x15 x14 ∧ x5.eval (List.ofFn (x11 x15 x14)) = Bool.true ∧ x12.eval (List.ofFn (x11 x15 x14)) = Bool.false) → (44 : ℕ) * (Fintype.card { x15 : Fin (x2 + x2) // ∃ (x16 : Fin x2), ∃ x17 ∈ x13 x16, x11 x17 x16 x15 = Bool.true } - (1 : ℕ)) < ∑ x15 : Fin x2, (x13 x15).card → ∑ x16 : Fin x2, (x13 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x13 x17, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x16) (x11 x18 x17) = Bool.true } := by
  classical
  -- Count the lines through one point by counting all the other points on those lines.
  have pencil_size {q N : ℕ} (positive : 0 < q) (order : N = q*q+q+1)
      (I : Fin N → Fin N → Prop) [DecidableRel I]
      (lines : ∀ l, Fintype.card {p // I p l} = q+1)
      (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (p : Fin N) :
      (univ.filter (I p)).card = q+1 := by
    classical
    let hits (l r : Fin N) : ℕ := if I p l ∧ I r l ∧ r ≠ p then 1 else 0
    have byLine (l : Fin N) : ∑ r, hits l r = if I p l then q else 0 := by
      by_cases h : I p l
      · have eq : univ.filter (fun r => I r l ∧ r ≠ p) = (univ.filter (fun r => I r l)).erase p := by
          ext r
          simp [and_comm]
        have count := lines l
        rw [Fintype.card_subtype] at count
        have hp : p ∈ univ.filter (fun r => I r l) := by simp [h]
        simp [hits,h,Finset.sum_boole,eq,Finset.card_erase_of_mem hp,count]
      · simp [hits,h]
    have byPoint (r : Fin N) : ∑ l, hits l r = if r=p then 0 else 1 := by
      by_cases h : r=p
      · simp [hits,h]
      · obtain ⟨l,hl,only⟩ := unique p r (Ne.symm h)
        have eq : univ.filter (fun j => I p j ∧ I r j) = {l} := by
          ext j
          simp only [mem_filter,mem_univ,true_and,mem_singleton]
          exact ⟨fun e => only j e,fun e => e ▸ hl⟩
        simp [hits,h,Finset.sum_boole,eq]
    have total : ∑ l, ∑ r, hits l r = ∑ r, ∑ l, hits l r := Finset.sum_comm
    simp_rw [byLine,byPoint] at total
    have rest : univ.filter (fun r : Fin N => r ≠ p) = univ.erase p := by ext r; simp
    have rhs : (∑ r : Fin N, if r=p then 0 else 1 : ℕ) = N-1 := by
      calc
        _ = ∑ r : Fin N, if r ≠ p then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases h : r=p <;> simp [h]
        _ = _ := by rw [Finset.sum_boole,rest,Finset.card_erase_of_mem (Finset.mem_univ p)]; simp
    have lhs : (∑ l, if I p l then q else 0) = (univ.filter (I p)).card * q := by
      rw [← Finset.sum_filter]; simp
    rw [lhs,rhs] at total
    have prod : (univ.filter (I p)).card * q = (q+1)*q := by rw [total,order]; simp [Nat.add_mul]
    exact Nat.eq_of_mul_eq_mul_right positive prod

  -- A simple bipartite family has at most a*b pairs; both endpoint degree bounds apply.
  have density_arithmetic {a b e d : ℕ} (pairs : e ≤ a*b)
      (points : e ≤ d*a) (lines : e ≤ d*b) (degree : d ≤ 87) :
      e ≤ 44*(a+b-1) := by
    by_cases ha : a = 0
    · simp [ha] at pairs; omega
    by_cases hb : b = 0
    · simp [hb] at pairs; omega
    by_cases small : a ≤ 44
    · have := pairs.trans (Nat.mul_le_mul_right b small); omega
    by_cases small' : b ≤ 44
    · have := pairs.trans (Nat.mul_le_mul_left a small'); omega
    have pa := points.trans (Nat.mul_le_mul_right a degree)
    have lb := lines.trans (Nat.mul_le_mul_right b degree)
    omega

  have order_limit {q N : ℕ} (small : q ≤ 86) (order : N = q*q+q+1)
      (I : Fin N → Fin N → Prop) [DecidableRel I]
      (lines : ∀ l, Fintype.card {p // I p l} = q+1)
      (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
      (T : Fin N → Finset (Fin N)) (included : ∀ l p, p ∈ T l → I p l) :
      ∑ l, (T l).card ≤ 44*((univ.biUnion T).card + (univ.filter (fun l => (T l).Nonempty)).card - 1) := by
    classical
    let P := univ.biUnion T
    let L := univ.filter fun l => (T l).Nonempty
    let R (p : Fin N) := univ.filter fun l => p ∈ T l
    have transpose : ∑ l, (T l).card = ∑ p, (R p).card := by
      have column (l : Fin N) : (T l).card = ∑ p : Fin N, if p ∈ T l then 1 else 0 := by
        rw [Finset.sum_boole]; simp
      simp_rw [column]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_boole _ _)
    have limit (F : Fin N → Finset (Fin N)) (B : Finset (Fin N)) (k : ℕ)
        (each : ∀ i, (F i).card ≤ k) (off : ∀ i ∉ B, F i = ∅) :
        ∑ i, (F i).card ≤ k*B.card := by
      calc
        _ ≤ ∑ i : Fin N, if i ∈ B then k else 0 := Finset.sum_le_sum (by
          intro i _; by_cases h : i ∈ B <;> simp [h,each,off])
        _ = _ := by rw [← Finset.sum_filter]; simp [Nat.mul_comm]
    have noneL : ∀ l ∉ L, T l = ∅ := by simp [L,Finset.not_nonempty_iff_eq_empty]
    have noneP : ∀ p ∉ P, R p = ∅ := by
      intro p h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact h (Finset.mem_biUnion.mpr ⟨l,mem_univ _,(mem_filter.mp hl).2⟩)
    have byLine : ∀ l, (T l).card ≤ 87 := by
      intro l
      have bound := Finset.card_le_card (show T l ⊆ univ.filter (fun p => I p l) from
        fun p hp => mem_filter.mpr ⟨mem_univ _,included l p hp⟩)
      have c := lines l
      rw [Fintype.card_subtype] at c
      omega
    have byPoint : ∀ p, (R p).card ≤ 87 := by
      intro p
      have bound := Finset.card_le_card (show R p ⊆ univ.filter (I p) from
        fun l hl => mem_filter.mpr ⟨mem_univ _,included l p (mem_filter.mp hl).2⟩)
      by_cases h : 0 < q
      · rw [pencil_size h order I lines unique p] at bound
        omega
      · have cap := Finset.card_le_univ (R p)
        simp at cap
        have z : q=0 := by omega
        simp [z] at order
        omega
    have inside : ∀ l, (T l).card ≤ P.card := fun l => Finset.card_le_card
      (fun p hp => Finset.mem_biUnion.mpr ⟨l,mem_univ _,hp⟩)
    apply density_arithmetic (limit T L P.card inside noneL)
    · rw [transpose]; exact limit R P 87 byPoint noneP
    · exact limit T L 87 byLine noneL
    · decide



  have endpoint_count {N : ℕ} (T : Fin N → Finset (Fin N)) :
      Fintype.card {j : Fin (N+N) // ∃ l, ∃ p ∈ T l, pairInput (Fin.castAdd N p) (Fin.natAdd N l) j = true} =
      (univ.biUnion T).card + (univ.filter (fun l => (T l).Nonempty)).card := by
    classical
    let P := univ.biUnion T
    let L := univ.filter (fun l => (T l).Nonempty)
    let A := P.image (Fin.castAdd N)
    let B := L.image (Fin.natAdd N)
    rw [Fintype.card_subtype]
    have split : (univ.filter fun j => ∃ l, ∃ p ∈ T l, pairInput (Fin.castAdd N p) (Fin.natAdd N l) j = true) = A ∪ B := by
      ext j
      simp only [mem_filter,mem_univ,true_and,mem_union,mem_image,A,B]
      constructor
      · rintro ⟨l,p,hp,on⟩
        rcases of_decide_eq_true on with eq|eq
        · exact Or.inl ⟨p,mem_biUnion.mpr ⟨l,mem_univ _,hp⟩,eq.symm⟩
        · exact Or.inr ⟨l,mem_filter.mpr ⟨mem_univ _,p,hp⟩,eq.symm⟩
      · rintro (⟨p,ph,rfl⟩|⟨l,lh,rfl⟩)
        · obtain ⟨l,_,hp⟩ := mem_biUnion.mp ph
          exact ⟨l,p,hp,decide_eq_true (Or.inl rfl)⟩
        · obtain ⟨p,hp⟩ := (mem_filter.mp lh).2
          exact ⟨l,p,hp,decide_eq_true (Or.inr rfl)⟩
    have disjoint : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro j ha hb
      obtain ⟨p,_,rfl⟩ := mem_image.mp ha
      obtain ⟨l,_,eq⟩ := mem_image.mp hb
      have h := congrArg Fin.val eq
      change N+l.val = p.val at h
      omega
    rw [split,Finset.card_union_of_disjoint disjoint]
    change (P.image _).card + (L.image _).card = P.card + L.card
    rw [card_image_of_injective _ (Fin.castAdd_injective N N)]
    have inj : Function.Injective (Fin.natAdd N : Fin N → Fin (N+N)) := by
      intro a b h; apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val h)
    rw [card_image_of_injective _ inj]
  intro q N I inst C order lines unique minimal sound pair D T valid dense
  have large : 87 ≤ q := by
    by_contra! small
    have h := order_limit (by omega : q ≤ 86) order I lines unique T (fun l p hp => (valid l p hp).1)
    rw [endpoint_count] at dense
    omega
  let S := univ.filter (fun e : Fin N × Fin N => e.2 ∈ T e.1)
  let A (e : Fin N × Fin N) := univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
    gateVal (N+N) C j.val (pair e.2 e.1) = true)
  have count : S.card = ∑ l, (T l).card := by
    dsimp only [S]
    rw [Finset.card_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_boole]; simp
  have same : S.biUnion A = univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
    ∃ l, ∃ p ∈ T l, gateVal (N+N) C j.val (pair p l) = true) := by
    ext j
    simp only [A,S,mem_biUnion,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨l,p⟩,hp,off,on⟩; exact ⟨off,l,p,hp,on⟩
    · rintro ⟨off,l,p,hp,on⟩; exact ⟨(l,p),hp,off,on⟩
  rw [Fintype.card_subtype,← same,← count]
  by_contra! excess
  obtain ⟨U,sub,balance,heavy⟩ := core N C.size S A excess
  have ok := light q N I C large order lines unique minimal sound U
  obtain ⟨j,hj,low⟩ := ok (fun e he => valid e.1 e.2 (mem_filter.mp (sub he)).2) balance
  have high := heavy j hj
  change (U.filter fun e => j ∈ A e).card ≤ 44 at low
  omega
