import PEqualNP.MetaComplexity.Helpers.RunAsm4

/-!
# Run-of-four assembly, part 5: the run step and the class bound, given the end statement

Paper: the run-of-four argument in direct form, section 4 (cases I, II), section 6.
`StmtExt` gives a least list `gs`; split on `OneReader D gs`:
* I: two readers of a NOT gate on `y` (Drop 3 at false); two readers of `y`: Drop 3 at false, or
  both OR; at an inner `q2`, `q3` the drop table closes, at an end a third reader gives Drop 3 at
  false (`save3`), else state OO and `AsmEndOO`.
* II: an AND gate on a literal of `y` and a private gate: `stmtAnd` gives Drop 3 at false or
  Drop 4 at true; at an end the NOT state goes to `asm_endN` (Drop 5).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.EdgeFn

/-- Two readers of an input: three gates at false, or both are OR gates. -/
theorem asm_two_or {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (gp gq : Gate) (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs)
    (hgq : gs[q]? = some gq) (hiq : (i : ℕ) ∈ gq.inputs) :
    Drop f i false 3 gs.length ∨ (gp.op = GateOp.or ∧ gq.op = GateOp.or) := by
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl (L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)))
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl (L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)))
  have hor : ∀ g : Gate, fixBit g = true → g.op = GateOp.or := by
    intro g h
    unfold fixBit at h
    revert h
    cases g.op <;> simp
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inl ((L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc])))).mono
        (by norm_num) le_rfl)
    · exact Or.inr ⟨hor gp hc, hor gq (by rw [← hfb, hc])⟩
  · left
    by_cases hb : false = fixBit gp
    · exact L.third i false (hnc false) p q hpq hp hq (cp false (Or.inr hb))
    · have hb' : false = fixBit gq := by
        revert hb hfb
        cases fixBit gp <;> cases fixBit gq <;> simp
      exact L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inr hb'))

/-- The input form of a clean OR gate reading `a`. -/
theorem asm_or_form {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.or) {a : ℕ} (ha : a ∈ g.inputs) :
    ∃ u, g.inputs = [a, u] ∨ g.inputs = [u, a] := by
  rcases hcl p g hg with ⟨h, -⟩ | ⟨-, j, k, -, -, hin⟩
  · rw [hop] at h; cases h
  · rw [hin] at ha ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨k, Or.inl rfl⟩
    · exact ⟨j, Or.inr rfl⟩

/-- State OO at an end, or a third reader. -/
theorem asm_end_oo (hch : asmChain) (hOO : AsmEndOO) {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (q0 q1 q2 q3 q4 q5 : Fin (n + 1)) (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ)
    (L : Least (n + 1) (F G ∅) gs o)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      F G ∅ (Function.update x q1 b) ≠ F G ∅ (Function.update y q1 b))
    (p q : ℕ) (hpq : p ≠ q) (gp gq : Gate) (hgp : gs[p]? = some gp) (hip : (q1 : ℕ) ∈ gp.inputs)
    (hgq : gs[q]? = some gq) (hiq : (q1 : ℕ) ∈ gq.inputs) (hop : gp.op = GateOp.or)
    (hoq : gq.op = GateOp.or) :
    Drop (F G ∅) q1 false 3 gs.length ∨
    (Drop (F G ∅) q1 true 5 gs.length ∨ Drop (F G ∅) q2 false 3 gs.length ∨
      Drop (F G ∅) q2 true 4 gs.length ∨
      ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (n + 1)
        (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s') := by
  by_cases h3 : ∃ t, t ≠ p ∧ t ≠ q ∧ Reads gs t q1
  · obtain ⟨t, htp, htq, ht⟩ := h3
    exact Or.inl (L.save3 q1 false (hnc false) p q t hpq (Ne.symm htp) (Ne.symm htq)
      (rc_input false ⟨gp, hgp, hip⟩) (rc_input false ⟨gq, hgq, hiq⟩) (rc_input false ht))
  · push Not at h3
    obtain ⟨u1, hu1⟩ := asm_or_form L.hcl hgp hop hip
    obtain ⟨u2, hu2⟩ := asm_or_form L.hcl hgq hoq hiq
    exact Or.inr (hOO hch n G q0 q1 q2 q3 q4 q5 gs o p q gp gq u1 u2 r L hgp hop hu1 hgq hoq hu2 hpq
      (fun t ht => by
        by_cases h1 : t = p
        · exact Or.inl h1
        · by_cases h2 : t = q
          · exact Or.inr h2
          · exact absurd ht (h3 t h1 h2)))

/-- The run step: the bound at `A = ∅` at a graph with a run of four. -/
theorem asm_run (hch : asmChain) (hOO : AsmEndOO) (n : ℕ) (G : SimpleGraph (Fin n))
    (hr4 : asmRun4 G) (hih : IHV G) : BoundOf (HasCircuitSize n) G ∅ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, c0, d0, c5, d5, r, hc0, hc5⟩ := hr4
  intro s0 hC
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := q1.2; omega⟩
  have rs := asm_r4_symm r
  have nd := r.nd
  have o0 := r.out0
  have o5 := r.out5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd o0 o5
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := nd
  obtain ⟨hD, -⟩ := r4_stmtG3 n' G ∅ q0 q1 q2 q3 q4 q5 (fun i _ _ h => Finset.notMem_empty i h) r
  have hne : ({q1, q2, q3, q4} : Finset (Fin (n' + 1))).Nonempty := ⟨q1, by simp⟩
  obtain ⟨gs, o, L, hlen, hcase⟩ := stmtExt stmtLift stmtXMove stmtFront stmtWin
    (stmtTwo stmtExch stmtWin) n' (F G ∅) _ s0 hD hne hC
  suffices key : Phi1 G ∅ ≤ gs.length + 1 by omega
  have hend1 := asm_end_close G hih q0 q1 q2 q3 q4 q5 c0 d0 r hc0 (k := gs.length)
  have hend4 := asm_end_close G hih q5 q4 q3 q2 q1 q0 c5 d5 rs hc5 (k := gs.length)
  have hnbr : ∀ y ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))), ∃ u1 u2,
      (∀ w, G.Adj y w ↔ w = u1 ∨ w = u2) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨_, _, r.h1⟩
    · exact ⟨_, _, r.h2⟩
    · exact ⟨_, _, r.h3⟩
    · exact ⟨_, _, r.h4⟩
  have hcl0 : ∀ y ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))),
      Drop (F G ∅) y false 3 gs.length → Phi1 G ∅ ≤ gs.length + 1 := by
    intro y hy h
    obtain ⟨u1, u2, hN⟩ := hnbr y hy
    exact asm_cl0 G hih y u1 u2 ((hN u1).2 (Or.inl rfl)) (fun w hw => (hN w).1 hw) h
  have hmid : ∀ y, (y = q2 ∨ y = q3) → Drop (F G ∅) y true 4 gs.length →
      Phi1 G ∅ ≤ gs.length + 1 := by
    rintro y (rfl | rfl) h
    · exact hend1 (Or.inr (Or.inr (Or.inl h)))
    · exact hend4 (Or.inr (Or.inr (Or.inl h)))
  have hnc := hD.nc
  have hq1D : q1 ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))) := by simp
  have hq4D : q4 ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))) := by simp
  by_cases hOR : OneReader ({q1, q2, q3, q4} : Finset (Fin (n' + 1))) gs
  swap
  · -- case I
    have hI := hOR
    by_cases hA : ∀ y ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))), ∀ p q : ℕ,
        Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q
    · have hB : ¬ ∀ y ∈ ({q1, q2, q3, q4} : Finset (Fin (n' + 1))), ∀ pn : ℕ,
          gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
          ∀ p q : ℕ, Reads gs p (n' + 1 + pn) → Reads gs q (n' + 1 + pn) → p = q :=
        fun hB => hI ⟨hA, hB⟩
      push Not at hB
      obtain ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩ := hB
      exact hcl0 y hy (L.not_two_readers y (hnc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1
    · push Not at hA
      obtain ⟨y, hy, p, q, hp, hq, hpq⟩ := hA
      obtain ⟨gp, hgp, hip⟩ := hp
      obtain ⟨gq, hgq, hiq⟩ := hq
      rcases asm_two_or L y (hnc y hy) p q hpq gp gq hgp hip hgq hiq with h3 | ⟨hop, hoq⟩
      · exact hcl0 y hy h3
      have hy' := hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
      rcases hy' with rfl | rfl | rfl | rfl
      · rcases asm_end_oo hch hOO G q0 y q2 q3 q4 q5 r gs o L (hnc y hy) p q hpq gp gq hgp hip hgq hiq
          hop hoq with h3 | h
        · exact hcl0 y hy h3
        · exact hend1 h
      · rcases L.two_readers y (hnc y hy) p q hpq ⟨gp, hgp, hip⟩ ⟨gq, hgq, hiq⟩ with
          ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
        · exact hcl0 y hy h3
        · exact hcl0 y hy (h4.mono (by norm_num) le_rfl)
        · exact hmid y (Or.inl rfl) h4
      · rcases L.two_readers y (hnc y hy) p q hpq ⟨gp, hgp, hip⟩ ⟨gq, hgq, hiq⟩ with
          ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
        · exact hcl0 y hy h3
        · exact hcl0 y hy (h4.mono (by norm_num) le_rfl)
        · exact hmid y (Or.inr rfl) h4
      · rcases asm_end_oo hch hOO G q5 y q3 q2 q1 q0 rs gs o L (hnc y hy) p q hpq gp gq hgp hip hgq
          hiq hop hoq with h3 | h
        · exact hcl0 y hy h3
        · exact hend4 h
  · -- case II
    rcases hcase with hI | ⟨p, g, y, l, h, ⟨hgp, -, hin, hy, hlit, -⟩, hand, hh, ho, hpriv⟩
    · exact absurd hOR hI
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n' + 1 + ph := ⟨h - (n' + 1), by omega⟩
    have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
    have hhmem : n' + 1 + ph ∈ g.inputs := by rcases hin with e | e <;> rw [e] <;> simp
    have hphp : n' + 1 + ph < n' + 1 + p := (L.hcl p g hgp).lt _ hhmem
    have hfnc : ∃ x y : Fin (n' + 1) → Bool, F G ∅ x ≠ F G ∅ y := by
      obtain ⟨x, y, h⟩ := hnc q1 hq1D true
      exact ⟨_, _, h⟩
    have ho2 : o ≠ n' + 1 + ph := by
      rw [RunPNA.pna_out_last L hfnc (by omega)]
      omega
    obtain ⟨u1, u2, hN⟩ := hnbr y hy
    have hdep : Dep (F G ∅) y :=
      F_dep G ∅ y u1 ((hN u1).2 (Or.inl rfl)) (Finset.notMem_empty _)
    have hA := stmtAnd n' (F G ∅) gs o p ph l g y L (hnc y hy) hdep hgp hand hin hlit (by omega)
      hpriv ho ho2
    rcases hlit with hl | ⟨pn, rfl, hpn⟩
    · exact hcl0 y hy (hA.1 hl)
    have hly : n' + 1 + pn ≠ (y : ℕ) := by have := y.isLt; omega
    have h4 := hA.2 hly
    have he1 : ∀ t, Reads gs t y → t = pn := fun t ht => hOR.1 y hy t pn ht ⟨_, hpn, by simp⟩
    have hn1 : ∀ t, Reads gs t (n' + 1 + pn) → t = p := fun t ht =>
      hOR.2 y hy pn hpn t p ht ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hy' := hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl | rfl
    · exact hend1 (Or.inl (asm_endN hch n' G q0 y q2 r.h1 o0.2.1 gs o pn p ph g L hpn he1 hgp hand
        hin hn1 (by omega) hpriv ho))
    · exact hmid y (Or.inl rfl) h4
    · exact hmid y (Or.inr rfl) h4
    · exact hend4 (Or.inl (asm_endN hch n' G q5 y q3 rs.h1 o5.2.2.1 gs o pn p ph g L hpn he1 hgp
        hand hin hn1 (by omega) hpriv ho))

/-- The class bound, given the chain law and the end statement. -/
theorem asm_a1 (hch : asmChain) (hOO : AsmEndOO) : StmtA1 asmCls :=
  asm_ind asm_hered (fun _ G hG hE => asm_dich G hG hE) (asm_run hch hOO)

/-- Row L-meta-658 (statement verbatim) from the end statement `AsmEndOO`. -/
theorem asm_L658_of_end (hOO : AsmEndOO) : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w)) → ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 5 ≤ c.length) → (∀ X : Finset (Fin n), (∃ i j : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj i j) → PEqualNP.Library.Peel.GoodLeaf (PEqualNP.Library.Peel.delVerts G X) ∨ ∃ q0 q1 q2 q3 q4 q5 : Fin n, [q1, q2, q3, q4].Nodup ∧ q0 ∉ [q1, q2, q3, q4] ∧ q5 ∉ [q1, q2, q3, q4] ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q1 w ↔ w = q0 ∨ w = q2) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q2 w ↔ w = q1 ∨ w = q3) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q3 w ↔ w = q2 ∨ w = q4) ∧ (∀ w : Fin n, (PEqualNP.Library.Peel.delVerts G X).Adj q4 w ↔ w = q3 ∨ w = q5)) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1 :=
  fun hch => asm_row_of_a1 (asm_a1 hch hOO)

end PEqualNP.MetaComplexity.Helpers.RunAsm
