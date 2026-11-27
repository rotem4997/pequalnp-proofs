import PEqualNP.MetaComplexity.Helpers.RunAsm3
import PEqualNP.MetaComplexity.L596
import PEqualNP.MetaComplexity.Helpers.EdgeFnGraphPlan

/-!
# The q2 side, item E: outcome (q-d) of `AsmPQ2` through the checked row L-meta-596

Conjecture until the checker accepts. Row L-meta-596 is stated with the free input at
`Fin.last`. The least list `gs` for `F G ∅` is relabelled along the swap of `q3` and `Fin.last n`
(`asm_least`, `asmG`, `asmW` of `RunAsm2`), so `q3` is last, `e = q1`, `q4 = q4`; the
hypotheses of the row are supplied from the (q-d) facts about `gs`, and the size bound for
`x_last OR H` is moved back to the double restriction `x_q2 := 1, x_q1 := 0` by `relabel_size`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.EdgeFn PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Loc

/-- The read relation of the row (a NOT gate reads its head) is membership in a clean gate. -/
theorem pq2e_qaReads_iff {m : ℕ} {g : Gate} (h : CleanGate m g) (a : ℕ) :
    ((g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs)) ↔
      a ∈ g.inputs := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, _, _, h2⟩
  · rw [h2]; simp [h1, eq_comm]
  · have : g.op ≠ GateOp.not := by rcases h1 with h1 | h1 <;> rw [h1] <;> simp
    simp [this]

/-- `Fin.get` at a position. -/
theorem pq2e_get {gs : List Gate} {p : ℕ} {g : Gate} (h : gs[p]? = some g) :
    ∃ hp : p < gs.length, gs.get ⟨p, hp⟩ = g := by
  obtain ⟨hp, hg⟩ := List.getElem?_eq_some_iff.1 h
  exact ⟨hp, hg⟩

theorem pq2e_rg {m : ℕ} (σ : Equiv.Perm (Fin m)) (g : Gate) (a b : ℕ)
    (h : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    (relGate m m σ g).op = g.op ∧ (relGate m m σ g).inputs.length = 2 ∧
      asmW σ a ∈ (relGate m m σ g).inputs ∧ asmW σ b ∈ (relGate m m σ g).inputs := by
  rcases h with h | h <;> simp [relGate, h, asmW]

theorem pq2e_asmW_inj {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (σ i) = i) {a b : ℕ}
    (h : asmW σ a = asmW σ b) : a = b := by
  have := congrArg (asmW σ) h
  rwa [asmW_inv σ hσ, asmW_inv σ hσ] at this

theorem pq2e_snoc (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (hσ : ∀ i, σ (σ i) = i) (q3 : Fin (n + 1))
    (hq3 : σ q3 = Fin.last n) (X : Fin (n + 1) → Bool) (hX : X q3 = false) :
    (Fin.snoc (α := fun _ => Bool) (fun k : Fin n => X (σ k.castSucc)) false :
      Fin (n + 1) → Bool) ∘ σ = X := by
  funext i
  simp only [Function.comp]
  by_cases hi : σ i = Fin.last n
  · have : i = q3 := by rw [← hσ i, hi, ← hq3, hσ]
    rw [hi, this, hX]; simp
  · obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.2 hi
    rw [← hk, Fin.snoc_castSucc, hk, hσ]

theorem pq2e_gate2 {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (σ i) = i) (g : Gate) (a b : ℕ)
    (h : g.inputs = [a, b] ∨ g.inputs = [b, a]) (hab : a ≠ b) :
    (relGate m m σ g).op = g.op ∧ (relGate m m σ g).inputs.length = 2 ∧
      asmW σ a ∈ (relGate m m σ g).inputs ∧ asmW σ b ∈ (relGate m m σ g).inputs ∧
      asmW σ a ≠ asmW σ b :=
  ⟨(pq2e_rg σ g a b h).1, (pq2e_rg σ g a b h).2.1, (pq2e_rg σ g a b h).2.2.1,
    (pq2e_rg σ g a b h).2.2.2, fun h' => hab (pq2e_asmW_inj σ hσ h')⟩

theorem pq2e_qd (hch : asmChain) (n : ℕ) (G : SimpleGraph (Fin (n + 1)))
    (q0 q1 q2 q3 q4 q5 : Fin (n + 1)) (r : r4Run G q0 q1 q2 q3 q4 q5)
    (gs : List Gate) (o : ℕ) (L : Least (n + 1) (F G ∅) gs o)
    (p1 p2 a1 a2 o2 jM : ℕ) (g1 g2 ga1 ga2 go2 gM : Gate) (u1 u2 w1 w2 W2 z : ℕ)
    -- the two readers of x_q1 (the hypotheses of AsmPQ2)
    (hg1 : gs[p1]? = some g1) (ho1 : g1.op = GateOp.or)
    (hu1 : g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, q1])
    (hg2 : gs[p2]? = some g2) (ho2 : g2.op = GateOp.or)
    (hu2 : g2.inputs = [(q1 : ℕ), u2] ∨ g2.inputs = [u2, q1])
    (h12 : p1 ≠ p2) (hall : ∀ t, Reads gs t q1 → t = p1 ∨ t = p2)
    -- shape (i), the fields of AsmShapeI
    (ha12 : a1 ≠ a2) (hpa1 : p1 < a1) (hpa2 : p2 < a2)
    (hga1 : gs[a1]? = some ga1) (hgaop1 : ga1.op = GateOp.and)
    (hgain1 : ga1.inputs = [n + 1 + p1, w1] ∨ ga1.inputs = [w1, n + 1 + p1])
    (hga2 : gs[a2]? = some ga2) (hgaop2 : ga2.op = GateOp.and)
    (hgain2 : ga2.inputs = [n + 1 + p2, w2] ∨ ga2.inputs = [w2, n + 1 + p2])
    (hrd1 : ∀ t, Reads gs t (n + 1 + p1) → t = a1) (hrd2 : ∀ t, Reads gs t (n + 1 + p2) → t = a2)
    (hu1r : u1 < n + 1 ∨ ∃ t, t ≠ p1 ∧ Reads gs t u1)
    (hu2r : u2 < n + 1 ∨ ∃ t, t ≠ p2 ∧ Reads gs t u2)
    -- operands are two different wires (a least list has no OR(x, x) or AND(x, x))
    (hne_u1 : u1 ≠ q1) (hne_u2 : u2 ≠ q1) (hne_w1 : w1 ≠ n + 1 + p1) (hne_w2 : w2 ≠ n + 1 + p2)
    -- (q-d): the single reader o2 = OR(x_q2, W2) of x_q2 and the single reader M = AND(o2, z)
    (hgo2 : gs[o2]? = some go2) (hoo2 : go2.op = GateOp.or)
    (hoin2 : go2.inputs = [(q2 : ℕ), W2] ∨ go2.inputs = [W2, q2]) (hne_W2 : W2 ≠ q2)
    (hrq2 : ∀ t, Reads gs t q2 → t = o2) (ho2p1 : o2 ≠ p1) (ho2p2 : o2 ≠ p2)
    (hgM : gs[jM]? = some gM) (hMop : gM.op = GateOp.and)
    (hMin : gM.inputs = [n + 1 + o2, z] ∨ gM.inputs = [z, n + 1 + o2]) (hne_z : z ≠ n + 1 + o2)
    (hoM : o2 < jM) (hrM : ∀ t, Reads gs t (n + 1 + o2) → t = jM) :
    ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (n + 1)
      (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s' := by
  -- graph facts
  have nd := r.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h12', h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := nd
  have o0 := r.out0
  have o5 := r.out5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o0 o5
  obtain ⟨h01, h02, h03, h04⟩ := o0
  obtain ⟨h51, h52, h53, h54⟩ := o5
  have A12 : G.Adj q1 q2 := (r.h1 q2).2 (Or.inr rfl)
  have A23 : G.Adj q2 q3 := (r.h2 q3).2 (Or.inr rfl)
  have A34 : G.Adj q3 q4 := (r.h3 q4).2 (Or.inr rfl)
  have A45 : G.Adj q4 q5 := (r.h4 q5).2 (Or.inr rfl)
  have N1 := fun w => r.h1 w
  have N4 := fun w => r.h4 w
  -- the relabelling
  obtain ⟨σ, hσdef⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ = Equiv.swap q3 (Fin.last n) := ⟨_, rfl⟩
  have hσ : ∀ i, σ (σ i) = i := fun i => by rw [hσdef]; exact Equiv.swap_apply_self _ _ _
  have hq3 : σ q3 = Fin.last n := by rw [hσdef]; exact Equiv.swap_apply_left _ _
  have hσl : σ (Fin.last n) = q3 := by rw [← hq3, hσ]
  have L' := asm_least σ hσ L
  set gs' := asmG σ gs with hgs'
  set o' := asmW σ o
  have hgd : ∀ a b : Fin (n + 1), a ≠ b → σ a ≠ σ b := fun a b h h' => h (σ.injective h')
  have hnl : ∀ a : Fin (n + 1), a ≠ q3 → σ a ≠ Fin.last n := fun a h h' => h (by
    rw [← hσ a, h', hσl])
  -- point values of F
  have pt1 : F G ∅ (fun i => decide (i = q3)) = false := by
    apply F_false_of {q3}
    · intro i hi; simpa using hi
    · simp
    · intro i j hij hi hj
      simp at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij
  have pt2 : F G ∅ (fun i => decide (i = q3 ∨ i = q2)) = true :=
    F_true_of q2 q3 A23 (by simp) (by simp)
  have pt3 : F G ∅ (fun i => decide (i = q1)) = false := by
    apply F_false_of {q1}
    · intro i hi; simpa using hi
    · simp
    · intro i j hij hi hj
      simp at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij
  have pt4 : F G ∅ (fun i => decide (i = q1 ∨ i = q2)) = true :=
    F_true_of q1 q2 A12 (by simp) (by simp)
  have pt5 : F G ∅ (fun i => decide (i = q1 ∨ i = q4)) = false := by
    apply F_false_of {q1, q4}
    · intro i hi; simpa using hi
    · simp
    · intro i j hij hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      have l1 : ¬ G.Adj q1 q1 := G.loopless.irrefl _
      have l4 : ¬ G.Adj q4 q4 := G.loopless.irrefl _
      rcases hi with rfl | rfl
      · rcases (N1 j).1 hij with rfl | rfl <;> rcases hj with h | h <;> subst h <;>
          first | exact absurd hij l1 | exact absurd rfl h01 | exact absurd rfl h02 |
            exact h12' rfl | exact h12' rfl.symm | exact h24 rfl | exact h24 rfl.symm | exact h01 rfl | exact h04 rfl | exact h04 rfl.symm | exact h02 rfl.symm | exact h02 rfl | exact h01 rfl.symm
      · rcases (N4 j).1 hij with rfl | rfl <;> rcases hj with h | h <;> subst h <;>
          first | exact absurd hij l4 | exact h13 rfl | exact h34 rfl | exact h51 rfl |
            exact h54 rfl | exact h34 rfl.symm | exact h13 rfl.symm | exact h51 rfl.symm | exact h54 rfl.symm
  have pt6 : F G ∅ (fun i => decide (i = q1 ∨ i = q4 ∨ i = q2)) = true :=
    F_true_of q1 q2 A12 (by simp) (by simp)
  have pt7 : F G ∅ (fun i => decide (i = q1 ∨ i = q4 ∨ i = q3)) = true :=
    F_true_of q3 q4 A34 (by simp) (by simp)
  -- the function and the restricted function
  have cmp2 : ∀ y : Fin (n + 1) → Bool, ∀ a b : Fin (n + 1),
      Function.update (Function.update y (σ a) true) (σ b) false ∘ σ =
        Function.update (Function.update (y ∘ σ) a true) b false := by
    intro y a b
    rw [Function.update_comp_equiv, Function.update_comp_equiv]
    simp
  set H : (Fin n → Bool) → Bool := fun z => F G ∅ (Function.update (Function.update
    ((Fin.snoc (α := fun _ => Bool) z false : Fin (n + 1) → Bool) ∘ σ) q2 true) q1 false) with hHdef
  have hq2l : σ q2 ≠ Fin.last n := hnl q2 h23
  have hq1l : σ q1 ≠ Fin.last n := hnl q1 h13
  have hq4l : σ q4 ≠ Fin.last n := hnl q4 (Ne.symm h34)
  have hF1 : ∀ x : Fin (n + 1) → Bool,
      F G ∅ ((Function.update (Function.update x (σ q2) true) (σ q1) false) ∘ σ) =
        (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    intro x
    rw [cmp2]
    cases hx : x (Fin.last n)
    · simp only [Bool.false_or, hHdef]
      have : (Fin.snoc (α := fun _ => Bool) (fun i : Fin n => x i.castSucc) false) = x := by
        rw [← hx]; exact Fin.snoc_init_self x
      rw [this]
    · simp only [Bool.true_or]
      apply F_true_of q2 q3 A23
      · simp [Function.update_apply, h12', Ne.symm h12']
      · have : (x ∘ σ) q3 = true := by simp [Function.comp, hq3, hx]
        simp [Function.update_apply, Ne.symm h13, Ne.symm h23, this, hq3, hx]
  -- H is not constant
  have hHval : ∀ X : Fin (n + 1) → Bool, X q3 = false →
      H (fun k : Fin n => X (σ k.castSucc)) =
        F G ∅ (Function.update (Function.update X q2 true) q1 false) := by
    intro X hX
    simp only [hHdef]
    rw [pq2e_snoc n σ hσ q3 hq3 X hX]
  have hHnc : ∃ y y' : Fin n → Bool, H y ≠ H y' := by
    refine ⟨fun k => (fun _ : Fin (n + 1) => false) (σ k.castSucc),
      fun k => (fun i : Fin (n + 1) => decide (i = q4 ∨ i = q5)) (σ k.castSucc), ?_⟩
    have e1 := hHval (fun _ : Fin (n + 1) => false) rfl
    have e2 := hHval (fun i : Fin (n + 1) => decide (i = q4 ∨ i = q5))
      (by simp [h34, Ne.symm h53])
    beta_reduce at e1 e2 ⊢
    rw [e1, e2]
    have v1 : F G ∅ (Function.update (Function.update (fun _ : Fin (n + 1) => false) q2 true)
        q1 false) = false := by
      apply F_false_of {q2}
      · intro i hi
        by_cases h : i = q1
        · simp [Function.update_apply, h] at hi
        · by_cases h' : i = q2
          · simp [h']
          · simp [Function.update_apply, h, h'] at hi
      · simp
      · intro i j hij hi hj
        simp at hi hj; subst hi; subst hj; exact G.loopless.irrefl _ hij
    have v2 : F G ∅ (Function.update (Function.update (fun i : Fin (n + 1) => decide (i = q4 ∨ i = q5))
        q2 true) q1 false) = true := by
      apply F_true_of q4 q5 A45
      · simp [Function.update_apply, Ne.symm h14, Ne.symm h24]
      · simp [Function.update_apply, h51, Ne.symm h51, h52, Ne.symm h52]
    rw [v1, v2]; simp
  -- the gate side
  have hlenR : ∀ t w, Reads gs' t w → t < gs'.length := by
    rintro t w ⟨g, hg, -⟩
    exact (List.getElem?_eq_some_iff.1 hg).1
  have hltR : ∀ t w, Reads gs' t w → w < n + 1 + t := by
    rintro t w ⟨g, hg, hw⟩
    rcases L'.hcl t g hg with ⟨-, j, hj, hin⟩ | ⟨-, j, k, hj, hk, hin⟩
    · rw [hin] at hw; simp at hw; omega
    · rw [hin] at hw; simp at hw; omega
  have hRd : ∀ t w, Reads gs' t w ↔ Reads gs t (asmW σ w) := fun t w => asm_reads σ hσ gs t w
  have hQ : ∀ (j : Fin gs'.length) (a : ℕ),
      (((gs'.get j).op = GateOp.not ∧ (gs'.get j).inputs.head? = some a) ∨
        ((gs'.get j).op ≠ GateOp.not ∧ a ∈ (gs'.get j).inputs)) ↔ Reads gs' j a := by
    intro j a
    have hj : gs'[(j : ℕ)]? = some (gs'.get j) := by simp
    rw [pq2e_qaReads_iff (L'.hcl j _ hj) a]
    exact ⟨fun h => ⟨_, hj, h⟩, fun ⟨g, hg, h⟩ => by rw [hj] at hg; cases hg; exact h⟩
  have hgetg : ∀ p g (h : gs[p]? = some g), ∃ hp : p < gs'.length,
      gs'.get ⟨p, hp⟩ = relGate (n + 1) (n + 1) σ g := by
    intro p g h
    have : gs'[p]? = some (relGate (n + 1) (n + 1) σ g) := by
      rw [hgs', asmG_get, h]; rfl
    exact pq2e_get this
  -- the seven point values of F' = F after the relabelling
  have c1 : (fun i : Fin (n + 1) => decide (i = Fin.last n)) ∘ σ = fun i => decide (i = q3) := by
    funext i; simp only [Function.comp]; rw [← hq3]; simp
  have c2 : (fun i : Fin (n + 1) => decide (i = Fin.last n ∨ i = σ q2)) ∘ σ =
      fun i => decide (i = q3 ∨ i = q2) := by
    funext i; simp only [Function.comp]; rw [← hq3]; simp
  have c3 : (fun i : Fin (n + 1) => decide (i = σ q1)) ∘ σ = fun i => decide (i = q1) := by
    funext i; simp [Function.comp]
  have c4 : (fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q2)) ∘ σ =
      fun i => decide (i = q1 ∨ i = q2) := by
    funext i; simp [Function.comp]
  have c5 : (fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4)) ∘ σ =
      fun i => decide (i = q1 ∨ i = q4) := by
    funext i; simp [Function.comp]
  have c6 : (fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4 ∨ i = σ q2)) ∘ σ =
      fun i => decide (i = q1 ∨ i = q4 ∨ i = q2) := by
    funext i; simp [Function.comp]
  have c7 : (fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4 ∨ i = Fin.last n)) ∘ σ =
      fun i => decide (i = q1 ∨ i = q4 ∨ i = q3) := by
    funext i; simp only [Function.comp]; rw [← hq3]; simp
  have hmin : IsMinimalCircuit (n + 1) (Circuit.mk gs' o') :=
    asm_least_min L' ⟨_, _, by
      show F G ∅ ((fun i : Fin (n + 1) => decide (i = Fin.last n)) ∘ σ) ≠
        F G ∅ ((fun i : Fin (n + 1) => decide (i = Fin.last n ∨ i = σ q2)) ∘ σ)
      rw [c1, c2, pt1, pt2]; simp⟩
  obtain ⟨hp1, hG1⟩ := hgetg p1 g1 hg1
  obtain ⟨hp2, hG2⟩ := hgetg p2 g2 hg2
  obtain ⟨hpa1', hGa1⟩ := hgetg a1 ga1 hga1
  obtain ⟨hpa2', hGa2⟩ := hgetg a2 ga2 hga2
  obtain ⟨hpo2, hGo2⟩ := hgetg o2 go2 hgo2
  obtain ⟨hpM, hGM⟩ := hgetg jM gM hgM
  have hw : ∀ k : Fin (n + 1), asmW σ k = σ k := asmW_fin σ
  have hge : ∀ k, asmW σ (n + 1 + k) = n + 1 + k := fun k => asmW_ge σ (by omega)
  have hinj : ∀ (j : Fin gs'.length) (p : ℕ), (j : ℕ) = p → ∀ (hp : p < gs'.length),
      j = ⟨p, hp⟩ := fun j p h hp => Fin.ext h
  obtain ⟨s, hs5, hsH⟩ : ∃ s : ℕ, s + 5 ≤ (Circuit.mk gs' o').size ∧
      HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => x (Fin.last n) ||
        H (fun i : Fin n => x i.castSucc)) s := by
    refine L596 n (fun x => F G ∅ (x ∘ σ)) H (Circuit.mk gs' o') (σ q1) (σ q2) (σ q4)
      ⟨p1, hp1⟩ ⟨p2, hp2⟩ ⟨a1, hpa1'⟩ ⟨a2, hpa2'⟩ ⟨o2, hpo2⟩ ⟨jM, hpM⟩
      (asmW σ u1) (asmW σ u2) (asmW σ w1) (asmW σ w2) (asmW σ W2) (asmW σ z) hch
      ?_ hHnc hF1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmin (fun x => L'.hev x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_
    · exact ⟨hgd q1 q2 h12', hgd q1 q4 h14, hgd q2 q4 h24, hq1l, hq2l, hq4l⟩
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = Fin.last n)) ∘ σ) = false
      rw [c1, pt1]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = Fin.last n ∨ i = σ q2)) ∘ σ) = true
      rw [c2, pt2]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = σ q1)) ∘ σ) = false
      rw [c3, pt3]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q2)) ∘ σ) = true
      rw [c4, pt4]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4)) ∘ σ) = false
      rw [c5, pt5]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4 ∨ i = σ q2)) ∘ σ) = true
      rw [c6, pt6]
    · show F G ∅ ((fun i : Fin (n + 1) => decide (i = σ q1 ∨ i = σ q4 ∨ i = Fin.last n)) ∘ σ) = true
      rw [c7, pt7]
    · simp [Fin.ext_iff, Fin.lt_def, h12, ha12, hpa1, hpa2]
    · -- g1
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ g1 q1 u1 hu1 (fun h => hne_u1 h.symm)
      rw [asmW_fin σ q1] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨p1, hp1⟩ = relGate (n + 1) (n + 1) σ g1 := hG1
      rw [hG]
      exact ⟨h1.trans ho1, h2, h3, h4, h5⟩
    · -- g2
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ g2 q1 u2 hu2 (fun h => hne_u2 h.symm)
      rw [asmW_fin σ q1] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨p2, hp2⟩ = relGate (n + 1) (n + 1) σ g2 := hG2
      rw [hG]
      exact ⟨h1.trans ho2, h2, h3, h4, h5⟩
    · -- readers of e
      intro j _ hj
      have h1 := (hQ j _).1 hj
      have hx : asmW σ ((σ q1 : Fin (n + 1)) : ℕ) = q1 := by rw [asmW_fin, hσ]
      rw [hRd, hx] at h1
      rcases hall j h1 with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · -- a1
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ ga1 (n + 1 + p1) w1 hgain1
        (fun h => hne_w1 h.symm)
      rw [hge p1] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨a1, hpa1'⟩ = relGate (n + 1) (n + 1) σ ga1 := hGa1
      rw [hG]
      exact ⟨h1.trans hgaop1, h2, h3, h4, h5⟩
    · -- a2
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ ga2 (n + 1 + p2) w2 hgain2
        (fun h => hne_w2 h.symm)
      rw [hge p2] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨a2, hpa2'⟩ = relGate (n + 1) (n + 1) σ ga2 := hGa2
      rw [hG]
      exact ⟨h1.trans hgaop2, h2, h3, h4, h5⟩
    · intro j _ hj
      have h1 := (hQ j _).1 hj
      rw [hRd, hge] at h1
      exact Fin.ext (hrd1 j h1)
    · intro j _ hj
      have h1 := (hQ j _).1 hj
      rw [hRd, hge] at h1
      exact Fin.ext (hrd2 j h1)
    · rcases hu1r with h | ⟨t, htp, hr⟩
      · exact Or.inl (asmW_lt σ h)
      · right
        have hr' : Reads gs' t (asmW σ u1) := (hRd t _).2 (by rw [asmW_inv σ hσ]; exact hr)
        exact ⟨⟨t, hlenR t _ hr'⟩, fun h => htp (congrArg Fin.val h), hltR t _ hr',
          (hQ _ _).2 hr'⟩
    · rcases hu2r with h | ⟨t, htp, hr⟩
      · exact Or.inl (asmW_lt σ h)
      · right
        have hr' : Reads gs' t (asmW σ u2) := (hRd t _).2 (by rw [asmW_inv σ hσ]; exact hr)
        exact ⟨⟨t, hlenR t _ hr'⟩, fun h => htp (congrArg Fin.val h), hltR t _ hr',
          (hQ _ _).2 hr'⟩
    · exact hoM
    · exact ⟨fun h => ho2p1 (congrArg Fin.val h), fun h => ho2p2 (congrArg Fin.val h)⟩
    · -- o2
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ go2 q2 W2 hoin2 (fun h => hne_W2 h.symm)
      rw [asmW_fin σ q2] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨o2, hpo2⟩ = relGate (n + 1) (n + 1) σ go2 := hGo2
      rw [hG]
      exact ⟨h1.trans hoo2, h2, h3, h4, h5⟩
    · intro j _ hj
      have h1 := (hQ j _).1 hj
      have hx : asmW σ ((σ q2 : Fin (n + 1)) : ℕ) = q2 := by rw [asmW_fin, hσ]
      rw [hRd, hx] at h1
      exact Fin.ext (hrq2 j h1)
    · -- M
      obtain ⟨h1, h2, h3, h4, h5⟩ := pq2e_gate2 σ hσ gM (n + 1 + o2) z hMin
        (fun h => hne_z h.symm)
      rw [hge o2] at h3 h5
      have hG : (Circuit.mk gs' o').gates.get ⟨jM, hpM⟩ = relGate (n + 1) (n + 1) σ gM := hGM
      rw [hG]
      exact ⟨h1.trans hMop, h2, h3, h4, h5⟩
    · intro j _ hj
      have h1 := (hQ j _).1 hj
      rw [hRd, hge] at h1
      exact Fin.ext (hrM j h1)
  have hsz : (Circuit.mk gs' o').size = gs.length := by
    simp [Circuit.size, hgs', asmG_len]
  refine ⟨s, by omega, ?_⟩
  have hsH' := relabel_size σ _ s hsH
  have heq : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin (n + 1) → Bool => y (Fin.last n) || H (fun i : Fin n => y i.castSucc)) (x ∘ σ)) =
      fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false) := by
    funext x
    have h := hF1 (x ∘ σ)
    have hxx : (x ∘ σ) ∘ σ = x := by funext i; simp [Function.comp, hσ]
    rw [cmp2, hxx] at h
    exact h.symm
  rw [heq] at hsH'
  exact hsH'

end PEqualNP.MetaComplexity.Helpers.RunAsm
