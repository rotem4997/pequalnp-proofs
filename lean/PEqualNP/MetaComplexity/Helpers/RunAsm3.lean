import PEqualNP.MetaComplexity.Helpers.RunAsm2
import PEqualNP.MetaComplexity.Helpers.RunPNA
import PEqualNP.MetaComplexity.L588

/-!
# Run-of-four assembly, part 3: the NOT state at a run end drops five gates (given the chain law)

Paper: the run-of-four argument in direct form, section 4 case II.3 and section 5 ENTRY
"II.3 -> (P-NA) -> either Drop 5 or NA -> (P-NL) -> Drop 5". (P-NA) is `RunPNA.pna_main`; the
NA state goes to the checked row L-meta-588 after the inputs are relabelled by the swap of `q0`
and `Fin.last n`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.EdgeFn PEqualNP.MetaComplexity.Helpers.RunPNA

/-- The statement of row L-meta-568 (the free-input chain law), verbatim. -/
def asmChain : Prop :=
  (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w))

theorem asm_relGate_ge {m : ℕ} (σ : Equiv.Perm (Fin m)) (g : Gate) (h : ∀ a ∈ g.inputs, m ≤ a) :
    relGate m m σ g = g := by
  cases g with
  | mk op ins =>
    simp only [relGate, Gate.mk.injEq, true_and]
    conv_rhs => rw [← List.map_id ins]
    apply List.map_congr_left
    intro a ha
    exact asmW_ge σ (h a ha)

/-- The edge function with `x_e := 1`, `e` adjacent to `u`, depends on `u`. -/
theorem asm_dep1 {N : ℕ} (G : SimpleGraph (Fin N)) (e u : Fin N) (heu : G.Adj e u)
    (hnoe : ∀ w, G.Adj e w → w ≠ e) :
    F G ∅ (Function.update (fun _ => false) e true) = false ∧
      F G ∅ (Function.update (Function.update (fun _ => false) u true) e true) = true := by
  have hue : u ≠ e := heu.ne.symm
  constructor
  · apply F_false_of {e}
    · intro i hi
      by_cases h : i = e
      · simp [h]
      · simp [Function.update_apply, h] at hi
    · simp
    · intro i j hij hi hj
      simp at hi hj
      subst hi; subst hj
      exact G.loopless.irrefl _ hij
  · exact F_true_of e u heu (by simp) (by simp [Function.update_apply, hue])

/-- The value of `Fin.snoc z false` at `Fin.last n`... and at a cast. -/
theorem asm_snoc_false {n : ℕ} (k : Fin (n + 1)) :
    (Fin.snoc (α := fun _ => Bool) (fun _ : Fin n => false) false) k = false := by
  induction k using Fin.lastCases <;> simp

/-- (P-NA) then L-meta-588: the NOT state at a run end drops five gates at `x_e := 1`. -/
theorem asm_endN (hch : asmChain) (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (q0 e q2 : Fin (n + 1))
    (he : ∀ w, G.Adj e w ↔ w = q0 ∨ w = q2) (h02 : q0 ≠ q2)
    (gs : List Gate) (o pn pm ph : ℕ) (gm : Gate) (L : Least (n + 1) (F G ∅) gs o)
    (hpn : gs[pn]? = some ⟨GateOp.not, [(e : ℕ)]⟩) (he1 : ∀ t, Reads gs t e → t = pn)
    (hpm : gs[pm]? = some gm) (hmop : gm.op = GateOp.and)
    (hmin : gm.inputs = [n + 1 + pn, n + 1 + ph] ∨ gm.inputs = [n + 1 + ph, n + 1 + pn])
    (hn1 : ∀ t, Reads gs t (n + 1 + pn) → t = pm)
    (hph : ph < gs.length) (hh1 : ∀ t, Reads gs t (n + 1 + ph) → t = pm)
    (ho : o ≠ n + 1 + pm) : Drop (F G ∅) e true 5 gs.length := by
  have heq0 : G.Adj e q0 := (he q0).2 (Or.inl rfl)
  have heq2 : G.Adj e q2 := (he q2).2 (Or.inr rfl)
  have hnoe : ∀ w, G.Adj e w → w ≠ e := fun w h => h.ne.symm
  have hnc : ∃ x x' : Fin (n + 1) → Bool,
      F G ∅ (Function.update x e true) ≠ F G ∅ (Function.update x' e true) := by
    obtain ⟨h1, h2⟩ := asm_dep1 G e q0 heq0 hnoe
    exact ⟨fun _ => false, Function.update (fun _ => false) q0 true, by rw [h1, h2]; simp⟩
  have hfnc : ∃ x y : Fin (n + 1) → Bool, F G ∅ x ≠ F G ∅ y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  rcases pna_main n (F G ∅) gs o pn pm ph gm e L hnc hpn he1 hpm hmop hmin hn1 hph hh1 ho with
    h5 | ⟨pS, gS, s, hpS, hSop, hSin, -, hm1⟩
  · exact h5
  have hpnph : pn ≠ ph := pna_ne L hfnc pn pm ph gm hpm hmop hmin
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap q0 (Fin.last n) with hσdef
  have hσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  have L' := asm_least σ hσ L
  set gs' := asmG σ gs with hgs'
  set o' := asmW σ o
  set e' := σ e with he'
  have hwe : asmW σ (e' : ℕ) = e := by rw [asmW_fin, hσ]
  have hge : ∀ k, asmW σ (n + 1 + k) = n + 1 + k := fun k => asmW_ge σ (by omega)
  have hpn' : gs'[pn]? = some ⟨GateOp.not, [(e' : ℕ)]⟩ := by
    rw [hgs', asmG_get, hpn]
    simp only [Option.map_some, relGate, List.map_cons, List.map_nil]
    rw [show wmap (n + 1) (n + 1) σ (e : ℕ) = (e' : ℕ) from asmW_fin σ e]
  have hgm : relGate (n + 1) (n + 1) σ gm = gm := asm_relGate_ge σ gm (by
    intro a ha; rcases hmin with h | h <;> rw [h] at ha <;> simp at ha <;> omega)
  have hpm' : gs'[pm]? = some gm := by rw [hgs', asmG_get, hpm]; simp [hgm]
  have hpS' : gs'[pS]? = some (relGate (n + 1) (n + 1) σ gS) := by
    rw [hgs', asmG_get, hpS]; rfl
  have hSin' : n + 1 + pm ∈ (relGate (n + 1) (n + 1) σ gS).inputs :=
    List.mem_map.2 ⟨_, by rcases hSin with h | h <;> rw [h] <;> simp, hge pm⟩
  have hrd : ∀ t w, Reads gs' t w → Reads gs t (asmW σ w) := fun t w h =>
    (asm_reads σ hσ gs t w).1 h
  have he1' : ∀ t, Reads gs' t e' → t = pn := fun t h => he1 t (by have := hrd t _ h; rwa [hwe] at this)
  have hn1' : ∀ t, Reads gs' t (n + 1 + pn) → t = pm := fun t h => hn1 t (by have := hrd t _ h; rwa [hge] at this)
  have hh1' : ∀ t, Reads gs' t (n + 1 + ph) → t = pm := fun t h => hh1 t (by have := hrd t _ h; rwa [hge] at this)
  have hm1' : ∀ t, Reads gs' t (n + 1 + pm) → t = pS := fun t h => hm1 t (by have := hrd t _ h; rwa [hge] at this)
  have hph' : ph < gs'.length := by rw [hgs', asmG_len]; exact hph
  obtain ⟨hfan, pn'', pm'', pS'', ph'', -, -, -, hphv, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11,
    c12⟩ := pna_to_588 n gs' o' e' pn pm ph pS gm (relGate (n + 1) (n + 1) σ gS) L'.hcl hpnph hpn'
      he1' hpm' hmop hmin hn1' hph' hh1' hpS' hSop hSin' hm1'
  have hcf : ∀ y : Fin (n + 1) → Bool, circuitFun (n + 1) (Circuit.mk gs' o') y = F G ∅ (y ∘ σ) :=
    fun y => L'.hev y
  have hcomp : ∀ y : Fin (n + 1) → Bool,
      Function.update y e' true ∘ σ = Function.update (y ∘ σ) e true := by
    intro y
    rw [Function.update_comp_equiv]
    congr 1
    rw [he']
    exact Equiv.symm_apply_apply σ e
  have hq0e : q0 ≠ e := heq0.ne.symm
  have hσq0 : σ q0 = Fin.last n := by rw [hσdef]; exact Equiv.swap_apply_left _ _
  have hσl : σ (Fin.last n) = q0 := by rw [hσdef]; exact Equiv.swap_apply_right _ _
  have hne' : e' ≠ Fin.last n := by
    intro h
    apply hq0e
    rw [← hσl, ← h, he', hσ]
  set H : (Fin n → Bool) → Bool := fun z =>
    F G ∅ (Function.update ((Fin.snoc (α := fun _ => Bool) z false) ∘ σ) e true) with hHdef
  have hF1 : ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) (Circuit.mk gs' o') (Function.update x e' true) =
        (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := by
    intro x
    rw [hcf, hcomp]
    cases hx : x (Fin.last n)
    · simp only [Bool.false_or, hHdef]
      have : (Fin.snoc (α := fun _ => Bool) (fun i : Fin n => x i.castSucc) false) = x := by
        rw [← hx]; exact Fin.snoc_init_self x
      rw [this]
    · simp only [Bool.true_or]
      apply F_true_of e q0 heq0 (by simp)
      rw [Function.update_apply, if_neg hq0e]
      simp [hσq0, hx]
  have hH : ∃ y y' : Fin n → Bool, H y ≠ H y' := by
    have hq2l : σ q2 ≠ Fin.last n := by
      intro h; apply h02; rw [← hσl, ← h, hσ]
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hq2l
    refine ⟨fun _ => false, fun j => decide (j = i), ?_⟩
    have h0 : H (fun _ => false) = false := by
      rw [hHdef]
      apply F_false_of {e}
      · intro k hk
        by_cases h : k = e
        · simp [h]
        · rw [Function.update_apply, if_neg h] at hk
          simp [asm_snoc_false] at hk
      · simp
      · intro i' j' hij hi' hj'
        simp at hi' hj'
        subst hi'; subst hj'
        exact G.loopless.irrefl _ hij
    have h1 : H (fun j => decide (j = i)) = true := by
      rw [hHdef]
      apply F_true_of e q2 heq2 (by simp)
      rw [Function.update_apply, if_neg heq2.ne.symm]
      show (Fin.snoc (α := fun _ => Bool) (fun j : Fin n => decide (j = i)) false) (σ q2) = true
      rw [← hi, Fin.snoc_castSucc]
      simp
    rw [h0, h1]; simp
  have hpt : circuitFun (n + 1) (Circuit.mk gs' o') (fun i : Fin (n + 1) => decide (i = Fin.last n))
      = false := by
    rw [hcf]
    apply F_false_of {q0}
    · intro k hk
      simp only [Function.comp_apply, decide_eq_true_eq] at hk
      rw [Finset.mem_singleton, ← hσl, ← hk, hσ]
    · simp
    · intro i' j' hij hi' hj'
      simp at hi' hj'
      subst hi'; subst hj'
      exact G.loopless.irrefl _ hij
  have key := (PEqualNP.MetaComplexity.L588 hch n (Circuit.mk gs' o') H e' pn'' pm'' pS'' hfan hne' hH
    hF1 hpt c1 c2 c3 c4 c5 c6 c7 c8 c9).2 ph'' c10 c11 c12
  have hlen : (Circuit.mk gs' o').gates.length = gs.length := by
    show gs'.length = gs.length
    rw [hgs', asmG_len]
  rw [hlen] at key
  have key2 := relabel_size (⇑σ) _ _ key
  have hfun : (fun x : Fin (n + 1) → Bool =>
      circuitFun (n + 1) (Circuit.mk gs' o') (Function.update (x ∘ σ) e' true)) =
      fun x => F G ∅ (Function.update x e true) := by
    funext x
    rw [hcf, hcomp]
    congr 2
    funext i; simp [hσ]
  rw [hfun] at key2
  have hdep : ∀ u, G.Adj e u → ∃ x : Fin (n + 1) → Bool,
      (fun x => F G ∅ (Function.update x e true)) (Function.update x u (!x u)) ≠
        (fun x => F G ∅ (Function.update x e true)) x := by
    intro u hu
    obtain ⟨h1, h2⟩ := asm_dep1 G e u hu hnoe
    exact ⟨fun _ => false, by simp only [Bool.not_false]; rw [h1, h2]; simp⟩
  have h2 := dep_lower_set (n + 1) _ {q0, q2} (by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hdep _ heq0
    · rw [Finset.mem_singleton] at ht; subst ht; exact hdep _ heq2) _ key2
  rw [Finset.card_pair h02] at h2
  exact ⟨gs.length - 5, by omega, key2⟩

end PEqualNP.MetaComplexity.Helpers.RunAsm
