import PEqualNP.Library.Helpers.TableauRun

/-!
# DTIME(t) has circuits of size O((t + n + 1)^3)

Helper module (proofs only, no statement may use it).

`dtime_size`: the machine is simulated by `t n` layers of the step circuit of
`TableauStep`, on configurations of height at most `H = n + p * t n + 1`, from the bits of the
initial configuration; the answer is the bottom cell of the output stack. The symbols are
restricted to the finitely many that can ever be on a stack (`pushSet`, the input symbols and
the accepting output symbol). The size is `O(t n * H)`, below `c * (t n + n + 1) ^ 3`.
-/

open Turing

namespace PEqualNP.Library.Helpers.Tableau

open PEqualNP.Library.Helpers.Enum
open PEqualNP.CircuitLowerBounds
open Classical

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false

theorem arith (A W0 CB P X Y tt : ℕ) (hY : Y ≤ P * X) (ht : tt ≤ X) (hX : 1 ≤ X) :
    14 * A * Y + tt * ((A * Y + W0) * (7 * Y) + A * Y * CB) ≤
      (14 * A * P + (A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by
  have hX2 : X ≤ X ^ 3 := by nlinarith [pow_le_pow_right₀ hX (show 1 ≤ 3 by norm_num), pow_one X]
  have h1 : 14 * A * Y + tt * ((A * Y + W0) * (7 * Y) + A * Y * CB) ≤
      14 * A * (P * X) + X * ((A * (P * X) + W0 * X) * (7 * (P * X)) + A * (P * X) * (CB * X)) := by
    have : W0 ≤ W0 * X := Nat.le_mul_of_pos_right _ hX
    have : CB ≤ CB * X := Nat.le_mul_of_pos_right _ hX
    gcongr
  refine h1.trans ?_
  have e : 14 * A * (P * X) + X * ((A * (P * X) + W0 * X) * (7 * (P * X)) + A * (P * X) * (CB * X))
      = 14 * A * P * X + ((A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by ring
  rw [e]
  have e2 : (14 * A * P + (A * P + W0) * 7 * P + A * P * CB) * X ^ 3 =
      14 * A * P * X ^ 3 + ((A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by ring
  rw [e2]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hX2) _

theorem dtime_size (t : ℕ → ℕ) (L : Language Bool) (hL : L ∈ PEqualNP.Library.DTIME t) :
    ∃ c : ℕ, L ∈ SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3) := by
  obtain ⟨f, hf, cm, hcm⟩ := hL
  let tm := cm.tm
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  let ι : Bool → tm.Γ tm.k₀ := cm.inputAlphabet.invFun
  let ι' : Bool → tm.Γ tm.k₁ := cm.outputAlphabet.invFun
  let T : Set (Σ k, tm.Γ k) := ((⋃ l, pushSet (tm.m l)) ∪
    Set.range (fun b => (⟨tm.k₀, ι b⟩ : Σ k, tm.Γ k))) ∪ {⟨tm.k₁, ι' true⟩}
  have hTfin : T.Finite :=
    ((Set.finite_iUnion fun l => pushSet_finite (tm.m l)).union (Set.finite_range _)).union
      (Set.finite_singleton _)
  letI : Fintype T := hTfin.fintype
  have hT : ∀ l, pushSet (tm.m l) ⊆ T := fun l x hx =>
    Or.inl (Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩))
  have hι : ∀ b, (⟨tm.k₀, ι b⟩ : Σ k, tm.Γ k) ∈ T := fun b => Or.inl (Or.inr ⟨b, rfl⟩)
  have hgT : (⟨tm.k₁, ι' true⟩ : Σ k, tm.Γ k) ∈ T := Or.inr rfl
  let d : ℕ := Finset.univ.sup fun l => pops (tm.m l)
  let p : ℕ := PEqualNP.Library.Machines.maxPush tm
  have hd : ∀ l, pops (tm.m l) ≤ d := fun l =>
    Finset.le_sup (f := fun l => pops (tm.m l)) (Finset.mem_univ l)
  have hp : ∀ l, PEqualNP.Library.Machines.pushes (tm.m l) ≤ p := fun l =>
    Finset.le_sup (f := fun l => PEqualNP.Library.Machines.pushes (tm.m l)) (Finset.mem_univ l)
  let A : ℕ := Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
    Fintype.card tm.K * Fintype.card T + Fintype.card tm.K
  let W0 : ℕ := Fintype.card (Wix (K := tm.K) tm.Λ tm.σ T d)
  let C0 : ℕ := CB (Λ := tm.Λ) (σ := tm.σ) T d p
  let P : ℕ := p + 2
  refine ⟨14 * A * P + (A * P + W0) * 7 * P + A * P * C0, fun n => ?_⟩
  let H : ℕ := n + p * t n + 1
  obtain ⟨F, hF, eF⟩ := run_bits T H d p tm.k₀ tm.main tm.initialState ι tm.m hd hp hT hι n
    (t n) (by omega)
  obtain ⟨gs, w', hbasic, hlen, hsem⟩ := hF n (fun i : Fin n => i.1)
  let gT : T := ⟨⟨tm.k₁, ι' true⟩, hgT⟩
  let oIdx : Idx (K := tm.K) tm.Λ tm.σ T H := .inr (.inr (.inl (tm.k₁, ⟨0, by omega⟩, gT)))
  refine ⟨⟨gs, w' oIdx⟩, hbasic, ?_, ?_⟩
  · -- size
    change gs.length ≤ _
    refine hlen.trans ?_
    have hcI : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) ≤ A * (H + 1) := by
      simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, A]
      nlinarith
    have hcIW : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H ⊕ Wix (K := tm.K) tm.Λ tm.σ T d) ≤
        A * (H + 1) + W0 := by
      rw [Fintype.card_sum]; omega
    have h7 : 7 * H + 1 ≤ 7 * (H + 1) := by omega
    have step1 : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * 14 +
        t n * (Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H ⊕ Wix (K := tm.K) tm.Λ tm.σ T d) *
          (7 * H + 1) + Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * C0) ≤
        14 * A * (H + 1) + t n * ((A * (H + 1) + W0) * (7 * (H + 1)) + A * (H + 1) * C0) := by
      have : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * 14 ≤ 14 * A * (H + 1) := by
        nlinarith
      gcongr
    refine step1.trans (arith A W0 C0 P (t n + n + 1) (H + 1) (t n) ?_ (by omega) (by omega))
    simp only [H, P]
    nlinarith
  · -- correctness
    intro x hx
    subst hx
    let ρ : Fin x.length → Bool := fun i => x[i.1]
    have hrep : Rep x (fun i : Fin x.length => i.1) ρ := by
      intro i
      refine ⟨i.2, ?_⟩
      simp [ρ, List.getD_eq_getElem?_getD]
    have hout := (hsem x ρ rfl hrep oIdx).2
    rw [eF] at hout
    -- the run of the machine
    have hrun := cm.outputsFun x
    obtain ⟨⟨s, hs⟩, hsm⟩ := hrun
    have hinit : initList tm (List.map cm.inputAlphabet.invFun x) =
        initCfg tm.k₀ tm.main tm.initialState ι ρ := by
      rw [PEqualNP.Library.Machines.initList_eq]
      simp only [initCfg, ρ, List.ofFn_getElem]
      rfl
    have hfinal : (stepT tm.m)^[t x.length] (initCfg tm.k₀ tm.main tm.initialState ι ρ) =
        haltList tm [ι' (f x)] := by
      rw [← hinit]
      exact iterate_stepT tm.m s _ _ hs rfl _ (hsm.trans (hcm _))
    rw [hfinal] at hout
    change Circuit.eval _ x = true ↔ x ∈ L
    unfold Circuit.eval
    rw [run_wires]
    change (run gs x).getD (w' oIdx) false = true ↔ x ∈ L
    rw [hout]
    refine Iff.trans ?_ (hf x).symm
    simp only [oIdx, enc, PEqualNP.Library.Machines.haltList_eq, Function.update_self,
      List.reverse_singleton, symBit, gT, decide_eq_true_eq]
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and]
    constructor
    · intro h; exact cm.outputAlphabet.symm.injective h
    · intro h; rw [h]

end PEqualNP.Library.Helpers.Tableau
