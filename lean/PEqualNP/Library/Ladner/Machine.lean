import PEqualNP.Library.Ladner.Spec
import PEqualNP.Library.Ladner.Core
import PEqualNP.Library.Universal.BruteForce
import PEqualNP.Library.Universal.CompileBool
import PEqualNP.Library.Universal.VerifyCPT
import PEqualNP.Library.L015

/-!
# The machine part of the delayed diagonalization

Helper module (proofs only, no statement may use it). The history step is polynomial-time
computable, by combinators only; hence the padding condition is in P. Every enumerated decider
is in P, every language in P is one of them (by the compiler), short members of the verifier
language are found by a bounded exhaustive search, and some verifier language is NP-complete.
-/

namespace PEqualNP.Library.Ladner

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Primitives -/

theorem ones_eq (h : List Bool) :
    ones h = h.filterMap (fun b : Bool => if b then some true else none) := by
  induction h with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simpa [ones] using ih
    · simpa [ones] using ih

theorem cpt_ones : CPT ones :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ones_eq

theorem cpt_dropU {c a : List Bool → List Bool} (hc : CPT c) (ha : CPT a) :
    CPT (fun s => dropU (c s) (a s)) :=
  cpt_iterLen cpt_tail (fun s => by simp) hc ha

theorem cpt_le {a b : List Bool → List Bool} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => if decide ((a s).length ≤ (b s).length) then [true] else []) :=
  cpt_bitFlag (cpt_comp (cpt_pair hb ha) LenCmp.lenLE_polyTime)

theorem cpt_leFlag {a b : List Bool → List Bool} (ha : CPT a) (hb : CPT b) :
    CPT (fun s => leFlag (a s) (b s)) :=
  cptE (cpt_le ha hb) (fun s => by simp [leFlag])

/-! ### The capped power -/

theorem cpt_tpStep : CPT tpStep := by
  have h2 : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hr : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hacc : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hzz : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have htot : CPT tpTot := cpt_app2 hr hacc
  have hprod := cpt_mulU2 hacc hzz
  have hA : CPT tpAcc := cpt_sel (cpt_leFlag hprod htot) htot hprod
  exact cpt_pairB2 (cpt_dropU hA htot) (cpt_pairB2 hA hzz)

theorem tpStep_length (s : List Bool) : (tpStep s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := tpAcc_length s
  have h4 : (tpTot s).length = (unpairB s).1.length + (unpairB (unpairB s).2).1.length := by
    simp [tpTot]
  rw [tpStep, pairB_length, pairB_length, dropU_length, h3, h4]
  omega

theorem cpt_tpw {zz k N : List Bool → List Bool} (hzz : CPT zz) (hk : CPT k) (hN : CPT N) :
    CPT (fun s => tpw (zz s) (k s) (N s)) :=
  cpt_unpairB1_1 (cpt_unpairB2_1 (cpt_iterGrow cpt_tpStep 2 tpStep_length hk
    (cpt_pairB2 hN (cpt_pairB2 (cpt_const [true]) hzz))))

/-! ### The enumeration and the binary length -/

theorem cpt_candOf {c : List Bool → List Bool} (hc : CPT c) :
    CPT (fun s => (unpairB (succB^[(c s).length] [])).1) :=
  cpt_unpairB1_1 (cpt_iterGrow bf_cpt_succB 1 bf_succB_length hc (cpt_const []))

theorem cpt_half : CPT half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

theorem cpt_lgStep : CPT lgStep :=
  cptE (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 cpt_half)))
    (fun _ => rfl)

theorem lgStep_length (s : List Bool) : (lgStep s).length ≤ s.length + 2 := by
  have h := unpairB_length s
  unfold lgStep sel
  split
  · omega
  · rename_i hne
    have h1 : 1 ≤ (unpairB s).2.length := by
      rcases hb : (unpairB s).2 with _ | ⟨b, l⟩
      · exact absurd hb hne
      · simp
    rw [pairB_length, half_eq, un_length, List.length_cons]
    omega

theorem cpt_lgU {f : List Bool → List Bool} (hf : CPT f) : CPT (fun s => lgU (f s)) :=
  cptE (cpt_unpairB1_1 (cpt_iterGrow cpt_lgStep 2 lgStep_length hf
    (cpt_pairB2 (cpt_const []) hf))) (fun _ => rfl)

theorem cpt_Vflag {F w : List Bool → List Bool} (hF : CPT F) (hw : CPT w) :
    CPT (fun s => if V (F s, w s) then [true] else []) :=
  cpt_bitFlag (cpt_comp (cpt_pair hF hw) (cpt_V cpt_sstep))

/-! ### The history step -/

theorem comb (g0 g1 g3 d c : Bool) (S : List Bool) :
    sel (sel (if g0 then [true] else []) []
      (sel (if g1 then [true] else []) []
        (sel (if g3 then [true] else []) []
          (sel (if d then [true] else [])
            (sel S [] (sel (if c then [true] else []) [] [true]))
            (sel S [true] (sel (if c then [true] else []) [true] []))))))
      [false] [true] = [g0 && (g1 && (g3 && (d != (!S.isEmpty && c))))] := by
  cases g0 <;> cases g1 <;> cases g3 <;> cases d <;> cases c <;> cases S <;> simp [sel]

section Step

variable (cA : List Bool) (q : Polynomial ℕ)

theorem cpt_hstep : CPT (hstep cA q) := by
  have hh : CPT (fun h : List Bool => h) := cpt_id
  have hst : CPT ones := cpt_ones
  have hz : CPT cz := cpt_candOf hh
  have hpsi : CPT (fun h => psi (cz h)) := cpt_unpairB1_1 hz
  have hbase : CPT (fun h => base (cz h)) := cpt_cons1 true (cpt_cons1 true hz)
  have hclk : CPT clk := cpt_tpw hbase hst hh
  have hrq : CPT (fun h => rq (ones h)) := cpt_candOf hst
  have hqry : CPT (fun h => qry cA q (psi (cz h))) := cpt_comp hpsi (bf_cpt_query cA q)
  have g0 := cpt_le hpsi hh
  have g1 := cpt_le hclk hh
  have g3 := cpt_le (cpt_app2 hqry (cpt_const [true, true]))
    (cpt_lgU (cpt_mulU2 hh (cpt_const [true])))
  have dV := cpt_Vflag (cpt_pairB2 hrq (cpt_pairB2 hz hclk)) (cpt_const [])
  have hS := bf_cpt_srch hqry hh
  have hstg : CPT (fun h => stg (psi (cz h)) h) :=
    cpt_dropU (cpt_comp (cpt_dropU hpsi hh) cpt_ones) hst
  have hpad : CPT (fun h => padOf (cz h) h) :=
    cpt_tpw (cpt_cons1 true (cpt_cons1 true hpsi)) hstg hz
  have gc := cpt_le hpad hz
  have all := cpt_sel (cpt_sel g0 (cpt_const []) (cpt_sel g1 (cpt_const [])
    (cpt_sel g3 (cpt_const []) (cpt_sel dV
      (cpt_sel hS (cpt_const []) (cpt_sel gc (cpt_const []) (cpt_const [true])))
      (cpt_sel hS (cpt_const [true]) (cpt_sel gc (cpt_const [true]) (cpt_const [])))))))
    (cpt_const [false]) (cpt_const [true])
  exact cptE (cpt_app2 hh all) (fun h => by rw [comb]; rfl)

theorem hstep_length (h : List Bool) : (hstep cA q h).length ≤ h.length + 1 := by
  simp [hstep]

theorem cpt_Hs {c : List Bool → List Bool} (hc : CPT c) :
    CPT (fun s => Hs cA q (c s).length) :=
  cpt_iterGrow (cpt_hstep cA q) 1 (hstep_length cA q) hc (cpt_const [])

/-- The padding condition is in P. -/
theorem pad_in_P : {y : List Bool | Gp cA q y} ∈ P := by
  refine ⟨fun y => decide ((tpw (base (psi y)) (ones (Hs cA q (psi y).length)) y).length ≤
    y.length), fun y => ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, decide_eq_true_eq, tpw_length _ _ _ (by simp [base]), base_length]
    show ((psi y).length + 2) ^ stage cA q (psi y).length ≤ y.length ↔
      min (((psi y).length + 2) ^ stage cA q (psi y).length) (y.length + 1) ≤ y.length
    omega
  · have hpsi : CPT psi := cpt_unpairB1
    exact cpt_comp (cpt_pair cpt_id (cpt_tpw (cpt_cons1 true (cpt_cons1 true hpsi))
      (cpt_comp (cpt_Hs cA q hpsi) cpt_ones) cpt_id)) LenCmp.lenLE_polyTime

/-- Short members of the verifier language are found by a bounded exhaustive search. -/
theorem brute (n₁ : ℕ) : ∃ B ∈ P, (∀ x ∈ B, x ∈ Acq cA q) ∧
    ∀ x ∈ Acq cA q, x.length < n₁ → x ∈ B := by
  obtain ⟨C, hC⟩ : ∃ C, C = 2 ^ (2 * cA.length + (2 * n₁ + q.eval n₁ + 1) + 1) := ⟨_, rfl⟩
  have hB : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => !(srch (qry cA q x) (un C)).isEmpty) :=
    cpt_comp (g := fun l : List Bool => !l.isEmpty)
      (bf_cpt_srch (bf_cpt_query cA q) (cpt_const (un C))) bf_cpt_neL
  refine ⟨{x | (!(srch (qry cA q x) (un C)).isEmpty) = true},
    ⟨fun x => !(srch (qry cA q x) (un C)).isEmpty, fun _ => Iff.rfl, hB⟩,
    fun x hx => srch_sound _ _ hx, fun x hx hlt => srch_complete _ _ (fun w hw => ?_) hx⟩
  have h1 := qry_witness cA q x w hw
  have h2 : (qry cA q x).length ≤ 2 * cA.length + (2 * n₁ + q.eval n₁ + 1) + 1 := by
    rw [qry_length]
    have := Machines.eval_mono q (show x.length ≤ n₁ by omega)
    omega
  have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
  rw [un_length, hC]
  omega

end Step

/-! ### The enumeration of deciders -/

/-- Every enumerated decider is in P. -/
theorem dec_in_P (i : ℕ) : {z : List Bool | Dd i z = true} ∈ P := by
  have hclock : CPT (fun z : List Bool => un ((z.length + 2) ^ i)) := by
    have h := L055 ((Polynomial.X + Polynomial.C 2) ^ i)
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] at h
    exact h
  have h : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun z : List Bool => V (pairB (rq (un i)) (pairB z (un ((z.length + 2) ^ i))), [])) :=
    cpt_comp (g := V) (cpt_pair (cpt_pairB2 (cpt_const (rq (un i)))
      (cpt_pairB2 cpt_id hclock)) (cpt_const [])) (cpt_V cpt_sstep)
  exact ⟨Dd i, fun _ => Iff.rfl, h⟩

/-- Every language in P is one of the enumerated deciders. -/
theorem cover : ∀ L ∈ P, ∃ i, ∀ z, Dd i z = true ↔ z ∈ L := by
  rintro L ⟨f, hf, ⟨cM⟩⟩
  obtain ⟨c, d, hc⟩ := compileBool cM.tm cM.inputAlphabet cM.outputAlphabet
  obtain ⟨k0, hk0⟩ := poly_le_pow2 (Polynomial.C d * cM.time + Polynomial.C d)
  have hrun : ∀ z : List Bool, ∃ n, n ≤ cM.time.eval z.length ∧
      c.outputsWithin (z.map (fun b => cond b 1 0)) (d * n + d) [bitCode (f z)] := by
    intro z
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cM.time.eval z.length ∧
        (flip bind (Turing.TM2.step cM.tm.m))^[n]
          (some (Turing.initList cM.tm (z.map cM.inputAlphabet.invFun))) =
        some (Turing.haltList cM.tm [cM.outputAlphabet.invFun (f z)]) :=
      ⟨(cM.outputsFun z).steps, (cM.outputsFun z).steps_le_m, (cM.outputsFun z).evals_in_steps⟩
    exact ⟨n, hn, hc z (f z) n hev⟩
  obtain ⟨i, hi0⟩ : ∃ i, i = idx (pairB (encCode c) (un k0)) := ⟨_, rfl⟩
  have hi : k0 ≤ i := by
    rw [hi0]
    exact le_trans (by rw [pairB_length, un_length]; omega) (length_le_idx _)
  have hrq : rq (un i) = encCode c := by
    rw [rq, un_length, hi0]
    show (unpairB (cand (idx (pairB (encCode c) (un k0))))).1 = encCode c
    rw [cand_idx, unpairB_pairB]
  refine ⟨i, fun z => ?_⟩
  obtain ⟨n, hn, ho⟩ := hrun z
  have hle : d * n + d ≤ (z.length + 2) ^ i := by
    have h1 := hk0 z.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at h1
    have h2 : d * n ≤ d * cM.time.eval z.length := Nat.mul_le_mul_left d hn
    have h3 : (z.length + 2) ^ k0 ≤ (z.length + 2) ^ i := Nat.pow_le_pow_right (by omega) hi
    omega
  have ho' := Code.outputsWithin_mono c _ hle _ ho
  have hV : Dd i z = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) ((z.length + 2) ^ i) [1] := by
    rw [Dd, hrq, V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  refine hV.trans (Iff.trans ?_ (hf z).symm)
  constructor
  · intro h1
    have heq : [1] = [bitCode (f z)] := h1.2.symm.trans ho'.2
    cases hb : f z with
    | true => rfl
    | false => rw [hb] at heq; simp [bitCode] at heq
  · intro hb
    rw [hb] at ho'
    exact ho'

/-- Some verifier language is NP-complete. -/
theorem verifier : ∃ (cA : List Bool) (q : Polynomial ℕ), NPComplete (Acq cA q) := by
  obtain ⟨L, hL⟩ := L015
  obtain ⟨c, q, hcomp, hsound⟩ := np_code L hL.1
  have e : Acq (encCode c) q = L :=
    Set.ext (fun x => ⟨fun ⟨w, hw⟩ => hsound x _ w hw, fun hx => hcomp x _ le_rfl hx⟩)
  exact ⟨encCode c, q, by rw [e]; exact hL⟩

end PEqualNP.Library.Ladner
