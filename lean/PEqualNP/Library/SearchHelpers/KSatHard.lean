import PEqualNP.Library.SearchHelpers.KSatHardStr
import PEqualNP.Library.Universal.SStepCPT

/-!
# Helpers: SAT reduces to 3-SAT in polynomial time

Helper module (proofs only, no statement may use it).

The main result is `KSat.sat_reduces_ksat3`. The reduction is the function `g` of
`KSatHardStr.lean`: on the encoding of a formula `φ` it is the encoding of `split φ`
(`KSatHardSplit.lean`, a uniform variant of the splitting of Karp, 1972), which is a 3-CNF
formula satisfiable exactly when `φ` is; on a string that encodes no formula it is `[false]`.

This file proves that `g` is polynomial-time computable. The item functions and the two tests
are finite-state transducers, the item number `i` of a round is reached by iterating `dropI`,
and the rounds are concatenated by the loop `cpt_flatMapRange`.
-/

namespace PEqualNP.Library.SearchHelpers.KSat.Hard

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### The item functions and the tests as transducers -/

/-- States of the small transducers. `b`: at the start (or at a pair boundary). `t`, `f`: one
symbol further, after `true` or after `false`. `e`: finished. -/
inductive IS : Type
  | b | t | f | e
  deriving DecidableEq

instance : Fintype IS :=
  ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩

def hiD : IS → Bool → IS × Option Bool
  | .b, true => (.t, some true)
  | .b, false => (.f, some false)
  | .t, d => (.b, some d)
  | .f, d => (.e, some d)
  | .e, _ => (.e, none)

theorem hiD_e (l : List Bool) : fstRun hiD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, hiD, ih]

theorem hiD_run : ∀ s : List Bool, fstRun hiD (fun _ => none) IS.b s = headI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, hiD, headI, hiD_run r]
  | false :: d :: r => by simp [fstRun, hiD, headI, hiD_e]

theorem cpt_headI : CPTs headI :=
  fst_polyTime _ _ _ hiD (fun _ => none) IS.b (fun s => (hiD_run s).symm)

def diD : IS → Bool → IS × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, _ => (.e, none)
  | .e, a => (.e, some a)

theorem diD_e (l : List Bool) : fstRun diD (fun _ => none) IS.e l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, diD, ih]

theorem diD_run : ∀ s : List Bool, fstRun diD (fun _ => none) IS.b s = dropI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, diD, dropI, diD_run r]
  | false :: d :: r => by simp [fstRun, diD, dropI, diD_e]

theorem cpt_dropI : CPTs dropI :=
  fst_polyTime _ _ _ diD (fun _ => none) IS.b (fun s => (diD_run s).symm)

def ieD : IS → Bool → IS × Option Bool
  | .b, false => (.f, none)
  | .f, false => (.t, none)
  | .t, _ => (.t, none)
  | _, _ => (.e, none)

def ieF : IS → Option Bool
  | .t => some true
  | _ => none

theorem ieD_e (l : List Bool) : fstRun ieD ieF IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

theorem ieD_t (l : List Bool) : fstRun ieD ieF IS.t l = [true] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

theorem ieD_run (s : List Bool) : fstRun ieD ieF IS.b s = bflag (isEnd s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [fstRun, ieD, ieD_e, ieD_t, isEnd, bflag]

theorem cpt_isEndF : CPTs (fun s => bflag (isEnd s)) :=
  fst_polyTime _ _ _ ieD ieF IS.b (fun s => (ieD_run s).symm)

theorem cpt_wfF : CPTs (fun s => bflag (wfB s)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

/-! ### One round -/

theorem cpt_litY (pol : Bool) {I : List Bool → List Bool} (hI : CPTs I) :
    CPTs (fun s => litY pol (I s)) :=
  cptE (cpt_cons1 true (cpt_cons1 pol (cpt_app2 (cpt_comp (cpt_cons1 true hI) cpt_spread)
    (cpt_const [true, true, false, true])))) (fun _ => rfl)

theorem cpt_litX {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun s => litX (I s)) :=
  cptE (cpt_app2 (cpt_tk (cpt_const [true, true]) hI)
    (cpt_cons1 true (cpt_cons1 true (cpt_tail1 (cpt_tail1 hI))))) (fun _ => rfl)

theorem cpt_outI {I R : List Bool → List Bool} (hI : CPTs I) (hR : CPTs R) :
    CPTs (fun s => outI (I s) (R s)) := by
  have hEnd : CPTs (fun s => bflag (isEnd (R s))) :=
    cptE (cpt_comp hR cpt_isEndF) (fun _ => rfl)
  have hH : CPTs (fun s => headI (R s)) := cpt_comp hR cpt_headI
  have hI1 : CPTs (fun s => true :: I s) := cpt_cons1 true hI
  have hT : CPTs (fun s => litY true (true :: I s) ++ [false, false]) :=
    cpt_app2 (cpt_litY true hI1) (cpt_const [false, false])
  exact cptE (cpt_sel hR (cpt_const []) (cpt_sel hEnd
    (cpt_app2 (cpt_litY false hI) (cpt_app2 (cpt_litX hH) hT))
    (cpt_app2 (cpt_litY false hI) (cpt_app2 (cpt_const [false, false]) hT))))
    (fun _ => rfl)

/-- The round on the packed argument `pairB (un i) x`. -/
def rnd (y : List Bool) : List Bool :=
  outI (unpairB y).1 (dropI^[(unpairB y).1.length] (unpairB y).2)

theorem cpt_rnd : CPTs rnd :=
  cpt_outI cpt_unpairB1 (cpt_iterLen cpt_dropI dropI_length cpt_unpairB1 cpt_unpairB2)

/-! ### The whole function -/

theorem cpt_G : CPTs G :=
  cptE (cpt_flatMapRange cpt_rnd cpt_id cpt_id) (fun x => by
    simp only [rnd, unpairB_pairB, un_length]
    rfl)

theorem cpt_g : CPTs g :=
  cptE (cpt_sel cpt_wfF (cpt_const [false])
    (cpt_app2 (cpt_const (encodeClause [(Y 0, true)])) cpt_G)) (fun _ => rfl)

end PEqualNP.Library.SearchHelpers.KSat.Hard

namespace PEqualNP.Library.SearchHelpers.KSat

open PEqualNP.Search PEqualNP.Library.SearchHelpers.SatV Hard

/-- SAT reduces to 3-SAT in polynomial time (Karp, 1972). -/
theorem sat_reduces_ksat3 :
    PEqualNP.Library.PolyTimeReducible PEqualNP.Search.SAT (PEqualNP.Search.KSAT 3) := by
  refine ⟨g, cpt_g, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨φ, rfl, hs⟩
    exact ⟨split φ, isKCNF_split φ, (g_enc φ).symm, (satisfiable_split φ).2 hs⟩
  · rintro ⟨ψ, -, he, hs⟩
    cases hw : wfB x with
    | false =>
      rw [g_not x hw] at he
      exact absurd he (not_enc_false ψ)
    | true =>
      obtain ⟨φ, rfl⟩ := (wfB_iff x).1 hw
      rw [g_enc φ] at he
      obtain rfl := encodeCNF_injective he
      exact ⟨φ, rfl, (satisfiable_split φ).1 hs⟩

end PEqualNP.Library.SearchHelpers.KSat
