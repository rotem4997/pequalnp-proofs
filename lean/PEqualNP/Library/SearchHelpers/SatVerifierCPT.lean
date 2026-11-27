import PEqualNP.Library.SearchHelpers.SatVerifier
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.MetaComplexity.Helpers.Machines.StrEq

/-!
# The verifier for SAT is polynomial-time computable

Helper module (proofs only, no statement may use it).

The verifier `SV` of `SatVerifierDefs.lean` is polynomial-time computable on the pair encoding.
The pair is first packed into one string, and every subexpression of `SV` is then built bottom
up as a polynomial-time function of that string. Boolean subexpressions are carried as flag
strings (nonempty for true) and combined with `sel`. The item functions and the fixed-prefix
tests are finite-state transducers; the two bounded iterations go through `cpt_iterGrow`.
-/

namespace PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The item functions and the prefix tests as transducers -/

/-- States of the small transducers. `b`: at the start (or at a pair boundary). `t`, `f`: one
symbol further, after `true` or after `false`. `e`: finished. -/
private inductive IS : Type
  | b | t | f | e
  deriving DecidableEq

private instance : Fintype IS :=
  ⟨{.b, .t, .f, .e}, fun q => by cases q <;> simp⟩

private def hiD : IS → Bool → IS × Option Bool
  | .b, true => (.t, some true)
  | .b, false => (.f, some false)
  | .t, d => (.b, some d)
  | .f, d => (.e, some d)
  | .e, _ => (.e, none)

private theorem hiD_e (l : List Bool) : fstRun hiD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, hiD, ih]

private theorem hiD_run : ∀ s : List Bool, fstRun hiD (fun _ => none) IS.b s = headI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, hiD, headI, hiD_run r]
  | false :: d :: r => by simp [fstRun, hiD, headI, hiD_e]

private theorem cpt_headI : CPT headI :=
  fst_polyTime _ _ _ hiD (fun _ => none) IS.b (fun s => (hiD_run s).symm)

private def diD : IS → Bool → IS × Option Bool
  | .b, true => (.t, none)
  | .b, false => (.f, none)
  | .t, _ => (.b, none)
  | .f, _ => (.e, none)
  | .e, a => (.e, some a)

private theorem diD_e (l : List Bool) : fstRun diD (fun _ => none) IS.e l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, diD, ih]

private theorem diD_run : ∀ s : List Bool, fstRun diD (fun _ => none) IS.b s = dropI s
  | [] => rfl
  | [a] => by cases a <;> rfl
  | true :: d :: r => by simp [fstRun, diD, dropI, diD_run r]
  | false :: d :: r => by simp [fstRun, diD, dropI, diD_e]

private theorem cpt_dropI : CPT dropI :=
  fst_polyTime _ _ _ diD (fun _ => none) IS.b (fun s => (diD_run s).symm)

private def poD : IS → Bool → IS × Option Bool
  | .b, _ => (.t, none)
  | .t, true => (.e, some true)
  | _, _ => (.e, none)

private theorem poD_e (l : List Bool) : fstRun poD (fun _ => none) IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, poD, ih]

private theorem poD_run (s : List Bool) :
    fstRun poD (fun _ => none) IS.b s = bflag (polB s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · rfl
  · cases b <;> simp [fstRun, poD, poD_e, polB, bflag]

private theorem cpt_polF : CPT (fun s => bflag (polB s)) :=
  fst_polyTime _ _ _ poD (fun _ => none) IS.b (fun s => (poD_run s).symm)

private def ieD : IS → Bool → IS × Option Bool
  | .b, false => (.f, none)
  | .f, false => (.t, none)
  | .t, _ => (.t, none)
  | _, _ => (.e, none)

private def ieF : IS → Option Bool
  | .t => some true
  | _ => none

private theorem ieD_e (l : List Bool) : fstRun ieD ieF IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

private theorem ieD_t (l : List Bool) : fstRun ieD ieF IS.t l = [true] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, ieD, ih]

private theorem ieD_run (s : List Bool) : fstRun ieD ieF IS.b s = bflag (isEnd s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [fstRun, ieD, ieD_e, ieD_t, isEnd, bflag]

private theorem cpt_isEndF : CPT (fun s => bflag (isEnd s)) :=
  fst_polyTime _ _ _ ieD ieF IS.b (fun s => (ieD_run s).symm)

private theorem cpt_wfF : CPT (fun s => bflag (wfB s)) :=
  fst_polyTime _ _ _ (fun (q : WS) (a : Bool) => (wfD q a, (none : Option Bool)))
    (fun q => if q = WS.a then some true else none) WS.a (fun s => wfB_eq_fstRun s)

/-! ### Flags -/

private theorem flag_ne (F : List Bool) : sel F [] [true] = bflag (!F.isEmpty) := by
  cases F <;> simp [sel, bflag]

private theorem flag_em (F : List Bool) : sel F [true] [] = bflag F.isEmpty := by
  cases F <;> simp [sel, bflag]

private theorem flag_lit (m p : Bool) :
    sel (bflag m) (sel (bflag p) [true] []) (bflag p) = bflag ((m && p) || (!m && !p)) := by
  cases m <;> cases p <;> simp [sel, bflag]

private theorem flag_fin (a : Bool) (B : List Bool) :
    (!(sel (bflag a) [] (sel B [true] [])).isEmpty) = (a && B.isEmpty) := by
  cases a <;> cases B <;> simp [sel, bflag]

private theorem cpt_eqF {u v : List Bool → List Bool} (hu : CPT u) (hv : CPT v) :
    CPT (fun s => bflag (decide (u s = v s))) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  exact cptl (cpt_bitFlag (cpt_comp (cpt_pair hu hv) s)) (fun _ => rfl)

/-! ### Membership -/

private theorem cpt_memStep : CPT memStep := by
  have hc : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hr : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hd : CPT (fun s => dropI (unpairB (unpairB s).2).1) := cpt_comp hr cpt_dropI
  have hh : CPT (fun s => headI (unpairB (unpairB s).2).1) := cpt_comp hr cpt_headI
  have he : CPT (fun s => bflag (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))) :=
    cpt_eqF hh hc
  exact cptl (cpt_pairB2 hc (cpt_pairB2 hd (cpt_app2 hfl he))) (fun _ => rfl)

private theorem cpt_memB {C W : List Bool → List Bool} (hC : CPT C) (hW : CPT W) :
    CPT (fun s => bflag (memB (C s) (W s))) := by
  have hit : CPT (fun s => memStep^[(W s).length] (pairB (C s) (pairB (W s) []))) :=
    cpt_iterGrow cpt_memStep 3 memStep_length hW (cpt_pairB2 hC (cpt_pairB2 hW (cpt_const [])))
  have hF : CPT (fun s =>
      (unpairB (unpairB (memStep^[(W s).length] (pairB (C s) (pairB (W s) [])))).2).2) :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hit)
  exact cptl (cpt_sel hF (cpt_const []) (cpt_const [true])) (fun s => flag_ne _)

private theorem cpt_litB {I W : List Bool → List Bool} (hI : CPT I) (hW : CPT W) :
    CPT (fun s => bflag (litB (I s) (W s))) := by
  have hM : CPT (fun s => bflag (memB (I s).tail.tail (W s))) :=
    cpt_memB (cpt_tail1 (cpt_tail1 hI)) hW
  have hP : CPT (fun s => bflag (polB (I s))) :=
    cptl (cpt_comp hI cpt_polF) (fun _ => rfl)
  exact cptl (cpt_sel hM (cpt_sel hP (cpt_const [true]) (cpt_const [])) hP)
    (fun s => flag_lit _ _)

/-! ### Evaluation -/

private theorem cpt_evStep : CPT evStep := by
  have hW : CPT (fun s => stW s) := cpt_unpairB1
  have h2 : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hR : CPT (fun s => stR s) := cpt_unpairB1_1 h2
  have h3 : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hC : CPT (fun s => stC s) := cpt_unpairB1_1 h3
  have hB : CPT (fun s => stB s) := cpt_unpairB2_1 h3
  have hD : CPT (fun s => dropI (stR s)) := cpt_comp hR cpt_dropI
  have hH : CPT (fun s => headI (stR s)) := cpt_comp hR cpt_headI
  have hEnd : CPT (fun s => bflag (isEnd (stR s))) :=
    cptl (cpt_comp hR cpt_isEndF) (fun _ => rfl)
  have hL : CPT (fun s => bflag (litB (headI (stR s)) (stW s))) := cpt_litB hH hW
  have hE : CPT (fun s => bflag (stC s).isEmpty) :=
    cptl (cpt_sel hC (cpt_const [true]) (cpt_const [])) (fun s => flag_em _)
  exact cptl (cpt_pairB2 hW (cpt_pairB2 hD (cpt_sel hEnd
    (cpt_pairB2 (cpt_app2 hC hL) hB) (cpt_pairB2 (cpt_const []) (cpt_app2 hB hE)))))
    (fun _ => rfl)

/-! ### From a flag string to a decision bit -/

private theorem neS_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neS :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neS_true, Computability.encodeBool])

/-! ### The verifier -/

private theorem cpt_SVS :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => SV ((unpairB s).1, (unpairB s).2)) := by
  have hx : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hit : CPT (fun s => evStep^[((unpairB s).1).length]
      (pairB (unpairB s).2 (pairB (unpairB s).1 (pairB [] [])))) :=
    cpt_iterGrow cpt_evStep 5 evStep_length hx
      (cpt_pairB2 hw (cpt_pairB2 hx (cpt_pairB2 (cpt_const []) (cpt_const []))))
  have hB : CPT (fun s => stB (evStep^[((unpairB s).1).length]
      (pairB (unpairB s).2 (pairB (unpairB s).1 (pairB [] []))))) :=
    cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_unpairB2_1 hit))
  have hwf : CPT (fun s => bflag (wfB (unpairB s).1)) :=
    cptl (cpt_comp hx cpt_wfF) (fun _ => rfl)
  have all := cpt_sel hwf (cpt_const []) (cpt_sel hB (cpt_const [true]) (cpt_const []))
  exact cptl (cpt_comp all cpt_neS) (fun s => flag_fin _ _)

/-- The verifier for SAT is polynomial-time computable. -/
theorem cpt_SV : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool SV :=
  cptl (cpt_comp cpt_pairB cpt_SVS) (fun p => by
    obtain ⟨x, w⟩ := p
    simp only [unpairB_pairB])

end PEqualNP.Library.SearchHelpers.SatV
