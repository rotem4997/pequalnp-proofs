import PEqualNP.Library.Universal.LazyDefs
import PEqualNP.Library.Universal.VerifyCPT
import PEqualNP.Library.Universal.SStepCPT

/-!
# The lazy diagonal relation is polynomial-time computable

Helper module (proofs only, no statement may use it).

The relation `RD` of `LazyDefs.lean` is polynomial-time computable on the pair encoding. The
pair is first packed into one string, and every subexpression of `RD` is then built bottom up
as a polynomial-time function of that string. Boolean subexpressions are carried as flag
strings (nonempty for true) and combined with `sel`.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptl {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Halving and the binary length -/

private theorem cpt_half : CPT half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

private theorem cpt_lgStep : CPT lgStep :=
  cptl (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 cpt_half)))
    (fun _ => rfl)

private theorem lgStep_length (s : List Bool) : (lgStep s).length ≤ s.length + 2 := by
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

private theorem cpt_lgU {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => lgU (f s)) :=
  cptl (cpt_unpairB1_1 (cpt_iterGrow cpt_lgStep 2 lgStep_length hf
    (cpt_pairB2 (cpt_const []) hf))) (fun _ => rfl)

/-- The threshold test as a flag string. -/
private theorem cpt_condC {y mu : List Bool → List Bool} (hy : CPT y) (hmu : CPT mu) :
    CPT (fun s => if condC (y s) (mu s) then [true] else []) :=
  cptl (cpt_bitFlag (cpt_comp (cpt_pair (cpt_lgU (cpt_lgU hmu)) hy) LenCmp.lenLE_polyTime))
    (fun _ => rfl)

/-! ### The bounded search -/

private theorem cpt_succB : CPT succB :=
  fst_polyTime _ _ _ succD succFin true (fun _ => rfl)

private theorem succD_length (q : Bool) (s : List Bool) :
    (fstRun succD succFin q s).length ≤ s.length + 1 := by
  induction s generalizing q with
  | nil => cases q <;> simp [fstRun, succFin]
  | cons b l ih =>
    have h1 := ih b
    have h2 := ih false
    cases q <;> simp [fstRun, succD] <;> omega

private theorem succB_length (s : List Bool) : (succB s).length ≤ s.length + 1 :=
  succD_length true s

private theorem bflag_length (b : Bool) : (bflag b).length ≤ 1 := by
  cases b <;> simp [bflag]

private theorem srchStep_length (s : List Bool) : (srchStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := succB_length (unpairB (unpairB s).2).1
  have h4 := bflag_length (V ((unpairB s).1, (unpairB (unpairB s).2).1))
  unfold srchStep
  rw [pairB_length, pairB_length, List.length_append]
  omega

private theorem cpt_srchStep : CPT srchStep := by
  have hF : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hc : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hF hc) (cpt_V cpt_sstep)
  have hb : CPT (fun s => bflag (V ((unpairB s).1, (unpairB (unpairB s).2).1))) :=
    cptl (cpt_bitFlag hV) (fun _ => rfl)
  have hs : CPT (fun s => succB (unpairB (unpairB s).2).1) := cpt_comp hc cpt_succB
  exact cptl (cpt_pairB2 hF (cpt_pairB2 hs (cpt_app2 hfl hb))) (fun _ => rfl)

private theorem cpt_srch {F n : List Bool → List Bool} (hF : CPT F) (hn : CPT n) :
    CPT (fun s => srch (F s) (n s)) :=
  cptl (cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_iterGrow cpt_srchStep 5 srchStep_length hn
    (cpt_pairB2 hF (cpt_pairB2 (cpt_const []) (cpt_const [])))))) (fun _ => rfl)

/-! ### From a flag string to a decision bit -/

private theorem neL_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neL :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neL_true, Computability.encodeBool])

private theorem combL (a b v : Bool) (S : List Bool) :
    (!(sel (if a then [true] else []) (if v then [true] else [])
      (sel (if b then [true] else []) (sel S [true] []) [])).isEmpty) =
      ((!a && v) || (a && (!b && S.isEmpty))) := by
  cases a <;> cases b <;> cases v <;> cases S <;> simp [sel]

/-! ### The relation -/

private theorem cpt_RDS :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => RD ((unpairB s).1, (unpairB s).2)) := by
  have hz : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hcs : CPT (fun s => csOf (unpairB s).1) :=
    cptl (cpt_unpairB1_1 hz) (fun _ => rfl)
  have hz2 : CPT (fun s => (unpairB (unpairB s).1).2) := cpt_unpairB2_1 hz
  have hmu : CPT (fun s => muOf (unpairB s).1) :=
    cptl (cpt_unpairB2_1 hz2) (fun _ => rfl)
  have hy0 : CPT (fun s => y0Of (unpairB s).1) :=
    cptl (cpt_pairB2 (cpt_unpairB1_1 hz) (cpt_pairB2 (cpt_unpairB1_1 hz2) (cpt_const [])))
      (fun _ => rfl)
  have hmt : CPT (fun s => (muOf (unpairB s).1).tail) := cpt_tail1 hmu
  have c1 := cpt_condC hy0 hmu
  have c2 := cpt_condC hy0 hmt
  have hw1 : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hw
  have hw2 : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hw
  have hzt : CPT (fun s => (unpairB s).1 ++ [true]) := cpt_app2 hz (cpt_const [true])
  have hVa : CPT (fun s => pairB (csOf (unpairB s).1)
      (pairB ((unpairB s).1 ++ [true]) (unpairB (unpairB s).2).2)) :=
    cpt_pairB2 hcs (cpt_pairB2 hzt hw2)
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (pairB (csOf (unpairB s).1)
        (pairB ((unpairB s).1 ++ [true]) (unpairB (unpairB s).2).2),
        (unpairB (unpairB s).2).1)) :=
    cpt_comp (cpt_pair hVa hw1) (cpt_V cpt_sstep)
  have fv := cpt_bitFlag hV
  have hSF : CPT (fun s => pairB (csOf (unpairB s).1)
      (pairB (y0Of (unpairB s).1) (lgU (muOf (unpairB s).1)))) :=
    cpt_pairB2 hcs (cpt_pairB2 hy0 (cpt_lgU hmu))
  have hSn : CPT (fun s => muOf (unpairB s).1 ++ (muOf (unpairB s).1 ++
      (muOf (unpairB s).1 ++ muOf (unpairB s).1))) :=
    cpt_app2 hmu (cpt_app2 hmu (cpt_app2 hmu hmu))
  have hS := cpt_srch hSF hSn
  have fS := cpt_sel hS (cpt_const [true]) (cpt_const [])
  have all := cpt_sel c1 fv (cpt_sel c2 fS (cpt_const []))
  exact cptl (cpt_comp all cpt_neL) (fun s => combL _ _ _ _)

/-- The lazy diagonal relation is polynomial-time computable. -/
theorem cpt_RD : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
    Computability.encodeBool RD :=
  cptl (cpt_comp cpt_pairB cpt_RDS) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

end PEqualNP.Library.Universal
