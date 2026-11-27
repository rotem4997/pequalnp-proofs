import PEqualNP.Library.SearchHelpers.TwoSatStr
import PEqualNP.Library.SearchHelpers.KSatHard
import PEqualNP.MetaComplexity.Helpers.Machines.StrEq

/-!
# Helpers: the decision function for 2-SAT is polynomial-time computable

Helper module (proofs only, no statement may use it).

The function `dec` of `TwoSatStr.lean` is polynomial-time computable. Every subexpression is
built bottom up as a polynomial-time function of the input. Boolean subexpressions are carried
as flag strings (nonempty for true) and combined with `sel`. The item functions and the tests
are finite-state transducers. The rotation `stepS` keeps the length of the code of the formula
and lengthens the list by at most that length, so its iteration goes through the measured
iteration theorem; the check `chkStep` lengthens its state by a constant.
-/

namespace PEqualNP.Library.SearchHelpers.TwoSat

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.Library.SearchHelpers.Tab.StepW

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem cptG {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Small transducers -/

/-- Transition of the polarity test: the second symbol is written when it is `true`. -/
def poD : KSat.Hard.IS → Bool → KSat.Hard.IS × Option Bool
  | .b, _ => (.t, none)
  | .t, true => (.e, some true)
  | _, _ => (.e, none)

theorem poD_e (l : List Bool) : fstRun poD (fun _ => none) KSat.Hard.IS.e l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, poD, ih]

theorem poD_run (s : List Bool) :
    fstRun poD (fun _ => none) KSat.Hard.IS.b s = bflag (polB s) := by
  rcases s with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · rfl
  · cases b <;> simp [fstRun, poD, poD_e, polB, bflag]

theorem cpt_polF : CPTs (fun s => bflag (polB s)) :=
  fst_polyTime _ _ _ poD (fun _ => none) KSat.Hard.IS.b (fun s => (poD_run s).symm)

/-- Position inside a pair: at a pair boundary, after `true`, after `false`. -/
inductive Ph : Type
  | b | t | f
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{.b, .t, .f}, fun q => by cases q <;> simp⟩

/-- Transition of the width test. The state is the number of literals closed in the current
clause and the position inside a pair, or `none` after a rejection. Nothing is written. -/
def wD : Option (Fin 3 × Ph) → Bool → Option (Fin 3 × Ph) × Option Bool
  | none, _ => (none, none)
  | some (n, .b), true => (some (n, .t), none)
  | some (n, .b), false => (some (n, .f), none)
  | some (n, .t), _ => (some (n, .b), none)
  | some (n, .f), false => (if 0 < n.val then some (⟨0, by omega⟩, .b) else none, none)
  | some (n, .f), true =>
    (if h : n.val < 2 then some (⟨n.val + 1, by omega⟩, .b) else none, none)

/-- The symbol written at the end: `true` when the string is accepted. -/
def wF : Option (Fin 3 × Ph) → Option Bool
  | some (_, .b) => some true
  | _ => none

theorem wD_none (l : List Bool) : fstRun wD wF none l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun, wD, ih]

theorem wD_run : ∀ (x : List Bool) (n : ℕ) (h : n < 3),
    fstRun wD wF (some (⟨n, h⟩, Ph.b)) x = bflag (w2 n x)
  | [], n, h => by simp [fstRun, wF, w2, bflag]
  | [a], n, h => by cases a <;> simp [fstRun, wD, wF, w2, bflag]
  | true :: d :: r, n, h => by simp [fstRun, wD, w2, wD_run r n h]
  | false :: false :: r, n, h => by
    by_cases h0 : 0 < n
    · simp only [fstRun, wD, w2, h0, ite_true, Option.toList_none, List.nil_append,
        decide_true, Bool.true_and]
      exact wD_run r 0 (by omega)
    · simp [fstRun, wD, w2, h0, wD_none, bflag]
  | false :: true :: r, n, h => by
    by_cases h2 : n < 2
    · simp [fstRun, wD, w2, h2, wD_run r (n + 1) (by omega)]
    · simp [fstRun, wD, w2, h2, wD_none, bflag]

theorem cpt_w2F : CPTs (fun x => bflag (w2 0 x)) :=
  fst_polyTime _ _ _ wD wF (some (⟨0, by omega⟩, Ph.b))
    (fun x => (wD_run x 0 (by omega)).symm)

theorem neS_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

theorem cpt_neS :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neS_true, Computability.encodeBool])

/-! ### Flags -/

theorem flag_ne (F : List Bool) : sel F [] [true] = bflag (!F.isEmpty) := by
  cases F <;> simp [sel, bflag]

theorem flag_and (m p : Bool) : sel (bflag m) [] (bflag p) = bflag (m && p) := by
  cases m <;> cases p <;> simp [sel, bflag]

theorem flag_fin (a b : Bool) (B : List Bool) :
    (!(sel (bflag a) [] (sel (bflag b) [] (sel B [true] []))).isEmpty) =
      (a && (b && B.isEmpty)) := by
  cases a <;> cases b <;> cases B <;> simp [sel, bflag]

theorem cpt_eqF {u v : List Bool → List Bool} (hu : CPTs u) (hv : CPTs v) :
    CPTs (fun s => bflag (decide (u s = v s))) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
    PEqualNP.MetaComplexity.Helpers.Machines.strEq_polyTime (A := Bool)
  exact cptG (cpt_bitFlag (cpt_comp (cpt_pair hu hv) s)) (fun _ => rfl)

/-! ### Membership and the rotation -/

theorem cpt_memStep : CPTs memStep := by
  have hc : CPTs (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPTs (fun s => (unpairB s).2) := cpt_unpairB2
  have hr : CPTs (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hfl : CPTs (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hd : CPTs (fun s => dropI (unpairB (unpairB s).2).1) := cpt_comp hr KSat.Hard.cpt_dropI
  have hh : CPTs (fun s => headI (unpairB (unpairB s).2).1) := cpt_comp hr KSat.Hard.cpt_headI
  have he : CPTs (fun s => bflag (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))) :=
    cpt_eqF hh hc
  exact cptG (cpt_pairB2 hc (cpt_pairB2 hd (cpt_app2 hfl he))) (fun _ => rfl)

theorem cpt_memB {C W : List Bool → List Bool} (hC : CPTs C) (hW : CPTs W) :
    CPTs (fun s => bflag (memB (C s) (W s))) := by
  have hit : CPTs (fun s => memStep^[(W s).length] (pairB (C s) (pairB (W s) []))) :=
    cpt_iterGrow cpt_memStep 3 memStep_length hW (cpt_pairB2 hC (cpt_pairB2 hW (cpt_const [])))
  have hF : CPTs (fun s =>
      (unpairB (unpairB (memStep^[(W s).length] (pairB (C s) (pairB (W s) [])))).2).2) :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hit)
  exact cptG (cpt_sel hF (cpt_const []) (cpt_const [true])) (fun s => flag_ne _)

theorem cpt_negI {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun s => negI (I s)) := by
  have hP : CPTs (fun s => bflag (polB (I s))) := cptG (cpt_comp hI cpt_polF) (fun _ => rfl)
  have hT : CPTs (fun s => (I s).tail.tail) := cpt_tail1 (cpt_tail1 hI)
  exact cptG (cpt_sel hP (cpt_cons1 true (cpt_cons1 true hT)) (cpt_cons1 true (cpt_cons1 false hT)))
    (fun _ => rfl)

theorem cpt_fw {H G L : List Bool → List Bool} (hH : CPTs H) (hG : CPTs G) (hL : CPTs L) :
    CPTs (fun s => fw (H s) (G s) (L s)) :=
  cptG (cpt_sel (cpt_memB (cpt_negI hH) hL) (cpt_const []) hG) (fun _ => rfl)

theorem cpt_stepS : CPTs stepS := by
  have hF : CPTs (fun s => (unpairB s).1) := cpt_unpairB1
  have hL : CPTs (fun s => (unpairB s).2) := cpt_unpairB2
  have h1 := cpt_comp hF KSat.Hard.cpt_headI
  have d1 := cpt_comp hF KSat.Hard.cpt_dropI
  have h2 := cpt_comp d1 KSat.Hard.cpt_headI
  have d2 := cpt_comp d1 KSat.Hard.cpt_dropI
  have h3 := cpt_comp d2 KSat.Hard.cpt_headI
  have d3 := cpt_comp d2 KSat.Hard.cpt_dropI
  have hEnd : CPTs (fun s => bflag (isEnd (dropI (unpairB s).1))) :=
    cptG (cpt_comp d1 KSat.Hard.cpt_isEndF) (fun _ => rfl)
  have hbin := cpt_pairB2 (cpt_app2 d3 (cpt_app2 h1 (cpt_app2 h2 h3)))
    (cpt_app2 hL (cpt_app2 (cpt_fw h1 h2 hL) (cpt_fw h2 h1 hL)))
  have hunit := cpt_pairB2 (cpt_app2 d2 (cpt_app2 h1 h2)) (cpt_app2 hL (cpt_fw h1 h1 hL))
  exact cptG (cpt_sel hEnd hbin hunit) (fun _ => rfl)

theorem hd_len (s : List Bool) : (headI s).length + (dropI s).length = s.length := by
  have h := congrArg List.length (headI_dropI s)
  simpa using h

theorem stepP_shape (F L : List Bool) : ∃ F' L' : List Bool,
    stepP F L = pairB F' L' ∧ F'.length = F.length ∧ L'.length ≤ L.length + F.length := by
  have a1 := hd_len F
  have a2 := hd_len (dropI F)
  have a3 := hd_len (dropI (dropI F))
  have f1 := fw_length (headI F) (headI (dropI F)) L
  have f2 := fw_length (headI (dropI F)) (headI F) L
  have f3 := fw_length (headI F) (headI F) L
  unfold stepP sel
  split
  · refine ⟨_, _, rfl, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; omega
  · refine ⟨_, _, rfl, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; omega

theorem stepS_measure (y : List Bool) :
    (unpairB (stepS y)).1.length + 1 ≤ (unpairB y).1.length + 1 := by
  obtain ⟨F', L', h, hF, -⟩ := stepP_shape (unpairB y).1 (unpairB y).2
  rw [stepS, h, unpairB_pairB]
  exact Nat.succ_le_succ (le_of_eq hF)

theorem stepS_length (y : List Bool) :
    (stepS y).length ≤ y.length + ((unpairB y).1.length + 1) := by
  obtain ⟨F', L', h, hF, hL⟩ := stepP_shape (unpairB y).1 (unpairB y).2
  have h1 := unpairB_length y
  rw [stepS, h, pairB_length]
  omega

theorem cpt_closS {X A : List Bool → List Bool} (hX : CPTs X) (hA : CPTs A) :
    CPTs (fun s => closS (X s) (A s)) :=
  cpt_unpairB2_1 (cpt_iterMeasure cpt_stepS (fun y => (unpairB y).1.length + 1) 1
    stepS_measure stepS_length (fun y => by have := unpairB_length y; omega)
    (cpt_mulU2 hX hX) (cpt_pairB2 hX hA))

theorem cpt_badI {X I : List Bool → List Bool} (hX : CPTs X) (hI : CPTs I) :
    CPTs (fun s => bflag (badI (X s) (I s))) := by
  have hN := cpt_negI hI
  have m1 := cpt_memB hN (cpt_closS hX hI)
  have m2 := cpt_memB hI (cpt_closS hX hN)
  exact cptG (cpt_sel m1 (cpt_const []) m2) (fun s => flag_and _ _)

/-! ### The check -/

theorem cpt_chkStep : CPTs chkStep := by
  have hX : CPTs (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : CPTs (fun s => (unpairB s).2) := cpt_unpairB2
  have hR : CPTs (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hB : CPTs (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hD := cpt_comp hR KSat.Hard.cpt_dropI
  have hH := cpt_comp hR KSat.Hard.cpt_headI
  have hEnd : CPTs (fun s => bflag (isEnd (unpairB (unpairB s).2).1)) :=
    cptG (cpt_comp hR KSat.Hard.cpt_isEndF) (fun _ => rfl)
  have hbad := cpt_badI hX hH
  exact cptG (cpt_pairB2 hX (cpt_pairB2 hD (cpt_app2 hB
    (cpt_sel hR (cpt_const []) (cpt_sel hEnd hbad (cpt_const [])))))) (fun _ => rfl)

theorem selflag_length (r e : List Bool) (b : Bool) :
    (sel r [] (sel e (bflag b) [])).length ≤ 1 := by
  have := bflag_length b
  unfold sel
  split
  · simp
  · split
    · exact this
    · simp

theorem chkStep_length (s : List Bool) : (chkStep s).length ≤ s.length + 3 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := dropI_length (unpairB (unpairB s).2).1
  have h4 := selflag_length (unpairB (unpairB s).2).1 (bflag (isEnd (unpairB (unpairB s).2).1))
    (badI (unpairB s).1 (headI (unpairB (unpairB s).2).1))
  simp only [chkStep, pairB_length, List.length_append]
  omega

/-- The decision function for 2-SAT is polynomial-time computable. -/
theorem cpt_dec :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool dec := by
  have hit : CPTs (fun x => chkStep^[x.length] (pairB x (pairB x []))) :=
    cpt_iterGrow cpt_chkStep 3 chkStep_length cpt_id
      (cpt_pairB2 cpt_id (cpt_pairB2 cpt_id (cpt_const [])))
  have hB := cpt_unpairB2_1 (cpt_unpairB2_1 hit)
  have all := cpt_sel KSat.Hard.cpt_wfF (cpt_const [])
    (cpt_sel cpt_w2F (cpt_const []) (cpt_sel hB (cpt_const [true]) (cpt_const [])))
  exact cptG (cpt_comp all cpt_neS) (fun x => flag_fin _ _ _)

/-- 2-SAT is in P. -/
theorem ksat2_in_P : PEqualNP.Search.KSAT 2 ∈ PEqualNP.Library.P :=
  ⟨dec, fun x => (dec_iff x).symm, cpt_dec⟩

end PEqualNP.Library.SearchHelpers.TwoSat
