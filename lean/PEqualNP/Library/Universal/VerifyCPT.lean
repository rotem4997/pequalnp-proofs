import PEqualNP.Library.Universal.Verify
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Machines.LenLE

/-!
# The verification function is polynomial-time computable

Helper module (proofs only, no statement may use it).

Given that the string-level step `sstep` is polynomial-time computable, the verification
function `V` of `Verify.lean` is polynomial-time computable on the pair encoding. The pair is
first packed into one string, and every subexpression of `V` is then built bottom up as a
polynomial-time function of that string.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptv {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Header fields -/

private theorem cpt_hNst {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => hNst (f s)) :=
  cptv (cpt_comp (cpt_comp hf cpt_hd) cpt_tail) (fun _ => rfl)

private theorem cpt_hPc {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => hPc (f s)) :=
  cptv (cpt_comp (cpt_comp hf cpt_dropN) cpt_hd) (fun _ => rfl)

private theorem cpt_hSt {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => hSt (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN) cpt_hd) cpt_tail)
    (fun _ => rfl)

private theorem cpt_hKin {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => hKin (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN) cpt_dropN)
    cpt_hd) cpt_tail) (fun _ => rfl)

private theorem cpt_hKout {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => hKout (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp hf cpt_dropN) cpt_dropN)
    cpt_dropN) cpt_dropN) cpt_hd) cpt_tail) (fun _ => rfl)

/-! ### Iterations -/

/-- Iterating a function that grows by at most one symbol. -/
private theorem cpt_iterLen1 {g cnt arg : List Bool → List Bool} (hg : CPT g)
    (hgl : ∀ s, (g s).length ≤ s.length + 1) (hcnt : CPT cnt) (harg : CPT arg) :
    CPT (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c 1 hgl
  exact cptv (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

/-- Iterating the step. -/
private theorem cpt_iterS (hstep : CPT sstep) {cnt arg : List Bool → List Bool}
    (hcnt : CPT cnt) (harg : CPT arg) :
    CPT (fun s => sstep^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hstep
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => sstep^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure sstep c smeasure 7 smeasure_sstep sstep_length smeasure_le
  exact cptv (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

/-! ### The initial configuration -/

private theorem cpt_splitK {kf sk : List Bool → List Bool} (hkf : CPT kf) (hsk : CPT sk) :
    CPT (fun s => splitK (kf s) (sk s)) :=
  cptv (cpt_iterLen1 cpt_move move_length hkf (cpt_pairB2 hsk (cpt_const [])))
    (fun _ => rfl)

private theorem cpt_insK {kf new sk : List Bool → List Bool} (hkf : CPT kf) (hnew : CPT new)
    (hsk : CPT sk) : CPT (fun s => insK (kf s) (new s) (sk s)) := by
  have h := cpt_splitK hkf hsk
  have h1 := cpt_comp h cpt_unpairB1
  have h2 := cpt_comp h cpt_unpairB2
  exact cptv (cpt_sel h1 h2 (cpt_app2 h2 (cpt_app2 hnew h1))) (fun _ => rfl)

private theorem cpt_inSyms {x w : List Bool → List Bool} (hx : CPT x) (hw : CPT w) :
    CPT (fun s => inSyms (x s) (w s)) :=
  cptv (cpt_app2 (cpt_comp (cpt_comp hx cpt_spread) cpt_bump)
    (cpt_comp (cpt_comp (cpt_comp (cpt_comp hw cpt_spread) cpt_bump) cpt_bump) cpt_bump))
    (fun _ => rfl)

private theorem cpt_initS {cs x w : List Bool → List Bool} (hcs : CPT cs) (hx : CPT x)
    (hw : CPT w) : CPT (fun s => initS (cs s) (x s) (w s)) := by
  have h1 := cpt_comp hcs cpt_unpairB1
  have h2 := cpt_comp hcs cpt_unpairB2
  exact cptv (cpt_pairB2 h1 (cpt_pairB2 (cpt_hPc h2) (cpt_pairB2 (cpt_hSt h2)
    (cpt_insK (cpt_hKin h2) (cpt_inSyms hx hw) (cpt_comp (cpt_hNst h2) cpt_blank)))))
    (fun _ => rfl)

private theorem cpt_stkS {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => stkS (f s)) :=
  cptv (cpt_comp (cpt_comp (cpt_comp hf cpt_unpairB2) cpt_unpairB2) cpt_unpairB2)
    (fun _ => rfl)

/-! ### The test on the first four symbols -/

private inductive O4 : Type
  | s0 | s1 | s2 | s3 | ok | bad
  deriving DecidableEq

private instance : Fintype O4 :=
  Fintype.ofList [.s0, .s1, .s2, .s3, .ok, .bad] (fun x => by cases x <;> simp)

private def o4D : O4 → Bool → O4 × Option Bool
  | .s0, true => (.s1, none)
  | .s1, true => (.s2, none)
  | .s2, false => (.s3, none)
  | .s3, false => (.ok, none)
  | .ok, _ => (.ok, none)
  | _, _ => (.bad, none)

private def o4F : O4 → Option Bool
  | .ok => some true
  | _ => none

private theorem o4_ok (l : List Bool) : fstRun o4D o4F .ok l = [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_bad (l : List Bool) : fstRun o4D o4F .bad l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, o4D, ih]

private theorem o4_run (l : List Bool) :
    fstRun o4D o4F .s0 l = if l.take 4 = [true, true, false, false] then [true] else [] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp [fstRun, o4F]
  · cases a <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> simp [fstRun, o4D, o4F]
  · cases a <;> cases b <;> cases c <;> cases d <;> simp [fstRun, o4D, o4_ok, o4_bad]

private theorem cpt_o4 :
    CPT (fun l : List Bool => if l.take 4 = [true, true, false, false] then [true] else []) :=
  fst_polyTime _ _ _ o4D o4F .s0 (fun s => (o4_run s).symm)

/-! ### From a flag string to a decision bit -/

private theorem ne_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_ne :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, ne_true, Computability.encodeBool])

private theorem comb (a : Bool) (A : List Bool) (p : Prop) [Decidable p] :
    (!(sel (if a then [true] else []) []
      (sel (sel A [true] []) [] (sel (if p then [true] else []) [] [true]))).isEmpty) =
      (a && (A.isEmpty && decide p)) := by
  cases a <;> cases A <;> by_cases h : p <;> simp [sel, h]

/-! ### The verification function -/

private theorem cpt_VS (hstep : CPT sstep) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V ((unpairB s).1, (unpairB s).2)) := by
  have hz : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hw : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hcs : CPT (fun s => (unpairB (unpairB s).1).1) :=
    cptv (cpt_comp hz cpt_unpairB1) (fun _ => rfl)
  have hr : CPT (fun s => (unpairB (unpairB s).1).2) :=
    cptv (cpt_comp hz cpt_unpairB2) (fun _ => rfl)
  have hx : CPT (fun s => (unpairB (unpairB (unpairB s).1).2).1) :=
    cptv (cpt_comp hr cpt_unpairB1) (fun _ => rfl)
  have hb : CPT (fun s => (unpairB (unpairB (unpairB s).1).2).2) :=
    cptv (cpt_comp hr cpt_unpairB2) (fun _ => rfl)
  have hit := cpt_iterS hstep hb (cpt_initS hcs hx hw)
  have hc2 : CPT (fun s => (unpairB (unpairB (unpairB s).1).1).2) :=
    cptv (cpt_comp hcs cpt_unpairB2) (fun _ => rfl)
  have hko := cpt_hKout hc2
  have hD := cpt_iterLen cpt_dropL dropL_length hko (cpt_stkS hit)
  have f3 := cpt_comp hD cpt_o4
  have hA := cpt_comp (cpt_comp hit cpt_unpairB2) cpt_unpairB1
  have f2 := cpt_sel hA (cpt_const [true]) (cpt_const [])
  have f1 := cpt_bitFlag (cpt_comp (cpt_pair hb hw) LenCmp.lenLE_polyTime)
  have all := cpt_sel f1 (cpt_const []) (cpt_sel f2 (cpt_const [])
    (cpt_sel f3 (cpt_const []) (cpt_const [true])))
  exact cptv (cpt_comp all cpt_ne) (fun s => comb _ _ _)

/-- The verification function is polynomial-time computable, given that the step is. -/
theorem cpt_V (hstep : PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) sstep) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool V :=
  cptv (cpt_comp cpt_pairB (cpt_VS hstep)) (fun p => by
    obtain ⟨z, w⟩ := p
    simp only [unpairB_pairB])

end PEqualNP.Library.Universal
