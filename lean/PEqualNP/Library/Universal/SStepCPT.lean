import PEqualNP.Library.Universal.SStep
import PEqualNP.Library.Universal.PrimsCPT

/-!
# The string-level step is polynomial-time computable

Helper module (proofs only, no statement may use it).

Every subexpression of `sstep y` is shown to be `ComputableInPolyTime` as a function of the
single argument `y`, bottom up, from the primitives of `PrimsCPT.lean`. The main result is
`cpt_sstep`.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptE {f f' : List Bool → List Bool} (h : CPTs f) (e : ∀ a, f a = f' a) :
    CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Unary primitives after a function -/

theorem cpt_hd1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun y => hd (f y)) :=
  cpt_comp hf cpt_hd

theorem cpt_dropN1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun y => dropN (f y)) :=
  cpt_comp hf cpt_dropN

theorem cpt_tail1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun y => (f y).tail) :=
  cpt_comp hf cpt_tail

theorem cpt_takeL1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun y => takeL (f y)) :=
  cpt_comp hf cpt_takeL

theorem cpt_popT1 {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun y => popT (f y)) :=
  cpt_comp hf cpt_popT

theorem cpt_unpairB1_1 {f : List Bool → List Bool} (hf : CPTs f) :
    CPTs (fun y => (unpairB (f y)).1) :=
  cptE (cpt_comp hf cpt_unpairB1) (fun _ => rfl)

theorem cpt_unpairB2_1 {f : List Bool → List Bool} (hf : CPTs f) :
    CPTs (fun y => (unpairB (f y)).2) :=
  cptE (cpt_comp hf cpt_unpairB2) (fun _ => rfl)

/-- Putting a fixed symbol in front. -/
theorem cpt_cons1 (b : Bool) {f : List Bool → List Bool} (hf : CPTs f) :
    CPTs (fun y => b :: f y) :=
  cptE (cpt_app2 (cpt_const [b]) hf) (fun _ => rfl)

/-- Iterating a function that lengthens by at most a constant, a number of times given by a
second function. -/
theorem cpt_iterGrow {g cnt arg : List Bool → List Bool} (hg : CPTs g) (k : ℕ)
    (hgl : ∀ s, (g s).length ≤ s.length + k) (hcnt : CPTs cnt) (harg : CPTs arg) :
    CPTs (fun s => g^[(cnt s).length] (arg s)) := by
  obtain ⟨c⟩ := hg
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    Iter.iter_polyTime g c k hgl
  exact cptE (cpt_comp (cpt_pair harg hcnt) hI) (fun _ => rfl)

/-! ### Reading an instruction -/

theorem cpt_fetch {ps pc : List Bool → List Bool} (hps : CPTs ps) (hpc : CPTs pc) :
    CPTs (fun y => fetch (ps y) (pc y)) := by
  unfold fetch
  exact cpt_takeL1 (cpt_iterLen cpt_dropL dropL_length (cpt_tail1 hpc) hps)

theorem cpt_fOp {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fOp (I y)) := by
  unfold fOp
  exact cpt_hd1 hI

theorem cpt_fK {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fK (I y)) := by
  unfold fK
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 hI))

theorem cpt_fW {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fW (I y)) := by
  unfold fW
  exact cpt_tail1 (cpt_hd1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN1 {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fN1 (I y)) := by
  unfold fN1
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI)))

theorem cpt_fN2 {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fN2 (I y)) := by
  unfold fN2
  exact cpt_hd1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_fTb {I : List Bool → List Bool} (hI : CPTs I) : CPTs (fun y => fTb (I y)) := by
  unfold fTb
  exact cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 (cpt_dropN1 hI))))

theorem cpt_lookup {tb idx : List Bool → List Bool} (htb : CPTs tb) (hidx : CPTs idx) :
    CPTs (fun y => lookup (tb y) (idx y)) := by
  unfold lookup
  exact cpt_tail1 (cpt_hd1 (cpt_iterLen cpt_dropN dropN_length hidx htb))

theorem cpt_splitK {kf sk : List Bool → List Bool} (hkf : CPTs kf) (hsk : CPTs sk) :
    CPTs (fun y => splitK (kf y) (sk y)) := by
  unfold splitK
  exact cpt_iterGrow cpt_move 1 move_length hkf (cpt_pairB2 hsk (cpt_const []))

/-! ### The three selections -/

theorem cpt_pcSel {pc o n1 n2 valS : List Bool → List Bool} (hpc : CPTs pc) (ho : CPTs o)
    (hn1 : CPTs n1) (hn2 : CPTs n2) (hv : CPTs valS) :
    CPTs (fun y => pcSel (pc y) (o y) (n1 y) (n2 y) (valS y)) := by
  unfold pcSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  have h5 := cpt_tail1 h4
  have h6 := cpt_tail1 h5
  exact cpt_sel hpc hpc (cpt_sel ho (cpt_const []) (cpt_sel h1 hn1 (cpt_sel h2 hn1
    (cpt_sel h3 hn1 (cpt_sel h4 hn1 (cpt_sel h5 (cpt_sel hv hn2 hn1)
      (cpt_sel h6 (cpt_cons1 true hv) (cpt_const []))))))))

theorem cpt_stSel {pc o st valS valT : List Bool → List Bool} (hpc : CPTs pc) (ho : CPTs o)
    (hst : CPTs st) (hvS : CPTs valS) (hvT : CPTs valT) :
    CPTs (fun y => stSel (pc y) (o y) (st y) (valS y) (valT y)) := by
  unfold stSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  have h3 := cpt_tail1 h2
  have h4 := cpt_tail1 h3
  exact cpt_sel hpc hst (cpt_sel ho hst (cpt_sel h1 hst (cpt_sel h2 hvT (cpt_sel h3 hvT
    (cpt_sel h4 hvS hst)))))

theorem cpt_skSel {pc o sk r d pushed : List Bool → List Bool} (hpc : CPTs pc) (ho : CPTs o)
    (hsk : CPTs sk) (hr : CPTs r) (hd' : CPTs d) (hp : CPTs pushed) :
    CPTs (fun y => skSel (pc y) (o y) (sk y) (r y) (d y) (pushed y)) := by
  unfold skSel
  have h1 := cpt_tail1 ho
  have h2 := cpt_tail1 h1
  exact cpt_sel hpc hsk (cpt_sel ho hsk (cpt_sel h1
    (cpt_sel hr hd' (cpt_app2 hd' (cpt_app2 hp hr)))
    (cpt_sel h2 (cpt_app2 hd' (cpt_popT1 hr)) hsk)))

/-! ### The three outputs -/

theorem cpt_pcOut {ps pc st : List Bool → List Bool} (hps : CPTs ps) (hpc : CPTs pc)
    (hst : CPTs st) : CPTs (fun y => pcOut (ps y) (pc y) (st y)) := by
  unfold pcOut
  have hI := cpt_fetch hps hpc
  exact cpt_pcSel hpc (cpt_fOp hI) (cpt_fN1 hI) (cpt_fN2 hI) (cpt_lookup (cpt_fTb hI) hst)

theorem cpt_stOut {ps pc st sk : List Bool → List Bool} (hps : CPTs ps) (hpc : CPTs pc)
    (hst : CPTs st) (hsk : CPTs sk) : CPTs (fun y => stOut (ps y) (pc y) (st y) (sk y)) := by
  unfold stOut
  have hI := cpt_fetch hps hpc
  have hT := cpt_fTb hI
  exact cpt_stSel hpc (cpt_fOp hI) hst (cpt_lookup hT hst)
    (cpt_lookup hT (cpt_app2 (cpt_mulU2 hst (cpt_fW hI))
      (cpt_hd1 (cpt_unpairB1_1 (cpt_splitK (cpt_fK hI) hsk)))))

theorem cpt_skOut {ps pc st sk : List Bool → List Bool} (hps : CPTs ps) (hpc : CPTs pc)
    (hst : CPTs st) (hsk : CPTs sk) : CPTs (fun y => skOut (ps y) (pc y) (st y) (sk y)) := by
  unfold skOut
  have hI := cpt_fetch hps hpc
  have hS := cpt_splitK (cpt_fK hI) hsk
  exact cpt_skSel hpc (cpt_fOp hI) hsk (cpt_unpairB1_1 hS) (cpt_unpairB2_1 hS)
    (cpt_app2 (cpt_cons1 true (cpt_lookup (cpt_fTb hI) hst)) (cpt_const [false]))

theorem cpt_sstepParts {ps pc st sk : List Bool → List Bool} (hps : CPTs ps) (hpc : CPTs pc)
    (hst : CPTs st) (hsk : CPTs sk) :
    CPTs (fun y => sstepParts (ps y) (pc y) (st y) (sk y)) := by
  unfold sstepParts
  exact cpt_pairB2 hps (cpt_pairB2 (cpt_pcOut hps hpc hst)
    (cpt_pairB2 (cpt_stOut hps hpc hst hsk) (cpt_skOut hps hpc hst hsk)))

/-- The string-level step is polynomial-time computable. -/
theorem cpt_sstep : PEqualNP.Library.ComputableInPolyTime
    (fun x : List Bool => x) (fun x : List Bool => x) sstep := by
  have h2 : CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have h22 := cpt_unpairB2_1 h2
  have h : CPTs (fun y => sstepParts (unpairB y).1 (unpairB (unpairB y).2).1
      (unpairB (unpairB (unpairB y).2).2).1 (unpairB (unpairB (unpairB y).2).2).2) :=
    cpt_sstepParts cpt_unpairB1 (cpt_unpairB1_1 h2) (cpt_unpairB1_1 h22) (cpt_unpairB2_1 h22)
  exact h

end PEqualNP.Library.Universal
