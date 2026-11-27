import PEqualNP.MetaComplexity.Helpers.MachinePrintOut2
import PEqualNP.MetaComplexity.Helpers.MachinePrintFix
import PEqualNP.MetaComplexity.L503
import PEqualNP.MetaComplexity.Helpers.MachinePair

/-!
# The printer of the cover circuit is polynomial time

Helper module (proofs only, no statement may use it).

The input code is read into tokens (`tok1`), every segment is mirrored twice (`Mir`), and the
printing transducer `δF` writes the code of the input of D02 for `relGates true` of the tuples.
D02 (the checked row `L503`) prints the circuit code with absolute
wires, and the repair transducer (`fixf`) corrects the output wire when there is no gate. The
result is `encodeLgp (n, coverCircuitB n owners)` (`fixf_d02f`).
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## The whole printing run -/

def q0 : FS := (.hd, true, .c1, .k0, true)

theorem tuples_run : ∀ (ls : List (List ℕ)) (lead : Bool),
    out (.sg, lead, .c1, .k0, true) (ls.flatMap (fun l => mm (segT l) ++ [Tok.TE])) =
      (relGates lead ls).flatMap gE ∧
    ∃ lead', nxt (.sg, lead, .c1, .k0, true) (ls.flatMap (fun l => mm (segT l) ++ [Tok.TE])) =
      (.sg, lead', .c1, .k0, true)
  | [], lead => ⟨rfl, lead, rfl⟩
  | l :: ls, lead => by
    have hb := block lead l
    have ih := tuples_run ls (lead && decide (l.length < 2))
    simp only [List.flatMap_cons, out_append, nxt_append, hb.1, hb.2, ih.1, relGates,
      List.flatMap_append]
    exact ⟨by first | rfl | trivial, ih.2⟩

theorem header_run (n : ℕ) :
    out q0 (mm (List.replicate n Tok.H) ++ [Tok.HE]) = List.replicate n true ++ [false] ∧
    nxt q0 (mm (List.replicate n Tok.H) ++ [Tok.HE]) = (.sg, true, .c1, .k0, true) := by
  have h1 := rep_one q0 .H true rfl n
  have h2 := rep_none (.hd, true, .c2, .k0, true) .H rfl n
  have h3 := rep_none (.hd, true, .c3, .k0, true) .H rfl n
  have h4 := rep_none (.hd, true, .c4, .k0, true) .H rfl n
  unfold mm
  rw [List.reverse_replicate]
  simp only [List.append_assoc, List.cons_append, out_append, nxt_append, h1.1, h1.2, out_cons,
    nxt_cons]
  try simp only [q0, δF, Cp.next]
  simp only [out_append, nxt_append, h2.1, h2.2, out_cons, nxt_cons]
  try simp only [δF, Cp.next]
  simp only [out_append, nxt_append, h3.1, h3.2, out_cons, nxt_cons]
  try simp only [δF, Cp.next]
  simp only [out_append, nxt_append, h4.1, h4.2, out_cons, nxt_cons, out_nil]
  simp [δF, nxt]

theorem last_run (lead : Bool) : out (.sg, lead, .c1, .k0, true) (mm [Tok.LE]) = [false] := by
  simp [mm, out_cons, out_nil, δF]

theorem mm_joinS (segs : List (List Tok × Tok)) (last : List Tok)
    (hs : ∀ p ∈ segs, (∀ x ∈ p.1, Tok.isSep x = false) ∧ Tok.isSep p.2 = true)
    (hl : ∀ x ∈ last, Tok.isSep x = false) :
    Mir.mB Tok.isSep Tok.M [] (Mir.mB Tok.isSep Tok.M [] (joinS segs last).reverse []).reverse [] =
      joinS (segs.map (fun p => (mm p.1, p.2))) (mm last) := by
  rw [mB_joinS Tok.isSep Tok.M segs last [] hs hl, List.append_nil]
  have hs' : ∀ p ∈ segs.map (fun p => (mirSeg Tok.M p.1, p.2)),
      (∀ x ∈ p.1, Tok.isSep x = false) ∧ Tok.isSep p.2 = true := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨fun x hx => ?_, (hs q hq).2⟩
    simp only [mirSeg, List.mem_append, List.mem_reverse, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact (hs q hq).1 x h
    · rfl
    · exact (hs q hq).1 x h
  have hl' : ∀ x ∈ mirSeg Tok.M last, Tok.isSep x = false := by
    intro x hx
    simp only [mirSeg, List.mem_append, List.mem_reverse, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact hl x h
    · rfl
    · exact hl x h
  rw [mB_joinS Tok.isSep Tok.M _ _ [] hs' hl', List.append_nil, List.map_map, mm_eq]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [mm_eq]

/-- The string function: read, mirror twice, print. -/
def printG (w : List Bool) : List Bool :=
  out q0 (Mir.mB Tok.isSep Tok.M [] (Mir.mB Tok.isSep Tok.M [] (tok1 w).reverse []).reverse [])

theorem cpt_printG : ComputableInPolyTime (fun w : List Bool => w) (fun w : List Bool => w)
    printG := by
  have h1 := cpt_comp (cpt_comp (cpt_comp cpt_tok1 (cpt_mir Tok.isSep Tok.M))
    (cpt_mir Tok.isSep Tok.M)) (cpt_lrun δF (fun _ => []) q0)
  exact h1

theorem printG_eq (p : List ℕ × List (List ℕ)) :
    printG (encodeList unaryE p.1 ++ encodeList (encodeList unaryE) p.2) =
      d02enc (p.1.headD 0, relGates true p.2) := by
  unfold printG
  rw [tok1_eq, mm_joinS]
  · simp only [joinS, List.map_cons, List.flatMap_cons, List.flatMap_map, List.append_assoc]
    rw [← List.append_assoc (mm _) [Tok.HE], out_append, (header_run _).1, (header_run _).2,
      out_append, (tuples_run p.2 true).1]
    obtain ⟨lead', hl⟩ := (tuples_run p.2 true).2
    rw [hl, last_run, d02enc_eq]
    simp
  · intro q hq
    simp only [List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨l, _, rfl⟩
    · refine ⟨fun x hx => ?_, rfl⟩
      rw [List.eq_of_mem_replicate hx]; rfl
    · refine ⟨fun x hx => ?_, rfl⟩
      rcases segT_tok l x hx with h | rfl
      · cases x <;> first | rfl | exact absurd h (by simp [plainTok])
      · rfl
  · intro x hx
    simp only [List.mem_singleton] at hx
    rw [hx]; rfl

/-! ## The assembly -/

theorem cpt_relGates : ComputableInPolyTime
    (fun p : List ℕ × List (List ℕ) => encodeList unaryE p.1 ++ encodeList (encodeList unaryE) p.2)
    d02enc (fun p => (p.1.headD 0, relGates true p.2)) := by
  obtain ⟨c⟩ := cpt_printG
  exact MachinePair.cpt_transport c
    (fun p : List ℕ × List (List ℕ) => encodeList unaryE p.1 ++ encodeList (encodeList unaryE) p.2)
    _ (fun _ => rfl) (fun p => (printG_eq p).symm)

theorem cpt_d02f : ComputableInPolyTime d02enc encodeLgp d02f := PEqualNP.MetaComplexity.L503

theorem printer : PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × List (List ℕ) => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) p.2) PEqualNP.MetaComplexity.encodeLgp (fun p : List ℕ × List (List ℕ) => (p.1.headD 0, PEqualNP.MetaComplexity.coverCircuitB (p.1.headD 0) (p.2.map (fun l : List ℕ => (l.headD 0, l.tail))))) := by
  have h := cpt_comp (cpt_comp cpt_relGates cpt_d02f) cpt_fixf
  have e : (fun p : List ℕ × List (List ℕ) => fixf (d02f (p.1.headD 0, relGates true p.2))) =
      (fun p : List ℕ × List (List ℕ) => (p.1.headD 0, PEqualNP.MetaComplexity.coverCircuitB
        (p.1.headD 0) (p.2.map (fun l : List ℕ => (l.headD 0, l.tail))))) := by
    funext p; exact fixf_d02f _ _
  rw [e] at h
  exact h

end PEqualNP.MetaComplexity.Helpers.MachinePrint
