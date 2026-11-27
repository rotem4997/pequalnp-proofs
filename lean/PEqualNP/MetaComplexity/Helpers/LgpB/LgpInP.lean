import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LgpEncode
import PEqualNP.MetaComplexity.Helpers.LgpB.Columns
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.L008
import PEqualNP.Library.Machines.LenLE
import PEqualNP.MetaComplexity.Helpers.LgpB.Lookup

/-!
# Helper module (proofs only): if P = NP then the last-gate problem is in P

Inside the promise, `C` on `n` inputs is not minimal exactly when some fan-in-two circuit `D`
with fewer gates computes the same function on `n` inputs. That is a statement with an
existential block (the code of `D`) over a universal block (the inputs of length `n`, and `n`
is written in unary in the instance). Under P = NP both blocks collapse.

* `lgpDec`, `lgpVal`: decoding a string as an instance `(n, C)` and the value of the decoded
  circuit on a string of length `n` (`false` on every other string).
* `EvalPoly`: `lgpVal` is polynomial-time computable on pairs; it follows from `ValidPoly`
  (recognising codes of fan-in-two circuits, one finite automaton, `validPoly`) and
  `EvalValidPoly` (evaluating a valid code: one pass per gate with the binary-index lookup of
  `Machines/Lookup.lean`, iterated, `evalValidPoly`).
* `GcountPoly`: counting the gates of a code in unary, by one finite-state transducer.
* `lgpInP_of`: P = NP, `EvalPoly` and `GcountPoly` give `LgpInP`; `l109` assembles it.
-/

namespace PEqualNP.MetaComplexity.LgpB.LgpInP
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.CircuitLowerBounds PEqualNP.Library PEqualNP.Library.Machines
  PEqualNP.Library.Universal PEqualNP.MetaComplexity

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

local notation "CPTB" =>
  ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool

theorem cptc {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ## Decoding and evaluation -/

open Classical in
/-- The instance a string codes, if any. -/
noncomputable def lgpDec (s : List Bool) : Option (ℕ × Circuit) :=
  if h : ∃ p, encodeLgp p = s then some (Classical.choose h) else none

theorem lgpDec_encode (p : ℕ × Circuit) : lgpDec (encodeLgp p) = some p := by
  have h : ∃ q, encodeLgp q = encodeLgp p := ⟨p, rfl⟩
  unfold lgpDec
  rw [dite_cond_eq_true (eq_true h)]
  exact congrArg some (LgpEncode.encodeLgp_injective (Classical.choose_spec h))

open Classical in
/-- The value on `x` of the circuit coded by `s`: for `s` the code of `(n, C)` with `C` fan-in
two, `C` on `x` when `x` has length `n` and `false` otherwise; `false` when `s` codes nothing or
codes a circuit that is not fan-in two. -/
noncomputable def lgpVal (s x : List Bool) : Bool :=
  match lgpDec s with
  | some p => decide (x.length = p.1) && decide (FanInTwo p.2) && p.2.eval x
  | none => false

theorem lgpDec_some {s : List Bool} {p : ℕ × Circuit} (h : lgpDec s = some p) :
    encodeLgp p = s := by
  unfold lgpDec at h
  split_ifs at h with hh
  cases Option.some.inj h
  exact Classical.choose_spec hh

theorem lgpVal_encode (n : ℕ) (C : Circuit) (hC : FanInTwo C) (x : List Bool) :
    lgpVal (encodeLgp (n, C)) x = (decide (x.length = n) && C.eval x) := by
  simp [lgpVal, lgpDec_encode, hC]

/-- On strings of length `n`, the value of a string that does not code a fan-in-two circuit on
`n` inputs is `false`. -/
theorem lgpVal_other (n : ℕ) (w : List Bool)
    (hw : ¬ ∃ D : Circuit, w = encodeLgp (n, D) ∧ FanInTwo D) (x : List Bool)
    (hx : x.length = n) : lgpVal w x = false := by
  unfold lgpVal
  cases h : lgpDec w with
  | none => rfl
  | some p =>
    obtain ⟨n', D⟩ := p
    have e := lgpDec_some h
    by_cases hn : n' = n
    · subst hn
      by_cases hD : FanInTwo D
      · exact absurd ⟨D, e.symm, hD⟩ hw
      · simp [hD]
    · simp [hx, Ne.symm hn]

/-! ## The machine facts -/

/-- Machine fact (proved below, `validPoly`): whether a string codes an instance `(n, C)` with `C` fan-in two is
polynomial-time decidable. -/
def ValidPoly : Prop :=
  DecidableInPolyTime (fun x : List Bool => x)
    {s : List Bool | ∃ (n : ℕ) (C : Circuit), s = encodeLgp (n, C) ∧ FanInTwo C}

/-- Machine fact (proved below, `evalValidPoly`): a polynomial-time function of a pair of strings that, on the code of
`(n, C)` with `C` fan-in two and a string `x` of length `n`, is the value of `C` on `x`. -/
def EvalValidPoly : Prop :=
  ∃ ev : List Bool × List Bool → Bool,
    ComputableInPolyTime encodePair Computability.encodeBool ev ∧
      ∀ (n : ℕ) (C : Circuit) (x : List Bool), FanInTwo C → x.length = n →
        ev (encodeLgp (n, C), x) = C.eval x

/-- Evaluating a coded circuit on a string is polynomial-time computable. -/
def EvalPoly : Prop :=
  ComputableInPolyTime encodePair Computability.encodeBool
    (fun q : List Bool × List Bool => lgpVal q.1 q.2)

/-- Counting the gates of a coded circuit is polynomial-time computable (in unary). -/
def GcountPoly : Prop :=
  ∃ gc : List Bool → List Bool, CPT gc ∧
    ∀ (n : ℕ) (C : Circuit), (gc (encodeLgp (n, C))).length = C.size

/-! ## Boolean combinators -/

theorem ne_true_run (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

/-- From a flag string to a decision bit. -/
theorem cpt_ne : CPTB (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, ne_true_run, Computability.encodeBool])

/-- The flag string of a bit. -/
def flag (b : Bool) : List Bool := if b then [true] else []

/-- Any Boolean operation of two polynomial-time bits. -/
theorem cptb_op (op : Bool → Bool → Bool) {f g : List Bool → Bool} (hf : CPTB f) (hg : CPTB g) :
    CPTB (fun s => op (f s) (g s)) := by
  have F := cpt_bitFlag hf
  have G := cpt_bitFlag hg
  have h := cpt_sel F (cpt_sel G (cpt_const (flag (op false false)))
      (cpt_const (flag (op false true))))
    (cpt_sel G (cpt_const (flag (op true false))) (cpt_const (flag (op true true))))
  refine cptc (cpt_comp h cpt_ne) ?_
  intro s
  cases f s <;> cases g s <;> cases op false false <;> cases op false true <;>
    cases op true false <;> cases op true true <;> simp [sel, flag]

/-- If-then-else of polynomial-time bits. -/
theorem cptb_ite {c a b : List Bool → Bool} (hc : CPTB c) (ha : CPTB a) (hb : CPTB b) :
    CPTB (fun s => if c s then a s else b s) := by
  have h := cpt_sel (cpt_bitFlag hc) (cpt_bitFlag hb) (cpt_bitFlag ha)
  refine cptc (cpt_comp h cpt_ne) ?_
  intro s
  cases c s <;> cases a s <;> cases b s <;> simp [sel]

/-- A bit of a pair, computed from the packed pair. -/
theorem cpt_of_packed {f : List Bool × List Bool → Bool}
    (h : CPTB (fun s => f (unpairB s))) :
    ComputableInPolyTime encodePair Computability.encodeBool f :=
  cptc (cpt_comp cpt_pairB h) (fun q => by simp [unpairB_pairB])

/-- A bit of a pair, on the packed pair. -/
theorem cpt_to_packed {f : List Bool × List Bool → Bool}
    (h : ComputableInPolyTime encodePair Computability.encodeBool f) :
    CPTB (fun s => f (unpairB s)) :=
  cpt_comp cpt_unpairB h

/-- A bit of a pair of two polynomial-time strings. -/
theorem cpt_app {f : List Bool × List Bool → Bool}
    (h : ComputableInPolyTime encodePair Computability.encodeBool f)
    {u v : List Bool → List Bool} (hu : CPT u) (hv : CPT v) :
    CPTB (fun s => f (u s, v s)) :=
  cpt_comp (cpt_pair hu hv) h

/-! ## The inner block: disagreement -/

/-- The inner relation: the two circuits coded in the packed pair `t` disagree on `x`. -/
noncomputable def V1 (q : List Bool × List Bool) : Bool :=
  lgpVal (unpairB q.1).1 q.2 != lgpVal (unpairB q.1).2 q.2

theorem cpt_V1 (hE : EvalPoly) : ComputableInPolyTime encodePair Computability.encodeBool V1 := by
  apply cpt_of_packed
  have h1 := cpt_app hE (cpt_comp cpt_unpairB1 cpt_unpairB1) cpt_unpairB2
  have h2 := cpt_app hE (cpt_comp cpt_unpairB1 cpt_unpairB2) cpt_unpairB2
  exact cptc (cptb_op (fun a b => a != b) h1 h2) (fun s => rfl)

/-- The language of packed pairs of codes that disagree on some short string. -/
def Ldis : Language Bool :=
  {t | ∃ x : List Bool, x.length ≤ t.length ∧ V1 (t, x) = true}

theorem ldis_mem_NP (hE : EvalPoly) : Ldis ∈ NP :=
  ⟨{q | V1 q = true}, Polynomial.X, ⟨V1, fun _ => Iff.rfl, cpt_V1 hE⟩,
    fun t => by simp only [Polynomial.eval_X]; exact Iff.rfl⟩

/-! ## The outer block -/

/-- The outer relation, given a gate counter `gc` and a decider `g` of `Ldis`: the witness has
fewer gates and the pair is not in `Ldis`. -/
noncomputable def V2 (gc : List Bool → List Bool) (g : List Bool → Bool)
    (q : List Bool × List Bool) : Bool :=
  decide ((gc q.2).length < (gc q.1).length) && !g (pairB q.1 q.2)

theorem cpt_V2 {gc : List Bool → List Bool} {g : List Bool → Bool} (hc : CPT gc) (hg : CPTB g) :
    ComputableInPolyTime encodePair Computability.encodeBool (V2 gc g) := by
  apply cpt_of_packed
  have hp : CPT (fun s => pairB (unpairB s).1 (unpairB s).2) := cpt_pairB2 cpt_unpairB1 cpt_unpairB2
  have hle := cpt_app (u := fun s => gc (unpairB s).2) (v := fun s => gc (unpairB s).1)
    (cptc LenCmp.lenLE_polyTime (fun _ => rfl)) (cpt_comp cpt_unpairB2 hc)
    (cpt_comp cpt_unpairB1 hc)
  refine cptc (cptb_op (fun a b => !a && !b) hle (cpt_comp hp hg)) (fun s => ?_)
  simp only [V2]
  congr 1
  by_cases hh : (gc (unpairB s).1).length ≤ (gc (unpairB s).2).length <;> simp [hh] <;> omega

/-- The bound on the code of a witness. -/
noncomputable def wbound : Polynomial ℕ :=
  Polynomial.C 8 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X + Polynomial.C 8

/-- The non-minimal instances, as a language. -/
def Lnm (gc : List Bool → List Bool) (g : List Bool → Bool) : Language Bool :=
  {s | ∃ w : List Bool, w.length ≤ wbound.eval s.length ∧ V2 gc g (s, w) = true}

theorem lnm_mem_NP {gc : List Bool → List Bool} {g : List Bool → Bool} (hc : CPT gc)
    (hg : CPTB g) : Lnm gc g ∈ NP :=
  ⟨{q | V2 gc g q = true}, wbound, ⟨V2 gc g, fun _ => Iff.rfl, cpt_V2 hc hg⟩,
    fun s => Iff.rfl⟩

/-! ## Counting gates: one finite-state transducer -/

/-- States of the gate counter: unary prefix, start of a gate entry, the operation bits, the
operand list, inside a number (two states), done. -/
inductive GS : Type
  | U | G | O0 | O1F | O1T | O2 | IL | NA | NB | D
  deriving DecidableEq

instance : Fintype GS :=
  Fintype.ofList [GS.U, GS.G, GS.O0, GS.O1F, GS.O1T, GS.O2, GS.IL, GS.NA, GS.NB, GS.D]
    (fun x => by cases x <;> simp)

/-- The gate counter writes `true` at the start of every gate entry. -/
def δgc : GS → Bool → GS × Option Bool
  | GS.U, true => (GS.U, none)
  | GS.U, false => (GS.G, none)
  | GS.G, true => (GS.O0, some true)
  | GS.G, false => (GS.D, none)
  | GS.O0, false => (GS.O1F, none)
  | GS.O0, true => (GS.O1T, none)
  | GS.O1F, _ => (GS.IL, none)
  | GS.O1T, false => (GS.IL, none)
  | GS.O1T, true => (GS.O2, none)
  | GS.O2, false => (GS.NA, none)
  | GS.O2, true => (GS.IL, none)
  | GS.IL, true => (GS.NA, none)
  | GS.IL, false => (GS.G, none)
  | GS.NA, true => (GS.NB, none)
  | GS.NA, false => (GS.IL, none)
  | GS.NB, _ => (GS.NA, none)
  | GS.D, _ => (GS.D, none)

/-- The gate counter. -/
def gcount (s : List Bool) : List Bool := fstRun δgc (fun _ => none) GS.U s

theorem gc_done (r : List Bool) : fstRun δgc (fun _ => none) GS.D r = [] := by
  induction r with
  | nil => rfl
  | cons b r ih => simpa [fstRun, δgc] using ih

theorem gc_bits (l : List Bool) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.NA (l.flatMap (fun b => [true, b]) ++ false :: r) =
      fstRun δgc (fun _ => none) GS.IL r := by
  induction l with
  | nil => simp [fstRun, δgc]
  | cons b l ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    simp only [List.cons_append] at ih
    cases b <;> simp [fstRun, δgc, ih]

theorem gc_nat (k : ℕ) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.NA (encodeNat k ++ r) = fstRun δgc (fun _ => none) GS.IL r := by
  simpa [encodeNat] using gc_bits (Nat.bits k) r

theorem gc_natList (l : List ℕ) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.IL (encodeList encodeNat l ++ r) =
      fstRun δgc (fun _ => none) GS.G r := by
  induction l with
  | nil => simp [encodeList, fstRun, δgc]
  | cons a l ih =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append] at ih ⊢
    simp only [fstRun, δgc, Option.toList_none, List.nil_append]
    rw [gc_nat]
    exact ih

theorem gc_gate (g : Gate) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.O0 (encodeGate g ++ r) = fstRun δgc (fun _ => none) GS.G r := by
  obtain ⟨op, ins⟩ := g
  cases op <;>
    simp only [encodeGate, encodeGateOp, List.append_assoc, List.cons_append, List.nil_append,
      fstRun, δgc, Option.toList_none] <;>
    first
    | exact gc_natList ins r
    | (rw [gc_nat]; exact gc_natList ins r)

theorem gc_gates (gs : List Gate) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.G (encodeList encodeGate gs ++ r) =
      List.replicate gs.length true := by
  induction gs with
  | nil => simp [encodeList, fstRun, δgc, gc_done]
  | cons g gs ih =>
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append] at ih ⊢
    simp only [fstRun, δgc, Option.toList_some, Option.toList_none, List.length_cons,
      List.replicate_succ]
    rw [gc_gate]
    simpa using ih

theorem gc_unary (n : ℕ) (r : List Bool) :
    fstRun δgc (fun _ => none) GS.U (List.replicate n true ++ false :: r) =
      fstRun δgc (fun _ => none) GS.G r := by
  induction n with
  | zero => simp [fstRun, δgc]
  | succ n ih => simpa [List.replicate_succ, fstRun, δgc] using ih

theorem gcount_encodeLgp (n : ℕ) (C : Circuit) :
    gcount (encodeLgp (n, C)) = List.replicate C.size true := by
  simp only [gcount, encodeLgp]
  rw [gc_unary, gc_gates]
  rfl

theorem gcountPoly : GcountPoly :=
  ⟨gcount, fst_polyTime _ _ _ δgc (fun _ => none) GS.U (fun _ => rfl),
    fun n C => by rw [gcount_encodeLgp, List.length_replicate]⟩

/-! ## Evaluation from the two machine facts -/

theorem hd_encodeLgp (n : ℕ) (C : Circuit) :
    hd (encodeLgp (n, C)) = List.replicate n true := by
  have := hd_un n (encodeList encodeGate C.gates ++ encodeNat C.output)
  simpa [un, encodeLgp] using this

theorem evalPoly_of (hV : ValidPoly) (hEV : EvalValidPoly) : EvalPoly := by
  obtain ⟨fV, hfV, cV⟩ := hV
  obtain ⟨ev, cev, hev⟩ := hEV
  have h1 : CPTB (fun s => fV (unpairB s).1) := cpt_comp cpt_unpairB1 cV
  have hle1 := cpt_app (u := fun s => hd (unpairB s).1) (v := fun s => (unpairB s).2)
    (cptc LenCmp.lenLE_polyTime (fun _ => rfl)) (cpt_comp cpt_unpairB1 cpt_hd) cpt_unpairB2
  have hle2 := cpt_app (u := fun s => (unpairB s).2) (v := fun s => hd (unpairB s).1)
    (cptc LenCmp.lenLE_polyTime (fun _ => rfl)) cpt_unpairB2 (cpt_comp cpt_unpairB1 cpt_hd)
  have heq := cptb_op (fun a b => a && b) hle1 hle2
  have h3 : CPTB (fun s => ev (unpairB s)) := cpt_to_packed cev
  have hall := cptb_op (fun a b => a && b) (cptb_op (fun a b => a && b) h1 heq) h3
  apply cpt_of_packed
  refine cptc hall (fun t => ?_)
  obtain ⟨s, x⟩ := unpairB t
  show (fV s && (decide (x.length ≤ (hd s).length) && decide ((hd s).length ≤ x.length)) &&
    ev (s, x)) = lgpVal s x
  by_cases hs : ∃ (n : ℕ) (C : Circuit), s = encodeLgp (n, C) ∧ FanInTwo C
  · obtain ⟨n, C, rfl, hC⟩ := hs
    have e1 : fV (encodeLgp (n, C)) = true := (hfV _).1 ⟨n, C, rfl, hC⟩
    rw [e1, lgpVal_encode n C hC, hd_encodeLgp, List.length_replicate]
    by_cases hx : x.length = n
    · rw [hev n C x hC hx]
      simp [hx]
    · have hb : (decide (x.length ≤ n) && decide (n ≤ x.length)) = false := by
        by_cases h : x.length ≤ n <;> simp [h] <;> omega
      rw [hb]
      simp [hx]
  · have e1 : fV s = false := by
      cases h : fV s
      · rfl
      · exact absurd ((hfV s).2 h) hs
    rw [e1, Bool.false_and, Bool.false_and]
    unfold lgpVal
    cases h : lgpDec s with
    | none => rfl
    | some p =>
      obtain ⟨n, C⟩ := p
      have e := lgpDec_some h
      by_cases hC : FanInTwo C
      · exact absurd ⟨n, C, e.symm, hC⟩ hs
      · simp [hC]

/-! ## Lengths of codes -/

theorem length_pairs (l : List Bool) : (l.flatMap fun b => [true, b]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]
    omega

theorem length_encodeNat_le (k : ℕ) : (encodeNat k).length ≤ 2 * k + 1 := by
  have h : (Nat.bits k).length ≤ k := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  rw [encodeNat, List.length_append, length_pairs]
  simp only [List.length_singleton]
  omega

theorem length_encodeList_le {α : Type} (e : α → List Bool) (b : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (e a).length ≤ b) →
      (encodeList e l).length ≤ l.length * (b + 1) + 1
  | [], _ => by simp [encodeList]
  | a :: l, h => by
    have ih := length_encodeList_le e b l (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    have ha := h a List.mem_cons_self
    simp only [encodeList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    nlinarith

theorem length_encodeGate_le (m : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hb : ∀ a ∈ g.inputs, a ≤ m) :
    (encodeGate g).length ≤ 4 * m + 9 := by
  have h1 : (encodeGateOp g.op).length = 2 := by
    have h : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
    rcases h with h | h | h <;> rw [h] <;> rfl
  have h2 := length_encodeList_le encodeNat (2 * m + 1) g.inputs
    (fun a ha => (length_encodeNat_le a).trans (by have := hb a ha; omega))
  simp only [encodeGate, List.length_append, h1]
  nlinarith

theorem length_encodeLgp_clamp (n : ℕ) (C D : Circuit) (hD : FanInTwo D) (hs : D.size < C.size) :
    (encodeLgp (n, clampCircuit (n + D.size) D)).length ≤
      wbound.eval (encodeLgp (n, C)).length := by
  set L := (encodeLgp (n, C)).length
  have hL := LgpEncode.encodeLgp_length_ge n C
  set m := n + D.size
  have hm : m ≤ L := by simp only [m]; omega
  have hg := length_encodeList_le encodeGate (4 * m + 9) (clampCircuit m D).gates (by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine length_encodeGate_le m _ (hD g' hg').1 (by simpa [clampGate] using (hD g' hg').2) ?_
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
    exact Nat.min_le_right _ _)
  have ho := length_encodeNat_le (clampCircuit m D).output
  have ho' : (clampCircuit m D).output ≤ m := Nat.min_le_right _ _
  have hsz : (clampCircuit m D).gates.length ≤ L := by
    have h1 := size_clampCircuit m D
    unfold Circuit.size at h1 hs hL
    omega
  simp only [encodeLgp, List.length_append, List.length_replicate, List.length_cons]
  simp only [wbound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have : (clampCircuit m D).gates.length * (4 * m + 9 + 1) ≤ L * (4 * L + 10) :=
    Nat.mul_le_mul hsz (by omega)
  nlinarith

/-! ## The main argument -/

theorem fun_eq_of_lgpVal {n : ℕ} {C D : Circuit}
    (h : ∀ x : List Bool, x.length = n → C.eval x = D.eval x) :
    circuitFun n D = circuitFun n C := by
  funext y
  exact (h (List.ofFn y) (List.length_ofFn)).symm

/-- The circuit with no gate whose output wire does not exist on `n` inputs computes the
constant `false`. -/
theorem circuitFun_empty (n : ℕ) : circuitFun n ⟨[], n⟩ = fun _ => false := by
  funext y
  simp [circuitFun, Circuit.eval, Circuit.wires]

/-- P = NP, `EvalPoly` and `GcountPoly` give `LgpInP`. -/
theorem lgpInP_of (hPNP : P = NP) (hE : EvalPoly) (hG : GcountPoly) : LgpInP := by
  obtain ⟨gc, cgc, hgc⟩ := hG
  have hdis : Ldis ∈ P := hPNP ▸ ldis_mem_NP hE
  obtain ⟨g, hg, cg⟩ := hdis
  have hnm : (Lnm gc g)ᶜ ∈ P := PEqualNP.Library.L008 _ (hPNP ▸ lnm_mem_NP cgc cg)
  obtain ⟨h, hh, ch⟩ := hnm
  have cenc : ComputableInPolyTime encodeLgp (fun x : List Bool => x) encodeLgp :=
    filterMap_polyTime _ _ _ (fun b : Bool => some b) (fun p => by simp)
  refine ⟨fun p => h (encodeLgp p), cpt_comp cenc ch, ?_⟩
  rintro ⟨n, C⟩
  constructor
  · intro hY
    have hC : FanInTwo C := hY.1
    rw [← hh]
    rintro ⟨w, -, hw⟩
    simp only [V2, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
    obtain ⟨hlt, hw2⟩ := hw
    rw [hgc] at hlt
    have hnot : pairB (encodeLgp (n, C)) w ∉ Ldis := by
      intro hm
      have hm' := (hg _).1 hm
      rw [hm'] at hw2
      exact Bool.noConfusion hw2
    have heq : ∀ x : List Bool, x.length = n →
        lgpVal (encodeLgp (n, C)) x = lgpVal w x := by
      intro x hx
      by_contra hne
      apply hnot
      refine ⟨x, ?_, ?_⟩
      · have := LgpEncode.encodeLgp_length_ge n C
        rw [pairB_length]
        omega
      · simp only [V1, unpairB_pairB]
        simpa using hne
    by_cases hD : ∃ D : Circuit, w = encodeLgp (n, D) ∧ FanInTwo D
    · obtain ⟨D, rfl, hD⟩ := hD
      rw [hgc] at hlt
      have hf : circuitFun n D = circuitFun n C := by
        funext y
        have := heq (List.ofFn y) List.length_ofFn
        rw [lgpVal_encode n C hC, lgpVal_encode n D hD] at this
        simpa [circuitFun] using this.symm
      have : C.size ≤ D.size := hY.2 D hD hf
      omega
    · have hf : circuitFun n ⟨[], n⟩ = circuitFun n C := by
        rw [circuitFun_empty]
        funext y
        have := heq (List.ofFn y) List.length_ofFn
        rw [lgpVal_encode n C hC, lgpVal_other n w hD _ List.length_ofFn] at this
        simpa [circuitFun] using this.symm
      have : C.size ≤ (⟨[], n⟩ : Circuit).size := hY.2 ⟨[], n⟩ (fun g hg => by simp at hg) hf
      simp only [Circuit.size, List.length_nil] at this
      unfold Circuit.size at hlt
      omega
  · rintro ⟨hN, hnm⟩
    have hC : FanInTwo C := hN.1
    have : ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧ D.size < C.size := by
      by_contra hc
      push_neg at hc
      exact hnm ⟨hC, fun D hD hf => hc D hD hf⟩
    obtain ⟨D, hD, hf, hlt⟩ := this
    have hfalse : h (encodeLgp (n, C)) ≠ true := by
      intro hT
      have hmem := (hh _).2 hT
      apply hmem
      set m := n + D.size
      have hD' := fanInTwo_clampCircuit m D hD
      refine ⟨encodeLgp (n, clampCircuit m D), length_encodeLgp_clamp n C D hD hlt, ?_⟩
      simp only [V2, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨by rw [hgc, hgc, size_clampCircuit]; exact hlt, ?_⟩
      cases hgv : g (pairB (encodeLgp (n, C)) (encodeLgp (n, clampCircuit m D))) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨x, -, hx⟩ := (hg _).2 hgv
        simp only [V1, unpairB_pairB, lgpVal_encode n C hC, lgpVal_encode n _ hD'] at hx
        by_cases hxl : x.length = n
        · subst hxl
          have e1 : (clampCircuit m D).eval x = D.eval x :=
            eval_clampCircuit m D x (by simp only [m, Circuit.size]; omega)
          have e2 : D.eval x = C.eval x := by
            have := congrFun hf (fun i : Fin x.length => x[i])
            simpa [circuitFun, List.ofFn_getElem] using this
          simp [e1, e2] at hx
        · simp [hxl] at hx
    simpa using hfalse

end PEqualNP.MetaComplexity.LgpB.LgpInP

namespace PEqualNP.MetaComplexity.LgpB.LgpInP
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.CircuitLowerBounds PEqualNP.Library PEqualNP.Library.Machines
  PEqualNP.MetaComplexity

/-! ## Recognising codes of fan-in-two circuits: one finite automaton -/

/-- Inside a number: nothing read yet, last bit `true`, last bit `false`. -/
inductive NSt : Type
  | e | t | f
  deriving DecidableEq

instance : Fintype NSt :=
  Fintype.ofList [NSt.e, NSt.t, NSt.f] (fun x => by cases x <;> simp)

/-- Where a number sits: first operand, second operand, output. -/
inductive Ctx : Type
  | i1 | i2 | out
  deriving DecidableEq

instance : Fintype Ctx :=
  Fintype.ofList [Ctx.i1, Ctx.i2, Ctx.out] (fun x => by cases x <;> simp)

/-- States of the recogniser. -/
inductive VS : Type
  | U | G | O0 | O1F | O1T | I0 | I1 | I2 | N (c : Ctx) (st : NSt) | NB (c : Ctx) | Acc | Rej
  deriving DecidableEq

instance : Fintype VS :=
  Fintype.ofList ([VS.U, VS.G, VS.O0, VS.O1F, VS.O1T, VS.I0, VS.I1, VS.I2, VS.Acc, VS.Rej] ++
      ([Ctx.i1, Ctx.i2, Ctx.out].flatMap fun c =>
        [VS.NB c, VS.N c NSt.e, VS.N c NSt.t, VS.N c NSt.f]))
    (fun x => by
      cases x with
      | N c st => cases c <;> cases st <;> simp
      | NB c => cases c <;> simp
      | _ => simp)

/-- The state after a number. -/
def retV : Ctx → VS
  | Ctx.i1 => VS.I1
  | Ctx.i2 => VS.I2
  | Ctx.out => VS.Acc

/-- The state after a bit of a number. -/
def bitSt (b : Bool) : NSt := if b then NSt.t else NSt.f

/-- The transition function. -/
def δv : VS → Bool → VS
  | VS.U, true => VS.U
  | VS.U, false => VS.G
  | VS.G, true => VS.O0
  | VS.G, false => VS.N Ctx.out NSt.e
  | VS.O0, false => VS.O1F
  | VS.O0, true => VS.O1T
  | VS.O1F, _ => VS.I0
  | VS.O1T, false => VS.I0
  | VS.O1T, true => VS.Rej
  | VS.I0, true => VS.N Ctx.i1 NSt.e
  | VS.I0, false => VS.G
  | VS.I1, true => VS.N Ctx.i2 NSt.e
  | VS.I1, false => VS.G
  | VS.I2, true => VS.Rej
  | VS.I2, false => VS.G
  | VS.N c _, true => VS.NB c
  | VS.N _ NSt.f, false => VS.Rej
  | VS.N c NSt.e, false => retV c
  | VS.N c NSt.t, false => retV c
  | VS.NB c, b => VS.N c (bitSt b)
  | VS.Acc, _ => VS.Rej
  | VS.Rej, _ => VS.Rej

/-- The state reached. -/
def runV (q : VS) (r : List Bool) : VS := r.foldl δv q

@[simp] theorem runV_nil (q : VS) : runV q [] = q := rfl

@[simp] theorem runV_cons (q : VS) (b : Bool) (r : List Bool) :
    runV q (b :: r) = runV (δv q b) r := rfl

theorem runV_append (q : VS) (a b : List Bool) : runV q (a ++ b) = runV (runV q a) b := by
  simp [runV, List.foldl_append]

theorem runV_rej (r : List Bool) : runV VS.Rej r = VS.Rej := by
  induction r with
  | nil => rfl
  | cons b r ih => simpa [δv] using ih

theorem runV_acc (r : List Bool) (h : runV VS.Acc r = VS.Acc) : r = [] := by
  cases r with
  | nil => rfl
  | cons b r => simp [δv, runV_rej] at h

/-- The recogniser as a decision bit. -/
def validB (s : List Bool) : Bool := decide (runV VS.U s = VS.Acc)

theorem validB_run (q : VS) (r : List Bool) :
    fstRun (fun q b => (δv q b, (none : Option Bool))) (fun q => some (decide (q = VS.Acc))) q r =
      [decide (runV q r = VS.Acc)] := by
  induction r generalizing q with
  | nil => rfl
  | cons b r ih => exact ih (δv q b)

theorem cpt_validB :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool validB :=
  fst_polyTime _ _ _ (fun q b => (δv q b, (none : Option Bool)))
    (fun q => some (decide (q = VS.Acc))) VS.U (fun s => (validB_run VS.U s).symm)

/-! ### The last bit of a number -/

/-- The inside-a-number state after the bits `L`. -/
def lastSt : NSt → List Bool → NSt
  | st, [] => st
  | _, b :: L => lastSt (bitSt b) L

theorem runV_bits (c : Ctx) (st : NSt) (L : List Bool) :
    runV (VS.N c st) (L.flatMap fun b => [true, b]) = VS.N c (lastSt st L) := by
  induction L generalizing st with
  | nil => rfl
  | cons b L ih => simpa [δv, lastSt] using ih (bitSt b)

theorem lastSt_bits (k : ℕ) (hk : k ≠ 0) (st : NSt) : lastSt st (Nat.bits k) = NSt.t := by
  induction k using Nat.binaryRec' generalizing st with
  | zero => exact absurd rfl hk
  | bit b k h ih =>
    rw [Nat.bits_append_bit k b h]
    by_cases hk0 : k = 0
    · subst hk0
      have hb : b = true := by
        cases b
        · exact absurd (by simp) hk
        · rfl
      subst hb
      simp [lastSt, bitSt]
    · simp only [lastSt]
      exact ih hk0 _

theorem runV_nat (c : Ctx) (k : ℕ) (r : List Bool) :
    runV (VS.N c NSt.e) (encodeNat k ++ r) = runV (retV c) r := by
  rw [encodeNat, List.append_assoc, runV_append, runV_bits]
  by_cases hk : k = 0
  · subst hk
    simp [lastSt, δv]
  · rw [lastSt_bits k hk]
    simp [δv]

theorem lastSt_ne_nil (L : List Bool) (hL : L ≠ []) (st st' : NSt) :
    lastSt st L = lastSt st' L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons b L => rfl

theorem exists_bits (L : List Bool) (h : lastSt NSt.e L ≠ NSt.f) : ∃ k, Nat.bits k = L := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons b L ih =>
    by_cases hL : L = []
    · subst hL
      cases b
      · simp [lastSt, bitSt] at h
      · exact ⟨1, by decide⟩
    · have h' : lastSt NSt.e L ≠ NSt.f := by
        rw [lastSt_ne_nil L hL NSt.e (bitSt b)]
        exact h
      obtain ⟨k, hk⟩ := ih h'
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        exact hL hk
      refine ⟨Nat.bit b k, ?_⟩
      rw [Nat.bits_append_bit k b (fun h0 => absurd h0 hk0), hk]

/-! ### Soundness -/

theorem sound_N (r : List Bool) :
    (∀ (c : Ctx) (st : NSt), runV (VS.N c st) r = VS.Acc →
      ∃ (L r' : List Bool), r = (L.flatMap fun b => [true, b]) ++ false :: r' ∧
        lastSt st L ≠ NSt.f ∧ runV (retV c) r' = VS.Acc) ∧
    (∀ c : Ctx, runV (VS.NB c) r = VS.Acc →
      ∃ (b : Bool) (L r' : List Bool), r = b :: ((L.flatMap fun b => [true, b]) ++ false :: r') ∧
        lastSt (bitSt b) L ≠ NSt.f ∧ runV (retV c) r' = VS.Acc) := by
  induction r with
  | nil =>
    refine ⟨fun c st h => ?_, fun c h => ?_⟩ <;> simp at h
  | cons a r ih =>
    refine ⟨fun c st h => ?_, fun c h => ?_⟩
    · cases a with
      | true =>
        obtain ⟨b, L, r', rfl, hL, hr⟩ := ih.2 c (by simpa [δv] using h)
        exact ⟨b :: L, r', by simp, by simpa [lastSt] using hL, hr⟩
      | false =>
        cases st with
        | f => simp [δv, runV_rej] at h
        | e => exact ⟨[], r, by simp, by simp [lastSt], by simpa [δv] using h⟩
        | t => exact ⟨[], r, by simp, by simp [lastSt], by simpa [δv] using h⟩
    · obtain ⟨L, r', rfl, hL, hr⟩ := ih.1 c (bitSt a) (by simpa [δv] using h)
      exact ⟨a, L, r', rfl, hL, hr⟩

theorem sound_nat (c : Ctx) (r : List Bool) (h : runV (VS.N c NSt.e) r = VS.Acc) :
    ∃ (k : ℕ) (r' : List Bool), r = encodeNat k ++ r' ∧ runV (retV c) r' = VS.Acc := by
  obtain ⟨L, r', rfl, hL, hr⟩ := (sound_N r).1 c NSt.e h
  obtain ⟨k, rfl⟩ := exists_bits L hL
  exact ⟨k, r', by simp [encodeNat], hr⟩

theorem sound_I2 (r : List Bool) (h : runV VS.I2 r = VS.Acc) :
    ∃ r', r = false :: r' ∧ runV VS.G r' = VS.Acc := by
  cases r with
  | nil => simp at h
  | cons a r =>
    cases a
    · exact ⟨r, rfl, by simpa [δv] using h⟩
    · simp [δv, runV_rej] at h

theorem sound_I1 (r : List Bool) (h : runV VS.I1 r = VS.Acc) :
    ∃ (ins : List ℕ) (r' : List Bool), r = encodeList encodeNat ins ++ r' ∧ ins.length ≤ 1 ∧
      runV VS.G r' = VS.Acc := by
  cases r with
  | nil => simp at h
  | cons a r =>
    cases a
    · exact ⟨[], r, by simp [encodeList], by simp, by simpa [δv] using h⟩
    · obtain ⟨k, r1, rfl, h1⟩ := sound_nat Ctx.i2 r (by simpa [δv] using h)
      obtain ⟨r', rfl, h2⟩ := sound_I2 r1 h1
      exact ⟨[k], r', by simp [encodeList], by simp, h2⟩

theorem sound_I0 (r : List Bool) (h : runV VS.I0 r = VS.Acc) :
    ∃ (ins : List ℕ) (r' : List Bool), r = encodeList encodeNat ins ++ r' ∧ ins.length ≤ 2 ∧
      runV VS.G r' = VS.Acc := by
  cases r with
  | nil => simp at h
  | cons a r =>
    cases a
    · exact ⟨[], r, by simp [encodeList], by simp, by simpa [δv] using h⟩
    · obtain ⟨k, r1, rfl, h1⟩ := sound_nat Ctx.i1 r (by simpa [δv] using h)
      obtain ⟨ins, r', rfl, hl, h2⟩ := sound_I1 r1 h1
      refine ⟨k :: ins, r', by simp [encodeList], by simp; omega, h2⟩

/-- A gate accepted by the recogniser. -/
def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem sound_G : ∀ (m : ℕ) (r : List Bool), r.length ≤ m → runV VS.G r = VS.Acc →
    ∃ (gs : List Gate) (k : ℕ), r = encodeList encodeGate gs ++ encodeNat k ∧
      ∀ g ∈ gs, GateOK g
  | m, [], _, h => by simp at h
  | m, false :: r, _, h => by
    obtain ⟨k, r', rfl, h1⟩ := sound_nat Ctx.out r (by simpa [δv] using h)
    have := runV_acc r' h1
    subst this
    exact ⟨[], k, by simp [encodeList], by simp⟩
  | 0, true :: r, hl, _ => by simp at hl
  | m + 1, true :: r, hl, h => by
    simp only [runV_cons, δv] at h
    have key : ∃ (op : GateOp) (r1 : List Bool), r = encodeGateOp op ++ r1 ∧
        op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ runV VS.I0 r1 = VS.Acc := by
      match r, h with
      | [], h => simp at h
      | [a], h => cases a <;> simp [δv] at h
      | false :: false :: r1, h => exact ⟨GateOp.and, r1, rfl, by simp, by simpa [δv] using h⟩
      | false :: true :: r1, h => exact ⟨GateOp.or, r1, rfl, by simp, by simpa [δv] using h⟩
      | true :: false :: r1, h => exact ⟨GateOp.not, r1, rfl, by simp, by simpa [δv] using h⟩
      | true :: true :: r1, h => simp [δv, runV_rej] at h
    obtain ⟨op, r1, rfl, hop, h1⟩ := key
    obtain ⟨ins, r2, rfl, hins, h2⟩ := sound_I0 r1 h1
    have hlen : r2.length ≤ m := by
      have : (encodeGateOp op).length ≥ 0 := Nat.zero_le _
      have : (encodeList encodeNat ins).length ≥ 1 := by simp [encodeList]
      simp only [List.length_cons, List.length_append] at hl
      omega
    obtain ⟨gs, k, rfl, hgs⟩ := sound_G m r2 hlen h2
    refine ⟨⟨op, ins⟩ :: gs, k, ?_, ?_⟩
    · simp [encodeList, encodeGate, List.append_assoc]
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨hop, hins⟩
      · exact hgs g hg

theorem sound_U (r : List Bool) (h : runV VS.U r = VS.Acc) :
    ∃ (n : ℕ) (r' : List Bool), r = List.replicate n true ++ false :: r' ∧
      runV VS.G r' = VS.Acc := by
  induction r with
  | nil => simp at h
  | cons a r ih =>
    cases a
    · exact ⟨0, r, rfl, by simpa [δv] using h⟩
    · obtain ⟨n, r', rfl, h'⟩ := ih (by simpa [δv] using h)
      exact ⟨n + 1, r', by simp [List.replicate_succ], h'⟩

/-! ### Completeness -/

theorem complete_I0 (ins : List ℕ) (hl : ins.length ≤ 2) (r : List Bool) :
    runV VS.I0 (encodeList encodeNat ins ++ r) = runV VS.G r := by
  match ins, hl with
  | [], _ => simp [encodeList, δv]
  | [a], _ =>
    simp only [encodeList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.append_assoc, runV_cons, δv]
    rw [runV_nat]
    simp [retV, δv]
  | [a, b], _ =>
    simp only [encodeList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.append_assoc, runV_cons, δv]
    rw [runV_nat]
    simp only [retV, runV_cons, δv]
    rw [runV_nat]
    simp [retV, δv]

theorem complete_G (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (k : ℕ) :
    runV VS.G (encodeList encodeGate gs ++ encodeNat k) = VS.Acc := by
  induction gs with
  | nil =>
    simp only [encodeList, List.flatMap_nil, List.nil_append, List.singleton_append, runV_cons,
      δv]
    have := runV_nat Ctx.out k []
    simpa [retV] using this
  | cons g gs ih =>
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hins⟩ := hgs _ List.mem_cons_self
    have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by simpa using hop
    have ih' := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    simp only [encodeList, List.flatMap_cons, List.append_assoc, List.cons_append] at ih' ⊢
    simp only [runV_cons, δv]
    rcases hop' with h | h | h <;> subst h <;>
      simp only [encodeGate, encodeGateOp, List.append_assoc, List.cons_append, List.nil_append,
        runV_cons, δv] <;>
      rw [complete_I0 ins hins] <;>
      first
      | exact ih'
      | simpa only [List.append_assoc, List.cons_append] using ih'

theorem fanInTwo_iff (C : Circuit) : FanInTwo C ↔ ∀ g ∈ C.gates, GateOK g := Iff.rfl

theorem validB_iff (s : List Bool) :
    validB s = true ↔ ∃ (n : ℕ) (C : Circuit), s = encodeLgp (n, C) ∧ FanInTwo C := by
  simp only [validB, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨n, r, rfl, hr⟩ := sound_U s h
    obtain ⟨gs, k, rfl, hgs⟩ := sound_G r.length r le_rfl hr
    exact ⟨n, ⟨gs, k⟩, rfl, hgs⟩
  · rintro ⟨n, C, rfl, hC⟩
    have : runV VS.U (List.replicate n true) = VS.U := by
      induction n with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ, δv] using ih
    rw [encodeLgp, runV_append, this]
    simp only [runV_cons, δv]
    exact complete_G C.gates hC C.output

theorem validPoly : ValidPoly :=
  ⟨validB, fun s => (validB_iff s).symm, cpt_validB⟩

end PEqualNP.MetaComplexity.LgpB.LgpInP

namespace PEqualNP.MetaComplexity.LgpB.LgpInP
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.CircuitLowerBounds PEqualNP.Library PEqualNP.Library.Machines
  PEqualNP.Library.Universal PEqualNP.MetaComplexity

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

local notation "CPTB" =>
  ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool

/-! ## Evaluating a valid code: one pass per gate, wire lookup at a binary index -/

/-- States of the gate reader: the marker, the two operation bits, the operand list (before,
between and after the operands), inside the first or second operand (two states each), and
the rest of the string. -/
inductive ES : Type
  | S | O0 | O1 | L0 | A1 | B1 | L1 | A2 | B2 | L2 | Cp
  deriving DecidableEq

instance : Fintype ES :=
  Fintype.ofList [ES.S, ES.O0, ES.O1, ES.L0, ES.A1, ES.B1, ES.L1, ES.A2, ES.B2, ES.L2, ES.Cp]
    (fun x => by cases x <;> simp)

/-- What the gate reader writes: the rest of the string after the first gate, the bits of the
first or second operand, or a flag for: first operation bit, second operation bit, at least one
operand, two operands, the string starts with a gate. -/
inductive Mode : Type
  | rest | in1 | in2 | op0 | op1 | c1 | c2 | mk
  deriving DecidableEq

/-- The next state of the gate reader. -/
def nxt : ES → Bool → ES
  | ES.S, _ => ES.O0
  | ES.O0, _ => ES.O1
  | ES.O1, _ => ES.L0
  | ES.L0, true => ES.A1
  | ES.L0, false => ES.Cp
  | ES.A1, true => ES.B1
  | ES.A1, false => ES.L1
  | ES.B1, _ => ES.A1
  | ES.L1, true => ES.A2
  | ES.L1, false => ES.Cp
  | ES.A2, true => ES.B2
  | ES.A2, false => ES.L2
  | ES.B2, _ => ES.A2
  | ES.L2, _ => ES.Cp
  | ES.Cp, _ => ES.Cp

/-- The output of the gate reader in a mode. -/
def outE : Mode → ES → Bool → Option Bool
  | Mode.rest, ES.Cp, b => some b
  | Mode.in1, ES.B1, b => some b
  | Mode.in2, ES.B2, b => some b
  | Mode.op0, ES.O0, true => some true
  | Mode.op1, ES.O1, true => some true
  | Mode.c1, ES.L0, true => some true
  | Mode.c2, ES.L1, true => some true
  | Mode.mk, ES.S, true => some true
  | _, _, _ => none

/-- The transition function of the gate reader. -/
def δe (m : Mode) (q : ES) (b : Bool) : ES × Option Bool := (nxt q b, outE m q b)

/-- The gate reader. -/
def te (m : Mode) (r : List Bool) : List Bool := fstRun (δe m) (fun _ => none) ES.S r

theorem cpt_te (m : Mode) : CPT (te m) :=
  fst_polyTime _ _ _ (δe m) (fun _ => none) ES.S (fun _ => rfl)

theorem te_cp (m : Mode) (r : List Bool) :
    fstRun (δe m) (fun _ => none) ES.Cp r = if m = Mode.rest then r else [] := by
  induction r with
  | nil => cases m <;> rfl
  | cons b r ih => cases m <;> simp_all [fstRun, δe, nxt, outE]

theorem te_A1 (m : Mode) (L : List Bool) (r : List Bool) :
    fstRun (δe m) (fun _ => none) ES.A1 ((L.flatMap fun b => [true, b]) ++ false :: r) =
      (if m = Mode.in1 then L else []) ++ fstRun (δe m) (fun _ => none) ES.L1 r := by
  induction L with
  | nil => cases m <;> simp [fstRun, δe, nxt, outE]
  | cons b L ih => cases m <;> simp_all [fstRun, δe, nxt, outE]

theorem te_A2 (m : Mode) (L : List Bool) (r : List Bool) :
    fstRun (δe m) (fun _ => none) ES.A2 ((L.flatMap fun b => [true, b]) ++ false :: r) =
      (if m = Mode.in2 then L else []) ++ fstRun (δe m) (fun _ => none) ES.L2 r := by
  induction L with
  | nil => cases m <;> simp [fstRun, δe, nxt, outE]
  | cons b L ih => cases m <;> simp_all [fstRun, δe, nxt, outE]

theorem te_nat1 (m : Mode) (a : ℕ) (r : List Bool) :
    fstRun (δe m) (fun _ => none) ES.A1 (encodeNat a ++ r) =
      (if m = Mode.in1 then Nat.bits a else []) ++ fstRun (δe m) (fun _ => none) ES.L1 r := by
  simpa [encodeNat] using te_A1 m (Nat.bits a) r

theorem te_nat2 (m : Mode) (a : ℕ) (r : List Bool) :
    fstRun (δe m) (fun _ => none) ES.A2 (encodeNat a ++ r) =
      (if m = Mode.in2 then Nat.bits a else []) ++ fstRun (δe m) (fun _ => none) ES.L2 r := by
  simpa [encodeNat] using te_A2 m (Nat.bits a) r

/-- The value of an index written in binary, least significant bit first, as `cpt_lookup`
reads it. -/
def lk (W i : List Bool) : Bool :=
  W.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i) false

theorem lk_bits (W : List Bool) (k : ℕ) : lk W (Nat.bits k) = W.getD k false := by
  have e : (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) = Nat.bit := by
    funext b a
    cases b <;> simp [Nat.bit] <;> omega
  simp only [lk, e, LgpEncode.foldr_bits]

/-- The flag of a mode as a bit. -/
def fl (m : Mode) (r : List Bool) : Bool := !(te m r).isEmpty

/-- The value of a fan-in-two gate from its flags and the values of its operands. -/
def gval (o0 o1 c1 c2 a1 a2 : Bool) : Bool :=
  if o0 then !(c1 && a1) else if o1 then (c1 && a1) || (c2 && a2) else (!c1 || a1) && (!c2 || a2)

/-- The value of the first gate of `r` on the wires `W`. -/
def vOf (r W : List Bool) : Bool :=
  gval (fl Mode.op0 r) (fl Mode.op1 r) (fl Mode.c1 r) (fl Mode.c2 r) (lk W (te Mode.in1 r))
    (lk W (te Mode.in2 r))

/-- One step of the evaluator on the packed pair (rest of the code, wires): if the rest starts
with a gate, drop the gate and add its value as a new wire; otherwise do nothing. -/
def gstep (y : List Bool) : List Bool :=
  sel (te Mode.mk (unpairB y).1) y
    (pairB (te Mode.rest (unpairB y).1) ((unpairB y).2 ++ [vOf (unpairB y).1 (unpairB y).2]))

theorem vOf_gate (op : GateOp) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hins : ins.length ≤ 2)
    (r W : List Bool) :
    vOf (true :: (encodeGate ⟨op, ins⟩ ++ r)) W = op.eval (ins.map fun i => W.getD i false) := by
  match ins, hins with
  | [], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [vOf, gval, fl, te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList,
        te_cp, GateOp.eval]
  | [a], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [vOf, gval, fl, te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList,
        te_cp, te_nat1, lk_bits, GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [vOf, gval, fl, te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList,
        te_cp, te_nat1, te_nat2, lk_bits, GateOp.eval]

theorem te_gate_mk (g : Gate) (r : List Bool) :
    te Mode.mk (true :: (encodeGate g ++ r)) ≠ [] := by
  simp [te, fstRun, δe, outE]

theorem te_gate_rest (op : GateOp) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hins : ins.length ≤ 2)
    (r : List Bool) :
    te Mode.rest (true :: (encodeGate ⟨op, ins⟩ ++ r)) = r := by
  match ins, hins with
  | [], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList, te_cp]
  | [a], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList, te_cp, te_nat1]
  | [a, b], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp [te, fstRun, δe, nxt, outE, encodeGate, encodeGateOp, encodeList, te_cp, te_nat1,
        te_nat2]

theorem gstep_gate (g : Gate) (hg : GateOK g) (r W : List Bool) :
    gstep (pairB (true :: (encodeGate g ++ r)) W) =
      pairB r (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hins⟩ := hg
  have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by simpa using hop
  rw [gstep]
  simp only [unpairB_pairB]
  rw [sel, if_neg (te_gate_mk _ _), te_gate_rest op ins hop' hins, vOf_gate op ins hop' hins]

theorem te_mk_other (q : ES) (hq : q ≠ ES.S) (r : List Bool) :
    fstRun (δe Mode.mk) (fun _ => none) q r = [] := by
  induction r generalizing q with
  | nil => rfl
  | cons b r ih =>
    have h1 : outE Mode.mk q b = none := by cases q <;> cases b <;> simp_all [outE]
    have h2 : nxt q b ≠ ES.S := by cases q <;> cases b <;> simp [nxt]
    simp [fstRun, δe, h1, ih _ h2]

theorem gstep_idle (r W : List Bool) : gstep (pairB (false :: r) W) = pairB (false :: r) W := by
  have : te Mode.mk (false :: r) = [] := by
    simp [te, fstRun, δe, outE, te_mk_other _ (show nxt ES.S false ≠ ES.S by simp [nxt])]
  simp [gstep, unpairB_pairB, sel, this]

theorem gstep_iter_idle (k : ℕ) (r W : List Bool) :
    gstep^[k] (pairB (false :: r) W) = pairB (false :: r) W := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, gstep_idle, ih]

theorem gstep_gates (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (r : List Bool) :
    ∀ W : List Bool,
      gstep^[gs.length] (pairB ((gs.flatMap fun g => true :: encodeGate g) ++ r) W) =
        pairB r (wiresFrom gs W) := by
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons]
    simp only [List.cons_append, List.append_assoc]
    rw [gstep_gate g (hgs g List.mem_cons_self)]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _

theorem unpairB_len (y : List Bool) :
    2 * (unpairB y).1.length + (unpairB y).2.length ≤ y.length := by
  have h1 := congrArg List.length (List.takeWhile_append_dropWhile (p := id) (l := y))
  rw [List.length_append] at h1
  have h2 : ((y.dropWhile id).tail).length + 1 ≤ (y.dropWhile id).length ∨
      (y.dropWhile id).tail = [] := by
    cases y.dropWhile id with
    | nil => right; rfl
    | cons a l => left; simp
  simp only [unpairB, List.length_take, List.length_drop]
  rcases h2 with h2 | h2
  · omega
  · rw [h2]; simp

theorem gstep_length (y : List Bool) : (gstep y).length ≤ y.length := by
  unfold gstep sel
  split_ifs with h
  · exact le_rfl
  · have hne : (unpairB y).1 ≠ [] := by
      intro h0
      rw [h0] at h
      exact h rfl
    obtain ⟨b, r', hr⟩ := List.exists_cons_of_ne_nil hne
    have hrest : (te Mode.rest (unpairB y).1).length ≤ r'.length := by
      rw [hr]
      exact PEqualNP.MetaComplexity.LgpB.Machines.length_fstRun_le (δe Mode.rest) _ r'
    have hl := unpairB_len y
    have h1 : (unpairB y).1.length = r'.length + 1 := by rw [hr]; rfl
    rw [pairB_length]
    simp only [List.length_append, List.length_singleton]
    omega

/-- States of the output reader: skip one symbol, then read a number. -/
inductive OS : Type
  | X | A | B | D
  deriving DecidableEq

instance : Fintype OS := Fintype.ofList [OS.X, OS.A, OS.B, OS.D] (fun x => by cases x <;> simp)

/-- The output reader: after one symbol, the bits of a number. -/
def δo : OS → Bool → OS × Option Bool
  | OS.X, _ => (OS.A, none)
  | OS.A, true => (OS.B, none)
  | OS.A, false => (OS.D, none)
  | OS.B, b => (OS.A, some b)
  | OS.D, _ => (OS.D, none)

/-- The output reader. -/
def tout (r : List Bool) : List Bool := fstRun δo (fun _ => none) OS.X r

theorem tout_done (r : List Bool) : fstRun δo (fun _ => none) OS.D r = [] := by
  induction r with
  | nil => rfl
  | cons b r ih => simpa [fstRun, δo] using ih

theorem tout_A (L : List Bool) :
    fstRun δo (fun _ => none) OS.A ((L.flatMap fun b => [true, b]) ++ [false]) = L := by
  induction L with
  | nil => simp [fstRun, δo, tout_done]
  | cons b L ih => simpa [fstRun, δo] using ih

theorem tout_nat (k : ℕ) : tout (false :: encodeNat k) = Nat.bits k := by
  simp only [tout, fstRun, δo, Option.toList_none, List.nil_append, encodeNat]
  exact tout_A (Nat.bits k)

theorem cpt_tout : CPT tout := fst_polyTime _ _ _ δo (fun _ => none) OS.X (fun _ => rfl)

/-- The state of the evaluator after all its steps, on a packed pair (code, input). -/
def stF (y : List Bool) : List Bool :=
  gstep^[(unpairB y).1.length] (pairB (dropN (unpairB y).1) (unpairB y).2)

/-- The evaluator on a pair (code, input). -/
def evq (q : List Bool × List Bool) : Bool :=
  lk (unpairB (gstep^[q.1.length] (pairB (dropN q.1) q.2))).2
    (tout (unpairB (gstep^[q.1.length] (pairB (dropN q.1) q.2))).1)

theorem evq_encode (n : ℕ) (C : Circuit) (hC : FanInTwo C) (x : List Bool) :
    evq (encodeLgp (n, C), x) = C.eval x := by
  have hd : dropN (encodeLgp (n, C)) =
      (C.gates.flatMap fun g => true :: encodeGate g) ++ false :: encodeNat C.output := by
    have := dropN_un n (encodeList encodeGate C.gates ++ encodeNat C.output)
    simpa [un, encodeLgp, encodeList] using this
  have hlen : C.gates.length ≤ (encodeLgp (n, C)).length := by
    have := LgpEncode.encodeLgp_length_ge n C
    simp only [Circuit.size] at this
    omega
  obtain ⟨d, hdl⟩ := Nat.exists_eq_add_of_le hlen
  have hst : gstep^[(encodeLgp (n, C)).length] (pairB (dropN (encodeLgp (n, C))) x) =
      pairB (false :: encodeNat C.output) (wiresFrom C.gates x) := by
    rw [hdl, add_comm, Function.iterate_add_apply, hd, gstep_gates C.gates hC, gstep_iter_idle]
  simp only [evq, hst, unpairB_pairB, tout_nat, lk_bits]
  rfl

theorem cpt_evq : ComputableInPolyTime encodePair Computability.encodeBool evq := by
  apply cpt_of_packed
  have hstep : CPT gstep := by
    have hvb : CPTB (fun y => vOf (unpairB y).1 (unpairB y).2) := by
      have hf : ∀ m : Mode, CPTB (fun y => fl m (unpairB y).1) := fun m =>
        cptc (cpt_comp (cpt_comp cpt_unpairB1 (cpt_te m)) cpt_ne) (fun _ => rfl)
      have ha1 : CPTB (fun y => lk (unpairB y).2 (te Mode.in1 (unpairB y).1)) :=
        cpt_app (u := fun y => (unpairB y).2) (v := fun y => te Mode.in1 (unpairB y).1)
          (cptc PEqualNP.MetaComplexity.LgpB.Machines.cpt_lookup (fun _ => rfl))
          cpt_unpairB2 (cpt_comp cpt_unpairB1 (cpt_te Mode.in1))
      have ha2 : CPTB (fun y => lk (unpairB y).2 (te Mode.in2 (unpairB y).1)) :=
        cpt_app (u := fun y => (unpairB y).2) (v := fun y => te Mode.in2 (unpairB y).1)
          (cptc PEqualNP.MetaComplexity.LgpB.Machines.cpt_lookup (fun _ => rfl))
          cpt_unpairB2 (cpt_comp cpt_unpairB1 (cpt_te Mode.in2))
      have p1 := cptb_op (fun a b => a && b) (hf Mode.c1) ha1
      have p2 := cptb_op (fun a b => a && b) (hf Mode.c2) ha2
      have hX := cptb_op (fun a _ => !a) p1 p1
      have hY := cptb_op (fun a b => a || b) p1 p2
      have q1 := cptb_op (fun c a => !c || a) (hf Mode.c1) ha1
      have q2 := cptb_op (fun c a => !c || a) (hf Mode.c2) ha2
      have hZ := cptb_op (fun a b => a && b) q1 q2
      have hYZ := cptb_ite (hf Mode.op1) hY hZ
      exact cptc (cptb_ite (hf Mode.op0) hX hYZ) (fun y => by simp [vOf, gval])
    have hv : CPT (fun y => [vOf (unpairB y).1 (unpairB y).2]) := by
      have hb : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
          (fun b : Bool => [b]) :=
        filterMap_polyTime _ _ _ (fun b : Bool => some b) (fun b => by
          cases b <;> rfl)
      exact cpt_comp hvb hb
    exact cpt_sel (cpt_comp cpt_unpairB1 (cpt_te Mode.mk)) cpt_id
      (cpt_pairB2 (cpt_comp cpt_unpairB1 (cpt_te Mode.rest)) (cpt_app2 cpt_unpairB2 hv))
  have harg : CPT (fun y => pairB (dropN (unpairB y).1) (unpairB y).2) :=
    cpt_pairB2 (cptc (cpt_comp cpt_unpairB1 cpt_dropN) (fun _ => rfl)) cpt_unpairB2
  have hst : CPT stF :=
    cptc (cpt_iterLen hstep gstep_length cpt_unpairB1 harg) (fun _ => rfl)
  have hW : CPT (fun y => (unpairB (stF y)).2) :=
    cptc (cpt_comp hst cpt_unpairB2) (fun _ => rfl)
  have hI : CPT (fun y => tout (unpairB (stF y)).1) :=
    cptc (cpt_comp (cpt_comp hst cpt_unpairB1) cpt_tout) (fun _ => rfl)
  have hL : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => lk p.1 p.2) :=
    cptc PEqualNP.MetaComplexity.LgpB.Machines.cpt_lookup (fun _ => rfl)
  exact cptc (cpt_app hL hW hI) (fun _ => rfl)

theorem evalValidPoly : EvalValidPoly :=
  ⟨evq, cpt_evq, fun n C x hC _ => evq_encode n C hC x⟩

end PEqualNP.MetaComplexity.LgpB.LgpInP

namespace PEqualNP.MetaComplexity.LgpB.LgpInP
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library

/-- If P = NP then the last-gate problem is in P. -/
theorem l109 : P = NP → PEqualNP.MetaComplexity.LgpInP :=
  fun h => lgpInP_of h (evalPoly_of validPoly evalValidPoly) gcountPoly

end PEqualNP.MetaComplexity.LgpB.LgpInP
