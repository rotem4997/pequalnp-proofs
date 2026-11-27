import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18390_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

namespace MixerProof
namespace LocalMixerCertificate

def rows : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
def negatives : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
def pins : List ℕ := (List.range 11).map fun r => 1 <<< r

def hit (a b : ℕ) : Bool := (a &&& b) != 0
def within (a b : ℕ) : Bool := (a &&& b) == a

def neighbors (edges : List ℕ) : List ℕ := pins.map fun v =>
  edges.foldl (fun n e => if hit e v then n ||| (e ^^^ v) else n) 0

def allClauses : List ℕ := (List.range 2048).filter fun a =>
  a != 0 && ((pins.contains a) || (neighbors rows).any (within a))

def available (u : List ℕ) := neighbors (rows.filter fun e => !u.contains e)

def useful (u : List ℕ) (ns : List ℕ) (a : ℕ) : Bool :=
  u.all (hit a) && (pins.contains a || ns.any (within a))

def accepts (u : List ℕ) : Bool :=
  let ns := available u
  let clauses := allClauses.filter (useful u ns)
  let accepted := negatives.filter fun v => clauses.all (hit v)
  let points := accepted.foldl (fun z n => z ||| n) 0
  !accepted.isEmpty && ns.all fun n => u.any fun e => within (n &&& e) points

def triplesFrom (a : ℕ) : List (List ℕ) :=
  ((List.range 16).filter fun b => decide (a < b)).flatMap fun b =>
    ((List.range 16).filter fun c => decide (b < c)).map fun c =>
      [rows.getD a 0,rows.getD b 0,rows.getD c 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check0 : (triplesFrom 0).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check1 : (triplesFrom 1).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check2 : (triplesFrom 2).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check3 : (triplesFrom 3).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check4 : (triplesFrom 4).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check5 : (triplesFrom 5).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check6 : (triplesFrom 6).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check7 : (triplesFrom 7).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check8 : (triplesFrom 8).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check9 : (triplesFrom 9).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check10 : (triplesFrom 10).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check11 : (triplesFrom 11).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check12 : (triplesFrom 12).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check13 : (triplesFrom 13).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check14 : (triplesFrom 14).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check15 : (triplesFrom 15).all accepts = true := by decide +kernel

theorem checked {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 16) :
    accepts [rows.getD i 0,rows.getD j 0,rows.getD k 0] = true := by
  have hi : i < 16 := by omega
  have finite : (triplesFrom i).all accepts = true := by
    interval_cases i
    · exact check0
    · exact check1
    · exact check2
    · exact check3
    · exact check4
    · exact check5
    · exact check6
    · exact check7
    · exact check8
    · exact check9
    · exact check10
    · exact check11
    · exact check12
    · exact check13
    · exact check14
    · exact check15
  apply List.all_eq_true.mp finite
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true hij⟩, ?_⟩
  apply List.mem_map.mpr
  exact ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk,decide_eq_true hjk⟩, rfl⟩

end LocalMixerCertificate
namespace LocalMixerCertificate

lemma within_bit {a b i : ℕ} (h : within a b = true) (hi : a.testBit i = true) : b.testBit i = true := by
  have eq : a &&& b = a := by simpa [within] using h
  have hb := congrArg (fun x : ℕ => x.testBit i) eq
  simpa [Nat.testBit_and, hi] using hb

end LocalMixerCertificate
namespace LocalSignatures
open LocalMixerCertificate

def signature (rs : List ℕ) (m : ℕ) : ℕ :=
  (BitVec.ofBoolListLE (rs.map (hit m))).toNat

def improves (a b : ℕ) : Bool := ((a &&& 7) == (b &&& 7)) && within a b

lemma seven (i : ℕ) : (7 : ℕ).testBit i = decide (i < 3) := Nat.testBit_two_pow_sub_one 3 i

end LocalSignatures
namespace LocalPrune
open LocalSignatures

def insertMinimal (v : ℕ) (cs : List ℕ) : List ℕ :=
  if cs.any (fun q => improves q v) then cs else v :: cs.filter (fun q => !(improves v q))

def prune (vs : List ℕ) := vs.foldr insertMinimal []

def products (xs : List ℕ) := xs.flatMap fun a => xs.map (fun b => a &&& b)
def first (rs : List ℕ) := prune (products (prune rs))
def optional (r d : ℕ) (flag : Bool) := if flag then r ||| d else r

end LocalPrune
namespace LocalWordGeometry
open LocalMixerCertificate LocalSignatures LocalPrune

abbrev TopChoice := ℕ × ℕ × ℕ × ℕ × ℕ

abbrev TopChoice.left (t : TopChoice) := t.1
abbrev TopChoice.right (t : TopChoice) := t.2.1
abbrev TopChoice.useA (t : TopChoice) := t.2.2.1
abbrev TopChoice.useB (t : TopChoice) := t.2.2.2.1
abbrev TopChoice.anchors (t : TopChoice) := t.2.2.2.2

def topValue (opt : TopChoice) (a b : ℕ) : ℕ :=
  let operand := fun p r => r ||| (if opt.useA = p then a else 0) ||| (if opt.useB = p then b else 0)
  operand 1 opt.left &&& operand 2 opt.right

end LocalWordGeometry
namespace LocalGeometrySound
open LocalSignatures LocalPrune LocalWordGeometry

def model (o : List TopChoice) (a b index : ℕ) : Prop :=
  ∀ i : Fin 3, ∃ q ∈ o, topValue q a b ≤ 7 ∧ (topValue q a b).testBit i.val = true ∧ q.anchors.testBit index = true

end LocalGeometrySound
namespace LocalClip
open LocalSignatures LocalWordGeometry LocalGeometrySound LocalPrune LocalMixerCertificate

end LocalClip
namespace LocalBetter
open LocalWordGeometry LocalGeometrySound LocalPrune LocalSignatures LocalMixerCertificate

def Better (a b : ℕ) : Prop :=
  (∀ i < 3, b.testBit i = true → a.testBit i = true) ∧
  (∀ i ≥ 3, a.testBit i = true → b.testBit i = true)

def beats (a b : ℕ) : Bool := within (b &&& 7) (a &&& 7) && within (a >>> 3) (b >>> 3)

lemma beats_sound {a b : ℕ} (h : beats a b=true) : Better a b := by
  obtain ⟨up,dn⟩ := Bool.and_eq_true_iff.mp h
  constructor
  · intro i hi bit
    have pos : (b &&& 7).testBit i = true := by simp [Nat.testBit_and,seven,hi,bit]
    simpa [Nat.testBit_and,seven,hi] using within_bit up pos
  · intro i hi bit
    have eq : 3 + (i-3) = i := by omega
    have pos : (a >>> 3).testBit (i-3) = true := by simpa [Nat.testBit_shiftRight,eq] using bit
    simpa [Nat.testBit_shiftRight,eq] using within_bit dn pos

lemma self (a : ℕ) : Better a a := ⟨fun _ _ h => h,fun _ _ h => h⟩

lemma chain {a b c : ℕ} (ab : Better a b) (bc : Better b c) : Better a c :=
  ⟨fun i hi v => ab.1 i hi (bc.1 i hi v),fun i hi v => bc.2 i hi (ab.2 i hi v)⟩

lemma conj {a b c d : ℕ} (ac : Better a c) (bd : Better b d) : Better (a &&& b) (c &&& d) := by
  constructor
  · intro i hi h
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at h ⊢
    exact ⟨ac.1 i hi h.1,bd.1 i hi h.2⟩
  · intro i hi h
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at h ⊢
    exact ⟨ac.2 i hi h.1,bd.2 i hi h.2⟩

lemma disj {a b c d : ℕ} (ac : Better a c) (bd : Better b d) : Better (a ||| b) (c ||| d) := by
  constructor
  · intro i hi h
    rw [Nat.testBit_or,Bool.or_eq_true_iff] at h ⊢
    exact h.imp (ac.1 i hi) (bd.1 i hi)
  · intro i hi h
    rw [Nat.testBit_or,Bool.or_eq_true_iff] at h ⊢
    exact h.imp (ac.2 i hi) (bd.2 i hi)

lemma flag {a b c d : ℕ} (ac : Better a c) (bd : Better b d) (f : Bool) :
    Better (LocalPrune.optional a b f) (LocalPrune.optional c d f) := by
  cases f
  · exact ac
  · exact disj ac bd

lemma top (q : TopChoice) {a b c d : ℕ} (ac : Better a c) (bd : Better b d) :
    Better (topValue q a b) (topValue q c d) := by
  have choose (p : Prop) [Decidable p] {u v : ℕ} (h : Better u v) : Better (if p then u else 0) (if p then v else 0) := by
    by_cases yes : p <;> simp [yes,h,self]
  have side (p r : ℕ) : Better (r ||| (if q.useA=p then a else 0) ||| (if q.useB=p then b else 0))
    (r ||| (if q.useA=p then c else 0) ||| (if q.useB=p then d else 0)) :=
    disj (disj (self r) (choose _ ac)) (choose _ bd)
  exact conj (side 1 _) (side 2 _)

lemma safe {a b : ℕ} (h : Better a b) (hb : b≤7) : a≤7 := by
  by_contra no
  have high : 2^3 ≤ a := by change 8 ≤ a; omega
  obtain ⟨i,lo,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow high
  have large : 2^i ≤ b := Nat.ge_two_pow_of_testBit (h.2 i lo bit)
  have pow : (2 : ℕ)^3 ≤ 2^i := Nat.pow_le_pow_of_le (by decide) lo
  omega

end LocalBetter
namespace LocalLambda
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm

end LocalLambda
namespace LocalTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

end LocalTransfer
namespace LocalPure
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer

lemma value_of_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    val C (List.ofFn x) v.val = x v := by
  rw [val_input (n := n) (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma upward {n : ℕ} {C : Circuit} (x : Fin n → Bool) {a b : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) a b) (yes : val C (List.ofFn x) b = true) :
    val C (List.ofFn x) a = true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact yes
  | head step _ ih =>
    obtain ⟨k,hk,rfl,hop,port,hprior⟩ := step
    exact (val_or (n := n) (by simp) hk hop).mpr ⟨_,port,hprior,ih⟩

lemma raw_pin {n : ℕ} {C : Circuit} {v : Fin n} (x : Fin n → Bool) {w : ℕ}
    (hv : v ∈ orIn n C w) (hon : x v = true) : val C (List.ofFn x) w = true :=
  upward x (mem_orIn_reach v hv) ((value_of_input C x v).trans hon)

lemma raw_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ orIn n C (n+k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n+k ∧ u ∈ orIn n C w := by
  constructor
  · intro hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w,hs,rest⟩
    · have := u.isLt; omega
    · obtain ⟨j,hj,eq,op,port,lt⟩ := hs
      have : j = k := by omega
      subst j
      exact ⟨hj,op,w,port,lt,reach_mem_orIn u rest⟩
  · rintro ⟨hk,op,w,port,lt,hu⟩
    apply reach_mem_orIn u
    exact Relation.ReflTransGen.head ⟨k,hk,rfl,op,port,lt⟩ (mem_orIn_reach u hu)

end LocalPure
namespace LocalMixTrace
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer

end LocalMixTrace
namespace LocalBefore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer LocalPure

end LocalBefore
namespace LocalReceiver
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalMixTrace LocalBefore

lemma top_ports {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨valid,hand,_⟩ := Finset.mem_filter.mp ha
  have hk := Finset.mem_range.mp valid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  change val C (List.ofFn x) (n+a) = true ↔ _
  rw [val_and (n := n) (by simp) hk hand]
  constructor
  · intro pos b
    apply (pos _ _).2
    fin_cases b <;> simp [opnd,ports]
  · intro h i hi
    refine ⟨ao.2.1 a hk i hi,?_⟩
    have choices : i = p ∨ i = q := by simpa [ports] using hi
    rcases choices with rfl | rfl
    · simpa [opnd,ports] using h 0
    · simpa [opnd,ports] using h 1

end LocalReceiver
namespace LocalMixCore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver

lemma path_le {n : ℕ} {C : Circuit} {w v : ℕ} (path : Relation.ReflTransGen (OrStep n C) w v) : v ≤ w := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih =>
    obtain ⟨_,_,rfl,_,_,lt⟩ := step
    omega

lemma reach_le {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) : n+k ≤ w :=
  path_le (orReaches_reach k w h).1

end LocalMixCore
namespace LocalCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open LocalLambda

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

end LocalCone
namespace LocalEmptyOR
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalBefore

end LocalEmptyOR
namespace LocalBelow
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open LocalTransfer LocalPure

end LocalBelow
namespace LocalSingleMix
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver LocalMixCore

end LocalSingleMix
namespace LocalDark
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalCone LocalSingleMix

lemma and_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {a : ℕ} (valid : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) :
    a ∈ junk G C ∨ a ∈ tops G C := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_cases h : a ∈ junk G C
  · exact Or.inl h
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr valid,hand,?_⟩
    intro x yes
    cases f : graphFun G ∅ x
    · exact (h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr valid,hand,valid,x,yes,f⟩)).elim
    · rfl

end LocalDark
namespace LocalNormal
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalCone LocalDark

lemma eval_sources {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, val C (List.ofFn x) w = true ↔
      (∃ v ∈ orIn n C w, x v = true) ∨
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧ gateVal n C a x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid
    constructor
    · intro yes
      by_cases pin : w < n
      · let v : Fin n := ⟨w,pin⟩
        exact Or.inl ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩,(value_of_input C x v).symm.trans yes⟩
      · obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
        have hk : k < C.gates.length := by omega
        rcases ao.1 _ (gateAt_mem hk) with ha | ho
        · exact Or.inr ⟨k,hk,ha,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,yes⟩
        · obtain ⟨p,hp,back,on⟩ := (val_or (n := n) (by simp) hk ho).mp yes
          rcases (ih p back (by omega)).mp on with ⟨v,hv,xv⟩ | ⟨a,ha,hand,path,xa⟩
          · exact Or.inl ⟨v,(raw_gate C k v).mpr ⟨hk,ho,p,hp,back,hv⟩,xv⟩
          · exact Or.inr ⟨a,ha,hand,(orReaches_iff n C k a).mpr ⟨hk,Or.inr ⟨ho,p,hp,back,path⟩⟩,xa⟩
    · rintro (⟨v,hv,on⟩ | ⟨a,_,_,path,on⟩)
      · exact raw_pin x hv on
      · exact upward x (orReaches_reach a w path).1 on

lemma or_inside {n : ℕ} (C : Circuit) (a : ℕ) :
    ∀ k, OrReaches n C (n+k) a → a=k ∨ InCone n C a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro h
    obtain ⟨valid,eq | ⟨_,p,hp,back,rest⟩⟩ := (orReaches_iff n C k a).mp h
    · exact Or.inl eq
    · have ge := rest.1
      obtain ⟨j,rfl⟩ : ∃ j, p=n+j := ⟨p-n,by omega⟩
      have earlier : j<k := by omega
      exact Or.inr ((inCone_iff n C a k).mpr ⟨valid,j,earlier,hp,ih j earlier rest⟩)

lemma port_in_cone {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {j p a : ℕ}
    (hj : j < C.gates.length) (port : p ∈ (gateAt C j).inputs) (path : OrReaches n C p a) :
    InCone n C a j := by
  have ge := path.1
  have lim := ao.2.1 j hj p port
  obtain ⟨k,rfl⟩ : ∃ k, p=n+k := ⟨p-n,by omega⟩
  exact (inCone_iff n C a j).mpr ⟨hj,k,by omega,port,or_inside C a k path⟩

lemma port_sources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C)
    (lo hi : ℕ) (J : junk G C = {lo,hi}) {j p : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (port : p ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔ (∃ v ∈ orIn n C p, x v = true) ∨
      (OrReaches n C p lo ∧ gateVal n C lo x = true) ∨ (OrReaches n C p hi ∧ gateVal n C hi x = true) := by
  letI : DecidableEq GateOp := gateOpDecEq
  constructor
  · intro yes
    have earlier := ao.2.1 j hj p port
    rcases (eval_sources C ao x p (by omega)).mp yes with raw | ⟨a,ha,op,path,pos⟩
    · exact Or.inl raw
    · rcases and_cases G C ha op with dirty | top
      · have which : a=lo ∨ a=hi := by simpa [J] using dirty
        rcases which with rfl | rfl
        · exact Or.inr (Or.inl ⟨path,pos⟩)
        · exact Or.inr (Or.inr ⟨path,pos⟩)
      · exact (tf a ha j hj op (Finset.mem_filter.mp top).2.2 hand (port_in_cone ao hj port path)).elim
  · rintro (⟨v,hv,on⟩ | ⟨path,on⟩ | ⟨path,on⟩)
    · exact raw_pin x hv on
    · exact upward x (orReaches_reach lo p path).1 on
    · exact upward x (orReaches_reach hi p path).1 on

end LocalNormal
namespace LocalInjections
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal

lemma opnd_mem {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k : ℕ} (hk : k<C.gates.length) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  fin_cases b <;> simp [opnd,ports]

end LocalInjections
namespace LocalMixerTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver

end LocalMixerTransfer
namespace LocalCentreTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open LocalTransfer LocalPure LocalBefore LocalBelow LocalLambda LocalEmptyOR

end LocalCentreTransfer
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
namespace LocalCoverProfile

abbrev V := Fin 11
abbrev Edge := Sym2 V

def code : List ℕ := [9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97]
abbrev graph : SimpleGraph V := edgeGraph 11 (code.map fun n => (n / 11,n % 11))
def pairs : List (V × V) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def missing (K : Finset V) : Finset Edge :=
  ((pairs.filter fun p => decide (p.1 ∉ K ∧ p.2 ∉ K)).map fun p => s(p.1,p.2)).toFinset

abbrev fourProfiles (K : Finset V) (U : Finset Edge) : Prop :=
  (K = {5,7,8,10} ∧ U = {s(0,9),s(1,4),s(3,6)}) ∨
  (K = {7,8,9,10} ∧ U = {s(1,4),s(2,5),s(3,6)}) ∨
  (K = {6,8,9,10} ∧ U = {s(1,4),s(2,5),s(3,7)}) ∨
  (K = {3,8,9,10} ∧ U = {s(1,4),s(2,5),s(6,7)})

lemma listed_edges : ∀ p ∈ pairs, graph.Adj p.1 p.2 := by
  unfold graph
  decide +kernel

lemma missing_subset {U : Finset Edge} {K : Finset V}
    (h : (graph.deleteEdges (U : Set Edge)).IsVertexCover (K : Set V)) : missing K ⊆ U := by
  intro e he
  simp only [missing, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨p, ⟨hp, ha, hb⟩, rfl⟩ := he
  by_contra outside
  exact (h (SimpleGraph.deleteEdges_adj.mpr ⟨listed_edges p hp,outside⟩)).elim ha hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma four_check : ∀ K : Finset V, K.card ≤ 4 → (missing K).card ≤ 3 →
    K.card = 4 ∧ (missing K).card = 3 ∧ fourProfiles K (missing K) := by decide +kernel

lemma four_only {U : Finset Edge} {K : Finset V} (hU : U.card = 3)
    (hK : (graph.deleteEdges (U : Set Edge)).IsVertexCover (K : Set V)) (hk : K.card ≤ 4) :
    K.card = 4 ∧ fourProfiles K U := by
  have sub := missing_subset hK
  obtain ⟨four,three,profile⟩ := four_check K hk ((Finset.card_le_card sub).trans hU.le)
  have eq : missing K = U := Finset.eq_of_subset_of_card_le sub (by omega)
  exact ⟨four,eq ▸ profile⟩

end LocalCoverProfile
namespace LocalCoverProfile

def edgeAt (i : Fin 16) : Edge :=
  let p := pairs.getD i.val (0,0)
  s(p.1,p.2)

end LocalCoverProfile
namespace LocalMasks
open LocalMixerCertificate

def mask {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => decide (i ∈ A)))).toNat

lemma mask_bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) :
    (mask A).testBit v.val = decide (v ∈ A) := by
  unfold mask
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

lemma mask_above {n : ℕ} (A : Finset (Fin n)) {i : ℕ} (h : n ≤ i) :
    (mask A).testBit i = false := by
  simp [mask,BitVec.testBit_toNat,List.getD_eq_getElem?_getD,Nat.not_lt.mpr h]

lemma hit_iff {n : ℕ} (A : Finset (Fin n)) (x : ℕ) :
    hit (mask A) x = true ↔ ∃ v ∈ A, x.testBit v.val = true := by
  constructor
  · intro h
    have ne : mask A &&& x ≠ 0 := by simpa [hit] using h
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero ne
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at hi
    by_cases bound : i < n
    · let v : Fin n := ⟨i,bound⟩
      exact ⟨v,of_decide_eq_true ((mask_bit A v).symm.trans hi.1),hi.2⟩
    · have off := mask_above A (Nat.le_of_not_gt bound)
      exact (Bool.false_ne_true (off.symm.trans hi.1)).elim
  · rintro ⟨v,hv,hx⟩
    simp only [hit,bne_iff_ne]
    intro zero
    have h := congrArg (fun a : ℕ => a.testBit v.val) zero
    simp [Nat.testBit_and,mask_bit,hv,hx] at h

end LocalMasks
namespace LocalGraphRows
open LocalCoverProfile LocalMixerCertificate LocalMasks
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def rowAt (i : Fin 16) := rows.getD i.val 0
def endpointAt (i : Fin 16) := pairs.getD i.val (0,0)
def testsAt (i : Fin 16) := pairInput (endpointAt i).1 (endpointAt i).2

lemma row_matches : ∀ (i : Fin 16) (v : V), (rowAt i).testBit v.val = testsAt i v := by
  decide +kernel

end LocalGraphRows
namespace LocalCentreCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

def omitted (i j k : Fin 16) : Finset Edge := {edgeAt i,edgeAt j,edgeAt k}

end LocalCentreCase
namespace LocalMixerCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase
open LocalLambda LocalReceiver LocalMixerTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

end LocalMixerCase
namespace LocalMixerCertificate

end LocalMixerCertificate
namespace LocalMixerCertificate

end LocalMixerCertificate
namespace LocalSmallCover
open LocalCoverProfile LocalMixerCertificate LocalMasks LocalGraphRows LocalCentreCase
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

end LocalSmallCover
namespace LocalWireWords
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal LocalInjections LocalMasks LocalMixerCertificate
open LocalSignatures LocalPrune LocalCoverProfile LocalGraphRows LocalCentreCase LocalSmallCover

def packed (rs : List ℕ) (f : ℕ → Bool) := (BitVec.ofBoolListLE (rs.map f)).toNat
def rowInput {n : ℕ} (r : ℕ) : Fin n → Bool := fun v => r.testBit v.val
def wireWord (n : ℕ) (C : Circuit) (rs : List ℕ) (w : ℕ) :=
  packed rs (fun r => val C (List.ofFn (rowInput (n := n) r)) w)

lemma packed_bit (rs : List ℕ) (f : ℕ → Bool) (i : ℕ) :
    (packed rs f).testBit i = if h : i < rs.length then f rs[i] else false := by
  unfold packed
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
  by_cases h : i<rs.length <;> simp [List.getD_eq_getElem?_getD,h]

lemma pack_congr (rs : List ℕ) {f g : ℕ → Bool} (h : ∀ r ∈ rs, f r = g r) : packed rs f = packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [packed_bit,packed_bit]
  split
  · exact h _ (by simp)
  · rfl

lemma pack_and (rs : List ℕ) (f g : ℕ → Bool) :
    packed rs (fun x => f x && g x) = packed rs f &&& packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_or (rs : List ℕ) (f g : ℕ → Bool) :
    packed rs (fun x => f x || g x) = packed rs f ||| packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_off (rs : List ℕ) : packed rs (fun _ => false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_optional (rs : List ℕ) (f g : ℕ → Bool) (flag : Bool) :
    packed rs (fun x => f x || (flag && g x)) = LocalPrune.optional (packed rs f) (packed rs g) flag := by
  cases flag <;> simp [LocalPrune.optional,pack_or]

lemma product_word {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k p q : ℕ} (valid : k<C.gates.length)
    (hand : (gateAt C k).op=GateOp.and) (ports : (gateAt C k).inputs=[p,q]) (rs : List ℕ) :
    wireWord n C rs (n+k) = wireWord n C rs p &&& wireWord n C rs q := by
  unfold wireWord
  rw [← pack_and]
  apply pack_congr
  intro r _
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true_iff,val_and (n := n) (by simp) valid hand]
  constructor
  · intro h
    exact ⟨(h p (by simp [ports])).2,(h q (by simp [ports])).2⟩
  · rintro ⟨hp,hq⟩ t ht
    have which : t=p ∨ t=q := by simpa [ports] using ht
    refine ⟨ao.2.1 k valid t ht,?_⟩
    exact which.elim (fun eq => eq.symm ▸ hp) (fun eq => eq.symm ▸ hq)

lemma port_word {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C = {lo,hi})
    {j p : ℕ} (valid : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and)
    (port : p ∈ (gateAt C j).inputs) (rs : List ℕ) :
    wireWord n C rs p =
      LocalPrune.optional (LocalPrune.optional (signature rs (mask (orIn n C p))) (wireWord n C rs (n+lo)) (decide (OrReaches n C p lo)))
        (wireWord n C rs (n+hi)) (decide (OrReaches n C p hi)) := by
  unfold wireWord
  change packed rs _ = LocalPrune.optional (LocalPrune.optional (packed rs (hit (mask (orIn n C p)))) _ _) _ _
  rw [← pack_optional,← pack_optional]
  apply pack_congr
  intro r _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq,hit_iff]
  simpa only [gateVal,LocalTransfer.val,rowInput,or_assoc] using
    (port_sources G C ao tf lo hi J valid hand port (rowInput r))

lemma dirty_words {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (order : lo<hi)
    (J : junk G C = {lo,hi}) (rs raw : List ℕ)
    (support : ∀ p : ℕ, signature rs (mask (orIn n C p)) ∈ raw) :
    ∃ r ∈ raw, ∃ s ∈ raw, ∃ l ∈ raw, ∃ t ∈ raw, ∃ lf rf : Bool,
      wireWord n C rs (n+lo) = r &&& s ∧
      wireWord n C rs (n+hi) = LocalPrune.optional l (r &&& s) lf &&& LocalPrune.optional t (r &&& s) rf := by
  letI : DecidableEq GateOp := gateOpDecEq
  have jl : lo ∈ junk G C := by simp [J]
  have jh : hi ∈ junk G C := by simp [J]
  have low := Finset.mem_filter.mp jl
  have high := Finset.mem_filter.mp jh
  have lb := Finset.mem_range.mp low.1
  have hb := Finset.mem_range.mp high.1
  obtain ⟨p,q,lp⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem lb))
  obtain ⟨l,t,hp⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hb))
  let w := fun j => signature rs (mask (orIn n C j))
  let d := wireWord n C rs (n+lo)
  have lowPort (v : ℕ) (pv : v ∈ (gateAt C lo).inputs) : wireWord n C rs v = w v := by
    have back := ao.2.1 lo lb v pv
    have noL : ¬OrReaches n C v lo := fun h => Nat.not_le_of_lt back (reach_le h)
    have noH : ¬OrReaches n C v hi := by
      intro h
      have lim := reach_le h
      omega
    simpa [LocalPrune.optional,noL,noH,w] using port_word G C ao tf lo hi J lb low.2.1 pv rs
  have highPort (v : ℕ) (pv : v ∈ (gateAt C hi).inputs) :
      wireWord n C rs v = LocalPrune.optional (w v) d (decide (OrReaches n C v lo)) := by
    have back := ao.2.1 hi hb v pv
    have noH : ¬OrReaches n C v hi := fun h => Nat.not_le_of_lt back (reach_le h)
    simpa [noH,LocalPrune.optional,w,d] using port_word G C ao tf lo hi J hb high.2.1 pv rs
  have dword : d = w p &&& w q := by
    rw [show d = _ from product_word ao lb low.2.1 lp rs,lowPort p (by simp [lp]),lowPort q (by simp [lp])]
  refine ⟨w p,support p,w q,support q,w l,support l,w t,support t,decide (OrReaches n C l lo),decide (OrReaches n C t lo),dword,?_⟩
  rw [product_word ao hb high.2.1 hp rs,highPort l (by simp [hp]),highPort t (by simp [hp]),dword]

end LocalWireWords
namespace LocalActive
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal LocalInjections LocalMasks
open LocalMixerCertificate LocalSignatures LocalPrune LocalWireWords

end LocalActive
namespace LocalCenters
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalReceiver LocalCoverProfile

end LocalCenters
namespace LocalGeoBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalSmallCover
open LocalNormal LocalWireWords LocalSignatures LocalWordGeometry

end LocalGeoBridge
namespace LocalAnchorChoice
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase
open LocalGeoBridge LocalSignatures LocalWordGeometry
open PEqualNP.MetaComplexity.NestedCover

end LocalAnchorChoice
namespace LocalTopWord
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalLambda LocalTransfer LocalReceiver LocalNormal LocalActive LocalCenters
open LocalWireWords LocalCentreCase LocalMixerCertificate LocalMasks LocalSignatures LocalWordGeometry
open LocalAnchorChoice

end LocalTopWord
namespace LocalRowWitness
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalGraphRows LocalCoverProfile LocalWireWords LocalMixerCertificate LocalCentreCase

def edgeIndex (i j k : Fin 16) (r : Fin 3) : Fin 16 := if r=0 then i else if r=1 then j else k

end LocalRowWitness
namespace LocalDarkTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver LocalMixCore LocalSingleMix LocalDark

end LocalDarkTransfer
namespace LocalExtraObstruction
open LocalMixerCertificate

end LocalExtraObstruction
namespace LocalExtraCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix LocalSmallCover LocalExtraObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

end LocalExtraCase
namespace LocalRoutedGraph
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

end LocalRoutedGraph
namespace LocalAllSingle
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix LocalDarkTransfer LocalExtraCase LocalRoutedGraph
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

end LocalAllSingle
namespace LocalTwoMixers
open LocalCoverProfile LocalGraphRows LocalCentreCase LocalReceiver LocalMixCore LocalAllSingle
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

end LocalTwoMixers
namespace LocalModelBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalWireWords LocalActive LocalCenters LocalRowWitness LocalTopWord
open LocalCentreCase LocalWordGeometry LocalGeometrySound LocalInjections LocalMixerCertificate
open LocalMasks LocalPrune LocalNormal LocalGeoBridge LocalSignatures

end LocalModelBridge
namespace LocalSignalCert
open LocalBetter LocalClip LocalGeometrySound LocalWordGeometry LocalSignatures LocalPrune LocalMixerCertificate

def reps (rs xs : List ℕ) := xs.all fun x => rs.any (fun r => beats r x)

lemma rep {rs raw : List ℕ} (ok : reps rs raw=true) {w : ℕ} (mem : w ∈ raw) :
    ∃ x ∈ rs, Better x w := by
  obtain ⟨x,hx,le⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok w mem)
  exact ⟨x,hx,beats_sound le⟩

lemma possible {rs : List ℕ} {p a : ℕ} (hp : p ∈ rs) (f : Bool) :
    LocalPrune.optional p a f ∈ rs ++ rs.map (fun r => r ||| a) := by
  cases f
  · exact List.mem_append_left _ hp
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

end LocalSignalCert
namespace LocalMatchingCheck
open LocalBetter LocalSignalCert

def usable (w i : ℕ) := decide (w ≤ 7) && w.testBit i
def wins (pins : List ℕ) (a b i : ℕ) :=
  usable (a &&& b) i || pins.any fun p => usable (a &&& p) i || usable (b &&& p) i
def allThree (pins : List ℕ) (a b : ℕ) :=
  wins pins a b 0 && wins pins a b 1 && wins pins a b 2
def entryOK (pins rs : List ℕ) (e : ℕ × List ℕ) :=
  reps e.2 (rs ++ rs.map (fun r => r ||| e.1)) &&
    e.2.all (fun l => e.2.all fun r => !(allThree pins e.1 (l &&& r)))

lemma usable_better {a b i : ℕ} (h : Better a b) (low : i<3) (yes : usable b i=true) : usable a i=true := by
  obtain ⟨ok,on⟩ := Bool.and_eq_true_iff.mp yes
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (safe h (of_decide_eq_true ok)),h.1 i low on⟩

lemma wins_better (pins : List ℕ) {a b c d i : ℕ} (ac : Better a c) (bd : Better b d) (low : i<3)
    (h : wins pins c d i=true) : wins pins a b i=true := by
  apply Bool.or_eq_true_iff.mpr
  rcases Bool.or_eq_true_iff.mp h with both | anyPin
  · exact Or.inl (usable_better (conj ac bd) low both)
  · obtain ⟨p,hp,term⟩ := List.any_eq_true.mp anyPin
    exact Or.inr (List.any_eq_true.mpr ⟨p,hp,Bool.or_eq_true_iff.mpr
      ((Bool.or_eq_true_iff.mp term).imp (usable_better (conj ac (self p)) low)
        (usable_better (conj bd (self p)) low))⟩)

lemma all_of_wins (pins : List ℕ) {a b : ℕ} (yes : ∀ i : Fin 3, wins pins a b i.val=true) :
    allThree pins a b=true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨yes 0,yes 1⟩,yes 2⟩

lemma cert_forbids (pins raw rs : List ℕ) (entries : List (ℕ × List ℕ))
    (cover : reps rs raw=true)
    (firsts : rs.all (fun x => rs.all fun y => (entries.map Prod.fst).any fun a => beats a (x &&& y))=true)
    (checked : entries.all (entryOK pins rs)=true)
    {r s l t : ℕ} (hr : r ∈ raw) (hs : s ∈ raw) (hl : l ∈ raw) (ht : t ∈ raw) (lf rf : Bool) :
    let a := r &&& s
    let b := LocalPrune.optional l a lf &&& LocalPrune.optional t a rf
    ¬(∀ i : Fin 3, wins pins a b i.val=true) := by
  intro a b model
  obtain ⟨r',mr,cr⟩ := rep cover hr
  obtain ⟨s',ms,cs⟩ := rep cover hs
  obtain ⟨l',ml,cl⟩ := rep cover hl
  obtain ⟨t',mt,ct⟩ := rep cover ht
  obtain ⟨d,mem,lower⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp firsts r' mr) s' ms)
  obtain ⟨⟨d,ports⟩,hd,rfl⟩ := List.mem_map.mp mem
  have ca : Better d a := chain (beats_sound lower) (conj cr cs)
  obtain ⟨pmap,guard⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (d,ports) hd)
  obtain ⟨x,hx,bx⟩ := rep pmap (possible ml lf)
  obtain ⟨y,hy,byy⟩ := rep pmap (possible mt rf)
  have cb : Better (x &&& y) b := conj (chain bx (flag cl ca lf)) (chain byy (flag ct ca rf))
  have bad := List.all_eq_true.mp (List.all_eq_true.mp guard x hx) y hy
  have good := all_of_wins pins (fun i => wins_better pins ca cb i.isLt (model i))
  simp [good] at bad

end LocalMatchingCheck
namespace LocalMatchingData
open LocalMatchingCheck LocalSignalCert

def pins : List ℕ := [0,121,1921,410,1634,684,1364]
def raw : List ℕ := [0,121,410,507,684,765,958,1023,1364,1405,1502,1535,1634,1659,1774,1791,1910,1919,1921,1947,1965,1983,2005,2015,2019,2031,2039,2041,2042,2043,2044,2045,2046,2047]
def rs : List ℕ := [0,121,410,684,1364,1634,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039]
def entry0 : ℕ × List ℕ := (1,[1,411,685,1365,1635,959,1503,1775,1911])
def entry1 : ℕ × List ℕ := (2,[2,123,686,1366,1923,767,1407,1967,2007])
def entry2 : ℕ × List ℕ := (4,[4,125,414,1638,1925,511,1663,1951,2023])
def entry3 : ℕ × List ℕ := (123,[0,123,410,684,767,1364,1407,1634,1921,958,1502,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry4 : ℕ × List ℕ := (125,[0,125,410,511,684,1364,1634,1663,1921,958,1502,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry5 : ℕ × List ℕ := (411,[0,411,121,684,959,1364,1503,1634,1921,765,1405,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry6 : ℕ × List ℕ := (414,[0,414,121,511,684,1364,1634,1921,1951,765,1405,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry7 : ℕ × List ℕ := (483,[0,483,121,410,684,1007,1364,1527,1634,1921,765,958,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015])
def entry8 : ℕ × List ℕ := (685,[0,685,121,410,959,1364,1634,1775,1921,507,1405,1502,1535,1659,1910,1919,1947,2005,2015,2019,2039])
def entry9 : ℕ × List ℕ := (686,[0,686,121,410,767,1364,1634,1921,1967,507,1405,1502,1535,1659,1910,1919,1947,2005,2015,2019,2039])
def entry10 : ℕ × List ℕ := (725,[0,725,121,410,684,991,1364,1634,1783,1921,507,958,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2019,2031])
def entry11 : ℕ × List ℕ := (822,[0,822,121,410,684,895,1364,1634,1921,1975,507,765,1405,1502,1535,1659,1774,1791,1947,1965,2005,2015,2019,2031])
def entry12 : ℕ × List ℕ := (1230,[0,1230,121,410,684,1279,1364,1634,1921,1999,507,765,958,1023,1405,1659,1910,1919,1947,1965,1983,2005,2019,2039])
def entry13 : ℕ × List ℕ := (1325,[0,1325,121,410,684,1364,1471,1634,1903,1921,507,765,958,1023,1502,1659,1774,1791,1910,1947,2005,2015,2019,2039])
def entry14 : ℕ × List ℕ := (1365,[0,1365,121,410,684,1503,1634,1911,1921,507,765,958,1023,1659,1774,1791,1947,1965,1983,2019,2031])
def entry15 : ℕ × List ℕ := (1366,[0,1366,121,410,684,1407,1634,1921,2007,507,765,958,1023,1659,1774,1791,1947,1965,1983,2019,2031])
def entry16 : ℕ × List ℕ := (1563,[0,1563,121,410,684,1364,1634,1727,1887,1921,507,765,958,1023,1405,1502,1535,1774,1910,1965,2005,2019,2031,2039])
def entry17 : ℕ × List ℕ := (1635,[0,1635,121,410,684,1364,1775,1911,1921,507,765,958,1023,1405,1502,1535,1947,1965,1983,2005,2015])
def entry18 : ℕ × List ℕ := (1638,[0,1638,121,410,684,1364,1663,1921,2023,507,765,958,1023,1405,1502,1535,1947,1965,1983,2005,2015])
def entry19 : ℕ × List ℕ := (1923,[0,1923,121,410,684,1364,1634,1967,2007,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919])
def entry20 : ℕ × List ℕ := (1925,[0,1925,121,410,684,1364,1634,1951,2023,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919])
def entry21 : ℕ × List ℕ := (511,[0,121,410,511,684,1364,1634,1921,765,958,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry22 : ℕ × List ℕ := (767,[0,121,410,684,767,1364,1634,1921,507,958,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry23 : ℕ × List ℕ := (895,[0,121,410,684,895,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry24 : ℕ × List ℕ := (959,[0,121,410,684,959,1364,1634,1921,507,765,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry25 : ℕ × List ℕ := (991,[0,121,410,684,991,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry26 : ℕ × List ℕ := (1007,[0,121,410,684,1007,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry27 : ℕ × List ℕ := (1015,[0,121,410,684,1015,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry28 : ℕ × List ℕ := (1279,[0,121,410,684,1279,1364,1634,1921,507,765,958,1023,1405,1502,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry29 : ℕ × List ℕ := (1407,[0,121,410,684,1364,1407,1634,1921,507,765,958,1023,1502,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry30 : ℕ × List ℕ := (1471,[0,121,410,684,1364,1471,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry31 : ℕ × List ℕ := (1503,[0,121,410,684,1364,1503,1634,1921,507,765,958,1023,1405,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry32 : ℕ × List ℕ := (1519,[0,121,410,684,1364,1519,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry33 : ℕ × List ℕ := (1527,[0,121,410,684,1364,1527,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry34 : ℕ × List ℕ := (1663,[0,121,410,684,1364,1634,1663,1921,507,765,958,1023,1405,1502,1535,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry35 : ℕ × List ℕ := (1727,[0,121,410,684,1364,1634,1727,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry36 : ℕ × List ℕ := (1759,[0,121,410,684,1364,1634,1759,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry37 : ℕ × List ℕ := (1775,[0,121,410,684,1364,1634,1775,1921,507,765,958,1023,1405,1502,1535,1659,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry38 : ℕ × List ℕ := (1783,[0,121,410,684,1364,1634,1783,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry39 : ℕ × List ℕ := (1855,[0,121,410,684,1364,1634,1855,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,2005,2015,2019,2031,2039])
def entry40 : ℕ × List ℕ := (1887,[0,121,410,684,1364,1634,1887,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2019,2031,2039])
def entry41 : ℕ × List ℕ := (1903,[0,121,410,684,1364,1634,1903,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2039])
def entry42 : ℕ × List ℕ := (1911,[0,121,410,684,1364,1634,1911,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1947,1965,1983,2005,2015,2019,2031])
def entry43 : ℕ × List ℕ := (1951,[0,121,410,684,1364,1634,1921,1951,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry44 : ℕ × List ℕ := (1967,[0,121,410,684,1364,1634,1921,1967,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,2005,2015,2019,2039])
def entry45 : ℕ × List ℕ := (1975,[0,121,410,684,1364,1634,1921,1975,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031])
def entry46 : ℕ × List ℕ := (1999,[0,121,410,684,1364,1634,1921,1999,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2039])
def entry47 : ℕ × List ℕ := (2007,[0,121,410,684,1364,1634,1921,2007,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2019,2031])
def entry48 : ℕ × List ℕ := (2023,[0,121,410,684,1364,1634,1921,2023,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015])
def entries : List (ℕ × List ℕ) := [entry0,entry1,entry2,entry3,entry4,entry5,entry6,entry7,entry8,entry9,entry10,entry11,entry12,entry13,entry14,entry15,entry16,entry17,entry18,entry19,entry20,entry21,entry22,entry23,entry24,entry25,entry26,entry27,entry28,entry29,entry30,entry31,entry32,entry33,entry34,entry35,entry36,entry37,entry38,entry39,entry40,entry41,entry42,entry43,entry44,entry45,entry46,entry47,entry48]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma closed : raw.contains 0 && raw.all (fun w => pins.all fun p => raw.contains (w ||| p)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dominates : reps rs raw=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma firsts : rs.all (fun a => rs.all fun b => (entries.map Prod.fst).any fun w => LocalBetter.beats w (a &&& b)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested0 : entryOK pins rs entry0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested1 : entryOK pins rs entry1=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested2 : entryOK pins rs entry2=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested3 : entryOK pins rs entry3=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested4 : entryOK pins rs entry4=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested5 : entryOK pins rs entry5=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested6 : entryOK pins rs entry6=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested7 : entryOK pins rs entry7=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested8 : entryOK pins rs entry8=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested9 : entryOK pins rs entry9=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested10 : entryOK pins rs entry10=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested11 : entryOK pins rs entry11=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested12 : entryOK pins rs entry12=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested13 : entryOK pins rs entry13=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested14 : entryOK pins rs entry14=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested15 : entryOK pins rs entry15=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested16 : entryOK pins rs entry16=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested17 : entryOK pins rs entry17=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested18 : entryOK pins rs entry18=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested19 : entryOK pins rs entry19=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested20 : entryOK pins rs entry20=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested21 : entryOK pins rs entry21=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested22 : entryOK pins rs entry22=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested23 : entryOK pins rs entry23=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested24 : entryOK pins rs entry24=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested25 : entryOK pins rs entry25=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested26 : entryOK pins rs entry26=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested27 : entryOK pins rs entry27=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested28 : entryOK pins rs entry28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested29 : entryOK pins rs entry29=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested30 : entryOK pins rs entry30=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested31 : entryOK pins rs entry31=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested32 : entryOK pins rs entry32=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested33 : entryOK pins rs entry33=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested34 : entryOK pins rs entry34=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested35 : entryOK pins rs entry35=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested36 : entryOK pins rs entry36=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested37 : entryOK pins rs entry37=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested38 : entryOK pins rs entry38=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested39 : entryOK pins rs entry39=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested40 : entryOK pins rs entry40=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested41 : entryOK pins rs entry41=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested42 : entryOK pins rs entry42=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested43 : entryOK pins rs entry43=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested44 : entryOK pins rs entry44=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested45 : entryOK pins rs entry45=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested46 : entryOK pins rs entry46=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested47 : entryOK pins rs entry47=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested48 : entryOK pins rs entry48=true := by decide +kernel
lemma checked : entries.all (entryOK pins rs) = true := by
  simp only [entries,List.all_cons,List.all_nil,tested0,tested1,tested2,tested3,tested4,tested5,tested6,tested7,tested8,tested9,tested10,tested11,tested12,tested13,tested14,tested15,tested16,tested17,tested18,tested19,tested20,tested21,tested22,tested23,tested24,tested25,tested26,tested27,tested28,tested29,tested30,tested31,tested32,tested33,tested34,tested35,tested36,tested37,tested38,tested39,tested40,tested41,tested42,tested43,tested44,tested45,tested46,tested47,tested48,Bool.and_true]
def rows0 : List ℕ := [513,18,72,11,67,25,81,522,578,536,592]
def rows1 : List ℕ := [18,36,72,14,70,42,98,28,84,56,112]
def rows2 : List ℕ := [18,36,136,14,134,42,162,28,148,56,176]
def rows3 : List ℕ := [18,36,192,70,134,98,162,84,148,112,176]

end LocalMatchingData
namespace LocalPinWitness
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalReceiver LocalInjections LocalNormal

def gatePin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (x : Fin n → Bool) : Prop :=
  gateVal n C g x=true ∧ ∃ v : Fin n, x v=true ∧
    ∀ y, gateVal n C g y=true → y v=true → graphFun G ∅ y=true

def twoGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (lo hi : ℕ) (x : Fin n → Bool) : Prop :=
  gateVal n C lo x=true ∧ gateVal n C hi x=true ∧
    ∀ y, gateVal n C lo y=true → gateVal n C hi y=true → graphFun G ∅ y=true

lemma witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C={lo,hi})
    (x : Fin n → Bool) (a : ℕ) (top : a ∈ tops G C) (b : Fin 2) (g : ℕ) (dirty : g ∈ junk G C)
    (on : gateVal n C a x=true) (path : OrReaches n C (opnd C a b) g) (gOn : gateVal n C g x=true) :
    gatePin G C lo x ∨ gatePin G C hi x ∨ twoGates G C lo hi x := by
  letI : DecidableEq GateOp := gateOpDecEq
  have which : g=lo ∨ g=hi := by simpa [J] using dirty
  obtain ⟨hb,hand,below⟩ := Finset.mem_filter.mp top
  have bound := Finset.mem_range.mp hb
  let p := opnd C a (1-b)
  have pair (y : Fin n → Bool) (yg : gateVal n C g y=true) (yp : LocalTransfer.val C (List.ofFn y) p=true) :
      graphFun G ∅ y=true := by
    apply below y
    apply (top_ports ao top y).mpr
    intro d
    have left := upward y (orReaches_reach g _ path).1 yg
    fin_cases b <;> fin_cases d
    · exact left
    · exact yp
    · exact yp
    · exact left
  have pOn := (top_ports ao top x).mp on (1-b)
  have deal (h : ℕ) (hs : h=lo ∨ h=hi) (hp : OrReaches n C p h) (hh : gateVal n C h x=true) :
      twoGates G C lo hi x := by
    have both (y : Fin n → Bool) (yg : gateVal n C g y=true) (yh : gateVal n C h y=true) :=
      pair y yg (upward y (orReaches_reach h p hp).1 yh)
    have distinct : g≠h := by
      intro eq
      obtain ⟨_,_,_,y,yg,bad⟩ := Finset.mem_filter.mp dirty
      have good := both y yg (eq ▸ yg)
      simp [bad] at good
    rcases which with gl | gh <;> rcases hs with hl | he
    · exact (distinct (gl.trans hl.symm)).elim
    · subst g; subst h
      exact ⟨gOn,hh,both⟩
    · subst g; subst h
      exact ⟨hh,gOn,fun y yl yh => both y yh yl⟩
    · exact (distinct (gh.trans he.symm)).elim
  rcases (port_sources G C ao tf lo hi J bound hand (opnd_mem ao bound (1-b)) x).mp pOn with
    ⟨v,mem,high⟩ | ⟨reach,low⟩ | ⟨reach,high⟩
  · have term : gatePin G C g x := ⟨gOn,v,high,fun y yg yv => pair y yg (raw_pin y mem yv)⟩
    exact which.elim (fun e => Or.inl (e ▸ term)) (fun e => Or.inr (Or.inl (e ▸ term)))
  · exact Or.inr (Or.inr (deal lo (Or.inl rfl) reach low))
  · exact Or.inr (Or.inr (deal hi (Or.inr rfl) reach high))

end LocalPinWitness
namespace LocalMatchingCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalMasks LocalCoverProfile LocalGraphRows LocalCentreCase LocalRowWitness LocalWireWords
open LocalSignatures LocalMatchingCheck LocalPinWitness

def pinColumn (rows : List ℕ) (v : V) := packed rows (fun r => r.testBit v.val)

abbrev profile (i j k : Fin 16) (rows : List ℕ) : Prop :=
  (∀ v : V, pinColumn rows v ∈ LocalMatchingData.pins) ∧
  (∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val]) = false) ∧
  3 ≤ rows.length ∧ ∀ b : Fin 3, rows.getD b.val 0 = rowAt (edgeIndex i j k b)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma profiles : profile 0 2 6 LocalMatchingData.rows0 ∧ profile 2 4 6 LocalMatchingData.rows1 ∧
    profile 2 4 7 LocalMatchingData.rows2 ∧ profile 2 4 12 LocalMatchingData.rows3 := by decide +kernel

lemma raw_mem (rows : List ℕ) (pinMem : ∀ v : V, pinColumn rows v ∈ LocalMatchingData.pins)
    (A : Finset V) : signature rows (mask A) ∈ LocalMatchingData.raw := by
  obtain ⟨zero,closed⟩ := Bool.and_eq_true_iff.mp LocalMatchingData.closed
  induction A using Finset.induction_on with
  | empty =>
    have eq : signature rows (mask (∅ : Finset V)) = 0 := by
      change packed rows _ = 0
      rw [← pack_off rows]
      apply pack_congr
      intro r _
      cases h : LocalMixerCertificate.hit (mask (∅ : Finset V)) r
      · rfl
      · obtain ⟨v,hv,_⟩ := (hit_iff _ _).mp h
        simp at hv
    exact eq ▸ List.contains_iff_mem.mp zero
  | @insert v A fresh ih =>
    have eq : signature rows (mask (insert v A)) = signature rows (mask A) ||| pinColumn rows v := by
      change packed rows _ = packed rows (LocalMixerCertificate.hit (mask A)) ||| packed rows (fun r => r.testBit v.val)
      rw [← pack_or]
      apply pack_congr
      intro r _
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true_iff,hit_iff,hit_iff]
      constructor
      · rintro ⟨u,hu,on⟩
        rcases Finset.mem_insert.mp hu with rfl | mem
        · exact Or.inr on
        · exact Or.inl ⟨u,mem,on⟩
      · rintro (⟨u,mem,on⟩ | on)
        · exact ⟨u,Finset.mem_insert_of_mem mem,on⟩
        · exact ⟨v,Finset.mem_insert_self _ _,on⟩
    rw [eq]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp closed _ ih) _ (pinMem v))

lemma clean_term (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (f : (V → Bool) → Bool) (sound : ∀ x, f x=true → graphFun graph ∅ x=true)
    (i : Fin 3) (hi : i.val<rows.length) (pos : f (rowInput rows[i.val])=true) :
    usable (packed rows (fun r => f (rowInput r))) i.val = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    by_contra over
    have large : 2^3 ≤ packed rows (fun r => f (rowInput r)) := by omega
    obtain ⟨t,ht,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow large
    rw [packed_bit] at bit
    split at bit
    next inside =>
      have bad := negative ⟨t,inside⟩ ht
      have good := sound _ bit
      simp [bad] at good
    next => contradiction
  · simpa only [packed_bit,dif_pos hi] using pos

lemma pin_on (C : Circuit) (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (i : Fin 3) (hi : i.val<rows.length) (g : ℕ) (term : gatePin graph C g (rowInput rows[i.val])) :
    ∃ v : V, usable (wireWord 11 C rows (11+g) &&& pinColumn rows v) i.val=true := by
  obtain ⟨yg,v,yv,sound⟩ := term
  refine ⟨v,?_⟩
  let f := fun y : V → Bool => gateVal 11 C g y && y v
  have good := clean_term rows negative f (fun y h => (Bool.and_eq_true_iff.mp h).elim (sound y))
    i hi (Bool.and_eq_true_iff.mpr ⟨yg,yv⟩)
  simpa only [f,pack_and,pinColumn,wireWord,gateVal,LocalTransfer.val,rowInput] using good

lemma both_on (C : Circuit) (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (i : Fin 3) (hi : i.val<rows.length) (lo high : ℕ) (term : twoGates graph C lo high (rowInput rows[i.val])) :
    usable (wireWord 11 C rows (11+lo) &&& wireWord 11 C rows (11+high)) i.val=true := by
  obtain ⟨yl,yh,sound⟩ := term
  let f := fun y : V → Bool => gateVal 11 C lo y && gateVal 11 C high y
  have good := clean_term rows negative f (fun y h => (Bool.and_eq_true_iff.mp h).elim (sound y))
    i hi (Bool.and_eq_true_iff.mpr ⟨yl,yh⟩)
  simpa only [f,pack_and,wireWord,gateVal,LocalTransfer.val,rowInput] using good

lemma rejects (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo high : ℕ) (order : lo<high) (J : junk graph C={lo,high})
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, ∃ b : Fin 2, ∃ g ∈ junk graph C,
      gateVal 11 C a (pairInput u v)=true ∧ OrReaches 11 C (opnd C a b) g ∧ gateVal 11 C g (pairInput u v)=true)
    (i j k : Fin 16) (U : Ustar graph C=omitted i j k) (rows : List ℕ) (cert : profile i j k rows) : False := by
  obtain ⟨pinMem,negative,long,first⟩ := cert
  obtain ⟨r,hr,s,hs,l,hl,t,ht,lf,rf,lower,upper⟩ :=
    dirty_words graph C ao tf lo high order J rows LocalMatchingData.raw (fun w => raw_mem rows pinMem _)
  apply cert_forbids LocalMatchingData.pins LocalMatchingData.raw LocalMatchingData.rs LocalMatchingData.entries
    LocalMatchingData.dominates LocalMatchingData.firsts LocalMatchingData.checked hr hs hl ht lf rf
  intro m
  simp only [← lower] at upper
  rw [← lower,← upper]
  let h := edgeIndex i j k m
  have member : edgeAt h ∈ omitted i j k := by fin_cases m <;> simp [h,edgeIndex,omitted]
  have missing : s((endpointAt h).1,(endpointAt h).2) ∈ Ustar graph C := U ▸ member
  obtain ⟨a,top,b,g,dirty,on,path,gOn⟩ := trace _ _ missing
  have term := witness graph C ao tf lo high J (testsAt h) a top b g dirty on path gOn
  have hm : m.val<rows.length := Nat.lt_of_lt_of_le m.isLt long
  have mr : rows[m.val]=rowAt h := by simpa [List.getD_eq_getElem?_getD,hm,h] using first m
  have hx : rowInput rows[m.val] = testsAt h := mr ▸ funext (row_matches h)
  rw [← hx] at term
  apply Bool.or_eq_true_iff.mpr
  rcases term with low | up | both
  · obtain ⟨v,yes⟩ := pin_on C rows negative m hm lo low
    exact Or.inr (List.any_eq_true.mpr ⟨_,pinMem v,Bool.or_eq_true_iff.mpr (Or.inl yes)⟩)
  · obtain ⟨v,yes⟩ := pin_on C rows negative m hm high up
    exact Or.inr (List.any_eq_true.mpr ⟨_,pinMem v,Bool.or_eq_true_iff.mpr (Or.inr yes)⟩)
  · exact Or.inl (both_on C rows negative m hm lo high both)

lemma four (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo high : ℕ) (order : lo<high) (J : junk graph C={lo,high})
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, ∃ b : Fin 2, ∃ g ∈ junk graph C,
      gateVal 11 C a (pairInput u v)=true ∧ OrReaches 11 C (opnd C a b) g ∧ gateVal 11 C g (pairInput u v)=true)
    (three : (Ustar graph C).card=3) (K : Finset V) (small : K.card≤4)
    (cover : (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (K : Set V)) : False := by
  obtain ⟨_,cases⟩ := four_only three cover small
  rcases cases with ⟨_,U⟩ | ⟨_,U⟩ | ⟨_,U⟩ | ⟨_,U⟩
  · exact rejects C ao tf lo high order J trace 0 2 6 U _ profiles.1
  · exact rejects C ao tf lo high order J trace 2 4 6 U _ profiles.2.1
  · exact rejects C ao tf lo high order J trace 2 4 7 U _ profiles.2.2.1
  · exact rejects C ao tf lo high order J trace 2 4 12 U _ profiles.2.2.2

end LocalMatchingCircuit
end MixerProof
namespace Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

end S90

namespace S98

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega

lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp

lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega

lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp

lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)

lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem

lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp

theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩

lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩

lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab

lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩

lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩

lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩

lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl

theorem main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]

end S98

theorem cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

theorem cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

theorem cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

theorem top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

theorem star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

theorem assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩

lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩

end Budget

theorem Budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact Budget.main n G C h4 hne hL hTF

end PEqualNP.Outside.L_meta_18390_aux
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.Outside.L_meta_18390_aux
abbrev listedGraph := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev graphDec : DecidableRel listedGraph.Adj := inferInstance

theorem residualCover (C : Circuit) :
    ∃ K : Finset (Fin 11), IsMinCover (listedGraph.deleteEdges ↑(Ustar listedGraph C)) K := by
  classical
  let H := listedGraph.deleteEdges ↑(Ustar listedGraph C)
  let P (n : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover ↑K ∧ K.card = n
  have ex : ∃ n, P n := ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K,hK,hcard⟩ := Nat.find_spec ex
  exact ⟨K,hK,fun T hT => hcard.trans_le (Nat.find_min' ex ⟨T,hT,rfl⟩)⟩

end PEqualNP.Outside.L_meta_18390_aux

namespace PEqualNP.Outside.L_meta_18390_aux.Two

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma residualConnection (hL : IsLeastAO G C) (hT : TopForm G C)
    (he : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
  obtain ⟨e, he⟩ := he
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, hr, _⟩ := residualTrace hL hT he
    rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨m, hl, ho, hi, hb, _⟩
    · have hz : side (n := n) C a b = ∅ := by
        change orIn n C (opnd C a b) = ∅
        rw [heq]
        exact andRawEmpty (junkData hj).2.1
      left
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
      fin_cases b
      · exact .inl hz
      · exact .inr hz
    · exact .inr ⟨m, lastOrOutside hL.1 hj hl ho hi hb⟩

open PEqualNP.MetaComplexity

abbrev G11 : SimpleGraph (Fin 11) :=
  edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def g11Edges : List (Nat × Nat) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def adjMask : Nat → Nat
  | 0 => 1536
  | 1 => 272
  | 2 => 1056
  | 3 => 192
  | 4 => 1282
  | 5 => 772
  | 6 => 1160
  | 7 => 584
  | 8 => 562
  | 9 => 417
  | 10 => 85
  | _ => 0

def lamList : List Nat :=
  [1, 2, 4, 5, 8, 16, 17, 18, 20, 21, 32, 33, 34, 48, 50, 64, 65, 68, 69, 72, 80, 81, 84, 85,
   128, 129, 136, 160, 161, 192, 256, 257, 258, 260, 272, 288, 289, 384, 385, 416, 417,
   512, 514, 516, 520, 528, 530, 544, 546, 560, 562, 576, 584, 768, 772, 1024, 1026, 1032,
   1056, 1152, 1160, 1280, 1282, 1536]

def tau5Pairs : List ((Nat × Nat) × (Nat × Nat)) :=
  [((0,9),(1,4)), ((0,9),(3,6)), ((0,10),(3,7)), ((1,4),(2,5)),
   ((1,4),(3,6)), ((1,4),(3,7)), ((1,4),(6,7)), ((1,8),(3,6)),
   ((1,8),(3,7)), ((1,8),(6,7)), ((2,5),(3,6)), ((2,5),(3,7)),
   ((2,5),(6,7)), ((3,6),(4,8)), ((3,7),(4,8)), ((4,8),(6,7))]

def popcount11 (m : Nat) : Nat :=
  (List.range 11).foldl (fun acc i => if m.testBit i then acc + 1 else acc) 0

def missedEdges (k : Nat) : List (Nat × Nat) :=
  g11Edges.filter fun e => !(k.testBit e.1 || k.testBit e.2)

def checkTau5 : Bool :=
  (List.range 2048).all fun k =>
    if popcount11 k != 5 then true
    else
      match missedEdges k with
      | [e1, e2] => (e1, e2) ∈ tau5Pairs
      | _ :: _ :: _ :: _ => true
      | _ => false

theorem checkTau5_ok : checkTau5 = true := by decide +kernel

def checkLamList : Bool :=
  (List.range 2048).all fun m =>
    if m == 0 then true
    else
      let isSing := (List.range 11).any fun v => m == (1 <<< v)
      let isNbr := (List.range 11).any fun c => (m &&& adjMask c) == m
      if isSing || isNbr then m ∈ lamList else true

theorem checkLamList_ok : checkLamList = true := by decide +kernel

def hasIndepNotAdj (A B D : Nat) (w : Nat) : Bool :=
  (List.range 11).any fun a =>
    A.testBit a &&
    (List.range 11).any fun b =>
      B.testBit b && !(adjMask a).testBit b &&
      (List.range 11).any fun d =>
        D.testBit d && !((adjMask a ||| adjMask b).testBit d) &&
        !((adjMask a ||| adjMask b ||| adjMask d).testBit w)

def hasIndep (A B D : Nat) : Bool :=
  (List.range 11).any fun a =>
    A.testBit a &&
    (List.range 11).any fun b =>
      B.testBit b && !(adjMask a).testBit b &&
      (List.range 11).any fun d =>
        D.testBit d && !((adjMask a ||| adjMask b).testBit d)

def checkPair (e1 e2 : Nat × Nat) : Bool :=
  let m1 := (1 <<< e1.1) ||| (1 <<< e1.2)
  let m2 := (1 <<< e2.1) ||| (1 <<< e2.2)
  let cand := lamList.filter fun s => (s &&& m1) != 0 && (s &&& m2) != 0
  (List.range 11).all fun z =>
    if z == e1.1 || z == e1.2 || z == e2.1 || z == e2.2 then true
    else
      [e1.1, e1.2].all fun w1 =>
        if !(adjMask z).testBit w1 then true
        else
          [e2.1, e2.2].all fun w2 =>
            if !(adjMask z).testBit w2 then true
            else
              cand.all fun A =>
                cand.all fun B =>
                  cand.all fun D =>
                    !hasIndep A B D || hasIndepNotAdj A B D w1 || hasIndepNotAdj A B D w2

def checkAllTriples : Bool := tau5Pairs.all fun p => checkPair p.1 p.2

theorem checkAllTriples_ok : checkAllTriples = true := by decide +kernel

theorem G11_noFourCycle : NoFourCycle G11 := by decide +kernel

theorem G11_edgeCard : G11.edgeFinset.card = 16 := by decide +kernel

theorem G11_adj_iff_adjMask (u v : Fin 11) : G11.Adj u v ↔ (adjMask u.val).testBit v.val = true := by
  revert u v; decide +kernel

theorem g11Edges_nodup_sym2 :
    (g11Edges.map fun p => s(p.1, p.2)).Nodup := by decide +kernel

theorem g11Edges_bounds : ∀ p ∈ g11Edges, p.1 < 11 ∧ p.2 < 11 := by decide +kernel

theorem g11Edges_adj : ∀ p ∈ g11Edges, ∀ (h1 : p.1 < 11) (h2 : p.2 < 11),
    G11.Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ := by decide +kernel

def toMask (S : Finset (Fin 11)) : Nat :=
  (List.finRange 11).foldl (fun acc v => if v ∈ S then acc ||| (1 <<< v.val) else acc) 0

theorem toMask_lt (S : Finset (Fin 11)) : toMask S < 2048 := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat), acc < 2 ^ 11 →
      l.foldl (fun a v => if v ∈ S then a ||| (1 <<< v.val) else a) acc < 2 ^ 11 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons v vs ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      split_ifs
      · apply Nat.or_lt_two_pow h
        have hv := v.isLt
        have : 1 <<< v.val = 2 ^ v.val := by simp [Nat.shiftLeft_eq]
        rw [this]
        exact Nat.pow_lt_pow_right (by omega) hv
      · exact h
  exact haux _ 0 (by omega)

theorem toMask_testBit (S : Finset (Fin 11)) (u : Fin 11) :
    (toMask S).testBit u.val = decide (u ∈ S) := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat),
      (l.foldl (fun a v => if v ∈ S then a ||| (1 <<< v.val) else a) acc).testBit u.val =
        (acc.testBit u.val || (u ∈ l && decide (u ∈ S))) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons v vs ih =>
      intro acc
      simp only [List.foldl_cons, ih]
      by_cases hvu : u = v
      · subst hvu
        by_cases huS : u ∈ S <;> simp [huS, Nat.testBit_or, Nat.testBit_shiftLeft]
      · have hne : v.val ≠ u.val := fun h => hvu (Fin.ext h.symm)
        by_cases hvS : v ∈ S
        · have hbit : (1 <<< v.val).testBit u.val = false := by
            rw [Nat.testBit_shiftLeft]
            by_cases hle : v.val ≤ u.val
            · have hpos : u.val - v.val ≠ 0 := by omega
              rcases Nat.exists_eq_succ_of_ne_zero hpos with ⟨k, hk⟩
              rw [hk]
              simp [hle, Nat.testBit_succ]
            · simp [hle]
          simp [hvS, hvu, Nat.testBit_or, hbit]
        · simp [hvS, hvu]
  have := haux (List.finRange 11) 0
  simp at this
  exact this

theorem popcount11_toMask (S : Finset (Fin 11)) : popcount11 (toMask S) = S.card := by
  have haux : ∀ (l : List (Fin 11)) (acc : Nat), l.Nodup →
      (l.map Fin.val).foldl (fun a i => if (toMask S).testBit i then a + 1 else a) acc =
        acc + (l.filter (fun v => decide (v ∈ S))).length := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons v vs ih =>
      intro acc hnd
      simp only [List.map_cons, List.foldl_cons, List.filter_cons]
      rw [toMask_testBit, ih _ (List.nodup_cons.mp hnd).2]
      cases decide (v ∈ S) <;> simp <;> omega
  have hrange : List.range 11 = (List.finRange 11).map Fin.val := by decide +kernel
  unfold popcount11
  rw [hrange, haux (List.finRange 11) 0 (List.nodup_finRange 11), Nat.zero_add]
  have hEq : S = ((List.finRange 11).filter (fun v => decide (v ∈ S))).toFinset := by
    ext v; simp
  have hcard : S.card = ((List.finRange 11).filter (fun v => decide (v ∈ S))).length := by
    conv_lhs => rw [hEq]
    exact List.toFinset_card_of_nodup ((List.nodup_finRange 11).filter _)
  omega

theorem toMask_eq_zero_iff (S : Finset (Fin 11)) : toMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have := toMask_testBit S u
    rw [h] at this
    simp [hu] at this
  · intro h
    subst h
    decide +kernel

theorem toMask_singleton (v : Fin 11) : toMask {v} = 1 <<< v.val := by
  revert v; decide +kernel

theorem toMask_and_adjMask (S : Finset (Fin 11)) (c : Fin 11)
    (hsub : ∀ v ∈ S, G11.Adj c v) : (toMask S &&& adjMask c.val) = toMask S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 11
  · let u : Fin 11 := ⟨i, hi⟩
    change ((toMask S).testBit u.val && (adjMask c.val).testBit u.val) = (toMask S).testBit u.val
    rw [toMask_testBit]
    by_cases hu : u ∈ S
    · simp [hu, (G11_adj_iff_adjMask c u).mp (hsub u hu)]
    · simp [hu]
  · have hlt := toMask_lt S
    have hpow : 2048 ≤ 2 ^ i := by
      have : 2 ^ 11 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h0 : (toMask S).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hpow)
    simp [h0]

theorem toMask_mem_lamList (S : Finset (Fin 11)) (hn : S.Nonempty)
    (hl : (∃ v : Fin 11, S = {v}) ∨ ∃ c : Fin 11, ∀ v ∈ S, G11.Adj c v) :
    toMask S ∈ lamList := by
  have hall := List.all_eq_true.mp checkLamList_ok (toMask S) (List.mem_range.mpr (toMask_lt S))
  have hnz : toMask S ≠ 0 := fun h => Finset.not_nonempty_empty ((toMask_eq_zero_iff S).mp h ▸ hn)
  have hnzb : (toMask S == 0) = false := beq_false_of_ne hnz
  simp only [hnzb, Bool.false_eq_true, ↓reduceIte] at hall
  have horT : (((List.range 11).any fun v => toMask S == 1 <<< v) ||
      ((List.range 11).any fun c => (toMask S &&& adjMask c) == toMask S)) = true := by
    rcases hl with ⟨v, rfl⟩ | ⟨c, hc⟩
    · apply Bool.or_eq_true_iff.mpr; left
      exact List.any_eq_true.mpr ⟨v.val, List.mem_range.mpr v.isLt, beq_iff_eq.mpr (toMask_singleton v)⟩
    · apply Bool.or_eq_true_iff.mpr; right
      exact List.any_eq_true.mpr ⟨c.val, List.mem_range.mpr c.isLt, beq_iff_eq.mpr (toMask_and_adjMask S c hc)⟩
  simp only [horT, ↓reduceIte, decide_eq_true_eq] at hall
  exact hall

theorem toMask_and_edge_ne_zero (S : Finset (Fin 11)) (u v : Fin 11)
    (h : u ∈ S ∨ v ∈ S) : (toMask S &&& ((1 <<< u.val) ||| (1 <<< v.val))) ≠ 0 := by
  intro h0
  rcases h with hu | hv
  · have hb := congrArg (fun x => x.testBit u.val) h0
    simp [Nat.testBit_and, Nat.testBit_or, toMask_testBit, hu, Nat.testBit_shiftLeft] at hb
  · have hb := congrArg (fun x => x.testBit v.val) h0
    simp [Nat.testBit_and, Nat.testBit_or, toMask_testBit, hv, Nat.testBit_shiftLeft] at hb

theorem G11_fullCover (K : Finset (Fin 11)) (hK : G11.IsVertexCover (K : Set _)) :
    7 ≤ K.card := by
  let w (v : Fin 11) : ℕ := if v ∈ K then 1 else 0
  have ew (u v : Fin 11) (he : G11.Adj u v) : 1 ≤ w u + w v := by
    rcases hK he with hu | hv
    · change u ∈ K at hu
      simp [w, hu]
    · change v ∈ K at hv
      simp [w, hv]
  have h0 := ew 1 4 (by decide +kernel)
  have h1 := ew 4 8 (by decide +kernel)
  have h2 := ew 8 1 (by decide +kernel)
  have h3 := ew 3 6 (by decide +kernel)
  have h4 := ew 6 7 (by decide +kernel)
  have h5 := ew 7 3 (by decide +kernel)
  have h6 := ew 0 9 (by decide +kernel)
  have h7 := ew 9 5 (by decide +kernel)
  have h8 := ew 5 2 (by decide +kernel)
  have h9 := ew 2 10 (by decide +kernel)
  have h10 := ew 10 0 (by decide +kernel)
  have hw : ∑ v, w v = K.card := by simp [w]
  simp [Fin.sum_univ_succ] at hw
  omega

theorem coneStrict (C : Circuit) : ∀ k h, InCone 11 C h k → h < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h hh
    obtain ⟨_, p, hp, _, hpath⟩ := (inCone_iff 11 C h k).mp hh
    rcases hpath with rfl | hpath
    · exact hp
    · exact (ih p hp h hpath).trans hp

theorem topStars {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hC4 : NoFourCycle G) (hAO : IsAO2 11 C) :
    ∀ a ∈ tops G C,
      let S : Fin 2 → Finset (Fin 11) := side C a
      (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1) := by
  intro a ha
  refine ⟨fun u hu v hv => topAdj hAO ha hu hv, ?_⟩
  by_contra hboth
  push Not at hboth
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hboth.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp hboth.2
  have hsub : ({v1, v2} : Finset (Fin 11)) ⊆ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨topAdj hAO ha hu1 hv1, topAdj hAO ha hu2 hv1⟩
    · exact ⟨topAdj hAO ha hu1 hv2, topAdj hAO ha hu2 hv2⟩
  have hcard2 : ({v1, v2} : Finset (Fin 11)).card = 2 := Finset.card_pair hvne
  have hle := (Finset.card_le_card hsub).trans (hC4 u1 u2 hune)
  omega

theorem residualTraceWithTop {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin 11}
    (he : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal 11 C a (pairInput u v) = true ∧
      OrReaches 11 C (opnd C a b) h ∧
      gateVal 11 C h (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩

theorem inCone_not_orReaches_has_and {C : Circuit} (hAO : IsAO2 11 C) (a : ℕ) :
    ∀ k, k < C.gates.length → InCone 11 C a k → ¬ OrReaches 11 C (11 + k) a →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ InCone 11 C a j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hcone hnor
    rcases hAO.1 _ (gateAt_mem hk) with hand | hor
    · exact ⟨k, hk, hand, hcone⟩
    · obtain ⟨_, p, hp, hpin, hpath⟩ := (inCone_iff 11 C a k).mp hcone
      rcases hpath with rfl | hcp
      · exfalso
        apply hnor
        exact (orReaches_iff 11 C k a).mpr ⟨hk, Or.inr ⟨hor, 11 + a, hpin, by omega,
          (orReaches_iff 11 C a a).mpr ⟨by omega, Or.inl rfl⟩⟩⟩
      · have hnorp : ¬ OrReaches 11 C (11 + p) a := by
          intro hrp
          exact hnor ((orReaches_iff 11 C k a).mpr ⟨hk, Or.inr ⟨hor, 11 + p, hpin, by omega, hrp⟩⟩)
        exact ih p hp (by omega) hcp hnorp

theorem top_orReaches_output {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {a : ℕ} (ha : a ∈ tops G C) :
    OrReaches 11 C C.output a := by
  by_contra hnor
  obtain ⟨ha_lt, ha_op, ha_below⟩ := topData ha
  let remap (w : ℕ) : ℕ := if w = 11 + a then 0 else if 11 + a < w then w - 1 else w
  let C' : Circuit :=
    ⟨(C.gates.eraseIdx a).map (fun g => ⟨g.op, g.inputs.map remap⟩), remap C.output⟩
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', List.length_eraseIdx, ha_lt]
  have hAO' : IsAO2 11 C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hL.1.1 g0 (List.mem_of_mem_eraseIdx hg0)
    · intro k hk w hw
      have hk_e : k < (C.gates.eraseIdx a).length := by simpa [C'] using hk
      have hge : C'.gates[k] = ⟨((C.gates.eraseIdx a)[k]).op, ((C.gates.eraseIdx a)[k]).inputs.map remap⟩ := by
        simp [C']
      rw [gateAt_eq hk, hge] at hw
      simp only [List.mem_map] at hw
      obtain ⟨w0, hw0, rfl⟩ := hw
      by_cases hka : k < a
      · rw [List.getElem_eraseIdx_of_lt hk_e hka] at hw0
        have hw0_lt : w0 < 11 + k := hL.1.2.1 k (by omega) w0 (by rw [gateAt_eq (by omega)]; exact hw0)
        simp only [remap]
        split_ifs <;> omega
      · rw [List.getElem_eraseIdx_of_ge hk_e (by omega)] at hw0
        have hk1 : k + 1 < C.gates.length := by
          rw [List.length_eraseIdx_of_lt ha_lt] at hk_e; omega
        have hw0_lt : w0 < 11 + (k + 1) :=
          hL.1.2.1 (k + 1) hk1 w0 (by rw [gateAt_eq hk1]; exact hw0)
        simp only [remap]
        split_ifs <;> omega
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp [hL.1.2.2 g0 (List.mem_of_mem_eraseIdx hg0)]
  have hgood_eval : ∀ (x : Fin 11 → Bool) (w : ℕ),
      w ≠ 11 + a → (∀ k, w = 11 + k → k < C.gates.length → ¬ InCone 11 C a k) →
      val C' (List.ofFn x) (remap w) = val C (List.ofFn x) w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hne hnc
      by_cases hw11 : w < 11
      · have hrm : remap w = w := by simp only [remap]; split_ifs <;> omega
        rw [hrm, val_input (n := 11) (by simp) hw11, val_input (n := 11) (by simp) hw11]
      · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
        by_cases hk : k < C.gates.length
        · have hka_ne : k ≠ a := by omega
          have hnc_k : ¬ InCone 11 C a k := hnc k rfl hk
          have hsub : ∀ u ∈ (gateAt C k).inputs,
              u < 11 + k ∧ u ≠ 11 + a ∧ (∀ k', u = 11 + k' → k' < C.gates.length → ¬ InCone 11 C a k') := by
            intro u hu
            have hult : u < 11 + k := hL.1.2.1 k hk u hu
            refine ⟨hult, ?_, ?_⟩
            · intro hua
              apply hnc_k
              exact (inCone_iff 11 C a k).mpr ⟨hk, a, by omega, hua ▸ hu, Or.inl rfl⟩
            · intro k' huk' hk' hc'
              apply hnc_k
              exact (inCone_iff 11 C a k).mpr ⟨hk, k', by omega, huk' ▸ hu, Or.inr hc'⟩
          by_cases hkl : k < a
          · have hrm : remap (11 + k) = 11 + k := by simp only [remap]; split_ifs <;> omega
            have hk' : k < C'.gates.length := by omega
            have hgate' : gateAt C' k = ⟨(gateAt C k).op, (gateAt C k).inputs.map remap⟩ := by
              rw [gateAt_eq hk', gateAt_eq hk]
              simp [C', List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx_of_lt ha_lt]; omega) hkl]
            rw [hrm, val_gate (n := 11) (by simp) hk', val_gate (n := 11) (by simp) hk, hgate']
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro u hu
            obtain ⟨hult, hune, hunc⟩ := hsub u hu
            have hrm_lt : remap u < 11 + k := by simp only [remap]; split_ifs <;> omega
            simp only [Function.comp_apply, ite_eq_left hrm_lt, ite_eq_left hult]
            exact ih u hult hune hunc
          · have hrm : remap (11 + k) = 11 + (k - 1) := by simp only [remap]; split_ifs <;> omega
            have hk' : k - 1 < C'.gates.length := by omega
            have hgate' : gateAt C' (k - 1) = ⟨(gateAt C k).op, (gateAt C k).inputs.map remap⟩ := by
              rw [gateAt_eq hk', gateAt_eq hk]
              have heq : (k - 1) + 1 = k := by omega
              simp only [C', List.getElem_map]
              rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx_of_lt ha_lt]; omega) (by omega)]
              simp [heq]
            rw [hrm, val_gate (n := 11) (by simp) hk', val_gate (n := 11) (by simp) hk, hgate']
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro u hu
            obtain ⟨hult, hune, hunc⟩ := hsub u hu
            have hrm_lt : remap u < 11 + (k - 1) := by simp only [remap]; split_ifs <;> omega
            simp only [Function.comp_apply, ite_eq_left hrm_lt, ite_eq_left hult]
            exact ih u hult hune hunc
        · have hge1 : 11 + C.gates.length ≤ 11 + k := by omega
          have hge2 : 11 + C'.gates.length ≤ remap (11 + k) := by
            simp only [remap]; split_ifs <;> omega
          rw [val_ge (n := 11) (by simp) hge2, val_ge (n := 11) (by simp) hge1]
  have hgood_out : C.output ≠ 11 + a ∧
      ∀ k, C.output = 11 + k → k < C.gates.length → ¬ InCone 11 C a k := by
    refine ⟨?_, ?_⟩
    · intro heq
      exact hnor (heq ▸ (orReaches_iff 11 C a a).mpr ⟨ha_lt, Or.inl rfl⟩)
    · intro k hk_eq hk_lt hcone
      obtain ⟨j, hj_lt, hj_op, hj_cone⟩ :=
        inCone_not_orReaches_has_and hL.1 a k hk_lt hcone (hk_eq ▸ hnor)
      exact hT a ha_lt j hj_lt ha_op ha_below hj_op hj_cone
  have hfun : circuitFun 11 C' = graphFun G ∅ := by
    rw [← hL.2.1]
    funext x
    exact hgood_eval x C.output hgood_out.1 hgood_out.2
  have hle := hL.2.2 C' hAO' hfun
  have hsize' : C'.size = C.size - 1 := hlen'
  have hpos : 0 < C.size := by change 0 < C.gates.length; omega
  omega

theorem tops_le_orT_add_one {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) (hEdge : ∃ u v : Fin 11, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  classical
  have hout_ge : 11 ≤ C.output := by
    by_contra hlt
    push Not at hlt
    let v : Fin 11 := ⟨C.output, hlt⟩
    have hv := congrFun hL.2.1 (pairInput v v)
    have hval : circuitFun 11 C (pairInput v v) = true := by
      change val C (List.ofFn (pairInput v v)) v.val = true
      rw [val_ofFn, pairInput_left]
    rw [hval] at hv
    have hadj := (graphFun_pair G v v).mp hv.symm
    exact G.loopless.irrefl v hadj
  have hout_lt : C.output < 11 + C.gates.length := by
    by_contra hge
    push Not at hge
    obtain ⟨u, v, huv⟩ := hEdge
    have hv := congrFun hL.2.1 (pairInput u v)
    have hval : circuitFun 11 C (pairInput u v) = false :=
      val_ge (n := 11) (by simp) hge
    rw [hval] at hv
    have htrue := (graphFun_pair G u v).mpr huv
    rw [htrue] at hv
    cases hv
  have hstep : ∀ (N : ℕ) (S : Finset ℕ),
      (∀ w ∈ S, w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11)) →
      ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a).card ≤
        S.card + ((orT G C).filter fun k => ∃ w ∈ S, OrReaches 11 C w k).card := by
    intro N
    induction N with
    | zero =>
      intro S hS
      have : S = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by have := (hS w hw).1; omega
      subst this; simp
    | succ N ih =>
      intro S hS
      by_cases hN : N ∈ S
      · obtain ⟨_, hN11, hNlt, hNbel⟩ := hS N hN
        let k := N - 11
        have hkN : N = 11 + k := by omega
        have hklt : k < C.gates.length := by omega
        let S0 := S.erase N
        rcases hL.1.1 _ (gateAt_mem hklt) with hand | hor
        · have hS0 : ∀ w ∈ S0, w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11) := by
            intro w hw
            have hmem := Finset.mem_of_mem_erase hw
            have hne := Finset.ne_of_mem_erase hw
            have := hS w hmem
            exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
          have hsubT : ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a) ⊆
              insert k ((tops G C).filter fun a => ∃ w ∈ S0, OrReaches 11 C w a) := by
            intro a ha
            obtain ⟨haT, w, hwS, hr⟩ := Finset.mem_filter.mp ha
            by_cases hwN : w = N
            · subst hwN
              rw [hkN] at hr
              rcases (orReaches_iff 11 C k a).mp hr with ⟨_, rfl | ⟨hor', _⟩⟩
              · exact Finset.mem_insert_self _ _
              · rw [hand] at hor'; cases hor'
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
                ⟨haT, w, Finset.mem_erase.mpr ⟨hwN, hwS⟩, hr⟩)
          have hsubO : ((orT G C).filter fun g => ∃ w ∈ S0, OrReaches 11 C w g) ⊆
              ((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
            intro g hg
            obtain ⟨hgO, w, hw, hr⟩ := Finset.mem_filter.mp hg
            exact Finset.mem_filter.mpr ⟨hgO, w, Finset.mem_of_mem_erase hw, hr⟩
          have hih := ih S0 hS0
          have hc1 := Finset.card_le_card hsubT
          have hc2 := Finset.card_insert_le k ((tops G C).filter fun a => ∃ w ∈ S0, OrReaches 11 C w a)
          have hc3 := Finset.card_le_card hsubO
          have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
          omega
        · have hopnd_below (b : Fin 2) :
              11 ≤ opnd C k b ∧ opnd C k b < 11 + k ∧ BelowF G C (opnd C k b - 11) := by
            have hltb := opndBound hL.1 hklt b
            have hmemb := opndMem hL.1 hklt b
            have h11 : 11 ≤ opnd C k b := by
              by_contra hlt11
              push Not at hlt11
              let v : Fin 11 := ⟨opnd C k b, hlt11⟩
              have hv : gateVal 11 C k (pairInput v v) = true := by
                rw [gateVal_eq_val, val_or (n := 11) (by simp) hklt hor]
                refine ⟨v.val, hmemb, hltb, ?_⟩
                rw [val_ofFn, pairInput_left]
              exact G.loopless.irrefl v ((graphFun_pair G v v).mp (hNbel _ hv))
            refine ⟨h11, hltb, ?_⟩
            intro x hx
            apply hNbel x
            rw [gateVal_eq_val, val_or (n := 11) (by simp) hklt hor]
            refine ⟨opnd C k b, hmemb, hltb, ?_⟩
            have heq : 11 + (opnd C k b - 11) = opnd C k b := by omega
            simpa only [gateVal_eq_val, heq] using hx
          let p := opnd C k 0
          let q := opnd C k 1
          let S' := insert p (insert q S0)
          have hS' : ∀ w ∈ S', w < N ∧ 11 ≤ w ∧ w < 11 + C.gates.length ∧ BelowF G C (w - 11) := by
            intro w hw
            simp only [S', Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · have := hopnd_below 0; exact ⟨by omega, this.1, by omega, this.2.2⟩
            · have := hopnd_below 1; exact ⟨by omega, this.1, by omega, this.2.2⟩
            · have hmem := Finset.mem_of_mem_erase hw
              have hne := Finset.ne_of_mem_erase hw
              have := hS w hmem
              exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
          have hsubT : ((tops G C).filter fun a => ∃ w ∈ S, OrReaches 11 C w a) ⊆
              ((tops G C).filter fun a => ∃ w ∈ S', OrReaches 11 C w a) := by
            intro a ha
            obtain ⟨haT, w, hwS, hr⟩ := Finset.mem_filter.mp ha
            by_cases hwN : w = N
            · subst hwN
              rw [hkN] at hr
              rcases (orReaches_iff 11 C k a).mp hr with ⟨_, rfl | ⟨_, u, hu, _, hru⟩⟩
              · have := (topData haT).2.1; rw [hor] at this; cases this
              · obtain ⟨b, rfl⟩ := inputsAsOpnd hL.1 hklt hu
                refine Finset.mem_filter.mpr ⟨haT, opnd C k b, ?_, hru⟩
                fin_cases b
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · exact Finset.mem_filter.mpr ⟨haT, w,
                Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩)), hr⟩
          have hkInO : k ∈ ((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
            refine Finset.mem_filter.mpr ⟨?_, N, hN, ?_⟩
            · simpa only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] using
                And.intro hklt (And.intro hor hNbel)
            · rw [hkN]; exact (orReaches_iff 11 C k k).mpr ⟨hklt, Or.inl rfl⟩
          have hsubO : ((orT G C).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
              (((orT G C).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).erase k) := by
            intro g hg
            obtain ⟨hgO, w, hw', hrg⟩ := Finset.mem_filter.mp hg
            have hwlt : w < N := (hS' w hw').1
            have hle := orStep_le (orReaches_reach g w hrg).1
            have hgne : g ≠ k := by omega
            refine Finset.mem_erase.mpr ⟨hgne, Finset.mem_filter.mpr ⟨hgO, ?_⟩⟩
            simp only [S', Finset.mem_insert] at hw'
            rcases hw' with rfl | rfl | hw0
            · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                ⟨hklt, Or.inr ⟨hor, p, opndMem hL.1 hklt 0, opndBound hL.1 hklt 0, hrg⟩⟩⟩
            · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                ⟨hklt, Or.inr ⟨hor, q, opndMem hL.1 hklt 1, opndBound hL.1 hklt 1, hrg⟩⟩⟩
            · exact ⟨w, Finset.mem_of_mem_erase hw0, hrg⟩
          have hih := ih S' hS'
          have hc1 := Finset.card_le_card hsubT
          have hc2 := Finset.card_le_card hsubO
          have hcO := Finset.card_erase_add_one hkInO
          have hcS' : S'.card ≤ S0.card + 2 := by
            have h1 : S'.card ≤ (insert q S0).card + 1 := Finset.card_insert_le p (insert q S0)
            have h2 : (insert q S0).card ≤ S0.card + 1 := Finset.card_insert_le q S0
            omega
          have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
          omega
      · exact ih S (fun w hw => by
          have := hS w hw
          have hne : w ≠ N := fun h => hN (h ▸ hw)
          exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩)
  have houtBel : BelowF G C (C.output - 11) := by
    intro x hx
    have heq : 11 + (C.output - 11) = C.output := by omega
    have hv : circuitFun 11 C x = true := by
      change val C (List.ofFn x) C.output = true
      rw [← heq]; exact hx
    rw [← hL.2.1]; exact hv
  have hmain := hstep (11 + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hout_lt, hout_ge, hout_lt, houtBel⟩)
  have hTfull : ((tops G C).filter fun a => ∃ w ∈ ({C.output} : Finset ℕ), OrReaches 11 C w a) = tops G C := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
    exact ⟨fun h => h.1, fun ha => ⟨ha, top_orReaches_output hL hT ha⟩⟩
  have hOsub : ((orT G C).filter fun k => ∃ w ∈ ({C.output} : Finset ℕ), OrReaches 11 C w k) ⊆ orT G C :=
    Finset.filter_subset _ _
  have hOcard := Finset.card_le_card hOsub
  rw [hTfull, Finset.card_singleton] at hmain
  omega

theorem orIn_gate {C : Circuit} {k : ℕ} (u : Fin 11) (hu : u ∈ orIn 11 C (11 + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ c ∈ (gateAt C k).inputs, c < 11 + k ∧ u ∈ orIn 11 C c := by
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with h | ⟨c, hstep, hr⟩
  · have := u.isLt; omega
  · obtain ⟨k', hk', e, hop, hin, hlt⟩ := hstep
    have hkk : k' = k := by omega
    subst hkk
    exact ⟨hk', hop, c, hin, hlt, reach_mem_orIn u hr⟩

theorem orIn_or_eq {C : Circuit} (hAO : IsAO2 11 C) {k : ℕ} (hk : k < C.gates.length)
    (hor : (gateAt C k).op = GateOp.or) :
    orIn 11 C (11 + k) = orIn 11 C (opnd C k 0) ∪ orIn 11 C (opnd C k 1) := by
  ext u
  simp only [Finset.mem_union]
  constructor
  · intro hu
    obtain ⟨_, _, c, hc, _, hcu⟩ := orIn_gate u hu
    obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hk hc
    fin_cases b
    · exact Or.inl hcu
    · exact Or.inr hcu
  · intro hu
    apply reach_mem_orIn
    rcases hu with h0 | h1
    · exact Relation.ReflTransGen.head
        ⟨k, hk, rfl, hor, opndMem hAO hk 0, opndBound hAO hk 0⟩ (mem_orIn_reach u h0)
    · exact Relation.ReflTransGen.head
        ⟨k, hk, rfl, hor, opndMem hAO hk 1, opndBound hAO hk 1⟩ (mem_orIn_reach u h1)

theorem starEdges_le_tops_add_lam {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hC4 : NoFourCycle G) (hAO : IsAO2 11 C) (hV : centreless G C = ∅) :
    (starEdges G C).card ≤ (tops G C).card + (lam G C).card ∧
      ∃ K : Finset (Fin 11), K.card ≤ (tops G C).card ∧
        ∀ u v : Fin 11, (G.deleteEdges ↑(Ustar G C)).Adj u v → u ∈ K ∨ v ∈ K := by
  classical
  have hStars := topStars hC4 hAO
  have hNonemptySide : ∀ a ∈ tops G C, ∀ b : Fin 2, (side (n := 11) C a b).Nonempty := by
    intro a ha b
    by_contra hne
    have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hmem : a ∈ centreless G C := by
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    rw [hV] at hmem
    exact Finset.notMem_empty a hmem
  have hCenterEx : ∀ a ∈ tops G C, ∃ b : Fin 2, ∃ c : Fin 11, side (n := 11) C a b = {c} := by
    intro a ha
    rcases (hStars a ha).2 with h0 | h1
    · have hpos := Finset.card_pos.mpr (hNonemptySide a ha 0)
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (by omega : (side (n := 11) C a 0).card = 1)
      exact ⟨0, c, hc⟩
    · have hpos := Finset.card_pos.mpr (hNonemptySide a ha 1)
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (by omega : (side (n := 11) C a 1).card = 1)
      exact ⟨1, c, hc⟩
  let cb (a : ℕ) : Fin 2 := if h : a ∈ tops G C then (hCenterEx a h).choose else 0
  let center (a : ℕ) : Fin 11 := if h : a ∈ tops G C then (hCenterEx a h).choose_spec.choose else 0
  have hCenterSpec (a : ℕ) (ha : a ∈ tops G C) : side (n := 11) C a (cb a) = {center a} := by
    simp only [cb, center, dite_eq_left ha]
    exact (hCenterEx a ha).choose_spec.choose_spec
  let leafOpnd (a : ℕ) : ℕ := opnd C a (1 - cb a)
  have hLeafAdj (a : ℕ) (ha : a ∈ tops G C) (v : Fin 11) (hv : v ∈ orIn 11 C (leafOpnd a)) :
      G.Adj (center a) v := by
    have hc : center a ∈ side (n := 11) C a (cb a) := by rw [hCenterSpec a ha]; simp
    have hside : v ∈ side (n := 11) C a (1 - cb a) := hv
    generalize hcb : cb a = b at hc hside
    fin_cases b
    · exact topAdj hAO ha hc hside
    · exact (topAdj hAO ha hside hc).symm
  let Tc (c : Fin 11) : Finset ℕ := (tops G C).filter fun a => center a = c
  let Wc (c : Fin 11) : Finset ℕ := (Tc c).image leafOpnd
  let Lc (c : Fin 11) : Finset (Fin 11) := (Wc c).biUnion (orIn 11 C)
  let Lamc (c : Fin 11) : Finset ℕ :=
    (lam G C).filter fun g => 2 ≤ (orIn 11 C (11 + g)).card ∧ ∀ u ∈ orIn 11 C (11 + g), G.Adj c u
  have hBound_c (c : Fin 11) : (Lc c).card ≤ (Wc c).card + (Lamc c).card := by
    have hstep : ∀ (N : ℕ) (S : Finset ℕ),
        (∀ w ∈ S, w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w) →
        (S.biUnion (orIn 11 C)).card ≤
          S.card + ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).card := by
      intro N
      induction N with
      | zero =>
        intro S hS
        have : S = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by have := (hS w hw).1; omega
        subst this; simp
      | succ N ih =>
        intro S hS
        by_cases hN : N ∈ S
        · by_cases hN11 : N < 11
          · have hall : ∀ w ∈ S, (orIn 11 C w).card ≤ 1 := by
              intro w hw
              have hw11 : w < 11 := by have := (hS w hw).1; omega
              let v : Fin 11 := ⟨w, hw11⟩
              have hsub : orIn 11 C w ⊆ {v} := by
                intro u hu
                rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with heq | ⟨_, hst, _⟩
                · exact Finset.mem_singleton.mpr (Fin.ext heq.symm)
                · obtain ⟨_, _, h11, _, _, _⟩ := hst; omega
              exact (Finset.card_le_card hsub).trans (by simp)
            calc (S.biUnion (orIn 11 C)).card
                ≤ ∑ w ∈ S, (orIn 11 C w).card := Finset.card_biUnion_le
              _ ≤ ∑ _w ∈ S, 1 := Finset.sum_le_sum hall
              _ = S.card := by simp
              _ ≤ S.card + _ := Nat.le_add_right _ _
          · let k := N - 11
            have hkN : N = 11 + k := by omega
            let S0 := S.erase N
            by_cases hEmpty : orIn 11 C N = ∅
            · have hsubU : S.biUnion (orIn 11 C) ⊆ S0.biUnion (orIn 11 C) := by
                intro u hu
                obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                have hwne : w ≠ N := fun h => by rw [h, hEmpty] at hwu; exact Finset.notMem_empty u hwu
                exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwne, hwS⟩, hwu⟩
              have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S0, OrReaches 11 C w g) ⊆
                  ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
                intro g hg
                obtain ⟨hgL, w, hw, hr⟩ := Finset.mem_filter.mp hg
                exact Finset.mem_filter.mpr ⟨hgL, w, Finset.mem_of_mem_erase hw, hr⟩
              have hih := ih S0 (fun w hw => by
                have hmem := Finset.mem_of_mem_erase hw
                have hne := Finset.ne_of_mem_erase hw
                have := hS w hmem
                exact ⟨by omega, this.2⟩)
              have hc1 := Finset.card_le_card hsubU
              have hc2 := Finset.card_le_card hsubM
              have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
              omega
            · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
              rw [hkN] at hu0
              obtain ⟨hklt, hor, _, _, _, _⟩ := orIn_gate u0 hu0
              let p := opnd C k 0
              let q := opnd C k 1
              have hUnion : orIn 11 C N = orIn 11 C p ∪ orIn 11 C q := hkN ▸ orIn_or_eq hAO hklt hor
              obtain ⟨_, a0, ha0Tc, hpath0⟩ := hS N hN
              have hStepChild (b : Fin 2) :
                  Relation.ReflTransGen (OrStep 11 C) (leafOpnd a0) (opnd C k b) :=
                hpath0.tail ⟨k, hklt, hkN, hor, opndMem hAO hklt b, opndBound hAO hklt b⟩
              by_cases hSmall : orIn 11 C p = ∅ ∨ orIn 11 C q = ∅ ∨ (orIn 11 C N).card ≤ 1
              · have hPick : ∃ b : Fin 2, orIn 11 C N = orIn 11 C (opnd C k b) := by
                  rcases hSmall with hp0 | hq0 | hc1
                  · exact ⟨1, by rw [hUnion, hp0, Finset.empty_union]⟩
                  · exact ⟨0, by rw [hUnion, hq0, Finset.union_empty]⟩
                  · have hsub : orIn 11 C p ⊆ orIn 11 C N := by rw [hUnion]; exact Finset.subset_union_left
                    by_cases hpne : (orIn 11 C p).Nonempty
                    · exact ⟨0, (Finset.eq_of_subset_of_card_le hsub (by have := Finset.card_pos.mpr hpne; omega)).symm⟩
                    · rw [Finset.not_nonempty_iff_eq_empty] at hpne
                      exact ⟨1, by rw [hUnion, hpne, Finset.empty_union]⟩
                obtain ⟨b, hbEq⟩ := hPick
                let S' := insert (opnd C k b) S0
                have hS' : ∀ w ∈ S', w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
                  intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | hw0
                  · exact ⟨by have := opndBound hAO hklt b; omega, a0, ha0Tc, hStepChild b⟩
                  · have hmem := Finset.mem_of_mem_erase hw0
                    have hne := Finset.ne_of_mem_erase hw0
                    have := hS w hmem
                    exact ⟨by omega, this.2⟩
                have hsubU : S.biUnion (orIn 11 C) ⊆ S'.biUnion (orIn 11 C) := by
                  intro u hu
                  obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                  by_cases hwN : w = N
                  · subst hwN
                    exact Finset.mem_biUnion.mpr ⟨opnd C k b, Finset.mem_insert_self _ _, hbEq ▸ hwu⟩
                  · exact Finset.mem_biUnion.mpr ⟨w,
                      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩), hwu⟩
                have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
                    ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) := by
                  intro g hg
                  obtain ⟨hgL, w, hw', hrg⟩ := Finset.mem_filter.mp hg
                  rcases Finset.mem_insert.mp hw' with rfl | hw0
                  · exact Finset.mem_filter.mpr ⟨hgL, N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, opnd C k b, opndMem hAO hklt b, opndBound hAO hklt b, hrg⟩⟩⟩
                  · exact Finset.mem_filter.mpr ⟨hgL, w, Finset.mem_of_mem_erase hw0, hrg⟩
                have hih := ih S' hS'
                have hc1 := Finset.card_le_card hsubU
                have hc2 := Finset.card_le_card hsubM
                have hcS' : S'.card ≤ S0.card + 1 := Finset.card_insert_le (opnd C k b) S0
                have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
                omega
              · push Not at hSmall
                obtain ⟨hpNon, hqNon, hcard2⟩ := hSmall
                have hkNotBel : ¬ BelowF G C k := by
                  intro hbel
                  have hv : gateVal 11 C k (pairInput u0 u0) = true :=
                    reach_var_val (pairInput u0 u0) (11 + k) u0 (mem_orIn_reach u0 hu0) (pairInput_left u0 u0)
                  exact G.loopless.irrefl u0 ((graphFun_pair G u0 u0).mp (hbel _ hv))
                have hkLam : k ∈ lam G C := by
                  refine Finset.mem_filter.mpr ⟨?_, hpNon, hqNon, ?_⟩
                  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
                      And.intro hklt (And.intro hor hkNotBel)
                  · obtain ⟨ha0T, ha0c⟩ := Finset.mem_filter.mp ha0Tc
                    refine ⟨a0, ha0T, 1 - cb a0, ?_, reach_orReaches hpath0 k hkN hklt⟩
                    have hsub1 : (1 : Fin 2) - (1 - cb a0) = cb a0 := by
                      generalize cb a0 = b; fin_cases b <;> rfl
                    rw [hsub1, hCenterSpec a0 ha0T, Finset.card_singleton]
                have hkAdj : ∀ u ∈ orIn 11 C (11 + k), G.Adj c u := by
                  intro u hu
                  obtain ⟨ha0T, ha0c⟩ := Finset.mem_filter.mp ha0Tc
                  have huLeaf : u ∈ orIn 11 C (leafOpnd a0) :=
                    reach_mem_orIn u (hpath0.trans (hkN ▸ mem_orIn_reach u hu))
                  rw [← ha0c]
                  exact hLeafAdj a0 ha0T u huLeaf
                have hkLamc : k ∈ Lamc c :=
                  Finset.mem_filter.mpr ⟨hkLam, by rw [← hkN]; omega, hkAdj⟩
                have hkInM : k ∈ ((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g) :=
                  Finset.mem_filter.mpr ⟨hkLamc, N, hN, hkN ▸ (orReaches_iff 11 C k k).mpr ⟨hklt, Or.inl rfl⟩⟩
                let S' := insert p (insert q S0)
                have hS' : ∀ w ∈ S', w < N ∧ ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
                  intro w hw
                  simp only [S', Finset.mem_insert] at hw
                  rcases hw with rfl | rfl | hw0
                  · exact ⟨by have := opndBound hAO hklt 0; omega, a0, ha0Tc, hStepChild 0⟩
                  · exact ⟨by have := opndBound hAO hklt 1; omega, a0, ha0Tc, hStepChild 1⟩
                  · have hmem := Finset.mem_of_mem_erase hw0
                    have hne := Finset.ne_of_mem_erase hw0
                    have := hS w hmem
                    exact ⟨by omega, this.2⟩
                have hsubU : S.biUnion (orIn 11 C) ⊆ S'.biUnion (orIn 11 C) := by
                  intro u hu
                  obtain ⟨w, hwS, hwu⟩ := Finset.mem_biUnion.mp hu
                  by_cases hwN : w = N
                  · subst hwN
                    rw [hUnion, Finset.mem_union] at hwu
                    rcases hwu with hup | huq
                    · exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_insert_self _ _, hup⟩
                    · exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), huq⟩
                  · exact Finset.mem_biUnion.mpr ⟨w,
                      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwN, hwS⟩)), hwu⟩
                have hsubM : ((Lamc c).filter fun g => ∃ w ∈ S', OrReaches 11 C w g) ⊆
                    (((Lamc c).filter fun g => ∃ w ∈ S, OrReaches 11 C w g).erase k) := by
                  intro g hg
                  obtain ⟨hgL, w, hw', hrg⟩ := Finset.mem_filter.mp hg
                  have hwlt : w < N := (hS' w hw').1
                  have hle := orStep_le (orReaches_reach g w hrg).1
                  have hgne : g ≠ k := by omega
                  refine Finset.mem_erase.mpr ⟨hgne, Finset.mem_filter.mpr ⟨hgL, ?_⟩⟩
                  simp only [S', Finset.mem_insert] at hw'
                  rcases hw' with rfl | rfl | hw0
                  · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, p, opndMem hAO hklt 0, opndBound hAO hklt 0, hrg⟩⟩⟩
                  · exact ⟨N, hN, hkN ▸ (orReaches_iff 11 C k g).mpr
                      ⟨hklt, Or.inr ⟨hor, q, opndMem hAO hklt 1, opndBound hAO hklt 1, hrg⟩⟩⟩
                  · exact ⟨w, Finset.mem_of_mem_erase hw0, hrg⟩
                have hih := ih S' hS'
                have hc1 := Finset.card_le_card hsubU
                have hc2 := Finset.card_le_card hsubM
                have hcM := Finset.card_erase_add_one hkInM
                have hcS' : S'.card ≤ S0.card + 2 := by
                  have h1 : S'.card ≤ (insert q S0).card + 1 := Finset.card_insert_le p (insert q S0)
                  have h2 : (insert q S0).card ≤ S0.card + 1 := Finset.card_insert_le q S0
                  omega
                have hS0card : S0.card + 1 = S.card := Finset.card_erase_add_one hN
                omega
        · exact ih S (fun w hw => by
            have := hS w hw
            have hne : w ≠ N := fun h => hN (h ▸ hw)
            exact ⟨by omega, this.2⟩)
    have hWlt : ∀ w ∈ Wc c, w < 11 + C.gates.length ∧
        ∃ a ∈ Tc c, Relation.ReflTransGen (OrStep 11 C) (leafOpnd a) w := by
      intro w hw
      obtain ⟨a, haTc, rfl⟩ := Finset.mem_image.mp hw
      have haT := (Finset.mem_filter.mp haTc).1
      have hlt : leafOpnd a < 11 + a := opndBound hAO (topData haT).1 (1 - cb a)
      exact ⟨by have := (topData haT).1; omega, a, haTc, Relation.ReflTransGen.refl⟩
    have hmain := hstep (11 + C.gates.length) (Wc c) hWlt
    have hsub : ((Lamc c).filter fun g => ∃ w ∈ Wc c, OrReaches 11 C w g) ⊆ Lamc c :=
      Finset.filter_subset _ _
    exact hmain.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _)
  have hStarSub : starEdges G C ⊆ Finset.univ.biUnion fun c : Fin 11 => (Lc c).image fun v => s(c, v) := by
    intro e he
    obtain ⟨a, haT, hp⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    dsimp only at hu hv ⊢
    refine Finset.mem_biUnion.mpr ⟨center a, Finset.mem_univ _, ?_⟩
    have haTc : a ∈ Tc (center a) := Finset.mem_filter.mpr ⟨haT, rfl⟩
    have hlo : leafOpnd a ∈ Wc (center a) := Finset.mem_image.mpr ⟨a, haTc, rfl⟩
    have hcs := hCenterSpec a haT
    have hloEq : leafOpnd a = opnd C a (1 - cb a) := rfl
    generalize hcb : cb a = b at hcs hloEq
    fin_cases b
    · change side (n := 11) C a 0 = {center a} at hcs
      change leafOpnd a = opnd C a 1 at hloEq
      rw [hcs, Finset.mem_singleton] at hu
      subst hu
      exact Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨leafOpnd a, hlo, by rw [hloEq]; exact hv⟩, rfl⟩
    · change side (n := 11) C a 1 = {center a} at hcs
      change leafOpnd a = opnd C a 0 at hloEq
      rw [hcs, Finset.mem_singleton] at hv
      subst hv
      exact Finset.mem_image.mpr ⟨u, Finset.mem_biUnion.mpr ⟨leafOpnd a, hlo, by rw [hloEq]; exact hu⟩, Sym2.eq_swap⟩
  have hSumT : ∑ c : Fin 11, (Tc c).card = (tops G C).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 11)) Tc := by
      intro c1 _ c2 _ hne
      change Disjoint (Tc c1) (Tc c2)
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
    have hpart : (Finset.univ : Finset (Fin 11)).biUnion Tc = tops G C := by
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Tc, Finset.mem_filter]
      exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨center a, ha, rfl⟩⟩
    rw [← hpart, Finset.card_biUnion hdisj]
  have hSumLam : ∑ c : Fin 11, (Lamc c).card ≤ (lam G C).card := by
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 11)) Lamc := by
      intro c1 _ c2 _ hne
      change Disjoint (Lamc c1) (Lamc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨_, h2, hadj1⟩ := Finset.mem_filter.mp hg1
      obtain ⟨_, _, hadj2⟩ := Finset.mem_filter.mp hg2
      have hsub : orIn 11 C (11 + g) ⊆ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
        fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1 w hw, hadj2 w hw⟩
      have hle := (Finset.card_le_card hsub).trans (hC4 c1 c2 hne)
      omega
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun c _ => Finset.filter_subset _ _)
  have hStarCard : (starEdges G C).card ≤ (tops G C).card + (lam G C).card := by
    calc (starEdges G C).card
        ≤ (Finset.univ.biUnion fun c : Fin 11 => (Lc c).image fun v => s(c, v)).card :=
          Finset.card_le_card hStarSub
      _ ≤ ∑ c : Fin 11, ((Lc c).image fun v => s(c, v)).card := Finset.card_biUnion_le
      _ ≤ ∑ c : Fin 11, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
      _ ≤ ∑ c : Fin 11, ((Wc c).card + (Lamc c).card) := Finset.sum_le_sum fun c _ => hBound_c c
      _ ≤ ∑ c : Fin 11, ((Tc c).card + (Lamc c).card) :=
          Finset.sum_le_sum fun c _ => Nat.add_le_add_right Finset.card_image_le _
      _ = (∑ c : Fin 11, (Tc c).card) + (∑ c : Fin 11, (Lamc c).card) := Finset.sum_add_distrib
      _ ≤ (tops G C).card + (lam G C).card := by omega
  refine ⟨hStarCard, (tops G C).image center, Finset.card_image_le, ?_⟩
  intro u v huv
  obtain ⟨hadj, hnotU⟩ := SimpleGraph.deleteEdges_adj.mp huv
  have hmemStar : s(u, v) ∈ starEdges G C := by
    by_contra hns
    exact hnotU (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hadj, hns⟩)
  obtain ⟨a, haT, hp⟩ := Finset.mem_biUnion.mp hmemStar
  obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  dsimp only at hx hy heq
  have hca : center a ∈ (tops G C).image center := Finset.mem_image.mpr ⟨a, haT, rfl⟩
  have hcs := hCenterSpec a haT
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
  generalize hcb : cb a = b at hcs
  fin_cases b
  · change side (n := 11) C a 0 = {center a} at hcs
    rw [hcs, Finset.mem_singleton] at hx
    subst hx
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hca
    · exact Or.inr hca
  · change side (n := 11) C a 1 = {center a} at hcs
    rw [hcs, Finset.mem_singleton] at hy
    subst hy
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr hca
    · exact Or.inl hca

theorem pure_lam_wire {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 11 C) {m : ℕ} (hR : orN G C \ lam G C = {m}) :
    ∀ w, w < 11 + m →
      (∃ x : Fin 11 → Bool, val C (List.ofFn x) w = true ∧ graphFun G ∅ x = false) →
      (∀ h ∈ junk G C, w ≠ 11 + h) →
      (∀ x : Fin 11 → Bool, val C (List.ofFn x) w = true ↔ ∃ v ∈ orIn 11 C w, x v = true) ∧
      (orIn 11 C w).Nonempty ∧
      ((∃ v : Fin 11, orIn 11 C w = {v}) ∨ ∃ c : Fin 11, ∀ v ∈ orIn 11 C w, G.Adj c v) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwm hdirty hnojunk
    by_cases hw11 : w < 11
    · let v0 : Fin 11 := ⟨w, hw11⟩
      have horIn : orIn 11 C w = {v0} := by
        ext u
        simp only [Finset.mem_singleton]
        constructor
        · intro hu
          rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with heq | ⟨_, hst, _⟩
          · exact Fin.ext heq.symm
          · obtain ⟨_, _, h11, _, _, _⟩ := hst; omega
        · rintro rfl
          exact reach_mem_orIn v0 Relation.ReflTransGen.refl
      refine ⟨?_, by rw [horIn]; exact Finset.singleton_nonempty v0, Or.inl ⟨v0, horIn⟩⟩
      intro x
      rw [horIn]
      simp only [Finset.mem_singleton, exists_eq_left]
      exact ⟨fun h => by rwa [← val_ofFn C x v0], fun h => by rwa [val_ofFn C x v0]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
      have hklt : k < C.gates.length := by
        by_contra hge
        obtain ⟨x, hx, _⟩ := hdirty
        have hfalse := val_ge (n := 11) (C := C) (x := List.ofFn x) (by simp) (by omega : 11 + C.gates.length ≤ 11 + k)
        rw [hfalse] at hx; cases hx
      have hNotBel : ¬ BelowF G C k := by
        intro hbel
        obtain ⟨x, hx, hfx⟩ := hdirty
        exact Bool.noConfusion (hfx.symm.trans (hbel x hx))
      have hor : (gateAt C k).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hklt) with hand | hor
        · exfalso
          have hkj : k ∈ junk G C :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, hand, hklt, hdirty⟩
          exact hnojunk k hkj rfl
        · exact hor
      have hkOrN : k ∈ orN G C := by
        simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hklt (And.intro hor hNotBel)
      have hkLam : k ∈ lam G C := by
        by_contra hnl
        have hkR : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hkOrN, hnl⟩
        rw [hR, Finset.mem_singleton] at hkR
        omega
      obtain ⟨_, hpNon, hqNon, a, haT, b, hcard1, hreach⟩ := Finset.mem_filter.mp hkLam
      have hChild (s : Fin 2) (hsNon : (orIn 11 C (opnd C k s)).Nonempty) :
          (∀ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C k s) = true ↔
            ∃ v ∈ orIn 11 C (opnd C k s), x v = true) := by
        have hlt := opndBound hAO hklt s
        obtain ⟨u, hu⟩ := hsNon
        have hdir : ∃ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C k s) = true ∧ graphFun G ∅ x = false :=
          ⟨pairInput u u, reach_var_val _ _ u (mem_orIn_reach u hu) (pairInput_left u u),
            Bool.eq_false_iff.mpr fun hf => G.loopless.irrefl u ((graphFun_pair G u u).mp hf)⟩
        have hnj : ∀ h ∈ junk G C, opnd C k s ≠ 11 + h := by
          intro h hh heq
          rw [heq, andRawEmpty (junkData hh).2.1] at hu
          exact Finset.notMem_empty u hu
        exact (ih (opnd C k s) hlt (by omega) hdir hnj).1
      have h0 := hChild 0 hpNon
      have h1 := hChild 1 hqNon
      have hUnion := orIn_or_eq hAO hklt hor
      have hVal : ∀ x : Fin 11 → Bool,
          val C (List.ofFn x) (11 + k) = true ↔ ∃ v ∈ orIn 11 C (11 + k), x v = true := by
        intro x
        rw [val_or (n := 11) (by simp) hklt hor, hUnion]
        constructor
        · rintro ⟨u, hu, _, hvu⟩
          obtain ⟨s, rfl⟩ := inputsAsOpnd hAO hklt hu
          fin_cases s
          · obtain ⟨v, hv, hxv⟩ := (h0 x).mp hvu
            exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
          · obtain ⟨v, hv, hxv⟩ := (h1 x).mp hvu
            exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
        · rintro ⟨v, hv, hxv⟩
          rcases Finset.mem_union.mp hv with hv0 | hv1
          · exact ⟨opnd C k 0, opndMem hAO hklt 0, opndBound hAO hklt 0, (h0 x).mpr ⟨v, hv0, hxv⟩⟩
          · exact ⟨opnd C k 1, opndMem hAO hklt 1, opndBound hAO hklt 1, (h1 x).mpr ⟨v, hv1, hxv⟩⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      have hNbr : ∀ v ∈ orIn 11 C (11 + k), G.Adj c v := by
        intro v hv
        have hvSide : v ∈ side (n := 11) C a b :=
          reach_mem_orIn v ((orReaches_reach k _ hreach).1.trans (mem_orIn_reach v hv))
        have hcSide : c ∈ side (n := 11) C a (1 - b) := by rw [hc]; simp
        fin_cases b
        · exact (topAdj hAO haT hvSide hcSide).symm
        · exact topAdj hAO haT hcSide hvSide
      refine ⟨hVal, ?_, Or.inr ⟨c, hNbr⟩⟩
      rw [hUnion]
      exact hpNon.mono Finset.subset_union_left

theorem gate_partition_card {G : SimpleGraph (Fin 11)} [DecidableRel G.Adj] (C : Circuit) :
    (tops G C).card + (junk G C).card + (orT G C).card + (lam G C).card + (orN G C \ lam G C).card ≤ C.size := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hdisj (A B : Finset ℕ) (h : Disjoint A B) : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint h
  have dTJ : Disjoint (tops G C) (junk G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    obtain ⟨_, _, hb⟩ := topData hk1
    obtain ⟨_, _, x, hx, hf⟩ := junkData hk2
    exact Bool.noConfusion (hf.symm.trans (hb x hx))
  have dTJoT : Disjoint (tops G C ∪ junk G C) (orT G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    have ho : (gateAt C k).op = GateOp.or := (Finset.mem_filter.mp hk2).2.1
    rcases Finset.mem_union.mp hk1 with hkT | hkJ
    · rw [(topData hkT).2.1] at ho; cases ho
    · rw [(junkData hkJ).2.1] at ho; cases ho
  have dAndOrN : Disjoint (tops G C ∪ junk G C ∪ orT G C) (orN G C) := Finset.disjoint_left.mpr fun k hk1 hk2 => by
    obtain ⟨_, hoN, hnb⟩ := Finset.mem_filter.mp hk2
    rcases Finset.mem_union.mp hk1 with hkTJ | hkOT
    · rcases Finset.mem_union.mp hkTJ with hkT | hkJ
      · rw [(topData hkT).2.1] at hoN; cases hoN
      · rw [(junkData hkJ).2.1] at hoN; cases hoN
    · exact hnb (Finset.mem_filter.mp hkOT).2.2
  have hLamSub : lam G C ⊆ orN G C := Finset.filter_subset _ _
  have hOrNcard : (orN G C \ lam G C).card + (lam G C).card = (orN G C).card :=
    Finset.card_sdiff_add_card_eq_card hLamSub
  have hSubAll : tops G C ∪ junk G C ∪ orT G C ∪ orN G C ⊆ Finset.range C.gates.length := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk1 | hk4
    · rcases Finset.mem_union.mp hk1 with hk2 | hk3
      · rcases Finset.mem_union.mp hk2 with hkT | hkJ
        · exact Finset.mem_range.mpr (topData hkT).1
        · exact Finset.mem_range.mpr (junkData hkJ).1
      · exact (Finset.mem_filter.mp hk3).1
    · exact (Finset.mem_filter.mp hk4).1
  have hle := Finset.card_le_card hSubAll
  rw [Finset.card_range] at hle
  rw [hdisj _ _ dAndOrN, hdisj _ _ dTJoT, hdisj _ _ dTJ] at hle
  change (tops G C).card + (junk G C).card + (orT G C).card + (lam G C).card +
    (orN G C \ lam G C).card ≤ C.gates.length
  omega

theorem main_proof_G11 (C : Circuit)
    (hLeast : IsLeastAO G11 C) (hTop : TopForm G11 C) (hSizeLt : C.size < 22)
    (hJunkEx : ∃ i j, junk G11 C = {i, j} ∧ InCone 11 C i j)
    (hU2 : (Ustar G11 C).card = 2) :
    2 ≤ 2 * (centreless G11 C).card + (orN G11 C \ lam G11 C).card := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra hlt
  obtain ⟨i, j, hJunk, hCone⟩ := hJunkEx
  have hOrder : i < j := coneStrict C j i hCone
  have hJunkCard : (junk G11 C).card = 2 := by
    rw [hJunk, Finset.card_pair (Nat.ne_of_lt hOrder)]
  have hUpos : (Ustar G11 C).Nonempty := Finset.card_pos.mp (by omega)
  have hOff : 1 ≤ 2 * (centreless G11 C).card + (orN G11 C \ lam G11 C).card := by
    rcases residualConnection hLeast hTop hUpos with hv | hr
    · have := Finset.card_pos.mpr hv; omega
    · have := Finset.card_pos.mpr hr; omega
  have hV : centreless G11 C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hR1 : (orN G11 C \ lam G11 C).card = 1 := by
    have hv0 : (centreless G11 C).card = 0 := by rw [hV]; simp
    omega
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hR1
  have hTleOrT : (tops G11 C).card ≤ (orT G11 C).card + 1 :=
    tops_le_orT_add_one hLeast hTop ⟨0, 9, by decide +kernel⟩
  obtain ⟨hStarLe, K, hKcardLe, hKcov⟩ := starEdges_le_tops_add_lam G11_noFourCycle hLeast.1 hV
  have hDisj5 := gate_partition_card (G := G11) C
  have hStarGe14 : 14 ≤ (starEdges G11 C).card := by
    have hsub : G11.edgeFinset ⊆ starEdges G11 C ∪ Ustar G11 C := by
      intro e he
      by_cases hs : e ∈ starEdges G11 C
      · exact Finset.mem_union_left _ hs
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hs⟩)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [G11_edgeCard] at hle
    omega
  have hTle5 : (tops G11 C).card ≤ 5 := by omega
  have hKge5 : 5 ≤ K.card := by
    let A := (Ustar G11 C).image (fun e => e.out.1)
    have hA : A.card ≤ (Ustar G11 C).card := Finset.card_image_le
    have hUn := Finset.card_union_le K A
    have hfull : G11.IsVertexCover ((K ∪ A : Finset (Fin 11)) : Set _) := by
      intro u v huv
      by_cases he : s(u, v) ∈ Ustar G11 C
      · have hv := Finset.mem_image_of_mem (fun e : Sym2 (Fin 11) => e.out.1) he
        have hs := Sym2.out_fst_mem s(u, v)
        rw [Sym2.mem_iff] at hs
        rcases hs with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hv))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hv))
      · exact (hKcov u v (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩)).imp
          (Finset.mem_union_left A) (Finset.mem_union_left A)
    have hc := G11_fullCover (K ∪ A) hfull
    omega
  have hK5 : K.card = 5 := by omega
  have hKmissed : ∀ p ∈ missedEdges (toMask K), ∃ h1 : p.1 < 11, ∃ h2 : p.2 < 11,
      s(⟨p.1, h1⟩, ⟨p.2, h2⟩) ∈ Ustar G11 C := by
    intro p hp
    simp only [missedEdges, List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff] at hp
    obtain ⟨hpg, h1b, h2b⟩ := hp
    obtain ⟨h1, h2⟩ := g11Edges_bounds p hpg
    refine ⟨h1, h2, ?_⟩
    by_contra hnotU
    have hadj : (G11.deleteEdges ↑(Ustar G11 C)).Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ :=
      SimpleGraph.deleteEdges_adj.mpr ⟨g11Edges_adj p hpg h1 h2, hnotU⟩
    rcases hKcov ⟨p.1, h1⟩ ⟨p.2, h2⟩ hadj with hu | hv
    · have := toMask_testBit K ⟨p.1, h1⟩
      simp [hu, h1b] at this
    · have := toMask_testBit K ⟨p.2, h2⟩
      simp [hv, h2b] at this
  have hMissedLenLe : (missedEdges (toMask K)).length ≤ 2 := by
    let f : (Nat × Nat) → Sym2 (Fin 11) := fun p =>
      if h : p.1 < 11 ∧ p.2 < 11 then s(⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else s(0, 0)
    have hnd : ((missedEdges (toMask K)).map f).Nodup := by
      have hsub : (missedEdges (toMask K)).Sublist g11Edges := List.filter_sublist
      have hnd0 : ((missedEdges (toMask K)).map fun p => s(p.1, p.2)).Nodup :=
        g11Edges_nodup_sym2.sublist (hsub.map _)
      have hndList : (missedEdges (toMask K)).Nodup := List.Nodup.of_map _ hnd0
      rw [List.nodup_map_iff_inj_on hndList] at hnd0 ⊢
      intro x hx y hy hxy
      apply hnd0 x hx y hy
      have hx' := g11Edges_bounds x (List.mem_of_mem_filter hx)
      have hy' := g11Edges_bounds y (List.mem_of_mem_filter hy)
      simp only [f, dite_eq_left hx', dite_eq_left hy', Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, Fin.ext_iff] at hxy ⊢
      exact hxy
    have hsubU : ((missedEdges (toMask K)).map f).toFinset ⊆ Ustar G11 C := by
      intro e he
      rw [List.mem_toFinset, List.mem_map] at he
      obtain ⟨p, hp, rfl⟩ := he
      obtain ⟨h1, h2, hmem⟩ := hKmissed p hp
      simpa only [f, dite_eq_left (And.intro h1 h2)] using hmem
    have hle := Finset.card_le_card hsubU
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at hle
    omega
  have hTau5Check : ∃ e1 e2, missedEdges (toMask K) = [e1, e2] ∧ (e1, e2) ∈ tau5Pairs := by
    have hall := List.all_eq_true.mp checkTau5_ok (toMask K) (List.mem_range.mpr (toMask_lt K))
    simp only [popcount11_toMask, hK5, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hall
    cases hme : missedEdges (toMask K) with
    | nil => rw [hme] at hall; simp at hall
    | cons e1 rest =>
      cases rest with
      | nil => rw [hme] at hall; simp at hall
      | cons e2 rest2 =>
        cases rest2 with
        | nil =>
          rw [hme] at hall
          exact ⟨e1, e2, rfl, decide_eq_true_eq.mp hall⟩
        | cons e3 rest3 =>
          rw [hme] at hMissedLenLe; simp at hMissedLenLe
  obtain ⟨e1, e2, hmeEq, hInTau5⟩ := hTau5Check
  obtain ⟨hu1, hv1lt, he1U⟩ := hKmissed e1 (by rw [hmeEq]; simp)
  obtain ⟨hu2, hv2lt, he2U⟩ := hKmissed e2 (by rw [hmeEq]; simp)
  have nonemptySide (a : ℕ) (ha : a ∈ tops G11 C) (b : Fin 2) : (orIn 11 C (opnd C a b)).Nonempty := by
    by_contra hne
    have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have hmem : a ∈ centreless G11 C := by
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    rw [hV] at hmem
    exact Finset.notMem_empty a hmem
  have junction (u v : Fin 11) (he : s(u, v) ∈ Ustar G11 C) :
      ∃ a ∈ tops G11 C, ∃ b : Fin 2, ∃ h ∈ junk G11 C,
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) m ∧
        gateVal 11 C h (pairInput u v) = true ∧
        Relation.ReflTransGen (OrStep 11 C) (opnd C a b) (11 + m) ∧
        11 + h ∈ (gateAt C m).inputs := by
    obtain ⟨a, ha, b, h, hh, hv, hr, hhval⟩ := residualTraceWithTop hLeast hTop he
    rcases lastOrBefore (orReaches_reach h _ hr).1 with heq | ⟨k, hk, hop, hin, hlt', hpath⟩
    · have hne := nonemptySide a ha b
      rw [heq, andRawEmpty (junkData hh).2.1] at hne
      exact (Finset.not_nonempty_empty hne).elim
    · have hkR : k ∈ orN G11 C \ lam G11 C := lastOrOutside hLeast.1 hh hk hop hin hlt'
      have hkm : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
      subst k
      exact ⟨a, ha, b, h, hh, hv, reach_orReaches hpath m rfl hk, hhval, hpath, hin⟩
  have hmData : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G11 C m := by
    have hmem : m ∈ orN G11 C \ lam G11 C := by simp [hm]
    have ho := (Finset.mem_sdiff.mp hmem).1
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using ho
  obtain ⟨hlen, ho, _⟩ := hmData
  obtain ⟨a1, ha1, b1, h0, hh0, hva1, hr1, hh0v1, hp1, hread0⟩ := junction ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩ he1U
  have hmOr : (orIn 11 C (11 + m)).Nonempty := by
    by_contra hno
    have hme := Finset.not_nonempty_iff_eq_empty.mp hno
    rcases Relation.ReflTransGen.cases_tail hp1 with heq | ⟨w, _, hs⟩
    · have hn := nonemptySide a1 ha1 b1
      rw [← heq, hme] at hn
      exact Finset.not_nonempty_empty hn
    · obtain ⟨k, hk, rfl, hkop, hkmem, hklt⟩ := hs
      obtain ⟨_, _, x, hd, hx⟩ := junkData hh0
      have hmv : val C (List.ofFn x) (11 + m) = true :=
        (val_or (by simp) hlen ho).mpr ⟨11 + h0, hread0, hLeast.1.2.1 m hlen _ hread0, hd⟩
      have hkv : val C (List.ofFn x) (11 + k) = true :=
        (val_or (by simp) hk hkop).mpr ⟨11 + m, hkmem, hklt, hmv⟩
      have hkNotBelow : ¬ BelowF G11 C k := fun hb =>
        Bool.noConfusion (hx.symm.trans (hb x hkv))
      have hkR : k ∈ orN G11 C \ lam G11 C := by
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, ?_⟩
        · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
            And.intro hk (And.intro hkop hkNotBelow)
        · intro hlam
          obtain ⟨_, h0', h1', _⟩ := Finset.mem_filter.mp hlam
          obtain ⟨b', hb'⟩ := inputsAsOpnd hLeast.1 hk hkmem
          have hne' : (orIn 11 C (opnd C k b')).Nonempty := by
            fin_cases b'
            · exact h0'
            · exact h1'
          rw [← hb', hme] at hne'
          exact Finset.not_nonempty_empty hne'
      have : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
      omega
  have huniq (h' : ℕ) (hh' : h' ∈ junk G11 C) (hd : 11 + h' ∈ (gateAt C m).inputs) : h' = h0 := by
    by_contra hne
    obtain ⟨p, q, hpq⟩ := binaryInputs hLeast.1 hlen
    have he1 := andRawEmpty (n := 11) (junkData hh0).2.1
    have he2 := andRawEmpty (n := 11) (junkData hh').2.1
    have hshape : (gateAt C m).inputs = [11 + h0, 11 + h'] ∨
        (gateAt C m).inputs = [11 + h', 11 + h0] := by
      rw [hpq] at hread0 hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hread0 hd
      rcases hread0 with h1 | h1 <;> rcases hd with h2 | h2
      · omega
      · exact Or.inl (by rw [hpq, ← h1, ← h2])
      · exact Or.inr (by rw [hpq, ← h2, ← h1])
      · omega
    obtain ⟨t, ht⟩ := hmOr
    obtain ⟨_, _, w, hw, _, htw⟩ := orIn_gate t ht
    rcases hshape with hs | hs <;> rw [hs] at hw <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;>
      rcases hw with rfl | rfl <;> simp [he1, he2] at htw
  obtain ⟨a2, ha2, b2, h0', hh0', hva2, hr2, hh0v2, _, hread0'⟩ := junction ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩ he2U
  have heqh0 : h0' = h0 := huniq h0' hh0' hread0'
  subst h0'
  obtain ⟨z, hz⟩ := hmOr
  have extractW (u v : Fin 11) (heU : s(u, v) ∈ Ustar G11 C) (a : ℕ) (ha : a ∈ tops G11 C) (b : Fin 2)
      (hva : gateVal 11 C a (pairInput u v) = true) (hrm : OrReaches 11 C (opnd C a b) m) :
      z ≠ u ∧ z ≠ v ∧ ∃ w : Fin 11, (w = u ∨ w = v) ∧ G11.Adj z w ∧
        ∀ x : Fin 11 → Bool, gateVal 11 C h0 x = true → x w = true → graphFun G11 ∅ x = true := by
    have hzSide : z ∈ side (n := 11) C a b :=
      reach_mem_orIn z ((orReaches_reach m _ hrm).1.trans (mem_orIn_reach z hz))
    have hNotOtherM : ¬ OrReaches 11 C (opnd C a (1 - b)) m := by
      intro hrm'
      have hzSide' : z ∈ side (n := 11) C a (1 - b) :=
        reach_mem_orIn z ((orReaches_reach m _ hrm').1.trans (mem_orIn_reach z hz))
      have : G11.Adj z z := by
        fin_cases b
        · exact topAdj hLeast.1 ha hzSide hzSide'
        · exact topAdj hLeast.1 ha hzSide' hzSide
      exact G11.loopless.irrefl z this
    obtain ⟨hl, hop, hbel⟩ := topData ha
    have hvOther := (andValOperands hLeast.1 hl hop (pairInput u v)).mp hva (1 - b)
    rcases operandSupport hLeast.1 hTop hl hop hvOther with ⟨w, hwSide, hwu⟩ | ⟨h', hh', hrh', _⟩
    · have hzw : G11.Adj z w := by
        fin_cases b
        · exact topAdj hLeast.1 ha hzSide hwSide
        · exact (topAdj hLeast.1 ha hwSide hzSide).symm
      have hneU : z ≠ u := by
        intro hzu
        have hmiss := (Finset.mem_sdiff.mp heU).2
        apply hmiss
        unfold starEdges
        rcases hwu with hwu | hwv
        · rw [hzu, hwu] at hzw
          exact (G11.loopless.irrefl u hzw).elim
        · fin_cases b
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(z, w), Finset.mem_product.mpr ⟨hzSide, hwSide⟩, by rw [hzu, hwv]⟩⟩
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(w, z), Finset.mem_product.mpr ⟨hwSide, hzSide⟩, by rw [hzu, hwv, Sym2.eq_swap]⟩⟩
      have hneV : z ≠ v := by
        intro hzv
        have hmiss := (Finset.mem_sdiff.mp heU).2
        apply hmiss
        unfold starEdges
        rcases hwu with hwu | hwv
        · fin_cases b
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(z, w), Finset.mem_product.mpr ⟨hzSide, hwSide⟩, by rw [hzv, hwu, Sym2.eq_swap]⟩⟩
          · exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
              ⟨(w, z), Finset.mem_product.mpr ⟨hwSide, hzSide⟩, by rw [hzv, hwu]⟩⟩
        · rw [hzv, hwv] at hzw
          exact (G11.loopless.irrefl v hzw).elim
      refine ⟨hneU, hneV, w, hwu, hzw, ?_⟩
      intro x hh0x hxw
      apply hbel x
      have hmx : val C (List.ofFn x) (11 + m) = true :=
        (val_or (by simp) hlen ho).mpr ⟨11 + h0, hread0, hLeast.1.2.1 m hlen _ hread0, hh0x⟩
      have hbx : val C (List.ofFn x) (opnd C a b) = true :=
        orStep_up (by simp) (orReaches_reach m _ hrm).1 hmx
      have h1bx : val C (List.ofFn x) (opnd C a (1 - b)) = true := sideVal hwSide hxw
      rw [andValBoth hLeast.1 hl hop x]
      fin_cases b
      · exact ⟨hbx, h1bx⟩
      · exact ⟨h1bx, hbx⟩
    · exfalso
      rcases lastOrBefore (orReaches_reach h' _ hrh').1 with heq | ⟨k, hk, hkop, hin, hlt', hpath⟩
      · have hne := nonemptySide a ha (1 - b)
        rw [heq, andRawEmpty (junkData hh').2.1] at hne
        exact Finset.not_nonempty_empty hne
      · have hkR : k ∈ orN G11 C \ lam G11 C := lastOrOutside hLeast.1 hh' hk hkop hin hlt'
        have hkm : k = m := by simpa only [hm, Finset.mem_singleton] using hkR
        subst k
        exact hNotOtherM (reach_orReaches hpath m rfl hk)
  obtain ⟨hzne1a, hzne1b, w1, hw1m, hzw1, hw1max⟩ := extractW ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩ he1U a1 ha1 b1 hva1 hr1
  obtain ⟨hzne2a, hzne2b, w2, hw2m, hzw2, hw2max⟩ := extractW ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩ he2U a2 ha2 b2 hva2 hr2
  have hh0_lt_m : h0 < m := by
    have := hLeast.1.2.1 m hlen (11 + h0) hread0; omega
  have hi_lt_m : i < m := by
    have hmem : h0 ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> omega
  have hPureOpnd (g : ℕ) (hg : g ∈ junk G11 C) (hgm : g < m) (b : Fin 2) (hni : opnd C g b ≠ 11 + i)
      (hnj : opnd C g b ≠ 11 + j) :
      (∀ x : Fin 11 → Bool, val C (List.ofFn x) (opnd C g b) = true ↔
        ∃ v ∈ orIn 11 C (opnd C g b), x v = true) ∧
      (orIn 11 C (opnd C g b)).Nonempty ∧
      ((∃ v : Fin 11, orIn 11 C (opnd C g b) = {v}) ∨
        ∃ c : Fin 11, ∀ v ∈ orIn 11 C (opnd C g b), G11.Adj c v) := by
    obtain ⟨hglt, hgop, x0, hx0, hfx0⟩ := junkData hg
    have hlt' := opndBound hLeast.1 hglt b
    have hdir : ∃ x, val C (List.ofFn x) (opnd C g b) = true ∧ graphFun G11 ∅ x = false :=
      ⟨x0, (andValOperands hLeast.1 hglt hgop x0).mp hx0 b, hfx0⟩
    have hno : ∀ h' ∈ junk G11 C, opnd C g b ≠ 11 + h' := by
      intro h' hh'
      have hmem : h' ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact hni
      · exact hnj
    exact pure_lam_wire hLeast.1 hm (opnd C g b) (by omega) hdir hno
  have hiJ : i ∈ junk G11 C := by rw [hJunk]; simp
  have hi_repr : ∃ A B : Finset (Fin 11),
      (∀ x, gateVal 11 C i x = true ↔ (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true)) ∧
      toMask A ∈ lamList ∧ toMask B ∈ lamList := by
    have hil := (junkData hiJ).1
    have hio := (junkData hiJ).2.1
    have hb0 := opndBound hLeast.1 hil 0
    have hb1 := opndBound hLeast.1 hil 1
    obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd i hiJ hi_lt_m 0 (by omega) (by omega)
    obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd i hiJ hi_lt_m 1 (by omega) (by omega)
    refine ⟨orIn 11 C (opnd C i 0), orIn 11 C (opnd C i 1), ?_,
      toMask_mem_lamList _ h0n h0l, toMask_mem_lamList _ h1n h1l⟩
    intro x
    rw [andValBoth hLeast.1 hil hio x, h0v x, h1v x]
  have hh0_repr : ∃ A B D : Finset (Fin 11),
      (∀ x, gateVal 11 C h0 x = true ↔
        (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true) ∧ (∃ v ∈ D, x v = true)) ∧
      toMask A ∈ lamList ∧ toMask B ∈ lamList ∧ toMask D ∈ lamList := by
    obtain ⟨Ai, Bi, hiV, hAi, hBi⟩ := hi_repr
    have hmem : h0 ∈ ({i, j} : Finset ℕ) := hJunk ▸ hh0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hh0i | hh0j
    · subst hh0i
      refine ⟨Ai, Bi, Bi, ?_, hAi, hBi, hBi⟩
      intro x
      rw [hiV x]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
    · have hjl := (junkData hh0).1
      have hjo := (junkData hh0).2.1
      have hb0 := opndBound hLeast.1 hjl 0
      have hb1 := opndBound hLeast.1 hjl 1
      by_cases h0i : opnd C h0 0 = 11 + i
      · by_cases h1i : opnd C h0 1 = 11 + i
        · refine ⟨Ai, Bi, Bi, ?_, hAi, hBi, hBi⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0i, h1i]
          change (gateVal 11 C i x = true ∧ gateVal 11 C i x = true) ↔ _
          rw [hiV x]
          exact ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨⟨h1, h2⟩, ⟨h1, h2⟩⟩⟩
        · obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd h0 hh0 hh0_lt_m 1 h1i (by omega)
          refine ⟨Ai, Bi, orIn 11 C (opnd C h0 1), ?_, hAi, hBi, toMask_mem_lamList _ h1n h1l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0i]
          change (gateVal 11 C i x = true ∧ val C (List.ofFn x) (opnd C h0 1) = true) ↔ _
          rw [hiV x, h1v x]
          exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
      · by_cases h1i : opnd C h0 1 = 11 + i
        · obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd h0 hh0 hh0_lt_m 0 h0i (by omega)
          refine ⟨Ai, Bi, orIn 11 C (opnd C h0 0), ?_, hAi, hBi, toMask_mem_lamList _ h0n h0l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h1i]
          change (val C (List.ofFn x) (opnd C h0 0) = true ∧ gateVal 11 C i x = true) ↔ _
          rw [hiV x, h0v x]
          exact ⟨fun ⟨h3, ⟨h1, h2⟩⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h3, ⟨h1, h2⟩⟩⟩
        · obtain ⟨h0v, h0n, h0l⟩ := hPureOpnd h0 hh0 hh0_lt_m 0 h0i (by omega)
          obtain ⟨h1v, h1n, h1l⟩ := hPureOpnd h0 hh0 hh0_lt_m 1 h1i (by omega)
          refine ⟨orIn 11 C (opnd C h0 0), orIn 11 C (opnd C h0 1), orIn 11 C (opnd C h0 1), ?_,
            toMask_mem_lamList _ h0n h0l, toMask_mem_lamList _ h1n h1l, toMask_mem_lamList _ h1n h1l⟩
          intro x
          rw [andValBoth hLeast.1 hjl hjo x, h0v x, h1v x]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h2⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  obtain ⟨A, B, D, hABD, hAl, hBl, hDl⟩ := hh0_repr
  have hHits (S : Finset (Fin 11)) (u v : Fin 11) (h : ∃ t ∈ S, pairInput u v t = true) :
      (toMask S &&& ((1 <<< u.val) ||| (1 <<< v.val))) != 0 := by
    obtain ⟨t, ht, hpt⟩ := h
    rw [pairInput_true] at hpt
    exact bne_iff_ne.mpr (toMask_and_edge_ne_zero S u v (by rcases hpt with rfl | rfl <;> [exact Or.inl ht; exact Or.inr ht]))
  have h1 := (hABD (pairInput ⟨e1.1, hu1⟩ ⟨e1.2, hv1lt⟩)).mp hh0v1
  have h2 := (hABD (pairInput ⟨e2.1, hu2⟩ ⟨e2.2, hv2lt⟩)).mp hh0v2
  let m1 := (1 <<< e1.1) ||| (1 <<< e1.2)
  let m2 := (1 <<< e2.1) ||| (1 <<< e2.2)
  let cand := lamList.filter fun s => (s &&& m1) != 0 && (s &&& m2) != 0
  have hAc : toMask A ∈ cand := List.mem_filter.mpr ⟨hAl, by simp [m1, m2, hHits A _ _ h1.1, hHits A _ _ h2.1]⟩
  have hBc : toMask B ∈ cand := List.mem_filter.mpr ⟨hBl, by simp [m1, m2, hHits B _ _ h1.2.1, hHits B _ _ h2.2.1]⟩
  have hDc : toMask D ∈ cand := List.mem_filter.mpr ⟨hDl, by simp [m1, m2, hHits D _ _ h1.2.2, hHits D _ _ h2.2.2]⟩
  have hCheck := List.all_eq_true.mp checkAllTriples_ok (e1, e2) hInTau5
  unfold checkPair at hCheck
  have hCheckZ := List.all_eq_true.mp hCheck z.val (List.mem_range.mpr z.isLt)
  have hzNotE : (z.val == e1.1 || z.val == e1.2 || z.val == e2.1 || z.val == e2.2) = false := by
    have h1a : z.val ≠ e1.1 := fun h => hzne1a (Fin.ext h)
    have h1b : z.val ≠ e1.2 := fun h => hzne1b (Fin.ext h)
    have h2a : z.val ≠ e2.1 := fun h => hzne2a (Fin.ext h)
    have h2b : z.val ≠ e2.2 := fun h => hzne2b (Fin.ext h)
    simp [h1a, h1b, h2a, h2b]
  simp only [hzNotE, Bool.false_eq_true, ↓reduceIte] at hCheckZ
  have hw1In : w1.val ∈ [e1.1, e1.2] := by
    rcases hw1m with rfl | rfl <;> simp
  have hw2In : w2.val ∈ [e2.1, e2.2] := by
    rcases hw2m with rfl | rfl <;> simp
  have hCheckW1 := List.all_eq_true.mp hCheckZ w1.val hw1In
  have hzw1b : (adjMask z.val).testBit w1.val = true := (G11_adj_iff_adjMask z w1).mp hzw1
  simp only [hzw1b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheckW1
  have hCheckW2 := List.all_eq_true.mp hCheckW1 w2.val hw2In
  have hzw2b : (adjMask z.val).testBit w2.val = true := (G11_adj_iff_adjMask z w2).mp hzw2
  simp only [hzw2b, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hCheckW2
  have hTrip := List.all_eq_true.mp
    (List.all_eq_true.mp
      (List.all_eq_true.mp hCheckW2 (toMask A) hAc) (toMask B) hBc) (toMask D) hDc
  have hHasInd : hasIndep (toMask A) (toMask B) (toMask D) = true := by
    obtain ⟨_, _, x, hx, hfx⟩ := junkData hh0
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩, ⟨d, hd, hxd⟩⟩ := (hABD x).mp hx
    have hnoAdj (u v : Fin 11) (hu : x u = true) (hv : x v = true) : ¬ G11.Adj u v := by
      intro hadj
      have : graphFun G11 ∅ x = true := by
        simp only [graphFun]; exact decide_eq_true ⟨u, v, hadj, hu, hv⟩
      rw [this] at hfx; cases hfx
    have hab : (adjMask a.val).testBit b.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj a b hxa hxb ((G11_adj_iff_adjMask a b).mpr h)
    have had : (adjMask a.val).testBit d.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj a d hxa hxd ((G11_adj_iff_adjMask a d).mpr h)
    have hbd : (adjMask b.val).testBit d.val = false :=
      Bool.eq_false_iff.mpr fun h => hnoAdj b d hxb hxd ((G11_adj_iff_adjMask b d).mpr h)
    unfold hasIndep
    refine List.any_eq_true.mpr ⟨a.val, List.mem_range.mpr a.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true ha, Bool.true_and]
    refine List.any_eq_true.mpr ⟨b.val, List.mem_range.mpr b.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true hb, hab, Bool.not_false, Bool.true_and, Bool.true_and]
    refine List.any_eq_true.mpr ⟨d.val, List.mem_range.mpr d.isLt, ?_⟩
    rw [toMask_testBit, decide_eq_true hd, Nat.testBit_or, had, hbd]
    rfl
  have hNoBad (w : Fin 11) (hwmax : ∀ x, gateVal 11 C h0 x = true → x w = true → graphFun G11 ∅ x = true) :
      hasIndepNotAdj (toMask A) (toMask B) (toMask D) w.val = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    unfold hasIndepNotAdj at htrue
    obtain ⟨a, haR, haB⟩ := List.any_eq_true.mp htrue
    simp only [Bool.and_eq_true] at haB
    obtain ⟨haBit, hBex⟩ := haB
    obtain ⟨b, hbR, hbB⟩ := List.any_eq_true.mp hBex
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbB
    obtain ⟨⟨hbBit, hab⟩, hDex⟩ := hbB
    obtain ⟨d, hdR, hdB⟩ := List.any_eq_true.mp hDex
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.testBit_or, Bool.or_eq_false_iff] at hdB
    obtain ⟨⟨hdBit, had, hbd⟩, ⟨haw, hbw⟩, hdw⟩ := hdB
    let af : Fin 11 := ⟨a, List.mem_range.mp haR⟩
    let bf : Fin 11 := ⟨b, List.mem_range.mp hbR⟩
    let df : Fin 11 := ⟨d, List.mem_range.mp hdR⟩
    have haA : af ∈ A := of_decide_eq_true (by rw [← toMask_testBit A af]; exact haBit)
    have hbB' : bf ∈ B := of_decide_eq_true (by rw [← toMask_testBit B bf]; exact hbBit)
    have hdD : df ∈ D := of_decide_eq_true (by rw [← toMask_testBit D df]; exact hdBit)
    let x : Fin 11 → Bool := fun v => decide (v = af ∨ v = bf ∨ v = df ∨ v = w)
    have hh0x : gateVal 11 C h0 x = true :=
      (hABD x).mpr ⟨⟨af, haA, by simp [x]⟩, ⟨bf, hbB', by simp [x]⟩, ⟨df, hdD, by simp [x]⟩⟩
    have hfx : graphFun G11 ∅ x = true := hwmax x hh0x (by simp [x])
    have hfx' : ∃ u v : Fin 11, G11.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hfx
    obtain ⟨u, v, huv, hxu, hxv⟩ := hfx'
    simp only [x, decide_eq_true_eq] at hxu hxv
    have noAdj (p q : Fin 11) (h0 : (adjMask p.val).testBit q.val = false) : ¬ G11.Adj p q :=
      fun h => by rw [(G11_adj_iff_adjMask p q).mp h] at h0; cases h0
    rcases hxu with hu | hu | hu | hu <;> rcases hxv with hv | hv | hv | hv
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj af bf hab huv
    · rw [hu, hv] at huv; exact noAdj af df had huv
    · rw [hu, hv] at huv; exact noAdj af w haw huv
    · rw [hu, hv] at huv; exact noAdj af bf hab huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj bf df hbd huv
    · rw [hu, hv] at huv; exact noAdj bf w hbw huv
    · rw [hu, hv] at huv; exact noAdj af df had huv.symm
    · rw [hu, hv] at huv; exact noAdj bf df hbd huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
    · rw [hu, hv] at huv; exact noAdj df w hdw huv
    · rw [hu, hv] at huv; exact noAdj af w haw huv.symm
    · rw [hu, hv] at huv; exact noAdj bf w hbw huv.symm
    · rw [hu, hv] at huv; exact noAdj df w hdw huv.symm
    · rw [hu, hv] at huv; exact G11.loopless.irrefl _ huv
  rw [hHasInd, hNoBad w1 hw1max, hNoBad w2 hw2max] at hTrip
  cases hTrip

theorem main_proof (G : SimpleGraph (Fin 11)) [inst : DecidableRel G.Adj] (C : Circuit)
    (hG : G = G11) (hLeast : IsLeastAO G C) (hTop : TopForm G C) (hSizeLt : C.size < 22)
    (hJunkEx : ∃ i j, junk G C = {i, j} ∧ InCone 11 C i j)
    (hU2 : (Ustar G C).card = 2) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  subst hG
  convert main_proof_G11 C (by convert hLeast) (by convert hTop) hSizeLt
    (by convert hJunkEx) (by convert hU2)

end PEqualNP.Outside.L_meta_18390_aux.Two

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_18390_aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem small_cover_profile : ∀ K : Finset (Fin 11), K.card ≤ 3 →
    8 ≤ K.card + (MixerProof.LocalCoverProfile.missing K).card := by decide +kernel

end PEqualNP.Outside.L_meta_18390_aux

open PEqualNP.Outside.L_meta_18390_aux in
theorem PEqualNP.Outside.L_meta_18390 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 = (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size := by
  intro G decG C i j eqGraph least top junkPair path
  subst G
  have same : decG = graphDec := Subsingleton.elim _ _
  subst decG
  letI : DecidableRel listedGraph.Adj := graphDec
  dsimp only
  intro eq budget _sides
  by_contra! small
  have no4 : NoFourCycle listedGraph := by dsimp [listedGraph]; decide +kernel
  have nonempty : listedGraph.edgeFinset.Nonempty :=
    ⟨s(0,9), SimpleGraph.mem_edgeFinset.mpr (by decide : listedGraph.Adj 0 9)⟩
  obtain ⟨K,cover⟩ := residualCover C
  have cap := (Budget 11 listedGraph C no4 nonempty least top).2 K cover
  let U := Ustar listedGraph C
  let p := 2 * (centreless listedGraph C).card + (orN listedGraph C \ lam listedGraph C).card
  change 3 + p = 2 * U.card at eq
  change (tops listedGraph C \ centreless listedGraph C).card + p ≤ 4 + U.card at budget
  have total : K.card + U.card ≤ 7 := by omega
  have leThree : U.card ≤ 3 := by
    by_contra! many
    have tiny : K.card ≤ 3 := by omega
    have short := small_cover_profile K tiny
    have sub : MixerProof.LocalCoverProfile.missing K ⊆ U :=
      MixerProof.LocalCoverProfile.missing_subset cover.1
    have := Finset.card_le_card sub
    omega
  by_cases two : U.card = 2
  · have h : 2 ≤ p := Two.main_proof listedGraph C rfl least top small ⟨i,j,junkPair,path⟩ two
    omega
  · have three : U.card = 3 := by omega
    have order := Two.coneStrict C j i path
    have trace (u v : Fin 11) (he : s(u,v) ∈ U) := Two.residualTraceWithTop least top he
    exact MixerProof.LocalMatchingCircuit.four C least.1 top i j order junkPair trace three K (by omega) cover.1
