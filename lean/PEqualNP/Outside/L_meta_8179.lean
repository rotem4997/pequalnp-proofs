import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace PEqualNP.Outside.L_meta_8179

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

private def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wiresLen {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  unfold Circuit.wires Circuit.size
  have h (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega
  rw [h]
  simp

private lemma gateGet {C : Circuit} {j : ℕ} (hj : j < C.size) :
    gateAt C j = C.gates[j]'hj := by
  simp [gateAt, List.getD, List.getElem?_eq_getElem hj]

private lemma gateSpec {n : ℕ} {C : Circuit} (hc : IsAO2 n C) {j : ℕ} (hj : j < C.size) :
    ∃ (op : GateOp) (a b : ℕ), gateAt C j = ⟨op, [a, b]⟩ ∧
      (op = .and ∨ op = .or) ∧ a < n + j ∧ b < n + j := by
  have hm : gateAt C j ∈ C.gates := gateGet hj ▸ List.getElem_mem hj
  have hlen := hc.2.2 _ hm
  have ht : ∀ L : List ℕ, L.length = 2 → ∃ a b, L = [a,b] := by
    intro L h
    match L with
    | [a,b] => exact ⟨a,b,rfl⟩
    | [] | [_] | _ :: _ :: _ :: _ => simp at h
  obtain ⟨a,b,hi⟩ := ht _ hlen
  have hg : gateAt C j = ⟨(gateAt C j).op, [a,b]⟩ := by
    exact congrArg (Gate.mk (gateAt C j).op) hi
  exact ⟨_, a, b, hg, hc.1 _ hm,
    hc.2.1 j hj a (by rw [hi]; simp), hc.2.1 j hj b (by rw [hi]; simp)⟩

private def push (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.size⟩

private lemma pushSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (push n C op a b).size = C.size + 1 := by simp [push, Circuit.size]

private lemma pushLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ}
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (push n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.1 g hg
    · have e := List.mem_singleton.mp hg
      simpa [e] using hop
  · intro j hj w hw
    have hj' : j < C.size + 1 := by rw [← pushSize n C op a b]; exact hj
    rw [gateGet hj] at hw
    by_cases h : j < C.size
    · rw [show (push n C op a b).gates[j]'hj = C.gates[j]'h from
        List.getElem_append_left h] at hw
      exact hc.2.1 j h w (by rwa [gateGet h])
    · have e : j = C.size := by omega
      subst j
      have hlast : (push n C op a b).gates[C.size]'hj = ⟨op, [a,b]⟩ := by
        simp [push, Circuit.size]
      rw [hlast] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc.2.2 g hg
    · simp [List.mem_singleton.mp hg]

private lemma pushWires {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    (push n C op a b).wires (List.ofFn x) =
      C.wires (List.ofFn x) ++ [op.eval [wire C x a, wire C x b]] := by
  simp [push, Circuit.wires, List.foldl_append, wire]

private lemma pushOld {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + C.size) :
    wire (push n C op a b) x w = wire C x w := by
  unfold wire
  rw [pushWires, List.getD_append _ _ _ _ (by rwa [wiresLen])]

private lemma pushNew {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    wire (push n C op a b) x (n + C.size) = op.eval [wire C x a, wire C x b] := by
  conv_lhs => unfold wire; rw [pushWires, ← wiresLen C x]
  simp

private def firstGates (C : Circuit) (k : ℕ) : Circuit := ⟨C.gates.take k, 0⟩

private lemma prefixNext {C : Circuit} {k : ℕ} (hk : k < C.size) :
    (firstGates C (k + 1)).gates = (firstGates C k).gates ++ [gateAt C k] := by
  rw [gateGet hk]
  exact List.take_succ_eq_append_getElem hk

private lemma prefixSize {C : Circuit} {k : ℕ} (hk : k ≤ C.size) :
    (firstGates C k).size = k := by simp [firstGates, Circuit.size, Nat.min_eq_left (show k ≤ C.gates.length from hk)]

private lemma prefixOld {n k : ℕ} {C : Circuit} (hk : k < C.size) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + k) :
    wire (firstGates C (k + 1)) x w = wire (firstGates C k) x w := by
  unfold wire Circuit.wires
  rw [prefixNext hk, List.foldl_append]
  exact List.getD_append _ _ _ _ (by
    change w < ((firstGates C k).wires (List.ofFn x)).length
    rwa [wiresLen, prefixSize (Nat.le_of_lt hk)])

private lemma prefixNew {n k a b : ℕ} {C : Circuit} {op : GateOp}
    (hk : k < C.size) (hg : gateAt C k = ⟨op, [a,b]⟩) (x : Fin n → Bool) :
    wire (firstGates C (k + 1)) x (n + k) =
      op.eval [wire (firstGates C k) x a, wire (firstGates C k) x b] := by
  calc
    _ = wire (push n (firstGates C k) op a b) x (n + (firstGates C k).size) := by
      unfold wire Circuit.wires
      rw [prefixNext hk, hg, prefixSize (Nat.le_of_lt hk)]
      rfl
    _ = _ := pushNew _ _ _ _ _

private def pinned {n : ℕ} (v : Fin n) (x : Fin n → Bool) (w : Fin n) : Bool :=
  if w = v then false else x w

private def read {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : Option ℕ) : Bool :=
  w.elim false (wire C x)

private def available (bound : ℕ) (w : Option ℕ) : Prop :=
  ∀ a, w = some a → a < bound

private lemma advance {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : Option ℕ}
    (ha : available (n + C.size) a) (hb : available (n + C.size) b) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ available (n + S.size) u ∧
      C.size ≤ S.size ∧ S.size ≤ C.size + 1 ∧
      ((a = none ∨ b = none) → S.size = C.size) ∧
      (op = .and → a = none ∨ b = none → u = none) ∧
      (∀ x : Fin n → Bool, read S x u = op.eval [read C x a, read C x b]) ∧
      (∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w) := by
  cases a with
  | none =>
    rcases hop with rfl | rfl
    · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
        fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    · exact ⟨C, b, hc, hb, le_rfl, by omega, fun _ => rfl,
        by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
  | some a =>
    cases b with
    | none =>
      rcases hop with rfl | rfl
      · exact ⟨C, none, hc, by simp [available], le_rfl, by omega, fun _ => rfl,
          fun _ _ => rfl, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
      · exact ⟨C, some a, hc, ha, le_rfl, by omega, fun _ => rfl,
          by simp, by simp [read, GateOp.eval], fun _ _ _ => rfl⟩
    | some b =>
      let S := push n C op a b
      have hs : S.size = C.size + 1 := pushSize _ _ _ _ _
      refine ⟨S, some (n + C.size), pushLegal hc hop (ha _ rfl) (hb _ rfl), ?_,
        by omega, by omega, by simp, by simp, pushNew _ _ _ _, ?_⟩
      · intro w hw
        injection hw with e
        omega
      · intro x w hw
        cases w with
        | none => rfl
        | some w => exact pushOld _ _ _ _ _ (hw _ rfl)

private lemma cutPrefix {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z) :
    ∀ k ≤ C.size, ∃ (S : Circuit) (loc : ℕ → Option ℕ), IsAO2 n S ∧
      S.size + ((Finset.range k).filter (· ∈ D)).card ≤ k ∧
      (∀ w < n + k, available (n + S.size) (loc w)) ∧
      (∀ w < n + k, w ∈ Z → loc w = none) ∧
      ∀ x w, w < n + k → read S x (loc w) = wire (firstGates C k) (pinned v x) w := by
  intro k
  induction k with
  | zero =>
    intro _
    let loc (w : ℕ) : Option ℕ := if w = v.val then none else some w
    refine ⟨⟨[], 0⟩, loc, ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly],
      by simp [ReadsBack], by simp⟩, by simp [Circuit.size], ?_, ?_, ?_⟩
    · intro w hw a ha
      by_cases e : w = v.val
      · simp [loc, e] at ha
      · have : w = a := by simpa [loc, e] using ha
        simp [Circuit.size]; omega
    · intro w hw hz
      simp [loc, hzin w (by omega) hz]
    · intro x w hw
      have h : w < n := by omega
      have he : (⟨w,h⟩ : Fin n) = v ↔ w = v.val := Fin.ext_iff
      by_cases e : w = v.val <;>
        simp [loc, e, read, wire, Circuit.wires, firstGates, pinned, he, List.getD, h]
  | succ k ih =>
    intro hk
    have hk' : k < C.size := by omega
    obtain ⟨S, loc, hs, cost, av, z, ev⟩ := ih (by omega)
    obtain ⟨op, a, b, hg, hop, ha, hb⟩ := gateSpec hc hk'
    obtain ⟨T, u, ht, uav, grow, cost1, cost0, uz, eu, preserve⟩ :=
      advance hs hop (av a ha) (av b hb)
    have zeroInput (h : ∃ w ∈ (gateAt C k).inputs, w ∈ Z) :
        loc a = none ∨ loc b = none := by
      obtain ⟨w, hw, hz⟩ := h
      rw [hg] at hw
      rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
      · exact Or.inl (z _ ha hz)
      · exact Or.inr (z _ hb hz)
    let newLoc (w : ℕ) := if w = n + k then u else loc w
    refine ⟨T, newLoc, ht, ?_, ?_, ?_, ?_⟩
    · rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        have := cost0 (zeroInput (hdg k h))
        omega
      · omega
    · intro w hw q hq
      by_cases e : w = n + k
      · exact uav q (by simpa [newLoc, e] using hq)
      · have := av w (by omega) q (by simpa [newLoc, e] using hq)
        omega
    · intro w hw hz
      by_cases e : w = n + k
      · subst w
        obtain ⟨hand, hin⟩ := hzg k hk' hz
        rw [hg] at hand
        simp [newLoc, uz hand (zeroInput hin)]
      · simp [newLoc, e, z w (by omega) hz]
    · intro x w hw
      by_cases e : w = n + k
      · subst w
        simp only [newLoc, ite_eq_left rfl, eu, prefixNew hk' hg, ev x a ha, ev x b hb]
      · have hw' : w < n + k := by omega
        rw [prefixOld hk' _ hw', show newLoc w = loc w by simp [newLoc, e],
          preserve x _ (av w hw'), ev x w hw']

private lemma cutCircuit {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v : Fin n) (Z D : Finset ℕ)
    (hzin : ∀ w < n, w ∈ Z → w = v.val)
    (hzg : ∀ j < C.size, n + j ∈ Z →
      (gateAt C j).op = .and ∧ ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hdg : ∀ j ∈ D, ∃ w ∈ (gateAt C j).inputs, w ∈ Z)
    (hd : ∀ j ∈ D, j < C.size) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + D.card ≤ C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  obtain ⟨S, loc, hs, cost, av, _, ev⟩ := cutPrefix hc v Z D hzin hzg hdg _ le_rfl
  have hD : (Finset.range C.size).filter (· ∈ D) = D := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨hd _ h, h⟩⟩
  rw [hD] at cost
  by_cases ho : C.output < n + C.size
  · refine ⟨S, loc C.output, hs, cost, av _ ho, fun x => ?_⟩
    have hp : (firstGates C C.size).gates = C.gates := by simp [firstGates, Circuit.size]
    simpa only [wire, Circuit.wires, hp, circuitFun, Circuit.eval] using ev x _ ho
  · refine ⟨S, none, hs, cost, by simp [available], fun x => ?_⟩
    change false = wire C (pinned v x) C.output
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen]; omega)]

private lemma memReaders {n j k : ℕ} {C : Circuit} :
    k ∈ readers n C j ↔ k < C.size ∧ n + j ∈ (gateAt C k).inputs := by
  simp [readers, Circuit.size]

private lemma cutMany {n d : ℕ} {C : Circuit} (hc : IsAO2 n C) (v : Fin n)
    (h : let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R) :
    ∃ (S : Circuit) (u : Option ℕ), IsAO2 n S ∧ S.size + d < C.size ∧
      available (n + S.size) u ∧ ∀ x, read S x u = circuitFun n C (pinned v x) := by
  let R := readers 0 C v.val
  change d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
    (gateAt C g).op = .and ∧ ¬ readers n C g ⊆ R at h
  have hr (j) (hj : j ∈ R) : j < C.size ∧ v.val ∈ (gateAt C j).inputs := by
    simpa only [R, memReaders, Nat.zero_add] using hj
  rcases h with h | ⟨he, g, hg, hand, hsub⟩
  · obtain ⟨S,u,hs,hcst,hu,hev⟩ := cutCircuit hc v {v.val} R
      (by simp) (by intro j hj hz; simp at hz; have := v.isLt; omega)
      (fun j hj => ⟨v.val, (hr j hj).2, by simp⟩) (fun j hj => (hr j hj).1)
    exact ⟨S,u,hs,by omega,hu,hev⟩
  · obtain ⟨k,hk,hkr⟩ := Finset.not_subset.mp hsub
    have hk' := memReaders.mp hk
    have hz (w : ℕ) : w ∈ ({v.val, n + g} : Finset ℕ) ↔ w = v.val ∨ w = n + g := by simp
    obtain ⟨S,u,hs,hcst,hu,hev⟩ :=
      cutCircuit hc v {v.val, n + g} (insert k R) (by
        intro w hw hm
        rcases (hz w).mp hm with e | e
        · exact e
        · omega) (by
        intro j hj hm
        have hv := v.isLt
        have e : j = g := by rcases (hz _).mp hm with h | h <;> omega
        subst j
        exact ⟨hand, v.val, (hr _ hg).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact ⟨n + g, hk'.2, by simp⟩
        · exact ⟨v.val, (hr _ hj).2, by simp⟩) (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hk'.1
        · exact (hr _ hj).1)
    rw [Finset.card_insert_of_notMem hkr, ← he] at hcst
    exact ⟨S,u,hs,by omega,hu,hev⟩

private lemma inputWire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : Fin n) :
    wire C x a.val = x a := by
  unfold wire Circuit.wires
  have h (gs : List Gate) (w : List Bool) (hw : a.val < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        a.val false = w.getD a.val false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih, List.getD_append _ _ _ _ hw]
      simp; omega
  rw [h _ _ (by simp)]
  simp

private lemma orList {n : ℕ} {C : Circuit} (hc : IsAO2 n C) :
    ∀ (tail : List (Fin n)) (a : Fin n),
    ∃ (S : Circuit) (u : ℕ), IsAO2 n S ∧ S.size = C.size + tail.length ∧
      u < n + S.size ∧
      (∀ x : Fin n → Bool, wire S x u = (a :: tail).any x) ∧
      ∀ (x : Fin n → Bool) w, available (n + C.size) w → read S x w = read C x w := by
  intro tail
  induction tail with
  | nil =>
    intro a
    refine ⟨C, a, hc, by simp, by have := a.isLt; omega, ?_, fun _ _ _ => rfl⟩
    intro x
    simpa using inputWire C x a
  | cons b tail ih =>
    intro a
    obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := ih b
    let T := push n S .or a.val u
    have ha : a.val < n + S.size := by have := a.isLt; omega
    have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
    refine ⟨T, n + S.size, pushLegal hs (Or.inr rfl) ha hu, ?_, by omega, ?_, ?_⟩
    · simp only [ht, hlen, List.length_cons]; omega
    · intro x
      rw [show wire T x (n + S.size) = _ from pushNew S .or a.val u x, inputWire, hev]
      simp [GateOp.eval]
    · intro x w hw
      rw [← hpres x w hw]
      cases w with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hw w rfl; omega)

private def withOutput (n : ℕ) (C : Circuit) (u : Option ℕ) : Circuit :=
  ⟨C.gates, u.getD (n + C.size)⟩

private lemma withOutputLegal {n : ℕ} {C : Circuit} (hc : IsAO2 n C) (u : Option ℕ) :
    IsAO2 n (withOutput n C u) :=
  hc

private lemma withOutputEval {n : ℕ} (C : Circuit) (u : Option ℕ) (x : Fin n → Bool) :
    circuitFun n (withOutput n C u) x = read C x u := by
  cases u with
  | some u => rfl
  | none =>
    change wire C x (n + C.size) = false
    unfold wire
    rw [List.getD_eq_default _ _ (by rw [wiresLen])]

private lemma restore {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (v a : Fin n) (tail : List (Fin n)) (base : Option ℕ)
    (hb : available (n + C.size) base) :
    ∃ S : Circuit, IsAO2 n S ∧ S.size ≤ C.size + tail.length + 2 ∧
      ∀ x, circuitFun n S x = (read C x base || (x v && (a :: tail).any x)) := by
  obtain ⟨S,u,hs,hlen,hu,hev,hpres⟩ := orList hc tail a
  let T := push n S .and v.val u
  have ht : T.size = S.size + 1 := pushSize _ _ _ _ _
  have hv : v.val < n + S.size := by have := v.isLt; omega
  have ht' : IsAO2 n T := pushLegal hs (Or.inl rfl) hv hu
  have hbase : available (n + T.size) base := by
    intro w hw
    have := hb _ hw
    omega
  obtain ⟨U,out,hU,_,_,hsz,_,_,he,hp⟩ :=
    advance ht' (op := .or) (Or.inr rfl) hbase
      (show available (n + T.size) (some (n + S.size)) from by
        intro w hw; injection hw with e; omega)
  refine ⟨withOutput n U out, withOutputLegal hU _, ?_, fun x => ?_⟩
  · change U.size ≤ _
    omega
  · rw [withOutputEval, he]
    have old : read T x base = read S x base := by
      cases base with
      | none => rfl
      | some w => exact pushOld _ _ _ _ _ (by have := hb w rfl; omega)
    rw [old, hpres x _ hb]
    change GateOp.or.eval [read C x base, wire T x (n + S.size)] = _
    rw [show wire T x (n + S.size) = _ from pushNew S .and v.val u x, inputWire, hev]
    simp [GateOp.eval]

private def leftEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.1.castAdd r

private def rightEnd {l r : ℕ} (e : Fin l × Fin r) : Fin (l + r) := e.2.natAdd l

private lemma endsNe {l r : ℕ} (e f : Fin l × Fin r) : leftEnd e ≠ rightEnd f := by
  intro h
  have he := congrArg Fin.val h
  change e.1.val = l + f.2.val at he
  have := e.1.isLt
  omega

private lemma leftEq {l r : ℕ} {e f : Fin l × Fin r} (h : leftEnd e = leftEnd f) :
    e.1 = f.1 :=
  Fin.ext (congrArg (fun z : Fin (l + r) => z.val) h)

private lemma rightEq {l r : ℕ} {e f : Fin l × Fin r} (h : rightEnd e = rightEnd f) :
    e.2 = f.2 := by
  apply Fin.ext
  have he := congrArg Fin.val h
  change l + e.2.val = l + f.2.val at he
  omega

private def linked {l r : ℕ} (v w : Fin (l + r)) (e : Fin l × Fin r) : Prop :=
  v = leftEnd e ∧ w = rightEnd e ∨ w = leftEnd e ∧ v = rightEnd e

private lemma sameEdge {l r : ℕ} {v w : Fin (l + r)} {e f : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w f) : e = f := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))
  · exact (endsNe e f (ha.symm.trans hd)).elim
  · exact (endsNe f e (hc.symm.trans hb)).elim
  · exact Prod.ext (leftEq (ha.symm.trans hc)) (rightEq (hb.symm.trans hd))

private lemma sameNeighbor {l r : ℕ} {v w w' : Fin (l + r)} {e : Fin l × Fin r}
    (he : linked v w e) (hf : linked v w' e) : w = w' := by
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hf with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact hb.trans hd.symm
  · exact (endsNe e e (ha.symm.trans hd)).elim
  · exact (endsNe e e (hc.symm.trans hb)).elim
  · exact ha.trans hc.symm

private noncomputable def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Finset (Fin n) := (G.neighborSet v).toFinite.toFinset

private lemma memNeighbors {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n} :
    w ∈ neighbors G v ↔ G.Adj v w := by
  simp [neighbors]

private lemma neighborsCard {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (neighbors G v).card = (G.neighborSet v).ncard := by
  exact (Set.ncard_eq_toFinset_card _ _).symm

private lemma chooseEdge {l r : ℕ} {E M : Finset (Fin l × Fin r)}
    {G : SimpleGraph (Fin (l + r))} (v : Fin (l + r))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hd : 2 ≤ (neighbors G v).card) :
    ∃ w ∈ neighbors G v, ∃ e ∈ E, e ∉ M ∧ linked v w e := by
  obtain ⟨w, hw, z, hz, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (neighbors G v).card)
  obtain ⟨e,he,hel⟩ := (adj _ _).mp (memNeighbors.mp hw)
  obtain ⟨f,hf,hfl⟩ := (adj _ _).mp (memNeighbors.mp hz)
  by_cases hem : e ∈ M
  · refine ⟨z,hz,f,hf,?_,hfl⟩
    intro hfm
    apply hne
    have h : e = f := by
      rcases hel with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases hfl with ⟨hc,hd⟩ | ⟨hc,hd⟩
      · exact ml e hem f hfm (leftEq (ha.symm.trans hc))
      · exact (endsNe e f (ha.symm.trans hd)).elim
      · exact (endsNe f e (hc.symm.trans hb)).elim
      · exact mr e hem f hfm (rightEq (hb.symm.trans hd))
    exact sameNeighbor hel (h ▸ hfl)
  · exact ⟨w,hw,e,he,hem,hel⟩

private def onEdge {l r : ℕ} (x : Fin (l + r) → Bool) (e : Fin l × Fin r) : Prop :=
  x (leftEnd e) = true ∧ x (rightEnd e) = true

private def edgeFun {l r : ℕ} (E : Finset (Fin l × Fin r)) (x : Fin (l + r) → Bool) : Bool :=
  decide (∃ (i : Fin l) (j : Fin r), (i,j) ∈ E ∧ x (i.castAdd r) = true ∧ x (j.natAdd l) = true)

private lemma edgeTrue {l r : ℕ} {E : Finset (Fin l × Fin r)} {x : Fin (l + r) → Bool} :
    edgeFun E x = true ↔ ∃ e ∈ E, onEdge x e := by
  rw [edgeFun, decide_eq_true_iff]
  exact ⟨fun ⟨i,j,h,hx,hy⟩ => ⟨(i,j),h,hx,hy⟩,
    fun ⟨e,h,hx,hy⟩ => ⟨e.1,e.2,h,hx,hy⟩⟩

private lemma pinEdge {l r : ℕ} {e : Fin l × Fin r} {v : Fin (l + r)} {x : Fin (l + r) → Bool} :
    onEdge (pinned v x) e ↔ v ≠ leftEnd e ∧ v ≠ rightEnd e ∧ onEdge x e := by
  rw [ne_comm (a := v) (b := leftEnd e), ne_comm (a := v) (b := rightEnd e)]
  by_cases hl : leftEnd e = v <;> by_cases hr : rightEnd e = v <;>
    simp [onEdge, pinned, hl, hr]

private lemma eraseSpec {l r : ℕ} {E : Finset (Fin l × Fin r)} {G : SimpleGraph (Fin (l + r))}
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    {v w₀ : Fin (l + r)} {e₀ : Fin l × Fin r} (hl : linked v w₀ e₀)
    {x : Fin (l + r) → Bool} :
    ((∃ e ∈ E, onEdge (pinned v x) e) ∨
      x v = true ∧ ∃ w ∈ (neighbors G v).erase w₀, x w = true) ↔
      ∃ e ∈ E.erase e₀, onEdge x e := by
  constructor
  · rintro (⟨e,he,hx⟩ | ⟨hv,w,hw,hx⟩)
    · obtain ⟨ha,hb,h⟩ := pinEdge.mp hx
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, h⟩
      rintro rfl
      exact hl.elim (fun h => ha h.1) (fun h => hb h.2)
    · obtain ⟨e,he,h⟩ := (adj _ _).mp (memNeighbors.mp (Finset.mem_of_mem_erase hw))
      refine ⟨e, Finset.mem_erase.mpr ⟨?_,he⟩, ?_⟩
      · rintro rfl
        exact (Finset.mem_erase.mp hw).1 (sameNeighbor h hl)
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hv,hx⟩
        · exact ⟨hx,hv⟩
  · rintro ⟨e,he,hx⟩
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp he
    by_cases ha : v = leftEnd e
    · have h : linked v (rightEnd e) e := Or.inl ⟨ha,rfl⟩
      refine Or.inr ⟨ha.symm ▸ hx.1, rightEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.2⟩
      · intro eq
        exact hne (sameEdge (eq ▸ h) hl)
      · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
    · by_cases hb : v = rightEnd e
      · have h : linked v (leftEnd e) e := Or.inr ⟨rfl,hb⟩
        refine Or.inr ⟨hb.symm ▸ hx.2, leftEnd e, Finset.mem_erase.mpr ⟨?_,?_⟩, hx.1⟩
        · intro eq
          exact hne (sameEdge (eq ▸ h) hl)
        · exact memNeighbors.mpr ((adj _ _).mpr ⟨e,hm,h⟩)
      · exact Or.inl ⟨e,hm,pinEdge.mpr ⟨ha,hb,hx⟩⟩

private lemma solve {l r : ℕ} (E M : Finset (Fin l × Fin r)) (C : Circuit)
    (G : SimpleGraph (Fin (l + r)))
    (adj : ∀ v w, G.Adj v w ↔ ∃ e ∈ E, linked v w e)
    (hc : IsAO2 (l + r) C)
    (hev : ∀ x, circuitFun (l + r) C x = edgeFun E x)
    (ml : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (mr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (v : Fin (l + r)) (hd : 2 ≤ (G.neighborSet v).ncard)
    (h : let d := (G.neighborSet v).ncard
      let R := readers 0 C v.val
      d < R.card ∨ d = R.card ∧ ∃ g ∈ R,
        (gateAt C g).op = .and ∧ ¬ readers (l + r) C g ⊆ R) :
    ∃ e ∈ E, e ∉ M ∧ ∃ S : Circuit, S.size < C.size ∧
      IsAO2 (l + r) S ∧ ∀ x, circuitFun (l + r) S x = edgeFun (E.erase e) x := by
  let N := neighbors G v
  have hN : N.card = (G.neighborSet v).ncard := neighborsCard _ _
  have hd' : 2 ≤ N.card := by omega
  obtain ⟨w,hw,e,he,hem,hl⟩ := chooseEdge v adj ml mr hd'
  let W := N.erase w
  have hW : W.card = N.card - 1 := Finset.card_erase_of_mem hw
  have hpos : 0 < W.card := by omega
  obtain ⟨a,tail,hlist⟩ : ∃ a tail, W.toList = a :: tail := by
    cases eq : W.toList with
    | nil =>
      have hz : W.card = 0 := by rw [← Finset.length_toList, eq]; rfl
      omega
    | cons a tail => exact ⟨a,tail,rfl⟩
  have ht : W.card = tail.length + 1 := by
    rw [← Finset.length_toList, hlist]
    rfl
  obtain ⟨S,base,hs,hsz,hav,hspec⟩ := cutMany hc v h
  obtain ⟨T,ht',htsz,htspec⟩ := restore hs v a tail base hav
  refine ⟨e,he,hem,T,by omega,ht',fun x => ?_⟩
  have hAny : (a :: tail).any x = true ↔ ∃ z ∈ W, x z = true := by
    rw [← hlist, List.any_eq_true]
    simp only [Finset.mem_toList]
  apply Bool.eq_iff_iff.mpr
  rw [htspec, hspec, hev, Bool.or_eq_true, Bool.and_eq_true, edgeTrue, hAny, edgeTrue]
  exact eraseSpec adj hl

end PEqualNP.Outside.L_meta_8179

theorem PEqualNP.Outside.L_meta_8179 :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x8 → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ x7 (x3.erase x15) x16 := by
  intro l r E M C G
  dsimp only
  intro adj _ hc ml mr h
  obtain ⟨v, hd, herr⟩ := h
  exact PEqualNP.Outside.L_meta_8179.solve E M C G adj hc.1 hc.2 ml mr v hd herr
