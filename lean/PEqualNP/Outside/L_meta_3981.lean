import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3981

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def f7 (x : Fin 7 → Bool) : Bool :=
  ([1, 12, 4, 15, 26, 35, 46, 63] : List ℕ).any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))

def seed7 (x : Fin 7 → Bool) : List Bool :=
  List.ofFn x ++ [false]

def validG (n : ℕ) (t : BinaryGate) : Prop :=
  (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
  t.left < n ∧ t.right < n ∧ t.left ≠ 7 ∧ t.right ≠ 7 ∧ t.left ≠ t.right

def isNonNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

lemma isNonNot_eq : (fun (x7 : Gate) => GateOp.rec Bool.true Bool.true Bool.false (fun _ => Bool.true) Bool.true x7.op) = isNonNot := by
  funext g; cases h : g.op <;> simp [isNonNot, h]

def upd2 (x : Fin 7 → Bool) (u v : Fin 7) (bu bv : Bool) : Fin 7 → Bool :=
  Function.update (Function.update x u bu) v bv

def qSet (v : Fin 7) : List (Fin 7) :=
  match v.val with
  | 0 => [2, 1, 5, 3]
  | 1 => [0, 4, 6, 3]
  | 2 => [4, 0, 1, 5]
  | 3 => [5, 1, 2, 6]
  | 4 => [0, 1, 2, 6]
  | 5 => [0, 1, 2, 6]
  | _ => [4, 0, 1, 2]

def maskVec (s : List (Fin 7)) : Fin 7 → Bool :=
  fun w => decide (w ∈ s)

def pairProfileCard (u v : Fin 7) (s1 s2 : List (Fin 7)) : ℕ :=
  let y1 := maskVec s1
  let y2 := maskVec s2
  let pts : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
  (pts.map fun p => (f7 (upd2 y1 u v p.1 p.2), f7 (upd2 y2 u v p.1 p.2))).dedup.length

lemma f7_nonconst_fix : ∀ (i : Fin 7) (c : Bool),
    ∃ (s1 s2 : List (Fin 7)), maskVec s1 i = c ∧ maskVec s2 i = c ∧ f7 (maskVec s1) ≠ f7 (maskVec s2) := by
  intro i c
  fin_cases i <;> cases c
  · exact ⟨[], [1, 2], rfl, rfl, by decide⟩
  · exact ⟨[0], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 4], rfl, rfl, by decide⟩
  · exact ⟨[1], [1, 0], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[2], [2, 1], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[3], [3, 5], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[4], [4, 0], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[5], [5, 1], rfl, rfl, by decide⟩
  · exact ⟨[], [0, 1], rfl, rfl, by decide⟩
  · exact ⟨[6], [6, 2], rfl, rfl, by decide⟩

lemma f7_dep : ∀ i : Fin 7, ∃ s : List (Fin 7), f7 (maskVec s) ≠ f7 (Function.update (maskVec s) i (!maskVec s i)) := by
  intro i
  fin_cases i
  · exact ⟨[1], by decide⟩
  · exact ⟨[0], by decide⟩
  · exact ⟨[1], by decide⟩
  · exact ⟨[5], by decide⟩
  · exact ⟨[0], by decide⟩
  · exact ⟨[1], by decide⟩
  · exact ⟨[2], by decide⟩

lemma f7_pair_three : ∀ (u v : Fin 7), u ≠ v →
    ∃ s1 s2 : List (Fin 7),
      (∀ w ∈ s1, w ≠ u ∧ w ≠ v) ∧ (∀ w ∈ s2, w ≠ u ∧ w ≠ v) ∧
      3 ≤ pairProfileCard u v s1 s2 := by
  have hcheck : (List.finRange 7).all (fun u =>
      (List.finRange 7).all (fun v =>
        if u == v then true else
        let cands : List (List (Fin 7)) := [] :: ((List.finRange 7).filter fun w => w ≠ u ∧ w ≠ v).map (fun w => [w])
        cands.any fun s1 => cands.any fun s2 => decide (3 ≤ pairProfileCard u v s1 s2))) = true := by
    decide +kernel
  intro u v huv
  rw [List.all_eq_true] at hcheck
  have hu := hcheck u (List.mem_finRange u)
  rw [List.all_eq_true] at hu
  have hv := hu v (List.mem_finRange v)
  have hneq : (u == v) = false := beq_false_of_ne huv
  rw [hneq] at hv
  simp only [Bool.false_eq_true, ↓reduceIte] at hv
  rw [List.any_eq_true] at hv
  obtain ⟨s1, hs1, hv2⟩ := hv
  rw [List.any_eq_true] at hv2
  obtain ⟨s2, hs2, hcard⟩ := hv2
  refine ⟨s1, s2, ?_, ?_, of_decide_eq_true hcard⟩
  · rcases List.mem_cons.mp hs1 with rfl | hs1'
    · simp
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs1'
      intro z hz
      rw [List.mem_singleton.mp hz]
      exact of_decide_eq_true (List.mem_filter.mp hw).2
  · rcases List.mem_cons.mp hs2 with rfl | hs2'
    · simp
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs2'
      intro z hz
      rw [List.mem_singleton.mp hz]
      exact of_decide_eq_true (List.mem_filter.mp hw).2

lemma qSet_props : ∀ v : Fin 7,
    v ∉ qSet v ∧ (qSet v).Nodup ∧ (qSet v).length = 4 ∧
    ∀ u1 ∈ qSet v, ∀ u2 ∈ qSet v, u1 ≠ u2 →
      ∃ s1 s2 : List (Fin 7),
        (∀ w ∈ s1, w ∈ qSet v ∧ w ≠ u1 ∧ w ≠ u2) ∧
        (∀ w ∈ s2, w ∈ qSet v ∧ w ≠ u1 ∧ w ≠ u2) ∧
        3 ≤ pairProfileCard u1 u2 s1 s2 := by
  have hcheck : (List.finRange 7).all (fun v =>
      let Q := qSet v
      decide (v ∉ Q) && decide Q.Nodup && decide (Q.length = 4) &&
      Q.all (fun u1 => Q.all (fun u2 =>
        if u1 == u2 then true else
        let rem := Q.filter fun w => w ≠ u1 ∧ w ≠ u2
        let cands : List (List (Fin 7)) := [] :: rem.map (fun w => [w])
        cands.any fun s1 => cands.any fun s2 => decide (3 ≤ pairProfileCard u1 u2 s1 s2)))) = true := by
    decide +kernel
  intro v
  rw [List.all_eq_true] at hcheck
  have hv := hcheck v (List.mem_finRange v)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨hnotin, hnd⟩, hlen⟩, hall⟩ := hv
  refine ⟨hnotin, hnd, hlen, ?_⟩
  intro u1 hu1 u2 hu2 hne
  rw [List.all_eq_true] at hall
  have h1 := hall u1 hu1
  rw [List.all_eq_true] at h1
  have h2 := h1 u2 hu2
  have hneq : (u1 == u2) = false := beq_false_of_ne hne
  rw [hneq] at h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h2
  rw [List.any_eq_true] at h2
  obtain ⟨s1, hs1, h3⟩ := h2
  rw [List.any_eq_true] at h3
  obtain ⟨s2, hs2, hcard⟩ := h3
  refine ⟨s1, s2, ?_, ?_, of_decide_eq_true hcard⟩
  · rcases List.mem_cons.mp hs1 with rfl | hs1'
    · simp
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs1'
      intro z hz
      rw [List.mem_singleton.mp hz]
      have hwf := List.mem_filter.mp hw
      exact ⟨hwf.1, of_decide_eq_true hwf.2⟩
  · rcases List.mem_cons.mp hs2 with rfl | hs2'
    · simp
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs2'
      intro z hz
      rw [List.mem_singleton.mp hz]
      have hwf := List.mem_filter.mp hw
      exact ⟨hwf.1, of_decide_eq_true hwf.2⟩

lemma pigeonhole_bool (h : Bool → Bool → Bool) (F : Bool → Bool → Bool × Bool)
    (h3 : 3 ≤ ([(false, false), (false, true), (true, false), (true, true)].map fun p => F p.1 p.2).dedup.length) :
    ∃ p1 p2 : Bool × Bool, h p1.1 p1.2 = h p2.1 p2.2 ∧ F p1.1 p1.2 ≠ F p2.1 p2.2 := by
  by_contra hno
  push Not at hno
  let pts : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
  let img := (pts.map fun p => F p.1 p.2).dedup
  have hsub : img.toFinset ⊆ (({false, true} : Finset Bool).image fun b =>
      if hb : ∃ p ∈ pts, h p.1 p.2 = b then F hb.choose.1 hb.choose.2 else (false, false)) := by
    intro y hy
    rw [List.mem_toFinset, List.mem_dedup, List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    refine Finset.mem_image.mpr ⟨h p.1 p.2, by cases h p.1 p.2 <;> simp, ?_⟩
    have hex : ∃ q ∈ pts, h q.1 q.2 = h p.1 p.2 := ⟨p, hp, rfl⟩
    rw [dif_pos hex]
    exact hno hex.choose p hex.choose_spec.2
  have hcard : img.length ≤ 2 := by
    have hnd : img.Nodup := List.nodup_dedup _
    rw [← List.toFinset_card_of_nodup hnd]
    calc img.toFinset.card ≤ (({false, true} : Finset Bool).image _).card := Finset.card_le_card hsub
      _ ≤ ({false, true} : Finset Bool).card := Finset.card_image_le
      _ ≤ 2 := by decide
  have h3' : 3 ≤ img.length := h3
  omega

lemma bcWires_len (gs : List BinaryGate) (xs : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) xs).length =
      xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma bcWires_prefix (gs : List BinaryGate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
    (gs.foldl (fun ws g => ws ++ [g.op (ws.getD g.left false) (ws.getD g.right false)]) xs).getD w false =
      xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hlen : w < (xs ++ [g.op (xs.getD g.left false) (xs.getD g.right false)]).length := by
      simp; omega
    rw [ih _ hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma bcWires_append (gs1 gs2 : List BinaryGate) (xs : List Bool) :
    (BinaryCircuit.wires ⟨gs1 ++ gs2, 0⟩ xs) =
      gs2.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)])
        (BinaryCircuit.wires ⟨gs1, 0⟩ xs) := by
  unfold BinaryCircuit.wires
  exact List.foldl_append

lemma bcWires_gate (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length) (x : Fin 7 → Bool)
    (hleft : gs[j].left < 8 + j) (hright : gs[j].right < 8 + j) :
    (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (8 + j) false =
      gs[j].op ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD gs[j].left false)
               ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD gs[j].right false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    calc gs = gs.take j ++ gs.drop j := h1.symm
      _ = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by rw [h2]
      _ = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by simp
  set step : List Bool → BinaryGate → List Bool :=
    fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  set acc := (gs.take j).foldl step (seed7 x)
  have haccLen : acc.length = 8 + j := by
    rw [bcWires_len, show (seed7 x).length = 8 by simp [seed7], List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have haccAt : ∀ u < 8 + j, (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD u false = acc.getD u false := by
    intro u hu
    unfold BinaryCircuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hu2 : u < (step acc gs[j]).length := by simp [step]; omega
    rw [bcWires_prefix (gs.drop (j + 1)) _ u hu2]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
  conv_lhs => unfold BinaryCircuit.wires; rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hjlt : 8 + j < (step acc gs[j]).length := by simp [step, haccLen]
  rw [bcWires_prefix (gs.drop (j + 1)) _ (8 + j) hjlt]
  simp only [step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  simp only [List.getD_eq_getElem?_getD] at haccAt
  rw [haccAt gs[j].left hleft, haccAt gs[j].right hright]

lemma seed7_getD (x : Fin 7 → Bool) (w : ℕ) (hw : w < 7) :
    (seed7 x).getD w false = x ⟨w, hw⟩ := by
  unfold seed7
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_ofFn]
  simp [hw]

lemma seed7_getD_seven (x : Fin 7 → Bool) :
    (seed7 x).getD 7 false = false := by
  unfold seed7
  simp [List.getD_eq_getElem?_getD]

set_option maxHeartbeats 1000000 in
lemma compile_step (gs : List BinaryGate) (wireMap : List (ℕ × Bool)) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hvalid : ∀ (j : ℕ) (hj : j < gs.length), validG (8 + j) gs[j])
    (haliasBound : ∀ p ∈ wireMap, p.1 < 8 + gs.length)
    (heval : ∀ (x : Fin 7 → Bool) (ws : List Bool),
      ws.length = wireMap.length →
      (∀ w < wireMap.length, ws.getD w false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (wireMap.getD w (7, false)).1 false != (wireMap.getD w (7, false)).2)) →
      True) :
    ∃ (gs' : List BinaryGate) (p : ℕ × Bool),
      gs.length ≤ gs'.length ∧
      gs'.length ≤ gs.length + (if isNonNot g then 1 else 0) ∧
      (∀ (j : ℕ) (hj : j < gs'.length), validG (8 + j) gs'[j]) ∧
      p.1 < 8 + gs'.length ∧
      (∀ (x : Fin 7 → Bool) (w : ℕ), w < 8 + gs.length →
        (BinaryCircuit.wires ⟨gs', 0⟩ (seed7 x)).getD w false = (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD w false) ∧
      (∀ (x : Fin 7 → Bool) (ws : List Bool),
        ws.length = wireMap.length →
        (∀ w < wireMap.length, ws.getD w false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (wireMap.getD w (7, false)).1 false != (wireMap.getD w (7, false)).2)) →
        g.op.eval (g.inputs.map fun i => ws.getD i false) =
          ((BinaryCircuit.wires ⟨gs', 0⟩ (seed7 x)).getD p.1 false != p.2)) := by
  have h7val : ∀ x : Fin 7 → Bool, (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD 7 false = false := by
    intro x; unfold BinaryCircuit.wires
    rw [bcWires_prefix gs (seed7 x) 7 (by simp [seed7]), seed7_getD_seven]
  have hread : ∀ (u : ℕ) (x : Fin 7 → Bool) (ws : List Bool),
      ws.length = wireMap.length →
      (∀ w < wireMap.length, ws.getD w false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (wireMap.getD w (7, false)).1 false != (wireMap.getD w (7, false)).2)) →
      ws.getD u false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (wireMap.getD u (7, false)).1 false != (wireMap.getD u (7, false)).2) := by
    intro u x ws hlen hws
    by_cases hu : u < wireMap.length
    · exact hws u hu
    · have h1 : ws.getD u false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ u)]
      have h2 : wireMap.getD u (7, false) = (7, false) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wireMap.length ≤ u)]
      rw [h1, h2, h7val x]; rfl
  have haliasGet : ∀ u, (wireMap.getD u (7, false)).1 < 8 + gs.length := by
    intro u
    by_cases hu : u < wireMap.length
    · have hmem : wireMap.getD u (7, false) ∈ wireMap := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
        exact List.getElem_mem hu
      exact haliasBound _ hmem
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wireMap.length ≤ u), Option.getD_none]
      omega
  rcases hfan.1 with hop | hop | hop
  · have hnn : isNonNot g = true := by simp [isNonNot, hop]
    cases hgin : g.inputs with
    | nil =>
      refine ⟨gs, (7, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => ?_⟩
      rw [hop, h7val x]; rfl
    | cons u1 tl =>
      cases tl with
      | nil =>
        refine ⟨gs, wireMap.getD u1 (7, false), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
        simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact hread u1 x ws hlen hws
      | cons u2 tl2 =>
        cases tl2 with
        | nil =>
          let p1 := wireMap.getD u1 (7, false)
          let p2 := wireMap.getD u2 (7, false)
          have hp1 : p1.1 < 8 + gs.length := haliasGet u1
          have hp2 : p2.1 < 8 + gs.length := haliasGet u2
          by_cases h17 : p1.1 = 7
          · by_cases hf1 : p1.2 = false
            · refine ⟨gs, (7, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hread u1 x ws hlen hws]
              change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) && _) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD 7 false != false)
              rw [h17, hf1, h7val x]; rfl
            · refine ⟨gs, p2, le_rfl, by simp [hnn], hvalid, hp2, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
              have hf1t : p1.2 = true := by cases h : p1.2 <;> simp_all
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
              change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) && _) = _
              rw [h17, hf1t, h7val x]; rfl
          · by_cases h27 : p2.1 = 7
            · by_cases hf2 : p2.2 = false
              · refine ⟨gs, (7, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [hread u2 x ws hlen hws]
                change (_ && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD 7 false != false)
                rw [h27, hf2, h7val x]; simp
              · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                have hf2t : p2.2 = true := by cases h : p2.2 <;> simp_all
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                change (_ && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) = _
                rw [h27, hf2t, h7val x]; simp [p1]
            · by_cases heq : p1.1 = p2.1
              · by_cases hf : p1.2 = p2.2
                · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  change ((_ != p1.2) && (_ != p2.2)) = (_ != p1.2)
                  rw [heq, hf]; cases ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2) <;> rfl
                · refine ⟨gs, (7, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, h7val x]
                  change ((_ != p1.2) && (_ != p2.2)) = false
                  rw [heq]
                  cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false <;> cases h1 : p1.2 <;> cases h2 : p2.2 <;> simp_all
              · let ng : BinaryGate := ⟨fun a b => (a == !p1.2) && (b == !p2.2), p1.1, p2.1⟩
                refine ⟨gs ++ [ng], (8 + gs.length, false), by simp, by simp [hnn], ?_, by simp, ?_, ?_⟩
                · intro j hj
                  rw [List.length_append, List.length_singleton] at hj
                  by_cases hlt : j < gs.length
                  · rw [List.getElem_append_left hlt]; exact hvalid j hlt
                  · have hjeq : j = gs.length := by omega
                    subst hjeq
                    rw [List.getElem_append_right le_rfl]
                    simp only [Nat.sub_self, List.getElem_cons_zero]
                    exact ⟨⟨!p1.2, !p2.2, rfl⟩, hp1, hp2, h17, h27, heq⟩
                · intro x w hw
                  rw [bcWires_append]
                  simp only [List.foldl_cons, List.foldl_nil]
                  have hlen : w < (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).length := by
                    unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed7]; omega
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
                · intro x ws hlen hws
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.bne_false]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  rw [bcWires_append]
                  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
                  have hlenW : (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).length = 8 + gs.length := by
                    unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed7]
                  rw [List.getElem?_append_right (by omega)]
                  simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ng, ← List.getD_eq_getElem?_getD]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) =
                    (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false == !p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false == !p2.2))
                  cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false <;>
                    cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false <;>
                    cases p1.2 <;> cases p2.2 <;> rfl
        | cons _ _ =>
          have := hfan.2; rw [hgin] at this; simp at this
  · have hnn : isNonNot g = true := by simp [isNonNot, hop]
    cases hgin : g.inputs with
    | nil =>
      refine ⟨gs, (7, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => ?_⟩
      rw [hop, h7val x]; rfl
    | cons u1 tl =>
      cases tl with
      | nil =>
        refine ⟨gs, wireMap.getD u1 (7, false), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
        simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hread u1 x ws hlen hws
      | cons u2 tl2 =>
        cases tl2 with
        | nil =>
          let p1 := wireMap.getD u1 (7, false)
          let p2 := wireMap.getD u2 (7, false)
          have hp1 : p1.1 < 8 + gs.length := haliasGet u1
          have hp2 : p2.1 < 8 + gs.length := haliasGet u2
          by_cases h17 : p1.1 = 7
          · by_cases hf1 : p1.2 = true
            · refine ⟨gs, (7, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hread u1 x ws hlen hws]
              change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) || _) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD 7 false != true)
              rw [h17, hf1, h7val x]; rfl
            · refine ⟨gs, p2, le_rfl, by simp [hnn], hvalid, hp2, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
              have hf1f : p1.2 = false := by cases h : p1.2 <;> simp_all
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
              change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) || _) = _
              rw [h17, hf1f, h7val x]; rfl
          · by_cases h27 : p2.1 = 7
            · by_cases hf2 : p2.2 = true
              · refine ⟨gs, (7, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [hread u2 x ws hlen hws]
                change (_ || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD 7 false != true)
                rw [h27, hf2, h7val x]; simp
              · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                have hf2f : p2.2 = false := by cases h : p2.2 <;> simp_all
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                change (_ || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) = _
                rw [h27, hf2f, h7val x]; simp [p1]
            · by_cases heq : p1.1 = p2.1
              · by_cases hf : p1.2 = p2.2
                · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  change ((_ != p1.2) || (_ != p2.2)) = (_ != p1.2)
                  rw [heq, hf]; cases ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2) <;> rfl
                · refine ⟨gs, (7, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, h7val x]
                  change ((_ != p1.2) || (_ != p2.2)) = true
                  rw [heq]
                  cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false <;> cases h1 : p1.2 <;> cases h2 : p2.2 <;> simp_all
              · let ng : BinaryGate := ⟨fun a b => (a == p1.2) && (b == p2.2), p1.1, p2.1⟩
                refine ⟨gs ++ [ng], (8 + gs.length, true), by simp, by simp [hnn], ?_, by simp, ?_, ?_⟩
                · intro j hj
                  rw [List.length_append, List.length_singleton] at hj
                  by_cases hlt : j < gs.length
                  · rw [List.getElem_append_left hlt]; exact hvalid j hlt
                  · have hjeq : j = gs.length := by omega
                    subst hjeq
                    rw [List.getElem_append_right le_rfl]
                    simp only [Nat.sub_self, List.getElem_cons_zero]
                    exact ⟨⟨p1.2, p2.2, rfl⟩, hp1, hp2, h17, h27, heq⟩
                · intro x w hw
                  rw [bcWires_append]
                  simp only [List.foldl_cons, List.foldl_nil]
                  have hlen : w < (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).length := by
                    unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed7]; omega
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
                · intro x ws hlen hws
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  rw [bcWires_append]
                  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
                  have hlenW : (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).length = 8 + gs.length := by
                    unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed7]
                  rw [List.getElem?_append_right (by omega)]
                  simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ng, ← List.getD_eq_getElem?_getD]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false != p1.2) || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false != p2.2)) =
                    ((((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false == p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false == p2.2)) != true)
                  cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false <;>
                    cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p2.1 false <;>
                    cases p1.2 <;> cases p2.2 <;> rfl
        | cons _ _ =>
          have := hfan.2; rw [hgin] at this; simp at this
  · rw [Set.mem_singleton_iff] at hop
    have hnn : isNonNot g = false := by simp [isNonNot, hop]
    cases hgin : g.inputs with
    | nil =>
      refine ⟨gs, (7, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => ?_⟩
      rw [hop, h7val x]; rfl
    | cons u1 tl =>
      let p1 := wireMap.getD u1 (7, false)
      refine ⟨gs, (p1.1, !p1.2), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
      simp only [hop, GateOp.eval, List.map_cons, List.headD_cons]
      rw [hread u1 x ws hlen hws]
      cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p1.1 false <;> cases p1.2 <;> rfl

lemma compile_list (cgs : List Gate)
    (hfan : ∀ g ∈ cgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ (gs : List BinaryGate) (wireMap : List (ℕ × Bool)),
      gs.length ≤ cgs.countP isNonNot ∧
      wireMap.length = 7 + cgs.length ∧
      (∀ (j : ℕ) (hj : j < gs.length), validG (8 + j) gs[j]) ∧
      (∀ p ∈ wireMap, p.1 < 8 + gs.length) ∧
      ∀ (x : Fin 7 → Bool) (w : ℕ), w < 7 + cgs.length →
        (cgs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn x)).getD w false =
          ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (wireMap.getD w (7, false)).1 false != (wireMap.getD w (7, false)).2) := by
  induction cgs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (List.range 7).map fun i => (i, false), by simp, by simp, by simp, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have := List.mem_range.mp hi
      omega
    · intro x w hw
      have hw7 : w < 7 := by simp at hw; omega
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
      have h1 : (List.ofFn x)[w]?.getD false = x ⟨w, hw7⟩ := by rw [List.getElem?_ofFn]; simp [hw7]
      have h2 : ((List.range 7).map fun i => (i, false))[w]?.getD (7, false) = (w, false) := by
        simp [List.getElem?_map, List.getElem?_range hw7]
      rw [h1, h2]
      simp only [BinaryCircuit.wires, List.foldl_nil, seed7, List.getElem?_append_left (by simp [hw7] : w < (List.ofFn x).length), List.getElem?_ofFn, dif_pos hw7, Option.getD_some, Bool.bne_false]
  | append_singleton cgs g ih =>
    have hfan1 : ∀ g' ∈ cgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hfanG := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    obtain ⟨gs, wireMap, hlen, halen, hvalid, hbound, heval⟩ := ih hfan1
    obtain ⟨gs', p, hge, hlen', hvalid', hp, hpres, hstep⟩ := compile_step gs wireMap g hfanG hvalid hbound (fun _ _ _ _ => trivial)
    refine ⟨gs', wireMap ++ [p], ?_, by simp [halen]; omega, hvalid', ?_, ?_⟩
    · rw [List.countP_append, List.countP_singleton]
      omega
    · intro q hq
      rcases List.mem_append.mp hq with h1 | h2
      · have := hbound q h1; omega
      · rw [List.mem_singleton.mp h2]; exact hp
    · intro x w hw
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      set ws := cgs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn x)
      have hwsLen : ws.length = 7 + cgs.length := by
        suffices h : ∀ (l : List Gate) (acc : List Bool),
            (l.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).length = acc.length + l.length by
          rw [h, List.length_ofFn]
        intro l; induction l with
        | nil => intro acc; simp
        | cons a r ihr => intro acc; simp only [List.foldl_cons, ihr, List.length_append, List.length_cons, List.length_nil]; omega
      by_cases hlt : w < 7 + cgs.length
      · have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length)]
        have h2 : (wireMap ++ [p]).getD w (7, false) = wireMap.getD w (7, false) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < wireMap.length)]
        rw [h1, h2, heval x w hlt]
        have hpw : (wireMap.getD w (7, false)).1 < 8 + gs.length := by
          have hmem : wireMap.getD w (7, false) ∈ wireMap := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : w < wireMap.length), Option.getD_some]
            exact List.getElem_mem _
          exact hbound _ hmem
        rw [hpres x _ hpw]
      · have hweq : w = 7 + cgs.length := by simp at hw; omega
        subst hweq
        have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD (7 + cgs.length) false =
            g.op.eval (g.inputs.map fun i => ws.getD i false) := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hwsLen]
        have h2 : (wireMap ++ [p]).getD (7 + cgs.length) (7, false) = p := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [halen]
        rw [h1, h2]
        exact hstep x ws (by omega) (fun u hu => heval x u (by omega))

lemma exists_valid_le (C : Circuit) (hfan : FanInTwo C) (hfun : circuitFun 7 C = f7)
    (hcnt : C.gates.countP isNonNot ≤ 10) :
    ∃ (k : ℕ), k ≤ 10 ∧ ∃ (all : List BinaryGate) (q : Bool),
      all.length = k ∧ 1 ≤ k ∧
      (∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j]) ∧
      ∀ x : Fin 7 → Bool, (BinaryCircuit.eval ⟨all, 8 + (k - 1)⟩ (seed7 x) != q) = f7 x := by
  obtain ⟨gs, wireMap, hlen, halen, hvalid, hbound, heval⟩ := compile_list C.gates hfan
  have hnotConst : ∀ (c : Bool), ¬ (∀ x : Fin 7 → Bool, f7 x = c) := by
    intro c hc
    have h0 := hc (maskVec [])
    have h1 := hc (maskVec [0, 1])
    have : f7 (maskVec []) ≠ f7 (maskVec [0, 1]) := by decide
    exact this (h0.trans h1.symm)
  have hnotInput : ∀ (i : Fin 7) (q : Bool), ¬ (∀ x : Fin 7 → Bool, (x i != q) = f7 x) := by
    intro i q hq
    obtain ⟨s1, s2, hs1, hs2, hne⟩ := f7_nonconst_fix i false
    have h1 := hq (maskVec s1)
    have h2 := hq (maskVec s2)
    rw [hs1] at h1; rw [hs2] at h2
    exact hne (h1.symm.trans h2)
  by_cases hout : C.output < 7 + C.gates.length
  · let p := wireMap.getD C.output (7, false)
    have hp : p.1 < 8 + gs.length := by
      have hmem : p ∈ wireMap := by
        dsimp only [p]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : C.output < wireMap.length), Option.getD_some]
        exact List.getElem_mem _
      exact hbound _ hmem
    have hceval : ∀ x : Fin 7 → Bool, ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD p.1 false != p.2) = f7 x := by
      intro x
      have h1 := congrFun hfun x
      unfold circuitFun Circuit.eval Circuit.wires at h1
      rw [← h1]
      exact (heval x C.output hout).symm
    by_cases hp7 : p.1 < 7
    · exfalso
      apply hnotInput ⟨p.1, hp7⟩ p.2
      intro x
      rw [← hceval x]
      unfold BinaryCircuit.wires
      rw [bcWires_prefix gs (seed7 x) p.1 (by simp [seed7]; omega), seed7_getD x p.1 hp7]
    · by_cases hpeq7 : p.1 = 7
      · exfalso
        apply hnotConst p.2
        intro x
        rw [← hceval x, hpeq7]
        unfold BinaryCircuit.wires
        rw [bcWires_prefix gs (seed7 x) 7 (by simp [seed7]), seed7_getD_seven]
        simp
      · let idx := p.1 - 8
        have hidx : idx < gs.length := by omega
        let all := gs.take (idx + 1)
        have hallLen : all.length = idx + 1 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]
        refine ⟨idx + 1, by omega, all, p.2, hallLen, by omega, ?_, ?_⟩
        · intro j hj
          have hlt : j < gs.length := by omega
          have hget : all[j] = gs[j] := List.getElem_take
          rw [hget]
          exact hvalid j hlt
        · intro x
          rw [← hceval x]
          have hpeq : p.1 = 8 + idx := by omega
          rw [hpeq, show idx + 1 - 1 = idx by omega]
          change ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD (8 + idx) false != p.2) =
            ((BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (8 + idx) false != p.2)
          have hsplit : gs = all ++ gs.drop (idx + 1) := (List.take_append_drop (idx + 1) gs).symm
          have hsame : (BinaryCircuit.wires ⟨gs, 0⟩ (seed7 x)).getD (8 + idx) false =
              (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD (8 + idx) false := by
            conv_lhs => rw [hsplit]
            rw [bcWires_append]
            have hlenAll : 8 + idx < (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).length := by
              unfold BinaryCircuit.wires; rw [bcWires_len, hallLen]; simp [seed7]
            exact bcWires_prefix (gs.drop (idx + 1)) _ (8 + idx) hlenAll
          rw [hsame]
  · exfalso
    apply hnotConst false
    intro x
    have h1 := congrFun hfun x
    unfold circuitFun Circuit.eval Circuit.wires at h1
    rw [← h1]
    have hlenW : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length =
        7 + C.gates.length := by
      suffices h : ∀ (l : List Gate) (acc : List Bool),
          (l.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).length = acc.length + l.length by
        rw [h, List.length_ofFn]
      intro l; induction l with
      | nil => intro acc; simp
      | cons a r ihr => intro acc; simp only [List.foldl_cons, ihr, List.length_append, List.length_cons, List.length_nil]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenW]; omega)]
    rfl

def shiftWire (cut : ℕ) (w : ℕ) : ℕ :=
  if w > cut then w - 1 else w

def shiftGate (cut : ℕ) (t : BinaryGate) : BinaryGate :=
  ⟨t.op, shiftWire cut t.left, shiftWire cut t.right⟩

lemma delete_unused (all : List BinaryGate) (i : ℕ) (hi : i + 1 < all.length)
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j])
    (hunused : ∀ t ∈ all.drop (i + 1), t.left ≠ 8 + i ∧ t.right ≠ 8 + i) :
    let all' := all.take i ++ (all.drop (i + 1)).map (shiftGate (8 + i))
    all'.length = all.length - 1 ∧
    (∀ (j : ℕ) (hj : j < all'.length), validG (8 + j) all'[j]) ∧
    ∀ x : Fin 7 → Bool,
      BinaryCircuit.eval ⟨all', 8 + (all.length - 2)⟩ (seed7 x) =
      BinaryCircuit.eval ⟨all, 8 + (all.length - 1)⟩ (seed7 x) := by
  intro all'
  have hlen : all'.length = all.length - 1 := by
    simp only [all', List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  refine ⟨hlen, ?_, ?_⟩
  · intro j hj
    by_cases hlt : j < i
    · have hget : all'[j] = all[j] := by
        dsimp only [all']
        rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
      rw [hget]
      exact hvalid j (by omega)
    · have hget : all'[j] = shiftGate (8 + i) all[j + 1] := by
        dsimp only [all']
        have htl : (all.take i).length = i := by rw [List.length_take]; omega
        rw [List.getElem_append_right (by omega)]
        simp only [List.getElem_map, List.getElem_drop, htl]
        congr 2; omega
      rw [hget]
      obtain ⟨hop, hl, hr, hl7, hr7, hne⟩ := hvalid (j + 1) (by omega)
      have hmem : all[j + 1] ∈ all.drop (i + 1) := by
        have : all[j + 1] = (all.drop (i + 1))[j - i]'(by rw [List.length_drop]; omega) := by
          simp only [List.getElem_drop]; congr 1; omega
        rw [this]; exact List.getElem_mem _
      obtain ⟨hln, hrn⟩ := hunused _ hmem
      refine ⟨hop, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
      · dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
      · dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
      · dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
      · dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
  · intro x
    have hwire : ∀ w < 8 + all'.length,
        (BinaryCircuit.wires ⟨all', 0⟩ (seed7 x)).getD w false =
        (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD (if w ≥ 8 + i then w + 1 else w) false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hlt : w < 8
        · have h1 : ¬ w ≥ 8 + i := by omega
          rw [if_neg h1]
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all' (seed7 x) w (by simp [seed7]; omega),
              bcWires_prefix all (seed7 x) w (by simp [seed7]; omega)]
        · let j := w - 8
          have hj : j < all'.length := by omega
          have hwj : w = 8 + j := by omega
          by_cases hji : j < i
          · have h1 : ¬ w ≥ 8 + i := by omega
            rw [if_neg h1, hwj]
            have hget : all'[j] = all[j] := by
              dsimp only [all']
              rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
            obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j (by omega)
            rw [bcWires_gate all' j hj x (by rw [hget]; exact hl) (by rw [hget]; exact hr),
                bcWires_gate all j (by omega) x hl hr, hget]
            have hihL := ih all[j].left (by omega) (by omega)
            have hihR := ih all[j].right (by omega) (by omega)
            rw [if_neg (by omega)] at hihL
            rw [if_neg (by omega)] at hihR
            rw [hihL, hihR]
          · have h1 : w ≥ 8 + i := by omega
            rw [if_pos h1, hwj, show 8 + j + 1 = 8 + (j + 1) by omega]
            have hget : all'[j] = shiftGate (8 + i) all[j + 1] := by
              dsimp only [all']
              have htl : (all.take i).length = i := by rw [List.length_take]; omega
              rw [List.getElem_append_right (by omega)]
              simp only [List.getElem_map, List.getElem_drop, htl]
              congr 2; omega
            obtain ⟨_, hl, hr, _, _, _⟩ := hvalid (j + 1) (by omega)
            have hmem : all[j + 1] ∈ all.drop (i + 1) := by
              have : all[j + 1] = (all.drop (i + 1))[j - i]'(by rw [List.length_drop]; omega) := by
                simp only [List.getElem_drop]; congr 1; omega
              rw [this]; exact List.getElem_mem _
            obtain ⟨hln, hrn⟩ := hunused _ hmem
            have hl' : (shiftGate (8 + i) all[j + 1]).left < 8 + j := by
              dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
            have hr' : (shiftGate (8 + i) all[j + 1]).right < 8 + j := by
              dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
            rw [bcWires_gate all' j hj x (by rw [hget]; exact hl') (by rw [hget]; exact hr'),
                bcWires_gate all (j + 1) (by omega) x hl hr, hget]
            dsimp only [shiftGate] at hl' hr' ⊢
            have hihL := ih (shiftWire (8 + i) all[j + 1].left) (by omega) (by omega)
            have hihR := ih (shiftWire (8 + i) all[j + 1].right) (by omega) (by omega)
            have hinvL : (if shiftWire (8 + i) all[j + 1].left ≥ 8 + i then shiftWire (8 + i) all[j + 1].left + 1 else shiftWire (8 + i) all[j + 1].left) = all[j + 1].left := by
              dsimp only [shiftWire]; split_ifs <;> omega
            have hinvR : (if shiftWire (8 + i) all[j + 1].right ≥ 8 + i then shiftWire (8 + i) all[j + 1].right + 1 else shiftWire (8 + i) all[j + 1].right) = all[j + 1].right := by
              dsimp only [shiftWire]; split_ifs <;> omega
            rw [hinvL] at hihL; rw [hinvR] at hihR
            rw [hihL, hihR]
    unfold BinaryCircuit.eval
    have hlt : 8 + (all.length - 2) < 8 + all'.length := by omega
    have hge : 8 + (all.length - 2) ≥ 8 + i := by omega
    have hres := hwire (8 + (all.length - 2)) hlt
    rw [if_pos hge, show 8 + (all.length - 2) + 1 = 8 + (all.length - 1) by omega] at hres
    exact hres

lemma eval_indep_of_unread (all : List BinaryGate) (u : Fin 7)
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j])
    (hunread : ∀ t ∈ all, t.left ≠ u.val ∧ t.right ≠ u.val)
    (x y : Fin 7 → Bool) (hxy : ∀ w : Fin 7, w ≠ u → x w = y w) :
    ∀ w < 8 + all.length, w ≠ u.val →
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD w false =
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwu
    by_cases hlt : w < 7
    · unfold BinaryCircuit.wires
      rw [bcWires_prefix all (seed7 x) w (by simp [seed7]; omega),
          bcWires_prefix all (seed7 y) w (by simp [seed7]; omega),
          seed7_getD x w hlt, seed7_getD y w hlt]
      exact hxy ⟨w, hlt⟩ (fun h => hwu (congrArg Fin.val h))
    · by_cases h7 : w = 7
      · subst h7
        unfold BinaryCircuit.wires
        rw [bcWires_prefix all (seed7 x) 7 (by simp [seed7]),
            bcWires_prefix all (seed7 y) 7 (by simp [seed7]),
            seed7_getD_seven, seed7_getD_seven]
      · let j := w - 8
        have hj : j < all.length := by omega
        have hwj : w = 8 + j := by omega
        obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
        obtain ⟨hlu, hru⟩ := hunread all[j] (List.getElem_mem hj)
        rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
        rw [ih all[j].left (by omega) (by omega) hlu, ih all[j].right (by omega) (by omega) hru]

lemma eval_bottleneck (all : List BinaryGate) (k : ℕ) (hk : k < all.length) (u v : Fin 7)
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j])
    (hsole : ∀ (j : ℕ) (hj : j < all.length), j ≠ k →
      all[j].left ≠ u.val ∧ all[j].right ≠ u.val ∧ all[j].left ≠ v.val ∧ all[j].right ≠ v.val)
    (x y : Fin 7 → Bool) (hxy : ∀ w : Fin 7, w ≠ u → w ≠ v → x w = y w)
    (hk_eq : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD (8 + k) false =
             (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD (8 + k) false) :
    ∀ w < 8 + all.length, w ≠ u.val → w ≠ v.val →
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD w false =
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwu hwv
    by_cases hlt : w < 7
    · unfold BinaryCircuit.wires
      rw [bcWires_prefix all (seed7 x) w (by simp [seed7]; omega),
          bcWires_prefix all (seed7 y) w (by simp [seed7]; omega),
          seed7_getD x w hlt, seed7_getD y w hlt]
      exact hxy ⟨w, hlt⟩ (fun h => hwu (congrArg Fin.val h)) (fun h => hwv (congrArg Fin.val h))
    · by_cases h7 : w = 7
      · subst h7
        unfold BinaryCircuit.wires
        rw [bcWires_prefix all (seed7 x) 7 (by simp [seed7]),
            bcWires_prefix all (seed7 y) 7 (by simp [seed7]),
            seed7_getD_seven, seed7_getD_seven]
      · let j := w - 8
        have hj : j < all.length := by omega
        have hwj : w = 8 + j := by omega
        by_cases hjk : j = k
        · rw [hwj, hjk]; exact hk_eq
        · obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
          obtain ⟨hlu, hru, hlv, hrv⟩ := hsole j hj hjk
          rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
          rw [ih all[j].left (by omega) (by omega) hlu hlv, ih all[j].right (by omega) (by omega) hru hrv]

def wireSupp (all : List BinaryGate) (Q : Finset (Fin 7)) : ℕ → Finset (Fin 7) :=
  fun w =>
    (all.foldl (fun (acc : List (Finset (Fin 7))) (g : BinaryGate) =>
      acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅])
      (List.ofFn (fun i : Fin 7 => if i ∈ Q then {i} else ∅) ++ [∅])).getD w ∅

lemma wireSupp_len (all : List BinaryGate) (Q : Finset (Fin 7)) :
    (all.foldl (fun (acc : List (Finset (Fin 7))) (g : BinaryGate) =>
      acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅])
      (List.ofFn (fun i : Fin 7 => if i ∈ Q then {i} else ∅) ++ [∅])).length = 8 + all.length := by
  suffices h : ∀ (l : List BinaryGate) (acc : List (Finset (Fin 7))),
      (l.foldl (fun acc g => acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅]) acc).length = acc.length + l.length by
    rw [h]; simp
  intro l; induction l with
  | nil => intro acc; simp
  | cons g r ih => intro acc; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega

lemma wireSupp_prefix (l : List BinaryGate) (acc : List (Finset (Fin 7))) (w : ℕ) (hw : w < acc.length) :
    (l.foldl (fun acc g => acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅]) acc).getD w ∅ = acc.getD w ∅ := by
  induction l generalizing acc with
  | nil => rfl
  | cons g r ih =>
    simp only [List.foldl_cons]
    have hlen : w < (acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅]).length := by simp; omega
    rw [ih _ hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

lemma wireSupp_input (all : List BinaryGate) (Q : Finset (Fin 7)) (w : ℕ) (hw : w < 7) :
    wireSupp all Q w = if (⟨w, hw⟩ : Fin 7) ∈ Q then {⟨w, hw⟩} else ∅ := by
  unfold wireSupp
  rw [wireSupp_prefix all _ w (by simp; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_ofFn]
  simp [hw]

lemma wireSupp_seven (all : List BinaryGate) (Q : Finset (Fin 7)) :
    wireSupp all Q 7 = ∅ := by
  unfold wireSupp
  rw [wireSupp_prefix all _ 7 (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma wireSupp_gate (all : List BinaryGate) (Q : Finset (Fin 7)) (j : ℕ) (hj : j < all.length)
    (hl : all[j].left < 8 + j) (hr : all[j].right < 8 + j) :
    wireSupp all Q (8 + j) = wireSupp all Q all[j].left ∪ wireSupp all Q all[j].right := by
  unfold wireSupp
  set step : List (Finset (Fin 7)) → BinaryGate → List (Finset (Fin 7)) :=
    fun acc g => acc ++ [acc.getD g.left ∅ ∪ acc.getD g.right ∅]
  set base : List (Finset (Fin 7)) := List.ofFn (fun i : Fin 7 => if i ∈ Q then ({i} : Finset (Fin 7)) else ∅) ++ [∅]
  have hsplit : all = all.take j ++ [all[j]] ++ all.drop (j + 1) := by
    have h1 : all.take j ++ all.drop j = all := List.take_append_drop j all
    have h2 : all.drop j = all[j] :: all.drop (j + 1) := List.drop_eq_getElem_cons hj
    calc all = all.take j ++ all.drop j := h1.symm
      _ = all.take j ++ (all[j] :: all.drop (j + 1)) := by rw [h2]
      _ = all.take j ++ [all[j]] ++ all.drop (j + 1) := by simp
  set acc := (all.take j).foldl step base
  have haccLen : acc.length = 8 + j := by
    have h := wireSupp_len (all.take j) Q
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h
    exact h
  have haccAt : ∀ u < 8 + j, (all.foldl step base).getD u ∅ = acc.getD u ∅ := by
    intro u hu
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hu2 : u < (step acc all[j]).length := by simp [step]; omega
    rw [wireSupp_prefix (all.drop (j + 1)) _ u hu2]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hjlt : 8 + j < (step acc all[j]).length := by simp [step, haccLen]
  rw [wireSupp_prefix (all.drop (j + 1)) _ (8 + j) hjlt]
  simp only [step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  simp only [step, List.getD_eq_getElem?_getD] at haccAt
  rw [haccAt all[j].left hl, haccAt all[j].right hr]

lemma wire_eq_of_agree_on_supp (all : List BinaryGate) (Q : Finset (Fin 7))
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j])
    (x y : Fin 7 → Bool) (hOutQ : ∀ w : Fin 7, w ∉ Q → x w = y w) :
    ∀ w < 8 + all.length, (∀ u ∈ wireSupp all Q w, x u = y u) →
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD w false =
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hag
    by_cases hlt : w < 7
    · unfold BinaryCircuit.wires
      rw [bcWires_prefix all (seed7 x) w (by simp [seed7]; omega),
          bcWires_prefix all (seed7 y) w (by simp [seed7]; omega),
          seed7_getD x w hlt, seed7_getD y w hlt]
      by_cases hQ : (⟨w, hlt⟩ : Fin 7) ∈ Q
      · exact hag ⟨w, hlt⟩ (by rw [wireSupp_input all Q w hlt, if_pos hQ]; exact Finset.mem_singleton_self _)
      · exact hOutQ ⟨w, hlt⟩ hQ
    · by_cases h7 : w = 7
      · subst h7
        unfold BinaryCircuit.wires
        rw [bcWires_prefix all (seed7 x) 7 (by simp [seed7]),
            bcWires_prefix all (seed7 y) 7 (by simp [seed7]),
            seed7_getD_seven, seed7_getD_seven]
      · let j := w - 8
        have hj : j < all.length := by omega
        have hwj : w = 8 + j := by omega
        obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
        rw [hwj, wireSupp_gate all Q j hj hl hr] at hag
        rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
        rw [ih all[j].left (by omega) (by omega) (fun u hu => hag u (Finset.mem_union_left _ hu)),
            ih all[j].right (by omega) (by omega) (fun u hu => hag u (Finset.mem_union_right _ hu))]

def reaches (all : List BinaryGate) : ℕ → ℕ → ℕ → Prop
  | 0, a, b => a = b
  | n + 1, a, b =>
    a = b ∨
    (∃ (j : ℕ) (hj : j < all.length), b = 8 + j ∧
      (reaches all n a all[j].left ∨ reaches all n a all[j].right))

lemma reaches_le (all : List BinaryGate)
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j]) :
    ∀ (n a b : ℕ), reaches all n a b → a ≤ b := by
  intro n
  induction n with
  | zero => intro a b h; simp [reaches] at h; omega
  | succ n ih =>
    intro a b h
    rcases h with rfl | ⟨j, hj, rfl, hL | hR⟩
    · exact le_rfl
    · have := ih _ _ hL; have := (hvalid j hj).2.1; omega
    · have := ih _ _ hR; have := (hvalid j hj).2.2.1; omega

lemma reaches_has_reader (all : List BinaryGate)
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j]) :
    ∀ (n a b : ℕ), reaches all n a b → a < b →
      ∃ (j : ℕ) (hj : j < all.length), 8 + j ≤ b ∧ (all[j].left = a ∨ all[j].right = a) := by
  intro n
  induction n with
  | zero => intro a b h hlt; simp [reaches] at h; omega
  | succ n ih =>
    intro a b h hlt
    rcases h with rfl | ⟨j, hj, rfl, hL | hR⟩
    · omega
    · by_cases ha : a = all[j].left
      · exact ⟨j, hj, le_rfl, Or.inl ha.symm⟩
      · have hle := reaches_le all hvalid n a all[j].left hL
        have hltL : a < all[j].left := by omega
        obtain ⟨j', hj', hle', hread⟩ := ih a all[j].left hL hltL
        have := (hvalid j hj).2.1
        exact ⟨j', hj', by omega, hread⟩
    · by_cases ha : a = all[j].right
      · exact ⟨j, hj, le_rfl, Or.inr ha.symm⟩
      · have hle := reaches_le all hvalid n a all[j].right hR
        have hltR : a < all[j].right := by omega
        obtain ⟨j', hj', hle', hread⟩ := ih a all[j].right hR hltR
        have := (hvalid j hj).2.2.1
        exact ⟨j', hj', by omega, hread⟩

lemma count_ge_two_of_two_readers (all : List BinaryGate) (z a b : ℕ)
    (ha : a < all.length) (hb : b < all.length) (hab : a ≠ b)
    (hza : all[a].left = z ∨ all[a].right = z) (hzb : all[b].left = z ∨ all[b].right = z) :
    2 ≤ (all.flatMap fun t => [t.left, t.right]).count z := by
  induction all generalizing a b with
  | nil => simp at ha
  | cons t r ih =>
    simp only [List.flatMap_cons, List.count_append]
    have h1 : ∀ (u : BinaryGate), (u.left = z ∨ u.right = z) → 1 ≤ [u.left, u.right].count z := by
      intro u hu
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      rcases hu with rfl | rfl <;> split_ifs <;> omega
    cases a with
    | zero =>
      cases b with
      | zero => exact False.elim (hab rfl)
      | succ b' =>
        have hza' := h1 t hza
        have hmem : r[b']'(by simp at hb; omega) ∈ r := List.getElem_mem _
        have hzb' : 0 < (r.flatMap fun t => [t.left, t.right]).count z := by
          rw [List.count_pos_iff, List.mem_flatMap]
          refine ⟨r[b']'(by simp at hb; omega), hmem, ?_⟩
          simp only [List.getElem_cons_succ] at hzb
          rcases hzb with h | h <;> simp [h]
        omega
    | succ a' =>
      cases b with
      | zero =>
        have hzb' := h1 t hzb
        have hmem : r[a']'(by simp at ha; omega) ∈ r := List.getElem_mem _
        have hza' : 0 < (r.flatMap fun t => [t.left, t.right]).count z := by
          rw [List.count_pos_iff, List.mem_flatMap]
          refine ⟨r[a']'(by simp at ha; omega), hmem, ?_⟩
          simp only [List.getElem_cons_succ] at hza
          rcases hza with h | h <;> simp [h]
        omega
      | succ b' =>
        have := ih a' b' (by simp at ha; omega) (by simp at hb; omega) (by omega) hza hzb
        omega

lemma tree_bottleneck (all : List BinaryGate) (Q : Finset (Fin 7))
    (hvalid : ∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j])
    (honce : ∀ w, (∃ hw : w < 7, (⟨w, hw⟩ : Fin 7) ∈ Q) ∨ (8 ≤ w ∧ w < 8 + all.length) →
      (all.flatMap fun t => [t.left, t.right]).count w ≤ 1)
    (k : ℕ) (hk : k < all.length)
    (x y : Fin 7 → Bool)
    (hxy : ∀ w : Fin 7, w ∉ wireSupp all Q (8 + k) → x w = y w)
    (hk_eq : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD (8 + k) false =
             (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD (8 + k) false) :
    ∀ w < 8 + all.length,
      (¬ (w < 8 + k ∧ (wireSupp all Q w ∩ wireSupp all Q (8 + k)).Nonempty)) →
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x)).getD w false =
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 y)).getD w false := by
  have hSuppMem : ∀ (w : ℕ), w < 8 + all.length → ∀ u ∈ wireSupp all Q w,
      u ∈ Q ∧ (w = u.val ∨ 8 ≤ w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw u hu
      by_cases hlt : w < 7
      · rw [wireSupp_input all Q w hlt] at hu
        split_ifs at hu with hQ
        · have heq : u = ⟨w, hlt⟩ := Finset.mem_singleton.mp hu
          exact ⟨heq ▸ hQ, Or.inl (congrArg Fin.val heq).symm⟩
        · exact False.elim (Finset.notMem_empty u hu)
      · by_cases h7 : w = 7
        · rw [h7, wireSupp_seven] at hu; exact False.elim (Finset.notMem_empty u hu)
        · let j := w - 8
          have hj : j < all.length := by omega
          have hwj : w = 8 + j := by omega
          obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
          rw [hwj, wireSupp_gate all Q j hj hl hr, Finset.mem_union] at hu
          rcases hu with hL | hR
          · exact ⟨(ih all[j].left (by omega) (by omega) u hL).1, Or.inr (by omega)⟩
          · exact ⟨(ih all[j].right (by omega) (by omega) u hR).1, Or.inr (by omega)⟩
  have hChain : ∀ (u : Fin 7) (w2 w1 : ℕ), w2 < 8 + all.length → w1 ≤ w2 →
      u ∈ wireSupp all Q w1 → u ∈ wireSupp all Q w2 → ∃ n, reaches all n w1 w2 := by
    intro u w2
    induction w2 using Nat.strong_induction_on with
    | ind w2 ih =>
      intro w1 hw2 hle hu1 hu2
      by_cases heq : w1 = w2
      · exact ⟨0, heq⟩
      · have hlt : w1 < w2 := by omega
        obtain ⟨huQ, hw1case⟩ := hSuppMem w1 (by omega) u hu1
        obtain ⟨_, hw2case⟩ := hSuppMem w2 hw2 u hu2
        have hw2ge8 : 8 ≤ w2 := by
          rcases hw2case with rfl | h8
          · rcases hw1case with rfl | h8'
            · omega
            · have := u.isLt; omega
          · exact h8
        let j := w2 - 8
        have hj : j < all.length := by omega
        have hw2j : w2 = 8 + j := by omega
        obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
        rw [hw2j, wireSupp_gate all Q j hj hl hr, Finset.mem_union] at hu2
        have hstep : ∀ c, c < 8 + j → (all[j].left = c ∨ all[j].right = c) → u ∈ wireSupp all Q c →
            ∃ n, reaches all n w1 w2 := by
          intro c hc hread huc
          by_cases hwc : w1 ≤ c
          · obtain ⟨n, hn⟩ := ih c (by omega) w1 (by omega) hwc hu1 huc
            refine ⟨n + 1, Or.inr ⟨j, hj, hw2j, ?_⟩⟩
            rcases hread with hL | hR
            · exact Or.inl (hL ▸ hn)
            · exact Or.inr (hR ▸ hn)
          · have hcw : c < w1 := by omega
            obtain ⟨n, hn⟩ := ih w1 (by omega) c (by omega) (by omega) huc hu1
            obtain ⟨j', hj', hle', hread'⟩ := reaches_has_reader all hvalid n c w1 hn hcw
            have hne : j' ≠ j := by omega
            have h2 := count_ge_two_of_two_readers all c j' j hj' hj hne hread' hread
            obtain ⟨_, hcCase⟩ := hSuppMem c (by omega) u huc
            have h1 : (all.flatMap fun t => [t.left, t.right]).count c ≤ 1 := by
              apply honce
              rcases hcCase with rfl | h8c
              · exact Or.inl ⟨u.isLt, huQ⟩
              · exact Or.inr ⟨h8c, by omega⟩
            omega
        rcases hu2 with hL | hR
        · exact hstep all[j].left hl (Or.inl rfl) hL
        · exact hstep all[j].right hr (Or.inr rfl) hR
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnot
    by_cases hwk : w = 8 + k
    · rw [hwk]; exact hk_eq
    · by_cases hdisj : (wireSupp all Q w ∩ wireSupp all Q (8 + k)).Nonempty
      · have hwgt : 8 + k < w := by
          by_contra hle; exact hnot ⟨by omega, hdisj⟩
        let j := w - 8
        have hj : j < all.length := by omega
        have hwj : w = 8 + j := by omega
        obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
        have hchildOk : ∀ c, c < 8 + j → (all[j].left = c ∨ all[j].right = c) →
            ¬ (c < 8 + k ∧ (wireSupp all Q c ∩ wireSupp all Q (8 + k)).Nonempty) := by
          intro c hc hread ⟨hck, ⟨u, hu⟩⟩
          obtain ⟨huc, huk⟩ := Finset.mem_inter.mp hu
          obtain ⟨huQ, hcCase⟩ := hSuppMem c (by omega) u huc
          obtain ⟨n, hn⟩ := hChain u (8 + k) c (by omega) (by omega) huc huk
          obtain ⟨j', hj', hle', hread'⟩ := reaches_has_reader all hvalid n c (8 + k) hn hck
          have hne : j' ≠ j := by omega
          have h2 := count_ge_two_of_two_readers all c j' j hj' hj hne hread' hread
          have h1 : (all.flatMap fun t => [t.left, t.right]).count c ≤ 1 := by
            apply honce
            rcases hcCase with rfl | h8c
            · exact Or.inl ⟨u.isLt, huQ⟩
            · exact Or.inr ⟨h8c, by omega⟩
          omega
        rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
        rw [ih all[j].left (by omega) (by omega) (hchildOk _ hl (Or.inl rfl)),
            ih all[j].right (by omega) (by omega) (hchildOk _ hr (Or.inr rfl))]
      · have hQsub : wireSupp all Q (8 + k) ⊆ Q := fun u hu => (hSuppMem (8 + k) (by omega) u hu).1
        apply wire_eq_of_agree_on_supp all Q hvalid x y (fun u huQ => hxy u (fun huk => huQ (hQsub huk))) w hw
        intro u huw
        apply hxy u
        intro huk
        exact hdisj ⟨u, Finset.mem_inter.mpr ⟨huw, huk⟩⟩

lemma main (C : Circuit) (hfan : FanInTwo C) (hfun : circuitFun 7 C = f7)
    (hcnt : C.gates.countP isNonNot ≤ 10) :
    ∃ (gs : List BinaryGate) (g : BinaryGate) (q : Bool),
      let p := (gs ++ [g]).flatMap fun t => [t.left, t.right]
      7 ≤ gs.length ∧ gs.length ≤ 9 ∧
      (∀ (j : ℕ) (hj : j < gs.length), validG (8 + j) gs[j]) ∧
      validG (8 + gs.length) g ∧ 8 ≤ g.left ∧ 8 ≤ g.right ∧
      (∀ i < gs.length, ∃ t ∈ (gs ++ [g]).drop (i + 1), t.left = 8 + i ∨ t.right = 8 + i) ∧
      12 ≤ gs.length + ((Finset.range 7).filter (fun i => p.count i = 1)).card ∧
      (∀ h ∈ gs ++ [g], h.left < 7 → h.right < 7 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1) ∧
      ∀ x : Fin 7 → Bool, ((BinaryCircuit.eval ⟨gs ++ [g], 8 + gs.length⟩ (seed7 x)) != q) = f7 x := by
  classical
  let Good (k : ℕ) : Prop :=
    1 ≤ k ∧ ∃ (all : List BinaryGate) (q : Bool),
      all.length = k ∧
      (∀ (j : ℕ) (hj : j < all.length), validG (8 + j) all[j]) ∧
      ∀ x : Fin 7 → Bool, (BinaryCircuit.eval ⟨all, 8 + (k - 1)⟩ (seed7 x) != q) = f7 x
  have hex : ∃ k, Good k := by
    obtain ⟨k, _, all, q, hall, hk1, hval, hev⟩ := exists_valid_le C hfan hfun hcnt
    exact ⟨k, hk1, all, q, hall, hval, hev⟩
  have hle10 : Nat.find hex ≤ 10 := by
    obtain ⟨k, hk10, all, q, hall, hk1, hval, hev⟩ := exists_valid_le C hfan hfun hcnt
    exact (Nat.find_min' hex ⟨hk1, all, q, hall, hval, hev⟩).trans hk10
  obtain ⟨hk1, all, q, hall, hvalid, heval⟩ := Nat.find_spec hex
  have hmin : ∀ k < all.length, ¬ Good k := by
    intro k hk
    rw [hall] at hk
    exact Nat.find_min hex hk
  have hall_ne : all ≠ [] := by intro h; rw [h] at hall; simp at hall; omega
  let gs := all.dropLast
  let g := all.getLast hall_ne
  have hsplit : all = gs ++ [g] := (List.dropLast_append_getLast hall_ne).symm
  have hgs_len : gs.length = all.length - 1 := List.length_dropLast
  have hgs_le9 : gs.length ≤ 9 := by omega
  have hgs_valid : ∀ (j : ℕ) (hj : j < gs.length), validG (8 + j) gs[j] := by
    intro j hj
    have h1 : all[j]'(by omega) = gs[j] := by
      conv_lhs => simp only [hsplit]
      exact List.getElem_append_left hj
    rw [← h1]
    exact hvalid j (by omega)
  have hg_eq : all[gs.length]'(by omega) = g := by
    conv_lhs => simp only [hsplit]
    rw [List.getElem_append_right le_rfl]
    simp
  have hg_valid : validG (8 + gs.length) g := by
    rw [← hg_eq]
    exact hvalid gs.length (by omega)
  have heval' : ∀ x : Fin 7 → Bool, (BinaryCircuit.eval ⟨gs ++ [g], 8 + gs.length⟩ (seed7 x) != q) = f7 x := by
    intro x
    rw [← hsplit, hgs_len, hall]
    exact heval x
  have hg_inputs : 8 ≤ g.left ∧ 8 ≤ g.right := by
    obtain ⟨⟨a, b, hop⟩, hl, hr, hl7, hr7, _⟩ := hg_valid
    constructor
    · by_contra hlt
      have hlt7 : g.left < 7 := by omega
      obtain ⟨s1, s2, hs1, hs2, hne⟩ := f7_nonconst_fix ⟨g.left, hlt7⟩ (!a)
      have hconst : ∀ s : List (Fin 7), maskVec s ⟨g.left, hlt7⟩ = !a → f7 (maskVec s) = q := by
        intro s hs
        rw [← heval' (maskVec s), ← hsplit]
        change ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD (8 + gs.length) false != q) = q
        rw [bcWires_gate all gs.length (by omega) (maskVec s) (by rw [hg_eq]; exact hl) (by rw [hg_eq]; exact hr)]
        rw [hg_eq, hop]
        have hread : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD g.left false = !a := by
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed7 (maskVec s)) g.left (by simp [seed7]; omega), seed7_getD _ g.left hlt7, hs]
        rw [hread]
        cases a <;> simp
      exact hne ((hconst s1 hs1).trans (hconst s2 hs2).symm)
    · by_contra hlt
      have hlt7 : g.right < 7 := by omega
      obtain ⟨s1, s2, hs1, hs2, hne⟩ := f7_nonconst_fix ⟨g.right, hlt7⟩ (!b)
      have hconst : ∀ s : List (Fin 7), maskVec s ⟨g.right, hlt7⟩ = !b → f7 (maskVec s) = q := by
        intro s hs
        rw [← heval' (maskVec s), ← hsplit]
        change ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD (8 + gs.length) false != q) = q
        rw [bcWires_gate all gs.length (by omega) (maskVec s) (by rw [hg_eq]; exact hl) (by rw [hg_eq]; exact hr)]
        rw [hg_eq, hop]
        have hread : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD g.right false = !b := by
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed7 (maskVec s)) g.right (by simp [seed7]; omega), seed7_getD _ g.right hlt7, hs]
        rw [hread]
        cases b <;> simp
      exact hne ((hconst s1 hs1).trans (hconst s2 hs2).symm)
  have hused : ∀ i < gs.length, ∃ t ∈ (gs ++ [g]).drop (i + 1), t.left = 8 + i ∨ t.right = 8 + i := by
    intro i hi
    by_contra hno
    push Not at hno
    rw [← hsplit] at hno
    have hi' : i + 1 < all.length := by omega
    obtain ⟨hlen', hval', hev'⟩ := delete_unused all i hi' hvalid hno
    have hgood' : Good (all.length - 1) := by
      refine ⟨by omega, _, q, hlen', hval', fun x => ?_⟩
      rw [show all.length - 1 - 1 = all.length - 2 by omega, hev' x, hall]
      exact heval x
    exact hmin (all.length - 1) (by omega) hgood'
  let p := all.flatMap fun t => [t.left, t.right]
  have hp_len : p.length = 2 * gs.length + 2 := by
    have hlen2 : (all.flatMap fun t => [t.left, t.right]).length = 2 * all.length := by
      induction all with
      | nil => simp
      | cons _ r ih => simp [ih]; omega
    change (all.flatMap fun t => [t.left, t.right]).length = 2 * gs.length + 2
    rw [hlen2]; omega
  have hp_in_pos : ∀ i < 7, 1 ≤ p.count i := by
    intro i hi
    by_contra h0
    have hc0 : p.count i = 0 := by omega
    have hunread : ∀ t ∈ all, t.left ≠ i ∧ t.right ≠ i := by
      intro t ht
      have hnotin : i ∉ p := List.count_eq_zero.mp hc0
      constructor <;> intro h <;> apply hnotin <;> rw [List.mem_flatMap] <;> exact ⟨t, ht, by simp [h]⟩
    obtain ⟨s, hs⟩ := f7_dep ⟨i, hi⟩
    have hsame : BinaryCircuit.eval ⟨all, 8 + gs.length⟩ (seed7 (maskVec s)) =
        BinaryCircuit.eval ⟨all, 8 + gs.length⟩ (seed7 (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩))) := by
      change (BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD (8 + gs.length) false =
        (BinaryCircuit.wires ⟨all, 0⟩ (seed7 (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩)))).getD (8 + gs.length) false
      apply eval_indep_of_unread all ⟨i, hi⟩ hvalid hunread
      · intro w hw; simp [Function.update, hw]
      · omega
      · dsimp; omega
    have h1 := heval' (maskVec s)
    have h2 := heval' (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩))
    rw [← hsplit] at h1 h2
    rw [hsame] at h1
    exact hs (h1.symm.trans h2)
  have hp_gate_pos : ∀ i < gs.length, 1 ≤ p.count (8 + i) := by
    intro i hi
    obtain ⟨t, ht, hread⟩ := hused i hi
    rw [← hsplit] at ht
    have htmem : t ∈ all := List.mem_of_mem_drop ht
    have hpos : 0 < p.count (8 + i) := by
      rw [List.count_pos_iff]
      exact List.mem_flatMap.mpr ⟨t, htmem, by rcases hread with h | h <;> simp [h]⟩
    omega
  have hsum_count : ∀ (S : Finset ℕ), ∑ w ∈ S, p.count w ≤ p.length := by
    intro S
    have h1 : ∀ (l : List ℕ), ∑ w ∈ S, l.count w ≤ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a r ih =>
        simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
        have h2 : ∑ w ∈ S, (if a == w then 1 else 0) ≤ 1 := by
          by_cases ha : a ∈ S
          · rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hba; simp [beq_false_of_ne (Ne.symm hba)]
            · intro h; exact False.elim (h ha)
          · rw [Finset.sum_eq_zero]
            · omega
            · intro b hb
              have hne : a ≠ b := fun h => ha (h ▸ hb)
              simp [beq_false_of_ne hne]
        omega
    exact h1 p
  let R1 := (Finset.range 7).filter fun i => p.count i = 1
  let R2 := (Finset.range 7).filter fun i => p.count i ≠ 1
  let Gset := (Finset.range gs.length).image fun i => 8 + i
  have hR12_card : R1.card + R2.card = 7 := by
    have hu : R1 ∪ R2 = Finset.range 7 := by
      ext w; simp only [R1, R2, Finset.mem_union, Finset.mem_filter]; tauto
    have hd : Disjoint R1 R2 := by
      rw [Finset.disjoint_left]; intro w h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]
  have hDisj_7_G : Disjoint (Finset.range 7) Gset := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have := Finset.mem_range.mp hw1
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw2
    omega
  have hCountBound : 12 ≤ gs.length + R1.card := by
    have hsumAll := hsum_count (Finset.range 7 ∪ Gset)
    rw [Finset.sum_union hDisj_7_G] at hsumAll
    have hsumG : gs.length ≤ ∑ w ∈ Gset, p.count w := by
      rw [Finset.sum_image (fun _ _ _ _ h => by omega)]
      calc gs.length = ∑ _i ∈ Finset.range gs.length, 1 := by simp
        _ ≤ ∑ i ∈ Finset.range gs.length, p.count (8 + i) :=
          Finset.sum_le_sum fun i hi => hp_gate_pos i (Finset.mem_range.mp hi)
    have hpart7 : ∑ w ∈ Finset.range 7, p.count w = ∑ w ∈ R1, p.count w + ∑ w ∈ R2, p.count w := by
      have hu : R1 ∪ R2 = Finset.range 7 := by
        ext w; simp only [R1, R2, Finset.mem_union, Finset.mem_filter]; tauto
      have hd : Disjoint R1 R2 := by
        rw [Finset.disjoint_left]; intro w h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw [← hu, Finset.sum_union hd]
    have hsumR1 : ∑ w ∈ R1, p.count w = R1.card := by
      calc ∑ w ∈ R1, p.count w = ∑ _w ∈ R1, 1 := Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2
        _ = R1.card := by simp
    have hsumR2 : 2 * R2.card ≤ ∑ w ∈ R2, p.count w := by
      calc 2 * R2.card = ∑ _w ∈ R2, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ w ∈ R2, p.count w := by
          apply Finset.sum_le_sum
          intro w hw
          have h1 := hp_in_pos w (Finset.mem_range.mp (Finset.mem_filter.mp hw).1)
          have h2 := (Finset.mem_filter.mp hw).2
          omega
    omega
  have hNoPairR1 : ∀ h ∈ all, h.left < 7 → h.right < 7 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1 := by
    intro h hh hltL hltR
    by_contra hboth
    push Not at hboth
    obtain ⟨hcL, hcR⟩ := hboth
    obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hh
    have hneLR : (⟨h.left, hltL⟩ : Fin 7) ≠ ⟨h.right, hltR⟩ := by
      intro heq
      have := (hvalid k hk).2.2.2.2.2
      rw [hget] at this
      exact this (congrArg Fin.val heq)
    have hsole : ∀ (j : ℕ) (hj : j < all.length), j ≠ k →
        all[j].left ≠ h.left ∧ all[j].right ≠ h.left ∧ all[j].left ≠ h.right ∧ all[j].right ≠ h.right := by
      intro j hj hjk
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq; have h2 := count_ge_two_of_two_readers all h.left j k hj hk hjk (Or.inl heq) (Or.inl (by rw [hget])); change 2 ≤ p.count h.left at h2; omega
      · intro heq; have h2 := count_ge_two_of_two_readers all h.left j k hj hk hjk (Or.inr heq) (Or.inl (by rw [hget])); change 2 ≤ p.count h.left at h2; omega
      · intro heq; have h2 := count_ge_two_of_two_readers all h.right j k hj hk hjk (Or.inl heq) (Or.inr (by rw [hget])); change 2 ≤ p.count h.right at h2; omega
      · intro heq; have h2 := count_ge_two_of_two_readers all h.right j k hj hk hjk (Or.inr heq) (Or.inr (by rw [hget])); change 2 ≤ p.count h.right at h2; omega
    let u : Fin 7 := ⟨h.left, hltL⟩
    let v : Fin 7 := ⟨h.right, hltR⟩
    obtain ⟨s1, s2, hs1, hs2, hcard3⟩ := f7_pair_three u v hneLR
    let F : Bool → Bool → Bool × Bool := fun bu bv =>
      (f7 (upd2 (maskVec s1) u v bu bv), f7 (upd2 (maskVec s2) u v bu bv))
    obtain ⟨p1, p2, hopEq, hFne⟩ := pigeonhole_bool h.op F hcard3
    have hagree : ∀ (s : List (Fin 7)),
        f7 (upd2 (maskVec s) u v p1.1 p1.2) = f7 (upd2 (maskVec s) u v p2.1 p2.2) := by
      intro s
      let x1 := upd2 (maskVec s) u v p1.1 p1.2
      let x2 := upd2 (maskVec s) u v p2.1 p2.2
      have hxy : ∀ w : Fin 7, w ≠ u → w ≠ v → x1 w = x2 w := by
        intro w hwu hwv; simp [x1, x2, upd2, Function.update, hwu, hwv]
      have hk_eq : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x1)).getD (8 + k) false =
          (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x2)).getD (8 + k) false := by
        obtain ⟨_, hl, hr, _, _, _⟩ := hvalid k hk
        rw [bcWires_gate all k hk x1 hl hr, bcWires_gate all k hk x2 hl hr, hget]
        unfold BinaryCircuit.wires
        rw [bcWires_prefix all (seed7 x1) h.left (by simp [seed7]; omega),
            bcWires_prefix all (seed7 x1) h.right (by simp [seed7]; omega),
            bcWires_prefix all (seed7 x2) h.left (by simp [seed7]; omega),
            bcWires_prefix all (seed7 x2) h.right (by simp [seed7]; omega),
            seed7_getD x1 h.left hltL, seed7_getD x1 h.right hltR,
            seed7_getD x2 h.left hltL, seed7_getD x2 h.right hltR]
        have hu1 : x1 u = p1.1 := by dsimp only [x1, upd2]; rw [Function.update_of_ne hneLR, Function.update_self]
        have hv1 : x1 v = p1.2 := by dsimp only [x1, upd2]; rw [Function.update_self]
        have hu2 : x2 u = p2.1 := by dsimp only [x2, upd2]; rw [Function.update_of_ne hneLR, Function.update_self]
        have hv2 : x2 v = p2.2 := by dsimp only [x2, upd2]; rw [Function.update_self]
        change h.op (x1 u) (x1 v) = h.op (x2 u) (x2 v)
        rw [hu1, hv1, hu2, hv2]
        exact hopEq
      have hsame := eval_bottleneck all k hk u v hvalid hsole x1 x2 hxy hk_eq (8 + gs.length) (by omega) (by omega) (by omega)
      have e1 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 x1)).getD (8 + gs.length) false != q) = f7 x1 := by
        have := heval' x1; rw [← hsplit] at this; exact this
      have e2 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 x2)).getD (8 + gs.length) false != q) = f7 x2 := by
        have := heval' x2; rw [← hsplit] at this; exact this
      rw [hsame] at e1
      exact e1.symm.trans e2
    exact hFne (Prod.ext (hagree s1) (hagree s2))
  have hR1_le_gs : R1.card ≤ gs.length := by
    have hmap : ∀ i ∈ R1, ∃ j, ∃ hj : j < gs.length, gs[j].left = i ∨ gs[j].right = i := by
      intro i hi
      have hc1 : p.count i = 1 := (Finset.mem_filter.mp hi).2
      have hmem : i ∈ p := List.count_pos_iff.mp (by omega)
      rw [List.mem_flatMap] at hmem
      obtain ⟨t, ht, hti⟩ := hmem
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      have hjlt : j < gs.length := by
        by_contra hge
        have hjeq : j = gs.length := by omega
        subst hjeq
        rw [hg_eq] at hti
        have hi7 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
        rcases hti with rfl | rfl <;> omega
      have hget : gs[j] = all[j] := by
        conv_rhs => simp only [hsplit]
        exact (List.getElem_append_left hjlt).symm
      refine ⟨j, hjlt, ?_⟩
      rw [hget]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
      exact hti.imp Eq.symm Eq.symm
    let f : ℕ → ℕ := fun i => if h : i ∈ R1 then (hmap i h).choose else 0
    have hsub : R1.image f ⊆ Finset.range gs.length := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      dsimp only [f]
      rw [dif_pos hi]
      exact Finset.mem_range.mpr (hmap i hi).choose_spec.1
    have hinj : Set.InjOn f (R1 : Set ℕ) := by
      intro i1 hi1' i2 hi2' heq
      have hi1 : i1 ∈ R1 := Finset.mem_coe.mp hi1'
      have hi2 : i2 ∈ R1 := Finset.mem_coe.mp hi2'
      dsimp only [f] at heq
      rw [dif_pos hi1, dif_pos hi2] at heq
      set j := (hmap i1 hi1).choose
      have hj : j < gs.length := (hmap i1 hi1).choose_spec.1
      have h1 : gs[j].left = i1 ∨ gs[j].right = i1 := (hmap i1 hi1).choose_spec.2
      have h2 : gs[j].left = i2 ∨ gs[j].right = i2 := by
        have h2' := (hmap i2 hi2).choose_spec.2
        simpa only [← heq] using h2'
      by_contra hne
      have hmem : gs[j] ∈ all := by rw [hsplit]; exact List.mem_append_left _ (List.getElem_mem hj)
      have hi1lt := Finset.mem_range.mp (Finset.mem_filter.mp hi1).1
      have hi2lt := Finset.mem_range.mp (Finset.mem_filter.mp hi2).1
      have hc1 := (Finset.mem_filter.mp hi1).2
      have hc2 := (Finset.mem_filter.mp hi2).2
      rcases h1 with hL1 | hR1 <;> rcases h2 with hL2 | hR2
      · exact hne (hL1.symm.trans hL2)
      · rcases hNoPairR1 gs[j] hmem (by omega) (by omega) with h | h
        · rw [hL1] at h; exact h hc1
        · rw [hR2] at h; exact h hc2
      · rcases hNoPairR1 gs[j] hmem (by omega) (by omega) with h | h
        · rw [hL2] at h; exact h hc2
        · rw [hR1] at h; exact h hc1
      · exact hne (hR1.symm.trans hR2)
    calc R1.card = (R1.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range gs.length).card := Finset.card_le_card hsub
      _ = gs.length := Finset.card_range _
  have hgs_ge7 : 7 ≤ gs.length := by
    by_contra hlt7
    have hgs6 : gs.length = 6 := by omega
    have hR1_6 : R1.card = 6 := by omega
    have hR2_1 : R2.card = 1 := by omega
    obtain ⟨vstar_n, hvstar⟩ := Finset.card_eq_one.mp hR2_1
    have hvstar_mem : vstar_n ∈ R2 := by rw [hvstar]; exact Finset.mem_singleton_self _
    have hvstar_lt : vstar_n < 7 := Finset.mem_range.mp (Finset.mem_filter.mp hvstar_mem).1
    let vstar : Fin 7 := ⟨vstar_n, hvstar_lt⟩
    have hGateCount1 : ∀ i < gs.length, p.count (8 + i) = 1 := by
      have hsumAll := hsum_count (Finset.range 7 ∪ Gset)
      rw [Finset.sum_union hDisj_7_G] at hsumAll
      have hpart7 : ∑ w ∈ Finset.range 7, p.count w = ∑ w ∈ R1, p.count w + ∑ w ∈ R2, p.count w := by
        have hu : R1 ∪ R2 = Finset.range 7 := by
          ext w; simp only [R1, R2, Finset.mem_union, Finset.mem_filter]; tauto
        have hd : Disjoint R1 R2 := by
          rw [Finset.disjoint_left]; intro w h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        rw [← hu, Finset.sum_union hd]
      have hsumR1 : ∑ w ∈ R1, p.count w = 6 := by
        calc ∑ w ∈ R1, p.count w = ∑ _w ∈ R1, 1 := Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2
          _ = R1.card := by simp
          _ = 6 := hR1_6
      have hsumR2 : 2 ≤ ∑ w ∈ R2, p.count w := by
        rw [hvstar, Finset.sum_singleton]
        have h1 := hp_in_pos vstar_n hvstar_lt
        have h2 := (Finset.mem_filter.mp hvstar_mem).2
        omega
      have hsumG_le : ∑ i ∈ Finset.range gs.length, p.count (8 + i) ≤ 6 := by
        rw [Finset.sum_image (fun _ _ _ _ h => by omega)] at hsumAll
        omega
      intro i hi
      by_contra hne1
      have hge2 : 2 ≤ p.count (8 + i) := by have := hp_gate_pos i hi; omega
      have hsum_ge7 : 7 ≤ ∑ j ∈ Finset.range gs.length, p.count (8 + j) := by
        have hsplitS := Finset.add_sum_erase (Finset.range gs.length) (fun j => p.count (8 + j)) (Finset.mem_range.mpr hi)
        have hrest : 5 ≤ ∑ j ∈ (Finset.range gs.length).erase i, p.count (8 + j) := by
          calc 5 = ((Finset.range gs.length).erase i).card := by
                rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hi), Finset.card_range]; omega
            _ = ∑ _j ∈ (Finset.range gs.length).erase i, 1 := by simp
            _ ≤ ∑ j ∈ (Finset.range gs.length).erase i, p.count (8 + j) :=
                Finset.sum_le_sum fun j hj => hp_gate_pos j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
        omega
      omega
    obtain ⟨hvnotin, hqnd, hqlen, hqpairs⟩ := qSet_props vstar
    let Q : Finset (Fin 7) := (qSet vstar).toFinset
    have hQcard : Q.card = 4 := by rw [List.toFinset_card_of_nodup hqnd, hqlen]
    have honce : ∀ w, (∃ hw : w < 7, (⟨w, hw⟩ : Fin 7) ∈ Q) ∨ (8 ≤ w ∧ w < 8 + all.length) → p.count w ≤ 1 := by
      intro w hw
      rcases hw with ⟨hwlt, hwQ⟩ | ⟨h8, hwlt⟩
      · have hne : w ≠ vstar_n := by
          intro heq
          apply hvnotin
          have hv_eq : vstar = ⟨w, hwlt⟩ := Fin.ext heq.symm
          have hmem : (⟨w, hwlt⟩ : Fin 7) ∈ qSet vstar := List.mem_toFinset.mp hwQ
          rw [← hv_eq] at hmem
          exact hmem
        have hwR1 : w ∈ R1 := by
          by_contra hnotR1
          have hwR2 : w ∈ R2 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, fun h => hnotR1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, h⟩)⟩
          rw [hvstar, Finset.mem_singleton] at hwR2
          exact hne hwR2
        have := (Finset.mem_filter.mp hwR1).2
        omega
      · by_cases hlast : w = 8 + gs.length
        · have h0 : p.count w = 0 := by
            rw [List.count_eq_zero]
            intro hmem
            rw [List.mem_flatMap] at hmem
            obtain ⟨t, ht, htw⟩ := hmem
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
            obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at htw
            rcases htw with rfl | rfl <;> omega
          omega
        · have hi : w - 8 < gs.length := by omega
          have := hGateCount1 (w - 8) hi
          rw [show 8 + (w - 8) = w by omega] at this
          omega
    have hOutSupp : Q ⊆ wireSupp all Q (8 + gs.length) := by
      intro u huQ
      by_contra hnotin
      obtain ⟨s, hs⟩ := f7_dep u
      have hsame := wire_eq_of_agree_on_supp all Q hvalid (maskVec s)
        (Function.update (maskVec s) u (!maskVec s u))
        (fun w hwQ => by simp [Function.update, show w ≠ u from fun h => hwQ (h ▸ huQ)])
        (8 + gs.length) (by omega)
        (fun w hw => by simp [Function.update, show w ≠ u from fun h => hnotin (h ▸ hw)])
      have e1 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 (maskVec s))).getD (8 + gs.length) false != q) = f7 (maskVec s) := by
        have := heval' (maskVec s); rw [← hsplit] at this; exact this
      have e2 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 (Function.update (maskVec s) u (!maskVec s u)))).getD (8 + gs.length) false != q) =
          f7 (Function.update (maskVec s) u (!maskVec s u)) := by
        have := heval' (Function.update (maskVec s) u (!maskVec s u)); rw [← hsplit] at this; exact this
      rw [hsame] at e1
      exact hs (e1.symm.trans e2)
    have hex2 : ∃ k, k < all.length ∧ 2 ≤ (wireSupp all Q (8 + k)).card := by
      refine ⟨gs.length, by omega, ?_⟩
      have := Finset.card_le_card hOutSupp
      omega
    let k0 := Nat.find hex2
    obtain ⟨hk0, hk0_2⟩ := Nat.find_spec hex2
    obtain ⟨_, hl0, hr0, _, _, _⟩ := hvalid k0 hk0
    have hL_le1 : (wireSupp all Q all[k0].left).card ≤ 1 := by
      by_cases hlt : all[k0].left < 7
      · rw [wireSupp_input all Q all[k0].left hlt]; split_ifs <;> simp
      · by_cases h7 : all[k0].left = 7
        · rw [h7, wireSupp_seven]; simp
        · have hj : all[k0].left - 8 < k0 := by omega
          have hnot := Nat.find_min hex2 hj
          push Not at hnot
          have := hnot (by omega)
          rw [show 8 + (all[k0].left - 8) = all[k0].left by omega] at this
          omega
    have hR_le1 : (wireSupp all Q all[k0].right).card ≤ 1 := by
      by_cases hlt : all[k0].right < 7
      · rw [wireSupp_input all Q all[k0].right hlt]; split_ifs <;> simp
      · by_cases h7 : all[k0].right = 7
        · rw [h7, wireSupp_seven]; simp
        · have hj : all[k0].right - 8 < k0 := by omega
          have hnot := Nat.find_min hex2 hj
          push Not at hnot
          have := hnot (by omega)
          rw [show 8 + (all[k0].right - 8) = all[k0].right by omega] at this
          omega
    have hUeq := wireSupp_gate all Q k0 hk0 hl0 hr0
    have hUle := Finset.card_union_le (wireSupp all Q all[k0].left) (wireSupp all Q all[k0].right)
    rw [hUeq] at hk0_2
    have hL1 : (wireSupp all Q all[k0].left).card = 1 := by omega
    have hR1' : (wireSupp all Q all[k0].right).card = 1 := by omega
    obtain ⟨u1, hu1⟩ := Finset.card_eq_one.mp hL1
    obtain ⟨u2, hu2⟩ := Finset.card_eq_one.mp hR1'
    have hSupp0 : wireSupp all Q (8 + k0) = {u1, u2} := by
      rw [hUeq, hu1, hu2]; ext z; simp
    have hu12 : u1 ≠ u2 := by
      intro heq; rw [← hUeq, hSupp0, heq, Finset.pair_eq_singleton] at hk0_2; simp at hk0_2
    have hu1Q : u1 ∈ qSet vstar := by
      rw [← List.mem_toFinset]
      have hmem : u1 ∈ wireSupp all Q all[k0].left := by rw [hu1]; exact Finset.mem_singleton_self _
      have hsub : ∀ w < 8 + all.length, wireSupp all Q w ⊆ Q := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hlt : w < 7
          · rw [wireSupp_input all Q w hlt]; split_ifs with hQ
            · exact Finset.singleton_subset_iff.mpr hQ
            · exact Finset.empty_subset _
          · by_cases h7 : w = 7
            · rw [h7, wireSupp_seven]; exact Finset.empty_subset _
            · let j := w - 8
              have hj : j < all.length := by omega
              have hwj : w = 8 + j := by omega
              obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
              rw [hwj, wireSupp_gate all Q j hj hl hr]
              exact Finset.union_subset (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
      exact hsub all[k0].left (by omega) hmem
    have hu2Q : u2 ∈ qSet vstar := by
      rw [← List.mem_toFinset]
      have hmem : u2 ∈ wireSupp all Q all[k0].right := by rw [hu2]; exact Finset.mem_singleton_self _
      have hsub : ∀ w < 8 + all.length, wireSupp all Q w ⊆ Q := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hlt : w < 7
          · rw [wireSupp_input all Q w hlt]; split_ifs with hQ
            · exact Finset.singleton_subset_iff.mpr hQ
            · exact Finset.empty_subset _
          · by_cases h7 : w = 7
            · rw [h7, wireSupp_seven]; exact Finset.empty_subset _
            · let j := w - 8
              have hj : j < all.length := by omega
              have hwj : w = 8 + j := by omega
              obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
              rw [hwj, wireSupp_gate all Q j hj hl hr]
              exact Finset.union_subset (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
      exact hsub all[k0].right (by omega) hmem
    obtain ⟨s1, s2, hs1, hs2, hcard3⟩ := hqpairs u1 hu1Q u2 hu2Q hu12
    let hfun0 : Bool → Bool → Bool := fun bu bv =>
      (BinaryCircuit.wires ⟨all, 0⟩ (seed7 (upd2 (maskVec []) u1 u2 bu bv))).getD (8 + k0) false
    let F : Bool → Bool → Bool × Bool := fun bu bv =>
      (f7 (upd2 (maskVec s1) u1 u2 bu bv), f7 (upd2 (maskVec s2) u1 u2 bu bv))
    obtain ⟨p1, p2, hEq0, hFne⟩ := pigeonhole_bool hfun0 F hcard3
    have hagree : ∀ (s : List (Fin 7)), (∀ w ∈ s, w ∈ qSet vstar ∧ w ≠ u1 ∧ w ≠ u2) →
        f7 (upd2 (maskVec s) u1 u2 p1.1 p1.2) = f7 (upd2 (maskVec s) u1 u2 p2.1 p2.2) := by
      intro s hs
      let x1 := upd2 (maskVec s) u1 u2 p1.1 p1.2
      let x2 := upd2 (maskVec s) u1 u2 p2.1 p2.2
      have hxy : ∀ w : Fin 7, w ∉ wireSupp all Q (8 + k0) → x1 w = x2 w := by
        intro w hw
        rw [hSupp0, Finset.mem_insert, Finset.mem_singleton] at hw
        push Not at hw
        simp [x1, x2, upd2, Function.update, hw.1, hw.2]
      have hk_x1 : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x1)).getD (8 + k0) false = hfun0 p1.1 p1.2 := by
        apply wire_eq_of_agree_on_supp all Q hvalid x1 (upd2 (maskVec []) u1 u2 p1.1 p1.2)
        · intro w hwQ
          have hwnot : w ∉ s := fun hws => hwQ (List.mem_toFinset.mpr (hs w hws).1)
          simp [x1, upd2, Function.update, maskVec, hwnot]
        · omega
        · intro w hw
          rw [hSupp0, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [x1, upd2, Function.update, hu12]
          · simp [x1, upd2, Function.update]
      have hk_x2 : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x2)).getD (8 + k0) false = hfun0 p2.1 p2.2 := by
        apply wire_eq_of_agree_on_supp all Q hvalid x2 (upd2 (maskVec []) u1 u2 p2.1 p2.2)
        · intro w hwQ
          have hwnot : w ∉ s := fun hws => hwQ (List.mem_toFinset.mpr (hs w hws).1)
          simp [x2, upd2, Function.update, maskVec, hwnot]
        · omega
        · intro w hw
          rw [hSupp0, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [x2, upd2, Function.update, hu12]
          · simp [x2, upd2, Function.update]
      have hk_eq : (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x1)).getD (8 + k0) false =
          (BinaryCircuit.wires ⟨all, 0⟩ (seed7 x2)).getD (8 + k0) false :=
        hk_x1.trans (hEq0.trans hk_x2.symm)
      have hsame := tree_bottleneck all Q hvalid honce k0 hk0 x1 x2 hxy hk_eq (8 + gs.length) (by omega) (by omega)
      have e1 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 x1)).getD (8 + gs.length) false != q) = f7 x1 := by
        have := heval' x1; rw [← hsplit] at this; exact this
      have e2 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed7 x2)).getD (8 + gs.length) false != q) = f7 x2 := by
        have := heval' x2; rw [← hsplit] at this; exact this
      rw [hsame] at e1
      exact e1.symm.trans e2
    exact hFne (Prod.ext (hagree s1 hs1) (hagree s2 hs2))
  refine ⟨gs, g, q, hgs_ge7, hgs_le9, hgs_valid, hg_valid, hg_inputs.1, hg_inputs.2, hused, ?_, ?_, heval'⟩
  · have hR1eq : R1 = (Finset.range 7).filter (fun x12 => List.count x12 ((gs ++ [g]).flatMap fun t => [t.left, t.right]) = 1) := by
      ext w; simp only [R1, p, Finset.mem_filter, hsplit]
    rw [← hR1eq]
    exact hCountBound
  · intro h hh hl hr
    have h1 := hNoPairR1 h (hsplit.symm ▸ hh) hl hr
    dsimp only [p] at h1
    rw [hsplit] at h1
    exact h1

end PEqualNP.Outside.L_meta_3981

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_3981 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (63 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (7 : ℕ) → Bool) → List Bool := fun (x2 : Fin (7 : ℕ) → Bool) => List.ofFn x2 ++ [Bool.false]; have x3 : ℕ → PEqualNP.MetaComplexity.BinaryGate → Prop := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryGate) => (∃ (x5 : Bool) (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) ∧ x4.left < x3 ∧ x4.right < x3 ∧ x4.left ≠ (7 : ℕ) ∧ x4.right ≠ (7 : ℕ) ∧ x4.left ≠ x4.right; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x4 →     PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x4 = x1 →       List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x8 : ℕ) => Bool.true) Bool.true x7.op) x4.gates ≤ (10 : ℕ) →         ∃ (x8 : List PEqualNP.MetaComplexity.BinaryGate) (x9 : PEqualNP.MetaComplexity.BinaryGate) (x10 : Bool),           have x11 : List ℕ := List.flatMap (fun (x11 : PEqualNP.MetaComplexity.BinaryGate) => [x11.left, x11.right]) (x8 ++ [x9]);           (7 : ℕ) ≤ x8.length ∧ x8.length ≤ (9 : ℕ) ∧ (∀ (x12 : ℕ) (x13 : x12 < x8.length), x3 ((8 : ℕ) + x12) x8[x12]) ∧ x3 ((8 : ℕ) + x8.length) x9 ∧ (8 : ℕ) ≤ x9.left ∧ (8 : ℕ) ≤ x9.right ∧ (∀ x12 < x8.length, ∃ x14 ∈ List.drop (x12 + (1 : ℕ)) (x8 ++ [x9]), x14.left = (8 : ℕ) + x12 ∨ x14.right = (8 : ℕ) + x12) ∧ (12 : ℕ) ≤ x8.length + {x12 ∈ Finset.range (7 : ℕ) | List.count x12 x11 = (1 : ℕ)}.card ∧ (∀ x12 ∈ x8 ++ [x9], x12.left < (7 : ℕ) → x12.right < (7 : ℕ) → List.count x12.left x11 ≠ (1 : ℕ) ∨ List.count x12.right x11 ≠ (1 : ℕ)) ∧ ∀ (x12 : Fin (7 : ℕ) → Bool), ({ gates := x8 ++ [x9], output := (8 : ℕ) + x8.length : PEqualNP.MetaComplexity.BinaryCircuit }.eval (x2 x12) != x10) = x1 x12 := by
  dsimp only
  intro C hfan hfun hcnt
  rw [PEqualNP.Outside.L_meta_3981.isNonNot_eq] at hcnt
  exact PEqualNP.Outside.L_meta_3981.main C hfan hfun hcnt

