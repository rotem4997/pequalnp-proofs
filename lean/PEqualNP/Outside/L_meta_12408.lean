import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408

open PEqualNP.CircuitLowerBounds

abbrev Point := Fin 14
abbrev Bit := Fin 4
abbrev Pair := Fin 6
abbrev Block := Finset Point
abbrev Config := Pair → Fin 5

def target (v : Bit) : Block :=
  Finset.univ.filter fun p => (p.val + 1).testBit v.val

def left (p : Pair) : Bit := (![0, 0, 0, 1, 1, 2] : Pair → Bit) p

def right (p : Pair) : Bit := (![1, 2, 3, 2, 3, 3] : Pair → Bit) p

def point0 (p : Pair) : Point := (![2, 4, 8, 5, 9, 11] : Pair → Point) p

def point1 (p : Pair) : Point := (![6, 6, 10, 6, 10, 12] : Pair → Point) p

def point2 (p : Pair) : Point := (![10, 12, 12, 13, 13, 13] : Pair → Point) p

def space (p : Pair) : Block := {point0 p, point1 p, point2 p}

def candidate (p : Pair) (i : Fin 5) : Block :=
  (![∅, {point0 p, point1 p}, {point0 p, point2 p}, {point1 p, point2 p},
    space p] : Fin 5 → Block) i

def incident (v : Bit) : Fin 3 → Pair :=
  (![![0, 1, 2], ![0, 3, 4], ![1, 3, 5], ![2, 4, 5]] : Bit → Fin 3 → Pair) v

theorem target_card : ∀ v, (target v).card = 7 := by decide +kernel

theorem space_exact : ∀ p, space p = target (left p) ∩ target (right p) := by decide +kernel

theorem pair_overlap : ∀ p q : Pair, p ≠ q → (space p ∩ space q).card ≤ 1 := by decide +kernel

theorem find_pair : ∀ v w : Bit, v ≠ w →
    ∃ p : Pair, space p = target v ∩ target w := by decide +kernel

theorem incident_exact : ∀ v p, v = left p ∨ v = right p ↔ ∃ j : Fin 3, incident v j = p := by
  decide +kernel

theorem unrelated : ∀ v p, v ≠ left p → v ≠ right p → (target v ∩ space p).card ≤ 1 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem two_choice (p : Pair) (S : Block) (hin : S ⊆ space p) (hcard : S.card = 2) :
    ∃ i : Fin 5, (i = 1 ∨ i = 2 ∨ i = 3) ∧ candidate p i = S := by
  obtain ⟨a, b, hne, rfl⟩ := Finset.card_eq_two.mp hcard
  have h : ∀ p : Pair, ∀ a b : Point, a ≠ b → a ∈ space p → b ∈ space p →
      ∃ i : Fin 5, (i = 1 ∨ i = 2 ∨ i = 3) ∧ candidate p i = {a, b} := by
    decide +kernel
  exact h p a b hne (hin (by simp)) (hin (by simp))

def shared (p : Pair) (S : Block) : Prop := 2 ≤ S.card ∧ S ⊆ space p

def owned (v : Bit) (S : Block) : Prop :=
  2 ≤ S.card ∧ S ⊆ target v ∧ ∀ p, ¬ shared p S

theorem shared_unique {S : Block} {p q : Pair} (hp : shared p S) (hq : shared q S) : p = q := by
  by_contra he
  have h := Finset.card_le_card (Finset.subset_inter hp.2 hq.2)
  have hc := pair_overlap p q he
  have hs := hp.1
  omega

theorem owned_unique {S : Block} {v w : Bit} (hv : owned v S) (hw : owned w S) : v = w := by
  by_contra he
  obtain ⟨p, hp⟩ := find_pair v w he
  apply hv.2.2 p
  exact ⟨hv.1, by rw [hp]; exact Finset.subset_inter hv.2.1 hw.2.1⟩

def qualifies (t : Bit ⊕ Pair) (S : Block) : Prop :=
  t.elim (fun v => owned v S) (fun p => shared p S)

def passes (t : Bit ⊕ Pair) (S : Block) : Bool :=
  match t with
  | .inl v => decide (2 ≤ S.card ∧ S ⊆ target v ∧ ∀ p : Pair, ¬ (2 ≤ S.card ∧ S ⊆ space p))
  | .inr p => decide (2 ≤ S.card ∧ S ⊆ space p)

theorem passes_spec {t : Bit ⊕ Pair} {S : Block} : passes t S = true ↔ qualifies t S := by
  cases t <;> simp [passes, qualifies, owned, shared]

theorem qualifies_unique {S : Block} {t u : Bit ⊕ Pair}
    (ht : qualifies t S) (hu : qualifies u S) : t = u := by
  cases t with
  | inl v =>
    cases u with
    | inl w => exact congrArg Sum.inl (owned_unique ht hu)
    | inr q => exact (ht.2.2 q hu).elim
  | inr p =>
    cases u with
    | inl w => exact (hu.2.2 p ht).elim
    | inr q => exact congrArg Sum.inr (shared_unique ht hu)

def count (xs : List Block) (t : Bit ⊕ Pair) : ℕ :=
  (xs.filter fun S => passes t S).length

theorem count_cons (xs : List Block) (S : Block) (t : Bit ⊕ Pair) :
    count (S :: xs) t = (if passes t S then 1 else 0) + count xs t := by
  cases h : passes t S <;> simp [count, h, Nat.add_comm]

theorem count_append (xs ys : List Block) (t : Bit ⊕ Pair) :
    count (xs ++ ys) t = count xs t + count ys t := by
  simp [count, List.filter_append]

theorem count_pos {xs : List Block} {t : Bit ⊕ Pair} {S : Block}
    (hS : S ∈ xs) (ht : qualifies t S) : 0 < count xs t := by
  have hm : S ∈ xs.filter (fun B => passes t B) := by simp [hS, passes_spec.mpr ht]
  have hn : (xs.filter (fun B => passes t B)).length ≠ 0 := by
    intro ho
    have := List.length_eq_zero_iff.mp ho
    rw [this] at hm
    contradiction
  exact Nat.pos_of_ne_zero hn

theorem total_count (xs : List Block) : (∑ t, count xs t) ≤ xs.length := by
  induction xs with
  | nil => simp [count]
  | cons S xs ih =>
    have htag : (Finset.univ.filter fun t => passes t S).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro t ht u hu
      exact qualifies_unique (passes_spec.mp (Finset.mem_filter.mp ht).2) (passes_spec.mp (Finset.mem_filter.mp hu).2)
    have heq : (∑ t : Bit ⊕ Pair, (if passes t S then 1 else 0 : ℕ)) =
        (Finset.univ.filter fun t => passes t S).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [count_cons, Finset.sum_add_distrib, List.length_cons, heq]
    omega

def charge (c : Fin 5) : ℕ := if c = 0 then 0 else if c = 4 then 2 else 1

def grant (v : Bit) (c : Fin 3 → Fin 5) (j : Fin 3) : Block :=
  candidate (incident v j) (c j)

def abstractScore (v : Bit) (c : Fin 3 → Fin 5) : ℕ :=
  ((Finset.univ : Finset (Fin 3)).powerset).sup fun J =>
    (J.biUnion (grant v c)).card - J.card

-- Packed maxima for the eight subsets of each of the three incident choices.
def maxima (v : Bit) : ℕ := (![32981548652233736993140356314473831153225166566970796205030857397848329088799022379776247966222260737314488885832, 32981548652233736993140356314473831153225166566970796205030857397848329088799022379776247966222260737314488885832, 32981548652233736993140356314473831153225166566970796205030857397848329088799022379776247966222260737314488885832, 32981548652233736993140356314473831153225166566970796205030857397848329088799022379776247966222260737314488885832] : Bit → ℕ) v

def localScore (v : Bit) (c : Fin 3 → Fin 5) : ℕ :=
  let k := (c 0).val + 5 * (c 1).val + 25 * (c 2).val
  (maxima v >>> (3 * k)) &&& 7

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem scores_agree : ∀ v c, localScore v c = abstractScore v c := by
  decide +kernel

def score (c : Config) (v : Bit) : ℕ := localScore v (fun j => c (incident v j))

def bound (c : Config) : ℕ := (∑ p, charge (c p)) + ∑ v, (6 - score c v)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_00 : ∀ a b c d : Fin 5, 20 ≤ bound ![0, 0, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_01 : ∀ a b c d : Fin 5, 20 ≤ bound ![0, 1, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_02 : ∀ a b c d : Fin 5, 20 ≤ bound ![0, 2, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_03 : ∀ a b c d : Fin 5, 20 ≤ bound ![0, 3, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_04 : ∀ a b c d : Fin 5, 20 ≤ bound ![0, 4, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_10 : ∀ a b c d : Fin 5, 20 ≤ bound ![1, 0, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_11 : ∀ a b c d : Fin 5, 20 ≤ bound ![1, 1, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_12 : ∀ a b c d : Fin 5, 20 ≤ bound ![1, 2, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_13 : ∀ a b c d : Fin 5, 20 ≤ bound ![1, 3, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_14 : ∀ a b c d : Fin 5, 20 ≤ bound ![1, 4, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_20 : ∀ a b c d : Fin 5, 20 ≤ bound ![2, 0, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_21 : ∀ a b c d : Fin 5, 20 ≤ bound ![2, 1, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_22 : ∀ a b c d : Fin 5, 20 ≤ bound ![2, 2, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_23 : ∀ a b c d : Fin 5, 20 ≤ bound ![2, 3, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_24 : ∀ a b c d : Fin 5, 20 ≤ bound ![2, 4, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_30 : ∀ a b c d : Fin 5, 20 ≤ bound ![3, 0, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_31 : ∀ a b c d : Fin 5, 20 ≤ bound ![3, 1, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_32 : ∀ a b c d : Fin 5, 20 ≤ bound ![3, 2, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_33 : ∀ a b c d : Fin 5, 20 ≤ bound ![3, 3, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_34 : ∀ a b c d : Fin 5, 20 ≤ bound ![3, 4, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_40 : ∀ a b c d : Fin 5, 20 ≤ bound ![4, 0, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_41 : ∀ a b c d : Fin 5, 20 ≤ bound ![4, 1, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_42 : ∀ a b c d : Fin 5, 20 ≤ bound ![4, 2, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_43 : ∀ a b c d : Fin 5, 20 ≤ bound ![4, 3, a, b, c, d] := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem check_44 : ∀ a b c d : Fin 5, 20 ≤ bound ![4, 4, a, b, c, d] := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem checked (c : Config) : 20 ≤ bound c := by
  have he : c = ![c 0, c 1, c 2, c 3, c 4, c 5] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  generalize c 0 = a
  generalize c 1 = b
  fin_cases a <;> fin_cases b
  · exact check_00 _ _ _ _
  · exact check_01 _ _ _ _
  · exact check_02 _ _ _ _
  · exact check_03 _ _ _ _
  · exact check_04 _ _ _ _
  · exact check_10 _ _ _ _
  · exact check_11 _ _ _ _
  · exact check_12 _ _ _ _
  · exact check_13 _ _ _ _
  · exact check_14 _ _ _ _
  · exact check_20 _ _ _ _
  · exact check_21 _ _ _ _
  · exact check_22 _ _ _ _
  · exact check_23 _ _ _ _
  · exact check_24 _ _ _ _
  · exact check_30 _ _ _ _
  · exact check_31 _ _ _ _
  · exact check_32 _ _ _ _
  · exact check_33 _ _ _ _
  · exact check_34 _ _ _ _
  · exact check_40 _ _ _ _
  · exact check_41 _ _ _ _
  · exact check_42 _ _ _ _
  · exact check_43 _ _ _ _
  · exact check_44 _ _ _ _

def initial : List Block := List.ofFn fun i : Point => {i}

def children (w : List Block) (g : Gate) : Finset Block :=
  (g.inputs.map fun i => w.getD i ∅).toFinset

def node (w : List Block) (g : Gate) : Block := (children w g).biUnion id

def trace (w : List Block) : List Gate → List Block
  | [] => []
  | g :: gs => node w g :: trace (w ++ [node w g]) gs

theorem children_card (w : List Block) (g : Gate) (h : g.inputs.length ≤ 2) :
    (children w g).card ≤ 2 := by
  exact (List.toFinset_card_le _).trans (by simpa using h)

theorem trace_length (w : List Block) (gs : List Gate) : (trace w gs).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

theorem split_tail (w : List Block) (g : Gate) (gs : List Gate) :
    w ++ trace w (g :: gs) = (w ++ [node w g]) ++ trace (w ++ [node w g]) gs := by
  simp [trace]

theorem read_available (w : List Block) (i : ℕ) : w.getD i ∅ = ∅ ∨ w.getD i ∅ ∈ w := by
  by_cases hi : i < w.length
  · right
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  · exact Or.inl (List.getD_eq_default _ _ (by omega))

theorem child_available (w : List Block) (g : Gate) {S : Block} (hS : S ∈ children w g) :
    S = ∅ ∨ S ∈ w := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
  exact read_available w i

theorem child_subset (w : List Block) (g : Gate) {S : Block} (hS : S ∈ children w g) :
    S ⊆ node w g := by
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨S, hS, ha⟩

def atPoint (p : Point) (S : Block) : Bool := decide (p ∈ S)

theorem getD_map_point (w : List Block) (p : Point) (i : ℕ) :
    (w.map (atPoint p)).getD i false = atPoint p (w.getD i ∅) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp only [List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [atPoint]

theorem eval_node (w : List Block) (g : Gate) (p : Point) (ho : g.op = .or) :
    g.op.eval (g.inputs.map fun i => (w.map (atPoint p)).getD i false) =
      atPoint p (node w g) := by
  rw [ho]
  apply Bool.eq_iff_iff.2
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map, getD_map_point,
    atPoint, decide_eq_true_eq, node, Finset.mem_biUnion, children, List.mem_toFinset]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hp⟩
    exact ⟨_, ⟨i, hi, rfl⟩, of_decide_eq_true hp⟩
  · rintro ⟨S, ⟨i, hi, rfl⟩, hp⟩
    exact ⟨_, ⟨i, hi, rfl⟩, decide_eq_true hp⟩

theorem eval_trace (gs : List Gate) (h : ∀ g ∈ gs, g.op = .or) (w : List Block) (p : Point) :
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (atPoint p)) = (w ++ trace w gs).map (atPoint p) := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hmap : (w ++ [node w g]).map (atPoint p) =
        w.map (atPoint p) ++ [atPoint p (node w g)] := by simp
    rw [eval_node w g p (h g List.mem_cons_self), ← hmap, split_tail]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) (w ++ [node w g])

theorem initial_point (p : Point) :
    initial.map (atPoint p) = List.ofFn (fun q : Point => decide (q = p)) := by
  rw [initial, List.map_ofFn]
  congr 1
  funext q
  simp [atPoint, eq_comm]

theorem all_small_initial (S : Block) (hS : S ∈ initial) : S.card ≤ 1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS
  simp

theorem trace_realizes (C : Circuit) (h : ∀ g ∈ C.gates, g.op = .or)
    (v : Bit) (o : ℕ) (hv : ∀ p : Point,
      (C.wires (List.ofFn fun q : Point => decide (q = p))).getD o false =
        (p.val + 1).testBit v.val) :
    target v ∈ initial ++ trace initial C.gates := by
  let W := initial ++ trace initial C.gates
  have he : W.getD o ∅ = target v := by
    ext p
    have hh := hv p
    rw [← initial_point, Circuit.wires, eval_trace C.gates h initial p, getD_map_point] at hh
    simpa only [W, target, Finset.mem_filter, Finset.mem_univ, true_and, atPoint,
      decide_eq_true_eq] using (Bool.eq_iff_iff.mp hh)
  rcases read_available W o with hz | hm
  · have hcard := target_card v
    rw [← he, hz, Finset.card_empty] at hcard
    omega
  · exact he ▸ hm

theorem shared_child (p : Pair) (w : List Block) (g : Gate)
    (hfan : g.inputs.length ≤ 2) (hS : node w g ⊆ space p) (hcard : 3 ≤ (node w g).card) :
    ∃ B ∈ w, shared p B := by
  by_contra hn
  push_neg at hn
  have hs : ∀ B ∈ children w g, B.card ≤ 1 := by
    intro B hB
    rcases child_available w g hB with rfl | ha
    · simp
    · have hsub := (child_subset w g hB).trans hS
      have := hn B ha
      simp [shared, hsub] at this
      omega
  have hc := Finset.card_biUnion_le (s := children w g) (t := id)
  simp only [id_eq] at hc
  have hsum : (∑ B ∈ children w g, B.card) ≤ (children w g).card := by
    rw [Finset.card_eq_sum_ones (s := children w g)]
    exact Finset.sum_le_sum hs
  have := children_card w g hfan
  change 3 ≤ ((children w g).biUnion id).card at hcard
  omega

theorem one_share_small (p : Pair) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Block)
    (hw : ∀ B ∈ w, shared p B → B.card ≤ 2)
    (hc : count (w ++ trace w gs) (.inr p) ≤ 1) :
    ∀ B ∈ w ++ trace w gs, shared p B → B.card ≤ 2 := by
  induction gs generalizing w with
  | nil => simpa [trace] using hw
  | cons g gs ih =>
    rw [split_tail] at hc ⊢
    refine ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) _ ?_ hc
    intro B hB hp
    rcases List.mem_append.mp hB with h | h
    · exact hw B h hp
    · have hEq : B = node w g := List.mem_singleton.mp h
      subst B
      by_contra hn
      obtain ⟨A, hA, hS⟩ := shared_child p w g (hg g List.mem_cons_self) hp.2 (by omega)
      have ha := count_pos (t := .inr p) hA hS
      rw [count_append, count_append, count_cons] at hc
      change (count w (.inr p) + ((if passes (.inr p) (node w g) then 1 else 0) +
        count [] (.inr p))) + count (trace (w ++ [node w g]) gs) (.inr p) ≤ 1 at hc
      have ht : passes (.inr p) (node w g) = true := passes_spec.mpr hp
      simp [ht] at hc
      omega

theorem choose_grants (xs : List Block)
    (hsmall : ∀ p, count xs (.inr p) ≤ 1 → ∀ S ∈ xs, shared p S → S.card ≤ 2) :
    ∃ c : Config, (∀ p, charge (c p) ≤ count xs (.inr p)) ∧
      ∀ p S, S ∈ xs → shared p S → S ⊆ candidate p (c p) := by
  classical
  have pointwise (p : Pair) : ∃ i : Fin 5, charge i ≤ count xs (.inr p) ∧
      ∀ S, S ∈ xs → shared p S → S ⊆ candidate p i := by
    by_cases h2 : 2 ≤ count xs (.inr p)
    · refine ⟨4, by simpa [charge] using h2, ?_⟩
      exact fun _ _ hs => hs.2
    by_cases h0 : count xs (.inr p) = 0
    · refine ⟨0, by simp [charge], ?_⟩
      intro S hm hs
      have := count_pos (t := .inr p) hm hs
      omega
    have h1 : count xs (.inr p) = 1 := by omega
    obtain ⟨S, hS⟩ := List.length_eq_one_iff.mp h1
    have hs : S ∈ xs.filter (fun B => passes (.inr p) B) := by simp [hS]
    have hsX := (List.mem_filter.mp hs).1
    have hp : shared p S := passes_spec.mp (List.mem_filter.mp hs).2
    have hcard : S.card = 2 := Nat.le_antisymm (hsmall p (by omega) S hsX hp) hp.1
    obtain ⟨i, hi, he⟩ := two_choice p S hp.2 hcard
    refine ⟨i, ?_, ?_⟩
    · rcases hi with rfl | rfl | rfl <;> simp [charge, h1]
    · intro T hT ht
      have hT' : T ∈ xs.filter (fun B => passes (.inr p) B) :=
        List.mem_filter.mpr ⟨hT, passes_spec.mpr ht⟩
      rw [hS, List.mem_singleton] at hT'
      rw [hT', he]
  refine ⟨fun p => (pointwise p).choose, fun p => (pointwise p).choose_spec.1,
    fun p => (pointwise p).choose_spec.2⟩

theorem share_side {v : Bit} {p : Pair} {S : Block}
    (hT : S ⊆ target v) (hS : shared p S) : ∃ j : Fin 3, incident v j = p := by
  apply (incident_exact v p).mp
  by_contra hn
  push_neg at hn
  have hsum := Finset.card_le_card (Finset.subset_inter hT hS.2)
  have := unrelated v p hn.1 hn.2
  have := hS.1
  omega

def permitted (c : Config) (v : Bit) (S : Block) : Prop :=
  S ⊆ target v ∧ (S.card ≤ 1 ∨ ∃ j : Fin 3, S ⊆ grant v (fun i => c (incident v i)) j)

def Good (c : Config) (v : Bit) (w : List Block) (k : ℕ) : Prop :=
  ∀ K : Finset Block, (∀ S ∈ K, S ⊆ target v ∧ (S = ∅ ∨ S ∈ w)) →
    ∃ F : Finset Block, (∀ S ∈ F, permitted c v S) ∧
      K.biUnion id ⊆ F.biUnion id ∧ F.card ≤ k + K.card

theorem initial_good (c : Config) (v : Bit) : Good c v initial 0 := by
  intro K hK
  refine ⟨K, ?_, le_rfl, by simp⟩
  intro S hS
  obtain ⟨hsub, h⟩ := hK S hS
  refine ⟨hsub, Or.inl ?_⟩
  rcases h with rfl | h
  · simp
  · exact all_small_initial S h

theorem step_good (c : Config) (v : Bit) (w : List Block) (g : Gate) (k : ℕ)
    (hg : g.inputs.length ≤ 2) (hgood : Good c v w k)
    (hgrant : ∀ p, shared p (node w g) → node w g ⊆ candidate p (c p)) :
    Good c v (w ++ [node w g]) (k + count [node w g] (.inl v)) := by
  classical
  intro K hK
  let U := node w g
  have old (S : Block) (hm : S ∈ K) (hne : S ≠ U) :
      S ⊆ target v ∧ (S = ∅ ∨ S ∈ w) := by
    obtain ⟨hS, he | hw⟩ := hK S hm
    · exact ⟨hS, Or.inl he⟩
    · rcases List.mem_append.mp hw with h | h
      · exact ⟨hS, Or.inr h⟩
      · exact (hne (List.mem_singleton.mp h)).elim
  by_cases hU : U ∈ K
  · have ht := (hK U hU).1
    have hKpos : 1 ≤ K.card := Finset.card_pos.mpr ⟨U, hU⟩
    have hrest : ∀ S ∈ K.erase U, S ⊆ target v ∧ (S = ∅ ∨ S ∈ w) :=
      fun S h => old S (Finset.mem_erase.mp h).2 (Finset.mem_erase.mp h).1
    by_cases ha : permitted c v U
    · obtain ⟨F, hF, hsub, hcard⟩ := hgood (K.erase U) hrest
      refine ⟨insert U F, ?_, ?_, ?_⟩
      · intro S hS
        rcases Finset.mem_insert.mp hS with rfl | h
        · exact ha
        · exact hF S h
      · intro x hx
        obtain ⟨S, hS, hxs⟩ := Finset.mem_biUnion.mp hx
        by_cases he : S = U
        · subst S
          exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_insert_self _ _, hxs⟩
        · have h' := hsub (Finset.mem_biUnion.mpr ⟨S, Finset.mem_erase.mpr ⟨he, hS⟩, hxs⟩)
          obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp h'
          exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_insert_of_mem hT, hxT⟩
      · rw [Finset.card_erase_of_mem hU] at hcard
        have := Finset.card_insert_le U F
        omega
    · have hown : owned v U := by
        refine ⟨?_, ht, ?_⟩
        · by_contra h
          exact ha ⟨ht, Or.inl (by omega)⟩
        · intro p hp
          obtain ⟨j, hj⟩ := share_side ht hp
          exact ha ⟨ht, Or.inr ⟨j, by simpa [grant, hj] using hgrant p hp⟩⟩
      let M := K.erase U ∪ children w g
      have hM : ∀ S ∈ M, S ⊆ target v ∧ (S = ∅ ∨ S ∈ w) := by
        intro S hS
        rcases Finset.mem_union.mp hS with h | h
        · exact hrest S h
        · exact ⟨(child_subset w g h).trans ht, child_available w g h⟩
      obtain ⟨F, hF, hsub, hcard⟩ := hgood M hM
      refine ⟨F, hF, ?_, ?_⟩
      · apply Finset.Subset.trans _ hsub
        intro x hx
        obtain ⟨S, hS, hxs⟩ := Finset.mem_biUnion.mp hx
        by_cases he : S = U
        · subst S
          obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hxs
          exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_union_right _ hT, hxT⟩
        · exact Finset.mem_biUnion.mpr
            ⟨S, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hS⟩), hxs⟩
      · have hm : M.card ≤ K.card - 1 + 2 := by
          have he := Finset.card_union_le (K.erase U) (children w g)
          rw [Finset.card_erase_of_mem hU] at he
          exact he.trans (Nat.add_le_add_left (children_card w g hg) _)
        have hp : 1 ≤ count [node w g] (.inl v) :=
          count_pos (List.mem_singleton_self _) hown
        omega
  · obtain ⟨F, hF, hsub, hcard⟩ :=
      hgood K (fun S hS => old S hS (fun he => hU (he ▸ hS)))
    exact ⟨F, hF, hsub, by omega⟩

theorem trace_good (c : Config) (v : Bit) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List Block) (k : ℕ)
    (hgood : Good c v w k)
    (hgrant : ∀ p S, S ∈ trace w gs → shared p S → S ⊆ candidate p (c p)) :
    Good c v (w ++ trace w gs) (k + count (trace w gs) (.inl v)) := by
  induction gs generalizing w k with
  | nil => simpa [trace, count] using hgood
  | cons g gs ih =>
    have hnext := step_good c v w g k (hg g List.mem_cons_self) hgood
      (fun p hp => hgrant p _ (by exact List.mem_cons_self) hp)
    have hh := ih (fun g h => hg g (List.mem_cons_of_mem _ h)) (w ++ [node w g])
      (k + count [node w g] (.inl v)) hnext
      (fun p S h hs => hgrant p S (List.mem_cons_of_mem _ h) hs)
    rw [split_tail]
    convert hh using 1
    simp only [trace, count_cons]
    simp [count, Nat.add_assoc]

theorem cover_cost (c : Config) (v : Bit) (F : Finset Block)
    (hF : ∀ S ∈ F, permitted c v S) (hcover : target v ⊆ F.biUnion id) :
    7 ≤ F.card + score c v := by
  classical
  let small := F.filter (fun S => S.card ≤ 1)
  let large := F.filter (fun S => ¬ S.card ≤ 1)
  let H := grant v (fun j => c (incident v j))
  have larger (S : { S // S ∈ large }) : ∃ j : Fin 3, S.1 ⊆ H j := by
    obtain ⟨hm, hs⟩ := Finset.mem_filter.mp S.2
    exact (hF S.1 hm).2.resolve_left hs
  let idx (S : { S // S ∈ large }) : Fin 3 := (larger S).choose
  let J := large.attach.image idx
  have hc : target v ⊆ (small.biUnion id) ∪ (J.biUnion H) := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp (hcover hx)
    by_cases hs : S.card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hs⟩, hxS⟩)
    · let a : { S // S ∈ large } := ⟨S, Finset.mem_filter.mpr ⟨hS, hs⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨idx a, Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩, (larger a).choose_spec hxS⟩)
  have hsmall : (small.biUnion id).card ≤ small.card := by
    calc
      (small.biUnion id).card ≤ ∑ S ∈ small, S.card := Finset.card_biUnion_le
      _ ≤ small.card := by
        rw [Finset.card_eq_sum_ones (s := small)]
        exact Finset.sum_le_sum (fun S hS => (Finset.mem_filter.mp hS).2)
  have hJ : J.card ≤ large.card := by
    simpa [J] using (Finset.card_image_le (s := large.attach) (f := idx))
  have hsum : small.card + large.card = F.card := Finset.card_filter_add_card_filter_not (s := F) (fun S : Block => S.card ≤ 1)
  have hscore : (J.biUnion H).card - J.card ≤ score c v := by
    rw [score, scores_agree]
    unfold abstractScore
    exact Finset.le_sup (f := fun K : Finset (Fin 3) => (K.biUnion H).card - K.card)
      (Finset.mem_powerset.mpr (Finset.subset_univ J))
  have htot := (Finset.card_le_card hc).trans
    (Finset.card_union_le (small.biUnion id) (J.biUnion H))
  rw [target_card] at htot
  omega

theorem initial_count (t : Bit ⊕ Pair) : count initial t = 0 := by
  unfold count
  have he : initial.filter (fun B => passes t B) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro B hB
    intro he
    have ht := passes_spec.mp he
    have h := all_small_initial B hB
    cases t with
    | inl v =>
      have hp : owned v B := ht
      have := hp.1
      omega
    | inr p =>
      have hp : shared p B := ht
      have := hp.1
      omega
  rw [he]
  rfl

theorem encoder_bound (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length ≤ 2)
    (hOut : ∀ v : Bit, ∃ w : ℕ, ∀ p : Point,
      (C.wires (List.ofFn fun q : Point => decide (q = p))).getD w false =
        (p.val + 1).testBit v.val) : 20 ≤ C.size := by
  let xs := trace initial C.gates
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g h => (hC g h).2
  have hsmall : ∀ p, count xs (.inr p) ≤ 1 →
      ∀ S ∈ xs, shared p S → S.card ≤ 2 := by
    intro p hp S hS hs
    apply one_share_small p C.gates hfan initial ?_ ?_ S (List.mem_append_right _ hS) hs
    · intro B hB _
      exact (all_small_initial B hB).trans (by decide)
    · simpa only [count_append, initial_count, Nat.zero_add] using hp
  obtain ⟨c, hp, hgrant⟩ := choose_grants xs hsmall
  have hpriv (v : Bit) : 6 - score c v ≤ count xs (.inl v) := by
    obtain ⟨o, ho⟩ := hOut v
    have hmem := trace_realizes C (fun g h => (hC g h).1) v o ho
    have hg := trace_good c v C.gates hfan initial 0 (initial_good c v) hgrant
    obtain ⟨F, hF, hsub, hlen⟩ := hg {target v} (by
      intro S hS
      rcases Finset.mem_singleton.mp hS with rfl
      exact ⟨Finset.Subset.rfl, Or.inr hmem⟩)
    have hc := cover_cost c v F hF (by simpa only [Finset.singleton_biUnion, id_eq] using hsub)
    rw [Finset.card_singleton, Nat.zero_add] at hlen
    change 6 - score c v ≤ count (trace initial C.gates) (.inl v)
    omega
  have ha : bound c ≤ ∑ t, count xs t := by
    have hL : (∑ v, (6 - score c v)) ≤ ∑ v, count xs (.inl v) :=
      Finset.sum_le_sum fun v _ => hpriv v
    have hR : (∑ p, charge (c p)) ≤ ∑ p, count xs (.inr p) :=
      Finset.sum_le_sum fun p _ => hp p
    rw [Fintype.sum_sum_type]
    unfold bound
    omega
  have hb := total_count xs
  have ht := checked c
  change 20 ≤ C.gates.length
  have hl : xs.length = C.gates.length := trace_length _ _
  omega

end PEqualNP.Outside.L_meta_12408

open PEqualNP.Outside.L_meta_12408 in
theorem PEqualNP.Outside.L_meta_12408 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, hC, hc, he⟩
  have := encoder_bound C hC he
  omega
