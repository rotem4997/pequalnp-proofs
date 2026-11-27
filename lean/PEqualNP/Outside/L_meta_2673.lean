import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2673


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

private def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

private def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

private def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

private lemma plane_support (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hT : ∀ p1 l1 : Fin N, I p1 l1 → circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false)
    (hq2 : 2 ≤ q) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  have hpair (p l : Fin N) (h : I p l) : circuitFun (N + N) C (pair p l) = true := hT p l h
  have hpoint (p : Fin N) : circuitFun (N + N) C (point p) = false := by
    apply hS
    · refine le_trans (Finset.card_le_card (t := {p}) (fun x hx => ?_)) (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, point, decide_eq_true_eq] at hx
      exact Finset.mem_singleton.mpr (Fin.castAdd_injective _ _ hx)
    · refine le_trans (Finset.card_le_card (t := ∅) (fun x hx => ?_)) (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, point, decide_eq_true_eq] at hx
      exact absurd hx.symm (cast_ne_nat p x)
    · rintro ⟨_, l, _, _, h⟩
      exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline (l : Fin N) : circuitFun (N + N) C (line l) = false := by
    apply hS
    · refine le_trans (Finset.card_le_card (t := ∅) (fun x hx => ?_)) (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, line, decide_eq_true_eq] at hx
      exact absurd hx (cast_ne_nat x l)
    · refine le_trans (Finset.card_le_card (t := {l}) (fun x hx => ?_)) (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, line, decide_eq_true_eq] at hx
      exact Finset.mem_singleton.mpr (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hx : N + x.val = N + l.val)))
    · rintro ⟨p, _, _, h, _⟩
      exact cast_ne_nat p l (of_decide_eq_true h)
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]


section ReadWitness

-- Decode capped multiplicities into actual words of input leaves.

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 2 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section Degrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

private def on (N : ℕ) (X Y : Set (Fin N)) (w : ℕ) : Prop :=
  (∃ p ∈ X, (p : ℕ) = w) ∨ ∃ l ∈ Y, N + (l : ℕ) = w

private lemma on_point {N : ℕ} (X Y : Set (Fin N)) (p : Fin N) :
    on N X Y p.val ↔ p ∈ X := by
  constructor
  · rintro (⟨q, hq, hv⟩ | ⟨l, _, hv⟩)
    · exact (Fin.ext hv : q = p) ▸ hq
    · omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

private lemma on_line {N : ℕ} (X Y : Set (Fin N)) (l : Fin N) :
    on N X Y (N + l.val) ↔ l ∈ Y := by
  constructor
  · rintro (⟨p, _, hv⟩ | ⟨l', hl', hv⟩)
    · omega
    · exact (Fin.ext (Nat.add_left_cancel hv) : l' = l) ▸ hl'
  · exact fun hl => Or.inr ⟨l, hl, rfl⟩

private noncomputable def bits {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) : Bool := by
  classical
  exact decide (on N X Y i.val)

private lemma bits_true {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) :
    bits X Y i = true ↔ on N X Y i.val := by
  classical
  simp [bits]

private def pcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (w < N)).length
private def lcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (N ≤ w)).length

private lemma sum_counts (N : ℕ) (t : List ℕ) : pcount N t + lcount N t = t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a < N
    · have hn : ¬ N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega
    · have hn : N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega

private def Hom (N : ℕ) (C : Circuit) (w a b : ℕ) (X Y : Set (Fin N)) : Prop :=
  ∃ t ∈ words (N + N) C w, pcount N t = a ∧ lcount N t = b ∧ ∀ j ∈ t, on N X Y j

private lemma hom_mono {N : ℕ} {C : Circuit} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (h : Hom N C w a b X Y) : Hom N C w a b X' Y' := by
  obtain ⟨t, ht, ha, hb, hxy⟩ := h
  exact ⟨t, ht, ha, hb, fun j hj => (hxy j hj).imp
    (fun ⟨p, hp, he⟩ => ⟨p, hx hp, he⟩) (fun ⟨l, hl, he⟩ => ⟨l, hy hl, he⟩)⟩

private lemma hom_pure_x {N : ℕ} {C : Circuit} {w a : ℕ} {X Y : Set (Fin N)} :
    Hom N C w a 0 X Y ↔ Hom N C w a 0 X ∅ := by
  refine ⟨?_, hom_mono (fun _ h => h) (Set.empty_subset _)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with hp | ⟨l, _, hl⟩
  · exact Or.inl hp
  · have hn : N ≤ j := by omega
    have hmem : j ∈ t.filter (fun w => decide (N ≤ w)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold lcount at hb
    rw [List.length_eq_zero_iff.mp hb] at hmem
    simp at hmem

private lemma hom_pure_y {N : ℕ} {C : Circuit} {w b : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 0 b X Y ↔ Hom N C w 0 b ∅ Y := by
  refine ⟨?_, hom_mono (Set.empty_subset _) (fun _ h => h)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, _, hp⟩ | hl
  · have hn : j < N := hp ▸ p.isLt
    have hmem : j ∈ t.filter (fun w => decide (w < N)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold pcount at ha
    rw [List.length_eq_zero_iff.mp ha] at hmem
    simp at hmem
  · exact Or.inr hl

private lemma hom_invalid {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ Hom N C w a b X Y := by
  simp [Hom, words_missing _ _ hw]

private lemma hom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) : 0 < a + b := by
  obtain ⟨t, ht, ha, hb, _⟩ := hh
  rw [← ha, ← hb, sum_counts]
  exact List.length_pos_iff.mpr (words_nonempty h ht)

private lemma hom_input {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)} (hw : w < N + N) :
    Hom N C w a b X Y ↔ on N X Y w ∧
      ((w < N ∧ a = 1 ∧ b = 0) ∨ (N ≤ w ∧ a = 0 ∧ b = 1)) := by
  unfold Hom
  rw [words_input C hw]
  by_cases h : w < N
  · have h' : ¬ N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]
  · have h' : N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]

private lemma hom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, Hom N C (operand C k i) a b X Y := by
  rw [Fin.exists_fin_two]
  unfold Hom
  rw [words_gate h k, ho]
  simp only [wordOp, Set.mem_union]
  exact ⟨fun ⟨t, hr, he⟩ => hr.imp (fun ht => ⟨t, ht, he⟩) (fun ht => ⟨t, ht, he⟩),
    fun h => h.elim (fun ⟨t, ht, he⟩ => ⟨t, Or.inl ht, he⟩) (fun ⟨t, ht, he⟩ => ⟨t, Or.inr ht, he⟩)⟩

private lemma hom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        Hom N C (operand C k 0) a₀ b₀ X Y ∧ Hom N C (operand C k 1) a₁ b₁ X Y := by
  unfold Hom
  rw [words_gate h k, ho]
  constructor
  · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, ha, hb, hxy⟩
    exact ⟨pcount N t, lcount N t, pcount N u, lcount N u, by simpa [pcount] using ha,
      by simpa [lcount] using hb, ⟨t, ht, rfl, rfl, fun j hj => hxy j (List.mem_append_left _ hj)⟩,
      ⟨u, hu, rfl, rfl, fun j hj => hxy j (List.mem_append_right _ hj)⟩⟩
  · rintro ⟨a₀, b₀, a₁, b₁, ha, hb, ⟨t, ht, rfl, rfl, hxy⟩, ⟨u, hu, rfl, rfl, hxy'⟩⟩
    exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, by simpa [pcount] using ha,
      by simpa [lcount] using hb, fun j hj => (List.mem_append.mp hj).elim (hxy j) (hxy' j)⟩

private lemma hom_and_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) (i : Fin 2)
    {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : Hom N C (operand C k i) a b X Y)
    (h₂ : Hom N C (operand C k (1 - i)) c d X Y) :
    Hom N C (outWire (N + N) k) (a + c) (b + d) X Y := by
  apply (hom_and h ho).mpr
  fin_cases i
  · exact ⟨a, b, c, d, rfl, rfl, h₁, h₂⟩
  · exact ⟨c, d, a, b, Nat.add_comm _ _, Nat.add_comm _ _, h₂, h₁⟩

private lemma hom_sound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) :
    circuitValue C (bits X Y) w = true := by
  obtain ⟨t, ht, _, _, hxy⟩ := hh
  apply (value_eq_terms h _ _).mpr
  refine ⟨t, ht, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨Fin.castAdd N p, rfl, (bits_true _ _ _).mpr ((on_point X Y p).mpr hp)⟩
  · exact ⟨Fin.natAdd N l, rfl, (bits_true _ _ _).mpr ((on_line X Y l).mpr hl)⟩

private lemma hom_output_safe {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C C.output a b X Y) :
    ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  have hv := hom_sound h hh
  change circuitFun (N + N) C (bits X Y) = true at hv
  rw [hC, decide_eq_true_eq] at hv
  obtain ⟨p, l, hi, hp, hl⟩ := hv
  exact ⟨p, (on_point X Y p).mp ((bits_true _ _ _).mp hp),
    l, (on_line X Y l).mp ((bits_true _ _ _).mp hl), hi⟩

private lemma card_points_le (N : ℕ) (t : List ℕ) :
    (Finset.univ.filter (fun p : Fin N => p.val ∈ t)).card ≤ pcount N t := by
  classical
  calc _ ≤ (t.filter fun w => decide (w < N)).toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun p : Fin N => p.val)
        · intro p hp
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
          exact ⟨hp, p.isLt⟩
        · intro p _ p' _ h
          exact Fin.ext h
    _ ≤ _ := List.toFinset_card_le _

private lemma card_lines_le (N : ℕ) (t : List ℕ) :
    (Finset.univ.filter (fun l : Fin N => N + l.val ∈ t)).card ≤ lcount N t := by
  classical
  calc _ ≤ (t.filter fun w => decide (N ≤ w)).toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun l : Fin N => N + l.val)
        · intro l hl
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
          exact ⟨hl, by omega⟩
        · intro l _ l' _ h
          exact Fin.ext (Nat.add_left_cancel h)
    _ ≤ _ := List.toFinset_card_le _

private lemma hom_output_safe2 {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false)
    {a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C C.output a b X Y) (ha : a ≤ 2) (hb : b ≤ 2) :
    ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  classical
  obtain ⟨t, ht, ha', hb', hxy⟩ := hh
  let X' : Set (Fin N) := {p | p.val ∈ t}
  let Y' : Set (Fin N) := {l | N + l.val ∈ t}
  have hh' : Hom N C C.output a b X' Y' := by
    refine ⟨t, ht, ha', hb', fun j hj => ?_⟩
    rcases hxy j hj with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
    · exact Or.inl ⟨p, hj, rfl⟩
    · exact Or.inr ⟨l, hj, rfl⟩
  have hv := hom_sound h hh'
  change circuitFun (N + N) C (bits X' Y') = true at hv
  by_contra hno
  have hp2 : (Finset.univ.filter (fun p2 : Fin N => bits X' Y' (Fin.castAdd N p2) = true)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card (fun p hp => ?_)) ((card_points_le N t).trans (ha' ▸ ha))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact (on_point X' Y' p).mp ((bits_true _ _ _).mp hp)
  have hl2 : (Finset.univ.filter (fun l2 : Fin N => bits X' Y' (Fin.natAdd N l2) = true)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card (fun l hl => ?_)) ((card_lines_le N t).trans (hb' ▸ hb))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact (on_line X' Y' l).mp ((bits_true _ _ _).mp hl)
  have hni : ¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ bits X' Y' (Fin.castAdd N p3) = true ∧
      bits X' Y' (Fin.natAdd N l3) = true := by
    rintro ⟨p, l, hi, hp, hl⟩
    have hp' : p ∈ X' := (on_point X' Y' p).mp ((bits_true _ _ _).mp hp)
    have hl' : l ∈ Y' := (on_line X' Y' l).mp ((bits_true _ _ _).mp hl)
    have hpX : p ∈ X := (on_point X Y p).mp (hxy _ hp')
    have hlY : l ∈ Y := (on_line X Y l).mp (hxy _ hl')
    exact hno ⟨p, hpX, l, hlY, hi⟩
  rw [hS _ hp2 hl2 hni] at hv
  exact Bool.false_ne_true hv

end Degrees


open Finset

section Charging

-- Follow a selector down to an OR edge where its support becomes small.
-- Each large support identifies a unique opposite endpoint by the absence of a four-cycle.

variable {A B W E : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]

private def fourFree : Prop :=
  ∀ ⦃c d : B⦄, c ≠ d → ∀ ⦃a b : A⦄, I a c → I a d → I b c → I b d → a = b

private noncomputable def single (f : Set A → Prop) : Finset A := by
  classical
  exact univ.filter (fun a => f {a})

private lemma mem_single (f : Set A → Prop) (a : A) : a ∈ single f ↔ f {a} := by
  classical
  simp [single]

private def clean (f : Set A → Prop) (c : B) : Prop :=
  ¬ f {a | ¬ I a c}

private lemma clean_single {f : Set A → Prop} (hm : Monotone f) {a : A} {c : B}
    (hc : clean I f c) (ha : a ∈ single f) : I a c := by
  by_contra hn
  exact hc (hm (Set.singleton_subset_iff.mpr hn) ((mem_single f a).mp ha))

private def almost (s : Finset A) (c : B) : Prop :=
  (s.filter fun a => ¬ I a c).card ≤ 1

private def approved (simple : Prop) (f : Set A → Prop) (c : B) : Prop :=
  (2 ≤ (single f).card ∧ clean I f c) ∨
    (simple ∧ 4 ≤ (single f).card ∧ almost I (single f) c)

private lemma almost_of_clean {f : Set A → Prop} (hm : Monotone f) {c : B}
    (hc : clean I f c) : almost I (single f) c := by
  classical
  have hzero : (single f).filter (fun a => ¬ I a c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact (Finset.mem_filter.mp ha).2 (clean_single I hm hc (Finset.mem_filter.mp ha).1)
  simp [almost, hzero]

private lemma almost_mono {s t : Finset A} (hst : s ⊆ t) {c : B}
    (h : almost I t c) : almost I s c :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hst)).trans h

private lemma almost_unique (hf : fourFree I) (s : Finset A) (hs : 4 ≤ s.card)
    {c d : B} (hc : almost I s c) (hd : almost I s d) : c = d := by
  classical
  by_contra hcd
  let good := s.filter (fun a => I a c ∧ I a d)
  have hgood : good.card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  let badC := s.filter (fun a => ¬ I a c)
  let badD := s.filter (fun a => ¬ I a d)
  have hcover : s ⊆ good ∪ (badC ∪ badD) := by
    intro a ha
    by_cases h1 : I a c <;> by_cases h2 : I a d <;> simp [good, badC, badD, ha, h1, h2]
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le good (badC ∪ badD))
  have hbad := Finset.card_union_le badC badD
  change badC.card ≤ 1 at hc
  change badD.card ≤ 1 at hd
  omega

private lemma exact_unique (hf : fourFree I) {f : Set A → Prop} (hm : Monotone f)
    (hs : 2 ≤ (single f).card) {c d : B} (hc : clean I f c) (hd : clean I f d) : c = d := by
  classical
  by_contra hcd
  have hcard : (single f).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (clean_single I hm hc ha) (clean_single I hm hd ha)
      (clean_single I hm hc hb) (clean_single I hm hd hb)
  omega

private lemma approved_unique (hf : fourFree I) {simple : Prop} {f : Set A → Prop}
    (hm : Monotone f) {c d : B} (hc : approved I simple f c) (hd : approved I simple f d) :
    c = d := by
  rcases hc with ⟨hs, hc⟩ | ⟨_, hs, hc⟩ <;> rcases hd with ⟨_, hd⟩ | ⟨_, hsd, hd⟩
  · exact exact_unique I hf hm hs hc hd
  · exact almost_unique I hf _ hsd (almost_of_clean I hm hc) hd
  · exact almost_unique I hf _ hs hc (almost_of_clean I hm hd)
  · exact almost_unique I hf _ hs hc hd

private lemma small_unapproved (simple : Prop) (f : Set A → Prop) (c : B)
    (simple_spec : simple → ∀ U, f U ↔ ∃ a ∈ single f, a ∈ U)
    (h : ¬ approved I simple f c)
    (ha : clean I f c ∨ simple ∧ almost I (single f) c) :
    ((single f).filter fun a => I a c).card ≤ 2 := by
  classical
  by_contra hbad
  have hs : 3 ≤ (single f).card := by
    have hcard := Finset.card_filter_le (single f) (fun a => I a c)
    omega
  rcases ha with hc | ⟨hsim, halm⟩
  · exact h (Or.inl ⟨by omega, hc⟩)
  by_cases h4 : 4 ≤ (single f).card
  · exact h (Or.inr ⟨hsim, h4, halm⟩)
  have hcard := Finset.card_filter_add_card_filter_not
    (s := single f) (p := fun a => I a c)
  have he : ((single f).filter fun a => ¬ I a c).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp he
  have hclean : clean I f c := by
    intro ht
    obtain ⟨a, ha, hni⟩ := (simple_spec hsim _).mp ht
    have hm' : a ∈ (single f).filter (fun a => ¬ I a c) := Finset.mem_filter.mpr ⟨ha, hni⟩
    simp [hempty] at hm'
  exact h (Or.inl ⟨by omega, hclean⟩)

private noncomputable def edgeCover (f : W → Set A → Prop) (simple : W → Prop) : Finset (A × B) := by
  classical
  exact univ.filter (fun p => I p.1 p.2 ∧ ∃ w, approved I (simple w) (f w) p.2 ∧
    p.1 ∈ single (f w))

private lemma cover_bound (hf : fourFree I) (f : W → Set A → Prop) (simple : W → Prop)
    (rank : W → ℕ) (arcs : Finset E) (src dst : E → W)
    (hm : ∀ w, Monotone (f w))
    (hs : ∀ w, simple w → ∀ U, f w U ↔ ∃ a ∈ single (f w), a ∈ U)
    (hr : ∀ w,
      (∀ c, ¬ approved I (simple w) (f w) c) ∨
      (∃ u v, rank u < rank w ∧ rank v < rank w ∧ ¬ simple w ∧
        ∀ U, f w U ↔ f u U ∧ f v U) ∨
      ((∀ e ∈ arcs, src e = w → rank (dst e) < rank w ∧ (simple w → simple (dst e))) ∧
        ∀ U, f w U ↔ ∃ e ∈ arcs, src e = w ∧ f (dst e) U)) :
    (edgeCover I f simple).card ≤ 2 * arcs.card := by
  classical
  let Pay (e : E) : Finset (A × B) := univ.filter fun p => I p.1 p.2 ∧
    approved I (simple (src e)) (f (src e)) p.2 ∧
    ¬ approved I (simple (dst e)) (f (dst e)) p.2 ∧
    (clean I (f (dst e)) p.2 ∨ simple (dst e) ∧ almost I (single (f (dst e))) p.2) ∧
    p.1 ∈ single (f (dst e))
  have pay_card (e : E) : (Pay e).card ≤ 2 := by
    by_cases hn : (Pay e).Nonempty
    · obtain ⟨p, hp⟩ := hn
      have hpv := (Finset.mem_filter.mp hp).2
      refine le_trans (Finset.card_le_card_of_injOn (t := (single (f (dst e))).filter (fun a => I a p.2)) Prod.fst ?_ ?_) ?_
      · intro q hq
        have hqv := (Finset.mem_filter.mp hq).2
        have he := approved_unique I hf (hm (src e)) hqv.2.1 hpv.2.1
        exact Finset.mem_filter.mpr ⟨hqv.2.2.2.2, he ▸ hqv.1⟩
      · intro q hq r hrr he
        exact Prod.ext he (approved_unique I hf (hm (src e))
          (Finset.mem_filter.mp hq).2.2.1 (Finset.mem_filter.mp hrr).2.2.1)
      · exact small_unapproved I _ _ _ (hs (dst e)) hpv.2.2.1 hpv.2.2.2.1
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have descend (w : W) (p : A × B) (hi : I p.1 p.2)
      (ha : approved I (simple w) (f w) p.2) (hsp : p.1 ∈ single (f w)) :
      ∃ e ∈ arcs, p ∈ Pay e := by
    induction ht : rank w using Nat.strong_induction_on generalizing w with
    | ind k ih =>
      rcases hr w with hl | ⟨u, v, hu, hv, hn, hmeet⟩ | ⟨hsub, hunion⟩
      · exact (hl _ ha).elim
      · have hw := (mem_single _ _).mp hsp
        obtain ⟨hpu, hpv⟩ := (hmeet _).mp hw
        obtain ⟨_, hc⟩ := ha.resolve_right (fun h => hn h.1)
        have hcu : clean I (f u) p.2 ∨ clean I (f v) p.2 := by
          by_cases hu : f u {a | ¬ I a p.2}
          · exact Or.inr (fun hv => hc ((hmeet _).mpr ⟨hu, hv⟩))
          · exact Or.inl hu
        have hSu : single (f w) ⊆ single (f u) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).1
        have hSv : single (f w) ⊆ single (f v) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).2
        have hs2 : 2 ≤ (single (f w)).card := (ha.resolve_right (fun h => hn h.1)).1
        rcases hcu with hcu | hcv
        · exact ih (rank u) (ht ▸ hu) u (Or.inl ⟨hs2.trans (Finset.card_le_card hSu), hcu⟩)
            ((mem_single _ _).mpr hpu) rfl
        · exact ih (rank v) (ht ▸ hv) v (Or.inl ⟨hs2.trans (Finset.card_le_card hSv), hcv⟩)
            ((mem_single _ _).mpr hpv) rfl
      · obtain ⟨e, he, hew, hep⟩ := (hunion _).mp ((mem_single _ _).mp hsp)
        have hsub' : single (f (dst e)) ⊆ single (f w) := by
          intro a ha'
          exact (mem_single _ _).mpr ((hunion _).mpr ⟨e, he, hew, (mem_single _ _).mp ha'⟩)
        have hnext : clean I (f (dst e)) p.2 ∨
            simple (dst e) ∧ almost I (single (f (dst e))) p.2 := by
          rcases ha with ⟨_, hc⟩ | ⟨hsw, _, hd⟩
          · exact Or.inl (fun hb => hc ((hunion _).mpr ⟨e, he, hew, hb⟩))
          · exact Or.inr ⟨(hsub e he hew).2 hsw, almost_mono I hsub' hd⟩
        by_cases hnext' : approved I (simple (dst e)) (f (dst e)) p.2
        · exact ih (rank (dst e)) (ht ▸ (hsub e he hew).1) _ hnext'
            ((mem_single _ _).mpr hep) rfl
        · refine ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_, hnext', hnext,
            (mem_single _ _).mpr hep⟩⟩
          simpa only [hew] using ha
  have hcover : edgeCover I f simple ⊆ arcs.biUnion Pay := by
    intro p hp
    obtain ⟨hi, w, ha, hsp⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr (descend w p hi ha hsp)
  calc
    _ ≤ (arcs.biUnion Pay).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ arcs, (Pay e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ arcs, 2 := Finset.sum_le_sum (fun e _ => pay_card e)
    _ = _ := by simp [Nat.mul_comm]

end Charging


section Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private lemma plane_four_free
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : fourFree I := by
  intro l l' hll p p' hp hpl' hp' hp'l'
  by_contra hpp
  obtain ⟨_, _, hunique⟩ := hu p p' hpp
  exact hll ((hunique l ⟨hp, hp'⟩).trans (hunique l' ⟨hpl', hp'l'⟩).symm)

private lemma pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · rw [hC, decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

private lemma setList_pair {p l : Fin N} (j : ℕ) :
    j ∈ setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔
      j = p.val ∨ j = N + l.val := by
  simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Fin.castAdd N p, Or.inl rfl, rfl⟩
    · exact ⟨Fin.natAdd N l, Or.inr rfl, rfl⟩

private lemma pair_counts {p l : Fin N} (t : List ℕ)
    (ht : ∀ a ∈ t, a = p.val ∨ a = N + l.val) :
    pcount N t = t.count p.val ∧ lcount N t = t.count (N + l.val) := by
  have hp : p.val < N := p.isLt
  have hne : p.val ≠ N + l.val := by omega
  have hl : ¬ N + l.val < N := by omega
  induction t with
  | nil => simp [pcount, lcount]
  | cons j t ih =>
    obtain ⟨h1, h2⟩ := ih (fun a ha => ht a (List.mem_cons_of_mem _ ha))
    change (t.filter _).length = _ at h1 h2
    rcases ht j (by simp) with rfl | rfl
    · have hpn : ¬ N ≤ p.val := by omega
      simp [pcount, lcount, hp, hpn, hne, Ne.symm hne, h1, h2, List.count_cons]
    · simp [pcount, lcount, hl, hne, Ne.symm hne, h1, h2, List.count_cons]

private lemma plane_read_cover
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false)
    {p l : Fin N} (hi : I p l) (hr : readsAtMost C (N + N) [p.val, N + l.val] 2 = true) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ Hom N C C.output a b {p} {l} := by
  obtain ⟨t, ht, hs, hu⟩ := read_to_terms h _ hr
  have hs' : ∀ j ∈ t, j = p.val ∨ j = N + l.val := fun j hj => by simpa using hs j hj
  obtain ⟨hp, hl⟩ := pair_counts (p := p) (l := l) t hs'
  have hpa : pcount N t ≤ 2 := hp ▸ hu _ (by simp)
  have hlb : lcount N t ≤ 2 := hl ▸ hu _ (by simp)
  have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := by
    refine ⟨t, ht, rfl, rfl, fun j hj => ?_⟩
    rcases hs' j hj with rfl | rfl
    · exact (on_point _ _ p).mpr (by simp)
    · exact (on_line _ _ l).mpr (by simp)
  have hp1 : 1 ≤ pcount N t := by
    by_contra! hn
    have he : pcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨a, ha, _⟩ := hom_output_safe2 I h hS (hom_pure_y.mp hh) (by omega) hlb
    exact ha
  have hl1 : 1 ≤ lcount N t := by
    by_contra! hn
    have he : lcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨_, _, b, hb, _⟩ := hom_output_safe2 I h hS (hom_pure_x.mp hh) hpa (by omega)
    exact hb
  exact ⟨_, _, hp1, hpa, hl1, hlb, hh⟩

private noncomputable def allEdges : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

private lemma allEdges_card (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

end Plane


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

private abbrev Occ (C : Circuit) := Fin C.size × Fin 2
private def atWire (N : ℕ) {C : Circuit} (e : Occ C) : ℕ := outWire (N + N) e.1
private def fromWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 e.2
private def otherWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 (1 - e.2)
private def flip {C : Circuit} (e : Occ C) : Occ C := (e.1, 1 - e.2)

private lemma earlier_occ {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : fromWire e < atWire N e := earlier h e.1 e.2

private lemma earlier_other {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : otherWire e < atWire N e := earlier h e.1 (1 - e.2)

private lemma at_bound (N : ℕ) {C : Circuit} (e : Occ C) :
    atWire N e < N + N + C.size := Nat.add_lt_add_left e.1.isLt _

private lemma at_eq {C : Circuit} {N : ℕ} {e : Occ C} {k : Fin C.size}
    (hh : atWire N e = outWire (N + N) k) : e.1 = k := by
  apply Fin.ext
  exact Nat.add_left_cancel hh

private def andAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.and
private def orAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.or

private def orLink (N : ℕ) (C : Circuit) (w t : ℕ) : Prop :=
  ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ atWire N e = t

private def orPath (N : ℕ) (C : Circuit) := ReflTransGen (orLink N C)

private lemma orPath_head {N : ℕ} {C : Circuit} {w t : ℕ} :
    orPath N C w t ↔ w = t ∨
      ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ orPath N C (atWire N e) t := by
  unfold orPath
  rw [ReflTransGen.cases_head_iff]
  constructor
  · rintro (he | ⟨u, ⟨e, ho, hf, rfl⟩, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨e, ho, hf, ht⟩
  · rintro (he | ⟨e, ho, hf, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨_, ⟨e, ho, hf, rfl⟩, ht⟩

private lemma or_reaches {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : Hom N C w a b X Y) : Hom N C t a b X Y := by
  induction hp with
  | refl => exact hw
  | tail _ hy ih =>
    obtain ⟨e, ho, rfl, rfl⟩ := hy
    exact (hom_or h ho).mpr ⟨e.2, ih⟩

private def tag (s : Bool) {N : ℕ} (p : Fin N) : ℕ :=
  if s then N + p.val else p.val

private lemma tag_lt (s : Bool) {N : ℕ} (p : Fin N) : tag s p < N + N := by
  cases s <;> simp [tag] <;> omega

private lemma tag_inj {s : Bool} {N : ℕ} {p q : Fin N} (h : tag s p = tag s q) : p = q := by
  cases s
  · exact Fin.ext h
  · exact Fin.ext (Nat.add_left_cancel h)

private def OHom (N : ℕ) (C : Circuit) (s : Bool) (w a b : ℕ) (X Y : Set (Fin N)) :=
  if s then Hom N C w b a Y X else Hom N C w a b X Y

private def oneSide (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) (X : Set (Fin N)) :=
  OHom N C s w a 0 X ∅

private def anySide (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X : Set (Fin N)) :=
  ∃ a, oneSide N C s w a X

private def onceSide (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X Y : Set (Fin N)) :=
  ∃ a, OHom N C s w a 1 X Y

private lemma ohom_mono {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') :
    OHom N C s w a b X Y → OHom N C s w a b X' Y' := by
  cases s
  · exact hom_mono hx hy
  · exact hom_mono hy hx

private lemma ohom_pure {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w a 0 X Y ↔ oneSide N C s w a X := by
  cases s
  · exact hom_pure_x
  · exact hom_pure_y

private lemma ohom_void {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ OHom N C s w a b X Y := by
  cases s <;> exact hom_invalid hw

private lemma ohom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)} (hh : OHom N C s w a b X Y) : 0 < a + b := by
  cases s
  · exact hom_pos h hh
  · rw [Nat.add_comm]
    exact hom_pos h hh

private lemma ohom_input {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : w < N + N) :
    OHom N C s w a b X Y ↔
      (a = 1 ∧ b = 0 ∧ ∃ x ∈ X, tag s x = w) ∨ (a = 0 ∧ b = 1 ∧ ∃ y ∈ Y, tag (!s) y = w) := by
  cases s
  · simp only [OHom, Bool.false_eq_true, ite_false, Bool.not_false, tag, ite_true, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inl ⟨ha, hb, i, hi, he⟩
      · omega
      · omega
      · exact Or.inr ⟨ha, hb, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, ha, hb⟩⟩
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, ha, hb⟩⟩
  · simp only [OHom, ite_true, Bool.not_true, tag, Bool.false_eq_true, ite_false, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inr ⟨hb, ha, i, hi, he⟩
      · omega
      · omega
      · exact Or.inl ⟨hb, ha, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, hb, ha⟩⟩
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, hb, ha⟩⟩

private lemma ohom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, OHom N C s (operand C k i) a b X Y := by
  cases s <;> exact hom_or h ho

private lemma ohom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        OHom N C s (operand C k 0) a₀ b₀ X Y ∧ OHom N C s (operand C k 1) a₁ b₁ X Y := by
  cases s
  · exact hom_and h ho
  · exact (hom_and h ho).trans ⟨
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩,
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩⟩

private lemma ohom_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {e : Occ C} (ho : andAt e) {s : Bool} {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : OHom N C s (fromWire e) a b X Y) (h₂ : OHom N C s (otherWire e) c d X Y) :
    OHom N C s (atWire N e) (a + c) (b + d) X Y := by
  cases s <;> exact hom_and_add h ho e.2 h₁ h₂

private lemma one_mono (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) :
    Monotone (oneSide N C s w a) := fun _ _ h hx => ohom_mono h (fun _ he => he) hx

private lemma any_mono (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) :
    Monotone (anySide N C s w) := fun _ _ h ⟨a, ha⟩ => ⟨a, one_mono N C s w a h ha⟩

private lemma one_input {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X : Set (Fin N)}
    (hw : w < N + N) : oneSide N C s w a X ↔ a = 1 ∧ ∃ x ∈ X, tag s x = w := by
  unfold oneSide
  rw [ohom_input hw]
  simp

private lemma one_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a : ℕ} {X : Set (Fin N)} :
    oneSide N C s (outWire (N + N) k) a X ↔ ∃ i : Fin 2, oneSide N C s (operand C k i) a X :=
  ohom_or h ho

private lemma any_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {X : Set (Fin N)} :
    anySide N C s (outWire (N + N) k) X ↔ ∃ i : Fin 2, anySide N C s (operand C k i) X := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, hi⟩ := (one_or h ho).mp ha
    exact ⟨i, a, hi⟩
  · rintro ⟨i, a, hi⟩
    exact ⟨a, (one_or h ho).mpr ⟨i, hi⟩⟩

private lemma one_and_small {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a : ℕ} {X : Set (Fin N)}
    (ha : a ≤ 2) :
    oneSide N C s (outWire (N + N) k) a X ↔
      a = 2 ∧ oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X := by
  unfold oneSide
  rw [ohom_and h ho]
  constructor
  · rintro ⟨a₀, b₀, a₁, b₁, h₁, h₂, h₀, h₁'⟩
    have := ohom_pos h h₀
    have := ohom_pos h h₁'
    obtain rfl : a₀ = 1 := by omega
    obtain rfl : a₁ = 1 := by omega
    obtain rfl : b₀ = 0 := by omega
    obtain rfl : b₁ = 0 := by omega
    exact ⟨by omega, h₀, h₁'⟩
  · rintro ⟨rfl, hl, hr⟩
    exact ⟨1, 0, 1, 0, rfl, rfl, hl, hr⟩

private lemma any_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {X : Set (Fin N)} :
    anySide N C s (outWire (N + N) k) X ↔
      anySide N C s (operand C k 0) X ∧ anySide N C s (operand C k 1) X := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨a₀, b₀, a₁, b₁, _, h₂, hl, hr⟩ := (ohom_and h ho).mp ha
    obtain rfl : b₀ = 0 := by omega
    obtain rfl : b₁ = 0 := by omega
    exact ⟨⟨a₀, hl⟩, ⟨a₁, hr⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, (ohom_and h ho).mpr ⟨a, 0, b, 0, rfl, rfl, ha, hb⟩⟩


section OneOccurrence

-- A word with one leaf on the marked side has a single path from that leaf.
-- An AND on that path contributes a selector on the other side.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private def onceLink (N : ℕ) (C : Circuit) (s : Bool) (X : Set (Fin N)) (w t : ℕ) : Prop :=
  ∃ e : Occ C, fromWire e = w ∧ atWire N e = t ∧
    (orAt e ∨ andAt e ∧ anySide N C s (otherWire e) X)

private def onceBack (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X : Set (Fin N)) : Prop :=
  ReflTransGen (onceLink N C s X) w C.output

private lemma once_step {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w t : ℕ} {X Y : Set (Fin N)} (he : onceLink N C s X w t)
    (hw : onceSide N C s w X Y) : onceSide N C s t X Y := by
  obtain ⟨e, rfl, rfl, ho | ⟨ho, d, hd⟩⟩ := he
  · obtain ⟨a, ha⟩ := hw
    exact ⟨a, (ohom_or h ho).mpr ⟨e.2, ha⟩⟩
  · obtain ⟨a, ha⟩ := hw
    exact ⟨a + d, ohom_add h ho ha (ohom_pure.mpr hd)⟩

private lemma once_follow {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w t : ℕ} {X Y : Set (Fin N)} (ht : ReflTransGen (onceLink N C s X) w t)
    (hw : onceSide N C s w X Y) : onceSide N C s t X Y := by
  induction ht with
  | refl => exact hw
  | tail _ he ih => exact once_step h he ih

private lemma once_leaf {N : ℕ} {C : Circuit} {s : Bool} {X Y : Set (Fin N)} {l : Fin N}
    (hl : l ∈ Y) : onceSide N C s (tag (!s) l) X Y :=
  ⟨0, (ohom_input (tag_lt _ _)).mpr (Or.inr ⟨rfl, rfl, l, hl, rfl⟩)⟩

private lemma once_origin {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {X Y : Set (Fin N)} (w : ℕ) (hw : onceSide N C s w X Y) :
    ∃ l ∈ Y, ReflTransGen (onceLink N C s X) (tag (!s) l) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    obtain ⟨d, hd⟩ := hw
    rcases wire_cases (N + N) C.size w with hi | ⟨k, rfl⟩ | hm
    · rcases (ohom_input hi).mp hd with hbad | ⟨_, _, l, hl, rfl⟩
      · omega
      · exact ⟨l, hl, .refl⟩
    · rcases op_kind h k with ho | ho
      · obtain ⟨a₀, b₀, a₁, b₁, _, hsum, hl, hr⟩ := (ohom_and h ho).mp hd
        by_cases hb₀ : b₀ = 1
        · obtain rfl : b₀ = 1 := hb₀
          obtain rfl : b₁ = 0 := by omega
          obtain ⟨l, hly, hp⟩ := ih _ (earlier h k 0) ⟨a₀, hl⟩
          exact ⟨l, hly, hp.tail ⟨(k, 0), rfl, rfl, Or.inr ⟨ho, a₁, ohom_pure.mp hr⟩⟩⟩
        · obtain rfl : b₀ = 0 := by omega
          obtain rfl : b₁ = 1 := by omega
          obtain ⟨l, hly, hp⟩ := ih _ (earlier h k 1) ⟨a₁, hr⟩
          exact ⟨l, hly, hp.tail ⟨(k, 1), rfl, rfl, Or.inr ⟨ho, a₀, ohom_pure.mp hl⟩⟩⟩
      · obtain ⟨b, hb⟩ := (ohom_or h ho).mp hd
        obtain ⟨l, hly, hp⟩ := ih _ (earlier h k b) ⟨d, hb⟩
        exact ⟨l, hly, hp.tail ⟨(k, b), rfl, rfl, Or.inl ho⟩⟩
    · exact (ohom_void hm hd).elim

private def adjFor {N : ℕ} (I : Fin N → Fin N → Prop) (s : Bool) (p l : Fin N) : Prop :=
  if s then I l p else I p l

private lemma oriented_output_safe {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} (hh : OHom N C s C.output a b X Y) :
    ∃ p ∈ X, ∃ l ∈ Y, adjFor I s p l := by
  cases s
  · exact hom_output_safe I h hC hh
  · obtain ⟨l, hl, p, hp, hi⟩ := hom_output_safe I h hC hh
    exact ⟨p, hp, l, hl, hi⟩

private lemma once_clean {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (s : Bool) (l : Fin N) :
    clean (adjFor I s) (onceBack N C s (tag (!s) l)) l := by
  intro hb
  obtain ⟨a, ha⟩ := once_follow h hb (once_leaf (Set.mem_singleton l))
  obtain ⟨p, hp, l', hl', hi⟩ := oriented_output_safe I h hC ha
  obtain rfl : l' = l := hl'
  exact hp hi

private abbrev OnceNode (C : Circuit) := (ℕ ⊕ ℕ) ⊕ Occ C
private def ofwd {C : Circuit} (w : ℕ) : OnceNode C := .inl (.inl w)
private def oback {C : Circuit} (w : ℕ) : OnceNode C := .inl (.inr w)
private def ojoin {C : Circuit} (e : Occ C) : OnceNode C := .inr e

private def onceNode (N : ℕ) {C : Circuit} (s : Bool) : OnceNode C → Set (Fin N) → Prop
  | .inl (.inl w) => anySide N C s w
  | .inl (.inr w) => onceBack N C s w
  | .inr e => fun X => anySide N C s (otherWire e) X ∧ onceBack N C s (atWire N e) X

private lemma onceBack_mono (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) :
    Monotone (onceBack N C s w) := by
  intro X Y hXY hp
  unfold onceBack at hp ⊢
  generalize C.output = t at hp ⊢
  induction hp with
  | refl => exact .refl
  | tail _ hh ih =>
    obtain ⟨e, rfl, rfl, ho | ⟨ho, hx⟩⟩ := hh
    · exact ih.tail ⟨e, rfl, rfl, Or.inl ho⟩
    · exact ih.tail ⟨e, rfl, rfl, Or.inr ⟨ho, any_mono N C s _ hXY hx⟩⟩

private lemma onceNode_mono (N : ℕ) {C : Circuit} (s : Bool) (w : OnceNode C) :
    Monotone (onceNode N s w) := by
  rcases w with (w | w) | e
  · exact any_mono N C s w
  · exact onceBack_mono N C s w
  · exact fun X Y h hx => ⟨any_mono N C s _ h hx.1, onceBack_mono N C s _ h hx.2⟩

private def onceRank (N : ℕ) {C : Circuit} (w : OnceNode C) : ℕ :=
  let m := N + N + C.size + 1
  match w with
  | .inl (.inl w) => w
  | .inl (.inr w) => m + 2 * (m - w)
  | .inr e => m + 2 * (m - atWire N e) + 1

private noncomputable def onceArcs (C : Circuit) : Finset (Occ C ⊕ Occ C) := by
  classical
  exact univ.filter fun a => a.elim orAt (fun _ => True)

private def onceSrc (N : ℕ) {C : Circuit} : Occ C ⊕ Occ C → OnceNode C
  | .inl e => ofwd (atWire N e)
  | .inr e => oback (fromWire e)

private noncomputable def onceDst (N : ℕ) {C : Circuit} : Occ C ⊕ Occ C → OnceNode C
  | .inl e => ofwd (fromWire e)
  | .inr e => by
    classical
    exact if orAt e then oback (atWire N e) else ojoin e

private lemma no_approved_small {A B : Type*} [Fintype A] (I : A → B → Prop) [DecidableRel I]
    {f : Set A → Prop} {s : Prop} (hc : (single f).card ≤ 1) (l : B) :
    ¬ approved I s f l := by
  rintro (⟨h, _⟩ | ⟨_, h, _⟩) <;> omega

private lemma once_rule {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w : OnceNode C) :
    (∀ c, ¬ approved J False (onceNode N s w) c) ∨
    (∃ u v : OnceNode C, onceRank N u < onceRank N w ∧ onceRank N v < onceRank N w ∧
      ¬ False ∧ ∀ X, onceNode N s w X ↔ onceNode N s u X ∧ onceNode N s v X) ∨
    ((∀ e ∈ onceArcs C, onceSrc N e = w → onceRank N (onceDst N e) < onceRank N w ∧
      (False → False)) ∧
      ∀ X, onceNode N s w X ↔
        ∃ e ∈ onceArcs C, onceSrc N e = w ∧ onceNode N s (onceDst N e) X) := by
  classical
  rcases w with (w | w) | e
  · rcases wire_cases (N + N) C.size w with hin | ⟨k, rfl⟩ | hmiss
    · apply Or.inl
      apply no_approved_small
      refine Finset.card_le_one_iff.mpr ?_
      intro p q hp hq
      obtain ⟨a, ha⟩ := (mem_single _ _).mp hp
      obtain ⟨b, hb⟩ := (mem_single _ _).mp hq
      obtain ⟨_, p', hp', hpt⟩ := (one_input hin).mp ha
      obtain ⟨_, q', hq', hqt⟩ := (one_input hin).mp hb
      obtain rfl : p' = p := hp'
      obtain rfl : q' = q := hq'
      exact tag_inj (hpt.trans hqt.symm)
    · rcases op_kind h k with ho | ho
      · right; left
        exact ⟨ofwd (operand C k 0), ofwd (operand C k 1), earlier h k 0, earlier h k 1,
          not_false, fun _ => any_and h ho⟩
      · right; right
        constructor
        · rintro (e | e) he hh
          · have heq : atWire N e = outWire (N + N) k := by simpa [onceSrc, ofwd] using hh
            exact ⟨by simpa [onceDst, onceRank, ofwd, heq] using earlier_occ h e, id⟩
          · simp [onceSrc, oback, ofwd] at hh
        · intro X
          change anySide N C s (outWire (N + N) k) X ↔ _
          rw [any_or h ho]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨.inl (k, i), by simp [onceArcs, orAt, ho], rfl, hi⟩
          · rintro ⟨(e | e), _, he, ht⟩
            · have heq : atWire N e = outWire (N + N) k := by simpa [onceSrc, ofwd] using he
              have he' := at_eq heq
              exact ⟨e.2, by simpa [onceNode, onceDst, ofwd, fromWire, he'] using ht⟩
            · simp [onceSrc, oback, ofwd] at he
    · apply Or.inl
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp _
      obtain ⟨_, hd⟩ := (mem_single _ _).mp hp
      exact (ohom_void hmiss hd).elim
  · by_cases hw : w = C.output
    · left
      intro c ha
      have ht : onceNode N s (oback (C := C) w) {a | ¬ J a c} := by
        subst w
        exact .refl
      exact (ha.resolve_right (fun z => z.1)).2 ht
    · right; right
      constructor
      · rintro (e | e) he hh
        · simp [onceSrc, ofwd, oback] at hh
        · have heq : fromWire e = w := by simpa [onceSrc, oback] using hh
          have hlt := earlier_occ h e
          have hb := at_bound N e
          refine ⟨?_, id⟩
          by_cases hOr : orAt e
          · simp [onceDst, hOr, onceRank, oback]
            omega
          · simp [onceDst, hOr, onceRank, oback, ojoin]
            omega
      · intro X
        change onceBack N C s w X ↔ _
        unfold onceBack
        rw [ReflTransGen.cases_head_iff]
        simp only [hw, false_or]
        constructor
        · rintro ⟨t, ⟨e, he, rfl, ho | ⟨ho, ha⟩⟩, ht⟩
          · exact ⟨.inr e, by simp [onceArcs], by simpa [onceSrc, oback] using he,
              by simpa [onceDst, ho, onceNode, oback, onceBack] using ht⟩
          · have hn : ¬ orAt e := fun hor => GateOp.noConfusion (ho.symm.trans hor)
            exact ⟨.inr e, by simp [onceArcs], by simpa [onceSrc, oback] using he,
              by simpa [onceDst, hn, onceNode, ojoin, onceBack] using And.intro ha ht⟩
        · rintro ⟨(e | e), _, he, ht⟩
          · simp [onceSrc, ofwd, oback] at he
          · have heq : fromWire e = w := by simpa [onceSrc, oback] using he
            by_cases hor : orAt e
            · refine ⟨atWire N e, ⟨e, heq, rfl, Or.inl hor⟩, ?_⟩
              simpa [onceDst, hor, onceNode, oback, onceBack] using ht
            · have hoa := (op_kind h e.1).resolve_right hor
              obtain ⟨ha, hb⟩ : anySide N C s (otherWire e) X ∧ onceBack N C s (atWire N e) X := by
                simpa [onceDst, hor, onceNode, ojoin] using ht
              exact ⟨_, ⟨e, heq, rfl, Or.inr ⟨hoa, ha⟩⟩, hb⟩
  · right; left
    refine ⟨ofwd (otherWire e), oback (atWire N e), ?_, ?_, not_false, fun _ => Iff.rfl⟩
    · have := earlier_other h e
      have := at_bound N e
      simp [onceRank, ojoin, ofwd]
      omega
    · simp [onceRank, oback, ojoin]

private noncomputable def onceEdges {N : ℕ} (C : Circuit) (J : Fin N → Fin N → Prop) [DecidableRel J]
    (s : Bool) : Finset (Fin N × Fin N) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧ onceBack N C s (tag (!s) e.2) {e.1}

private lemma once_bound {N : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 (N + N) C) (J : Fin N → Fin N → Prop) [DecidableRel J]
    (hf : fourFree J) (s : Bool)
    (hc : ∀ l : Fin N, clean J (onceBack N C s (tag (!s) l)) l) :
    (onceEdges C J s).card ≤ 8 * C.size + N := by
  classical
  let f := onceNode N (C := C) s
  let Pay (l : Fin N) : Finset (Fin N × Fin N) :=
    if (single (onceBack N C s (tag (!s) l))).card ≤ 1 then
      (single (onceBack N C s (tag (!s) l))).map ⟨fun p => (p, l), fun _ _ e => congrArg Prod.fst e⟩
    else ∅
  have hp (l : Fin N) : (Pay l).card ≤ 1 := by
    by_cases hsmall : (single (onceBack N C s (tag (!s) l))).card ≤ 1 <;> simp [Pay, hsmall]
  have hsmall : (univ.biUnion Pay).card ≤ N := by
    calc
      _ ≤ ∑ l : Fin N, (Pay l).card := Finset.card_biUnion_le
      _ ≤ ∑ _l : Fin N, 1 := Finset.sum_le_sum (fun l _ => hp l)
      _ = _ := by simp
  have hCover := cover_bound J hf f (fun _ => False) (onceRank N) (onceArcs C)
    (onceSrc N) (onceDst N) (onceNode_mono N s) (fun _ hb => hb.elim)
    (once_rule h J s)
  have hArc : (onceArcs C).card ≤ 4 * C.size := by
    apply (Finset.card_filter_le _ _).trans
    simp [Fintype.card_sum, Fintype.card_prod]
    omega
  have hsub : onceEdges C J s ⊆ edgeCover J f (fun _ => False) ∪ univ.biUnion Pay := by
    intro e he
    obtain ⟨hi, ht⟩ := (Finset.mem_filter.mp he).2
    have hmem := (mem_single _ _).mpr ht
    by_cases hsm : (single (onceBack N C s (tag (!s) e.2))).card ≤ 1
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_univ _, ?_⟩
      simp only [Pay, ite_eq_left hsm, Finset.mem_map]
      exact ⟨e.1, hmem, rfl⟩
    · have hbig : 2 ≤ (single (onceBack N C s (tag (!s) e.2))).card := by omega
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi,
        oback (tag (!s) e.2), Or.inl ⟨hbig, hc e.2⟩, hmem⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end OneOccurrence


section ChargingOne

open Finset

variable {A B W E : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]

private lemma cover_bound_one (hf : fourFree I) (f : W → Set A → Prop)
    (rank : W → ℕ) (arcs : Finset E) (src dst : E → W)
    (hm : ∀ w, Monotone (f w))
    (hr : ∀ w,
      (∀ c, ¬ approved I False (f w) c) ∨
      (∃ u v, rank u < rank w ∧ rank v < rank w ∧
        ∀ U, f w U ↔ f u U ∧ f v U) ∨
      ((∀ e ∈ arcs, src e = w → rank (dst e) < rank w) ∧
        ∀ U, f w U ↔ ∃ e ∈ arcs, src e = w ∧ f (dst e) U)) :
    (edgeCover I f (fun _ => False)).card ≤ arcs.card := by
  classical
  let Pay (e : E) : Finset (A × B) := univ.filter fun p => I p.1 p.2 ∧
    approved I False (f (src e)) p.2 ∧
    ¬ approved I False (f (dst e)) p.2 ∧
    clean I (f (dst e)) p.2 ∧
    p.1 ∈ single (f (dst e))
  have pay_card (e : E) : (Pay e).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro p hp q hq
    have hpv := (Finset.mem_filter.mp hp).2
    have hqv := (Finset.mem_filter.mp hq).2
    have he : p.2 = q.2 := approved_unique I hf (hm (src e)) hpv.2.1 hqv.2.1
    have hsmall : (single (f (dst e))).card ≤ 1 := by
      by_contra hbig
      exact hpv.2.2.1 (Or.inl ⟨by omega, hpv.2.2.2.1⟩)
    exact Prod.ext (Finset.card_le_one.mp hsmall _ hpv.2.2.2.2 _ hqv.2.2.2.2) he
  have descend (w : W) (p : A × B) (hi : I p.1 p.2)
      (ha : approved I False (f w) p.2) (hsp : p.1 ∈ single (f w)) :
      ∃ e ∈ arcs, p ∈ Pay e := by
    induction ht : rank w using Nat.strong_induction_on generalizing w with
    | ind k ih =>
      have hcl : 2 ≤ (single (f w)).card ∧ clean I (f w) p.2 := ha.resolve_right (fun h => h.1)
      rcases hr w with hl | ⟨u, v, hu, hv, hmeet⟩ | ⟨hsub, hunion⟩
      · exact (hl _ ha).elim
      · have hw := (mem_single _ _).mp hsp
        obtain ⟨hpu, hpv⟩ := (hmeet _).mp hw
        have hcu : clean I (f u) p.2 ∨ clean I (f v) p.2 := by
          by_cases hu : f u {a | ¬ I a p.2}
          · exact Or.inr (fun hv => hcl.2 ((hmeet _).mpr ⟨hu, hv⟩))
          · exact Or.inl hu
        have hSu : single (f w) ⊆ single (f u) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).1
        have hSv : single (f w) ⊆ single (f v) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).2
        rcases hcu with hcu | hcv
        · exact ih (rank u) (ht ▸ hu) u (Or.inl ⟨hcl.1.trans (Finset.card_le_card hSu), hcu⟩)
            ((mem_single _ _).mpr hpu) rfl
        · exact ih (rank v) (ht ▸ hv) v (Or.inl ⟨hcl.1.trans (Finset.card_le_card hSv), hcv⟩)
            ((mem_single _ _).mpr hpv) rfl
      · obtain ⟨e, he, hew, hep⟩ := (hunion _).mp ((mem_single _ _).mp hsp)
        have hnext : clean I (f (dst e)) p.2 :=
          fun hb => hcl.2 ((hunion _).mpr ⟨e, he, hew, hb⟩)
        by_cases hnext' : approved I False (f (dst e)) p.2
        · exact ih (rank (dst e)) (ht ▸ hsub e he hew) _ hnext'
            ((mem_single _ _).mpr hep) rfl
        · refine ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_, hnext', hnext,
            (mem_single _ _).mpr hep⟩⟩
          simpa only [hew] using ha
  have hcover : edgeCover I f (fun _ => False) ⊆ arcs.biUnion Pay := by
    intro p hp
    obtain ⟨hi, w, ha, hsp⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr (descend w p hi ha hsp)
  calc
    _ ≤ (arcs.biUnion Pay).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ arcs, (Pay e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ arcs, 1 := Finset.sum_le_sum (fun e _ => pay_card e)
    _ = _ := by simp

private lemma const_unapproved {f : Set A → Prop} (hc : ∀ X Y, f X → f Y) (c : B) :
    ¬ approved I False f c := by
  rintro (⟨h2, hcl⟩ | ⟨h, _⟩)
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (single f).card)
    exact hcl (hc _ _ ((mem_single f a).mp ha))
  · exact h

end ChargingOne


section OnceBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private def bLink (N : ℕ) (C : Circuit) (s : Bool) (X : Set (Fin N)) (u v : ℕ × ℕ) : Prop :=
  ∃ e : Occ C, fromWire e = u.1 ∧ atWire N e = v.1 ∧
    (orAt e ∧ v.2 = u.2 ∨ andAt e ∧ ∃ d, v.2 = u.2 + d ∧ oneSide N C s (otherWire e) d X)

private def bBack (N : ℕ) (C : Circuit) (s : Bool) (w j : ℕ) (X : Set (Fin N)) : Prop :=
  ∃ a ≤ 2, ReflTransGen (bLink N C s X) (w, j) (C.output, a)

private lemma b_step {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {u v : ℕ × ℕ} {X Y : Set (Fin N)} (he : bLink N C s X u v)
    (hw : OHom N C s u.1 u.2 1 X Y) : OHom N C s v.1 v.2 1 X Y := by
  obtain ⟨w, j⟩ := u
  obtain ⟨t, j'⟩ := v
  obtain ⟨e, h1, h2, ⟨ho, hv⟩ | ⟨ho, d, hv, hd⟩⟩ := he
  · change fromWire e = w at h1
    change atWire N e = t at h2
    change j' = j at hv
    subst h1 h2 hv
    exact (ohom_or h ho).mpr ⟨e.2, hw⟩
  · change fromWire e = w at h1
    change atWire N e = t at h2
    change j' = j + d at hv
    subst h1 h2 hv
    exact ohom_add h ho hw (ohom_pure.mpr hd)

private lemma b_follow {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {u v : ℕ × ℕ} {X Y : Set (Fin N)} (ht : ReflTransGen (bLink N C s X) u v)
    (hw : OHom N C s u.1 u.2 1 X Y) : OHom N C s v.1 v.2 1 X Y := by
  induction ht with
  | refl => exact hw
  | tail _ he ih => exact b_step h he ih

private lemma b_origin {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {X Y : Set (Fin N)} (w : ℕ) {a : ℕ} (hw : OHom N C s w a 1 X Y) :
    ∃ l ∈ Y, ReflTransGen (bLink N C s X) (tag (!s) l, 0) (w, a) := by
  induction w using Nat.strong_induction_on generalizing a with
  | ind w ih =>
    rcases wire_cases (N + N) C.size w with hi | ⟨k, rfl⟩ | hm
    · rcases (ohom_input hi).mp hw with ⟨_, hbad, _⟩ | ⟨rfl, _, l, hl, rfl⟩
      · omega
      · exact ⟨l, hl, .refl⟩
    · rcases op_kind h k with ho | ho
      · obtain ⟨a₀, b₀, a₁, b₁, hsa, hsum, hl, hr⟩ := (ohom_and h ho).mp hw
        by_cases hb₀ : b₀ = 1
        · obtain rfl : b₀ = 1 := hb₀
          obtain rfl : b₁ = 0 := by omega
          obtain ⟨l, hly, hp⟩ := ih _ (earlier h k 0) hl
          exact ⟨l, hly, hp.tail ⟨(k, 0), rfl, rfl, Or.inr ⟨ho, a₁, hsa.symm, ohom_pure.mp hr⟩⟩⟩
        · obtain rfl : b₀ = 0 := by omega
          obtain rfl : b₁ = 1 := by omega
          obtain ⟨l, hly, hp⟩ := ih _ (earlier h k 1) hr
          exact ⟨l, hly, hp.tail ⟨(k, 1), rfl, rfl, Or.inr ⟨ho, a₀, by omega, ohom_pure.mp hl⟩⟩⟩
      · obtain ⟨b, hb⟩ := (ohom_or h ho).mp hw
        obtain ⟨l, hly, hp⟩ := ih _ (earlier h k b) hb
        exact ⟨l, hly, hp.tail ⟨(k, b), rfl, rfl, Or.inl ⟨ho, rfl⟩⟩⟩
    · exact (ohom_void hm hw).elim

private lemma b_count {N : ℕ} {C : Circuit} {s : Bool} {X : Set (Fin N)} {u v : ℕ × ℕ}
    (ht : ReflTransGen (bLink N C s X) u v) : u.2 ≤ v.2 := by
  induction ht with
  | refl => exact le_rfl
  | tail _ he ih =>
    obtain ⟨e, _, _, ⟨_, hv⟩ | ⟨_, d, hv, _⟩⟩ := he
    · omega
    · omega

private lemma b_full {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C) {s : Bool}
    {X Y : Set (Fin N)} {u v : ℕ × ℕ}
    (ht : ReflTransGen (bLink N C s X) u v) (hu : 2 ≤ u.2) (hv : v.2 ≤ 2) :
    ReflTransGen (bLink N C s Y) u v := by
  induction ht with
  | refl => exact .refl
  | tail hb he ih =>
    have hm := b_count hb
    obtain ⟨e, h1, h2, ⟨ho, hc⟩ | ⟨ho, d, hc, hd⟩⟩ := he
    · exact (ih (by omega)).tail ⟨e, h1, h2, Or.inl ⟨ho, hc⟩⟩
    · have := ohom_pos h hd
      omega

private lemma bBack_const {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w j : ℕ} (hj : 2 ≤ j ∨ w = C.output) (X Y : Set (Fin N))
    (hx : bBack N C s w j X) : bBack N C s w j Y := by
  obtain ⟨a, ha, ht⟩ := hx
  rcases hj with hj | rfl
  · exact ⟨a, ha, b_full h ht hj ha⟩
  · have := b_count ht
    exact ⟨j, by simp at this; omega, .refl⟩

private lemma bBack_mono (N : ℕ) (C : Circuit) (s : Bool) (w j : ℕ) :
    Monotone (bBack N C s w j) := by
  rintro X Y hXY ⟨a, ha, hp⟩
  refine ⟨a, ha, ?_⟩
  refine ReflTransGen.mono (r := bLink N C s X) (p := bLink N C s Y) ?_ _ _ hp
  rintro u v ⟨e, h1, h2, hc⟩
  exact ⟨e, h1, h2, hc.imp id
    (fun ⟨ho, d, hv, hd⟩ => ⟨ho, d, hv, one_mono N C s _ d hXY hd⟩)⟩

private abbrev BNode (C : Circuit) := (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ (Occ C × ℕ × ℕ))
private def bfwd {C : Circuit} (w d : ℕ) : BNode C := .inl (w, d)
private def bback {C : Circuit} (w j : ℕ) : BNode C := .inr (.inl (w, j))
private def bjoin {C : Circuit} (e : Occ C) (j d : ℕ) : BNode C := .inr (.inr (e, j, d))

private def bNode (N : ℕ) {C : Circuit} (s : Bool) : BNode C → Set (Fin N) → Prop
  | .inl (w, d) => fun X => d ≤ 2 ∧ oneSide N C s w d X
  | .inr (.inl (w, j)) => bBack N C s w j
  | .inr (.inr (e, j, d)) => fun X =>
      oneSide N C s (otherWire e) d X ∧ bBack N C s (atWire N e) (j + d) X

private def bRank (N : ℕ) {C : Circuit} : BNode C → ℕ
  | .inl (w, _) => w
  | .inr (.inl (w, j)) => (N + N + C.size + 1) + 4 * ((N + N + C.size + 1) - w) + j
  | .inr (.inr (e, _, _)) => (N + N + C.size + 1) + 4 * ((N + N + C.size + 1) - atWire N e) + 3

private lemma bNode_mono (N : ℕ) {C : Circuit} (s : Bool) (w : BNode C) :
    Monotone (bNode N s w) := by
  rcases w with ⟨w, d⟩ | ⟨w, j⟩ | ⟨e, j, d⟩
  · exact fun X Y h hx => ⟨hx.1, one_mono N C s w d h hx.2⟩
  · exact bBack_mono N C s w j
  · exact fun X Y h hx => ⟨one_mono N C s _ d h hx.1, bBack_mono N C s _ _ h hx.2⟩

private noncomputable def bSrc (N : ℕ) {C : Circuit} (a : Occ C × Fin 4) : BNode C := by
  classical
  exact if orAt a.1 then
    (if a.2 = 0 then bfwd (atWire N a.1) 1 else if a.2 = 1 then bfwd (atWire N a.1) 2
      else if a.2 = 2 then bback (fromWire a.1) 0 else bback (fromWire a.1) 1)
  else (if a.2 = 2 then bback (fromWire a.1) 1 else bback (fromWire a.1) 0)

private noncomputable def bDst (N : ℕ) {C : Circuit} (a : Occ C × Fin 4) : BNode C := by
  classical
  exact if orAt a.1 then
    (if a.2 = 0 then bfwd (fromWire a.1) 1 else if a.2 = 1 then bfwd (fromWire a.1) 2
      else if a.2 = 2 then bback (atWire N a.1) 0 else bback (atWire N a.1) 1)
  else (if a.2 = 1 then bjoin a.1 0 2 else if a.2 = 2 then bjoin a.1 1 1 else bjoin a.1 0 1)

end OnceBudget

section FwdRule

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private lemma bSrc_fwd {N : ℕ} {C : Circuit} {a : Occ C × Fin 4} {w d : ℕ}
    (hs : bSrc N a = bfwd w d) :
    orAt a.1 ∧ atWire N a.1 = w ∧
      ((d = 1 ∧ bDst N a = bfwd (fromWire a.1) 1) ∨ (d = 2 ∧ bDst N a = bfwd (fromWire a.1) 2)) := by
  classical
  unfold bSrc at hs
  by_cases h1 : orAt a.1
  · rw [if_pos h1] at hs
    by_cases h2 : a.2 = 0
    · rw [if_pos h2] at hs
      simp only [bfwd, Sum.inl.injEq, Prod.mk.injEq] at hs
      refine ⟨h1, hs.1, Or.inl ⟨hs.2.symm, ?_⟩⟩
      unfold bDst
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h2] at hs
      by_cases h3 : a.2 = 1
      · rw [if_pos h3] at hs
        simp only [bfwd, Sum.inl.injEq, Prod.mk.injEq] at hs
        refine ⟨h1, hs.1, Or.inr ⟨hs.2.symm, ?_⟩⟩
        unfold bDst
        rw [if_pos h1, if_neg h2, if_pos h3]
      · rw [if_neg h3] at hs
        split_ifs at hs <;> simp [bfwd, bback] at hs
  · rw [if_neg h1] at hs
    split_ifs at hs <;> simp [bfwd, bback] at hs

private lemma b_rule_fwd {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w d : ℕ) :
    (∀ c, ¬ approved J False (bNode N s (bfwd (C := C) w d)) c) ∨
    (∃ u v : BNode C, bRank N u < bRank N (bfwd (C := C) w d) ∧
      bRank N v < bRank N (bfwd (C := C) w d) ∧
      ∀ U, bNode N s (bfwd (C := C) w d) U ↔ bNode N s u U ∧ bNode N s v U) ∨
    ((∀ e ∈ (univ : Finset (Occ C × Fin 4)), bSrc N e = bfwd w d →
        bRank N (bDst N e) < bRank N (bfwd (C := C) w d)) ∧
      ∀ U, bNode N s (bfwd (C := C) w d) U ↔
        ∃ e ∈ (univ : Finset (Occ C × Fin 4)), bSrc N e = bfwd w d ∧ bNode N s (bDst N e) U) := by
  classical
  rcases wire_cases (N + N) C.size w with hin | ⟨k, rfl⟩ | hmiss
  · left
    apply no_approved_small
    refine Finset.card_le_one_iff.mpr ?_
    intro p q hp hq
    have hp' : d ≤ 2 ∧ oneSide N C s w d {p} := (mem_single _ _).mp hp
    have hq' : d ≤ 2 ∧ oneSide N C s w d {q} := (mem_single _ _).mp hq
    obtain ⟨_, p', hp'', hpt⟩ := (one_input hin).mp hp'.2
    obtain ⟨_, q', hq'', hqt⟩ := (one_input hin).mp hq'.2
    obtain rfl : p' = p := hp''
    obtain rfl : q' = q := hq''
    exact tag_inj (hpt.trans hqt.symm)
  · rcases op_kind h k with ho | ho
    · by_cases hd : d = 2
      · subst hd
        right; left
        refine ⟨bfwd (operand C k 0) 1, bfwd (operand C k 1) 1, earlier h k 0, earlier h k 1,
          fun U => ?_⟩
        show (2 ≤ 2 ∧ oneSide N C s (outWire (N + N) k) 2 U) ↔
          (1 ≤ 2 ∧ oneSide N C s (operand C k 0) 1 U) ∧ (1 ≤ 2 ∧ oneSide N C s (operand C k 1) 1 U)
        rw [one_and_small h ho le_rfl]
        simp
      · left
        intro c
        apply const_unapproved
        intro X Y hX
        exfalso
        have hX' : d ≤ 2 ∧ oneSide N C s (outWire (N + N) k) d X := hX
        exact hd ((one_and_small h ho hX'.1).mp hX'.2).1
    · by_cases hd : d = 1 ∨ d = 2
      · right; right
        constructor
        · rintro a - hs
          obtain ⟨h1, h2, hb⟩ := bSrc_fwd hs
          have hk := at_eq h2
          have hlt := earlier_occ (N := N) h a.1
          rcases hb with ⟨_, hdst⟩ | ⟨_, hdst⟩
          · rw [hdst]
            show fromWire a.1 < outWire (N + N) k
            rw [← h2]
            exact hlt
          · rw [hdst]
            show fromWire a.1 < outWire (N + N) k
            rw [← h2]
            exact hlt
        · intro U
          constructor
          · intro hU
            have hU' : d ≤ 2 ∧ oneSide N C s (outWire (N + N) k) d U := hU
            obtain ⟨i, hi⟩ := (one_or h ho).mp hU'.2
            have hor : orAt ((k, i) : Occ C) := ho
            rcases hd with rfl | rfl
            · refine ⟨((k, i), 0), Finset.mem_univ _, ?_, ?_⟩
              · unfold bSrc
                rw [if_pos hor, if_pos rfl]
                rfl
              · unfold bDst
                rw [if_pos hor, if_pos rfl]
                exact ⟨by omega, hi⟩
            · refine ⟨((k, i), 1), Finset.mem_univ _, ?_, ?_⟩
              · unfold bSrc
                rw [if_pos hor, if_neg (by simp), if_pos rfl]
                rfl
              · unfold bDst
                rw [if_pos hor, if_neg (by simp), if_pos rfl]
                exact ⟨by omega, hi⟩
          · rintro ⟨a, -, hs, hdst⟩
            obtain ⟨h1, h2, hb⟩ := bSrc_fwd hs
            have hk := at_eq h2
            obtain ⟨e1, e2⟩ := a
            simp only at hk h1 h2
            subst hk
            rcases hb with ⟨rfl, hd'⟩ | ⟨rfl, hd'⟩
            · rw [hd'] at hdst
              have hdst' : 1 ≤ 2 ∧ oneSide N C s (operand C e1.1 e1.2) 1 U := hdst
              exact ⟨by omega, (one_or h ho).mpr ⟨e1.2, hdst'.2⟩⟩
            · rw [hd'] at hdst
              have hdst' : 2 ≤ 2 ∧ oneSide N C s (operand C e1.1 e1.2) 2 U := hdst
              exact ⟨le_rfl, (one_or h ho).mpr ⟨e1.2, hdst'.2⟩⟩
      · left
        intro c
        apply const_unapproved
        intro X Y hX
        exfalso
        have hX' : d ≤ 2 ∧ oneSide N C s (outWire (N + N) k) d X := hX
        have := ohom_pos h hX'.2
        omega
  · left
    intro c
    apply const_unapproved
    intro X Y hX
    exfalso
    have hX' : d ≤ 2 ∧ oneSide N C s w d X := hX
    exact ohom_void hmiss hX'.2

end FwdRule


section BRule

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private lemma b_rule_join {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (e : Occ C) (j d : ℕ) :
    (∀ c, ¬ approved J False (bNode N s (bjoin e j d)) c) ∨
    (∃ u v : BNode C, bRank N u < bRank N (bjoin e j d) ∧ bRank N v < bRank N (bjoin e j d) ∧
      ∀ X, bNode N s (bjoin e j d) X ↔ bNode N s u X ∧ bNode N s v X) := by
  by_cases hjd : j + d ≤ 2
  · right
    refine ⟨bfwd (otherWire e) d, bback (atWire N e) (j + d), ?_, ?_, fun X => ?_⟩
    · have := earlier_other h e
      have := at_bound N e
      simp only [bRank, bfwd, bjoin]
      omega
    · simp only [bRank, bback, bjoin]
      omega
    · change (oneSide N C s (otherWire e) d X ∧ bBack N C s (atWire N e) (j + d) X) ↔
        ((d ≤ 2 ∧ oneSide N C s (otherWire e) d X) ∧ bBack N C s (atWire N e) (j + d) X)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, h1⟩, h2⟩
      · rintro ⟨⟨_, h1⟩, h2⟩
        exact ⟨h1, h2⟩
  · left
    intro c ha
    rcases ha with ⟨h2, _⟩ | ⟨hf, _⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp
        (by omega : 0 < (single (bNode N s (bjoin (C := C) e j d))).card)
      obtain ⟨_, a', ha', hp⟩ := (mem_single _ a).mp ha
      have := b_count hp
      simp only at this
      omega
    · exact hf

private lemma b_rule_back {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w j : ℕ) :
    (∀ c, ¬ approved J False (bNode N s (bback (C := C) w j)) c) ∨
    ((∀ a ∈ (Finset.univ : Finset (Occ C × Fin 4)), bSrc N a = bback w j →
        bRank N (bDst N a) < bRank N (bback (C := C) w j)) ∧
      ∀ X, bNode N s (bback (C := C) w j) X ↔
        ∃ a ∈ (Finset.univ : Finset (Occ C × Fin 4)), bSrc N a = bback w j ∧
          bNode N s (bDst N a) X) := by
  classical
  by_cases hc : 2 ≤ j ∨ w = C.output
  · left
    intro c
    exact const_unapproved J (fun X Y hx => bBack_const h hc X Y hx) c
  · right
    push_neg at hc
    obtain ⟨hj, hw⟩ := hc
    constructor
    · rintro ⟨e, i⟩ _ hs
      have hlt := earlier_occ h e
      have hb := at_bound N e
      by_cases hor : orAt e
      · fin_cases i <;> simp [bSrc, bDst, hor, bfwd, bback, bRank] at hs ⊢ <;> omega
      · fin_cases i <;> simp [bSrc, bDst, hor, bfwd, bback, bjoin, bRank] at hs ⊢ <;> omega
    · intro X
      constructor
      · rintro ⟨a, ha, hp⟩
        rcases ReflTransGen.cases_head hp with he | ⟨⟨t1, t2⟩, hl, hr⟩
        · exact (hw (congrArg Prod.fst he)).elim
        · have hcnt := b_count hr
          simp only at hcnt
          obtain ⟨e, h1, h2, ⟨ho, h3⟩ | ⟨ho, d, h3, hd⟩⟩ := hl
          · change fromWire e = w at h1
            change atWire N e = t1 at h2
            change t2 = j at h3
            subst h1 h2 h3
            have hor : orAt e := ho
            obtain rfl | rfl : t2 = 0 ∨ t2 = 1 := by omega
            · refine ⟨(e, 2), Finset.mem_univ _, by simp [bSrc, hor], ?_⟩
              simp only [bDst, hor, if_true]
              exact ⟨a, ha, hr⟩
            · refine ⟨(e, 3), Finset.mem_univ _, by simp [bSrc, hor], ?_⟩
              simp only [bDst, hor, if_true]
              exact ⟨a, ha, hr⟩
          · change fromWire e = w at h1
            change atWire N e = t1 at h2
            change t2 = j + d at h3
            subst h1 h2 h3
            have hor : ¬ orAt e := fun hor => GateOp.noConfusion (ho.symm.trans hor)
            have hpos := ohom_pos h hd
            obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
                (j = 0 ∧ d = 1) ∨ (j = 0 ∧ d = 2) ∨ (j = 1 ∧ d = 1) := by omega
            · refine ⟨(e, 0), Finset.mem_univ _, by simp [bSrc, hor], ?_⟩
              simp only [bDst, hor, if_false]
              exact ⟨hd, a, ha, hr⟩
            · refine ⟨(e, 1), Finset.mem_univ _, by simp [bSrc, hor], ?_⟩
              simp only [bDst, hor, if_false]
              exact ⟨hd, a, ha, hr⟩
            · refine ⟨(e, 2), Finset.mem_univ _, by simp [bSrc, hor], ?_⟩
              simp only [bDst, hor, if_false]
              exact ⟨hd, a, ha, hr⟩
      · rintro ⟨⟨e, i⟩, _, hs, hd⟩
        by_cases hor : orAt e
        · fin_cases i <;> simp [bSrc, bDst, hor, bfwd, bback, bjoin, bNode] at hs hd
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 0))
              ⟨e, rfl, rfl, Or.inl ⟨hor, rfl⟩⟩ hp⟩
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 1))
              ⟨e, rfl, rfl, Or.inl ⟨hor, rfl⟩⟩ hp⟩
        · have hoa : andAt e := (op_kind h e.1).resolve_right hor
          fin_cases i <;> simp [bSrc, bDst, hor, bfwd, bback, bjoin, bNode] at hs hd
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨hx, a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 0 + 1))
              ⟨e, rfl, rfl, Or.inr ⟨hoa, 1, rfl, hx⟩⟩ hp⟩
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨hx, a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 0 + 2))
              ⟨e, rfl, rfl, Or.inr ⟨hoa, 2, rfl, hx⟩⟩ hp⟩
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨hx, a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 1 + 1))
              ⟨e, rfl, rfl, Or.inr ⟨hoa, 1, rfl, hx⟩⟩ hp⟩
          · obtain ⟨rfl, rfl⟩ := hs
            obtain ⟨hx, a', ha', hp⟩ := hd
            exact ⟨a', ha', ReflTransGen.head (b := (atWire N e, 0 + 1))
              ⟨e, rfl, rfl, Or.inr ⟨hoa, 1, rfl, hx⟩⟩ hp⟩

end BRule

section OnceAssembly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private noncomputable def onceB {N : ℕ} (C : Circuit) (J : Fin N → Fin N → Prop) [DecidableRel J]
    (s : Bool) : Finset (Fin N × Fin N) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧ ∃ a, 1 ≤ a ∧ a ≤ 2 ∧ OHom N C s C.output a 1 {e.1} {e.2}

private lemma b_rule {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w : BNode C) :
    (∀ c, ¬ approved J False (bNode N s w) c) ∨
    (∃ u v : BNode C, bRank N u < bRank N w ∧ bRank N v < bRank N w ∧
      ∀ X, bNode N s w X ↔ bNode N s u X ∧ bNode N s v X) ∨
    ((∀ e ∈ (univ : Finset (Occ C × Fin 4)), bSrc N e = w → bRank N (bDst N e) < bRank N w) ∧
      ∀ X, bNode N s w X ↔
        ∃ e ∈ (univ : Finset (Occ C × Fin 4)), bSrc N e = w ∧ bNode N s (bDst N e) X) := by
  rcases w with ⟨w, d⟩ | ⟨w, j⟩ | ⟨e, j, d⟩
  · exact b_rule_fwd h J s w d
  · rcases b_rule_back h J s w j with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inr h2)
  · rcases b_rule_join h J s e j d with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)

private lemma once_budget_bound {N : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 (N + N) C) (J : Fin N → Fin N → Prop) [DecidableRel J]
    (hf : fourFree J) (s : Bool)
    (hsafe : ∀ X Y : Set (Fin N), ∀ a, a ≤ 2 → OHom N C s C.output a 1 X Y →
      ∃ p ∈ X, ∃ l ∈ Y, J p l) :
    (onceB C J s).card ≤ 8 * C.size + N := by
  classical
  let g (l : Fin N) : Set (Fin N) → Prop := bBack N C s (tag (!s) l) 0
  let Pay (l : Fin N) : Finset (Fin N × Fin N) :=
    if (single (g l)).card ≤ 1 then
      (single (g l)).map ⟨fun p => (p, l), fun _ _ e => congrArg Prod.fst e⟩
    else ∅
  have hp (l : Fin N) : (Pay l).card ≤ 1 := by
    by_cases hsmall : (single (g l)).card ≤ 1 <;> simp [Pay, hsmall]
  have hsmall : (univ.biUnion Pay).card ≤ N := by
    calc
      _ ≤ ∑ l : Fin N, (Pay l).card := Finset.card_biUnion_le
      _ ≤ ∑ _l : Fin N, 1 := Finset.sum_le_sum (fun l _ => hp l)
      _ = _ := by simp
  have hCover := cover_bound_one J hf (bNode N (C := C) s) (bRank N)
    (univ : Finset (Occ C × Fin 4)) (bSrc N) (bDst N) (bNode_mono N s) (b_rule h J s)
  have hArc : (univ : Finset (Occ C × Fin 4)).card = 8 * C.size := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  have hclean (l : Fin N) : clean J (g l) l := by
    intro hb
    obtain ⟨a, ha, ht⟩ := hb
    have h0 : OHom N C s (tag (!s) l) 0 1 {x | ¬ J x l} {l} :=
      (ohom_input (tag_lt _ _)).mpr (Or.inr ⟨rfl, rfl, l, Set.mem_singleton l, rfl⟩)
    have hout := b_follow h ht h0
    obtain ⟨p, hp, l', hl', hi⟩ := hsafe _ _ a ha hout
    obtain rfl : l' = l := hl'
    exact hp hi
  have hsub : onceB C J s ⊆
      edgeCover J (bNode N (C := C) s) (fun _ => False) ∪ univ.biUnion Pay := by
    intro e he
    obtain ⟨hi, a, _, ha2, ht⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨l', hl', hpath⟩ := b_origin h C.output ht
    obtain rfl : l' = e.2 := hl'
    have hg : g e.2 {e.1} := ⟨a, ha2, hpath⟩
    have hmem : e.1 ∈ single (g e.2) := (mem_single _ _).mpr hg
    by_cases hsm : (single (g e.2)).card ≤ 1
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_univ _, ?_⟩
      simp only [Pay, if_pos hsm, Finset.mem_map]
      exact ⟨e.1, hmem, rfl⟩
    · have hbig : 2 ≤ (single (g e.2)).card := by omega
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi,
        bback (tag (!s) e.2) 0, Or.inl ⟨hbig, hclean e.2⟩, hmem⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end OnceAssembly


section Shapes

-- Classify the ways a binary AND can split the two side multiplicities.

open PEqualNP.CircuitLowerBounds Relation

private lemma ohom_pure_other {N : ℕ} {C : Circuit} {s : Bool}
    {w b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w 0 b X Y ↔ oneSide N C (!s) w b Y := by
  cases s
  · exact hom_pure_y
  · exact hom_pure_x

private lemma ohom_or_reach {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : OHom N C s w a b X Y) : OHom N C s t a b X Y := by
  cases s <;> exact or_reaches h hp hw

private lemma and_origin {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X Y : Set (Fin N)) (w : ℕ) :
    OHom N C s w a b X Y ↔ ∃ k : Fin C.size, (row C k).op = GateOp.and ∧
      orPath N C (outWire (N + N) k) w ∧ OHom N C s (outWire (N + N) k) a b X Y := by
  refine ⟨?_, fun ⟨_, _, hp, hh⟩ => ohom_or_reach h hp hh⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hh
    rcases wire_cases (N + N) C.size w with hi | ⟨k, rfl⟩ | hm
    · have hf := (ohom_input hi).mp hh
      rcases hf with hf | hf <;> omega
    · rcases op_kind h k with ho | ho
      · exact ⟨k, ho, .refl, hh⟩
      · obtain ⟨i, hsub⟩ := (ohom_or h ho).mp hh
        obtain ⟨k', ho', hp, ht⟩ := ih _ (earlier h k i) hsub
        exact ⟨k', ho', hp.tail ⟨(k, i), ho, rfl, rfl⟩, ht⟩
    · exact (ohom_void hm hh).elim

private lemma mixed11 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 1 1 X Y ↔ ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      oneSide N C false (fromWire e) 1 X ∧ oneSide N C true (otherWire e) 1 Y := by
  refine ⟨?_, ?_⟩
  · intro hw
    obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 1) (by decide : 0 < 1) X Y w).mp hw
    obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
    have hpos₁ := hom_pos h h₁
    have hpos₂ := hom_pos h h₂
    have hs : (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by omega
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨(k, 0), ho, hp, hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩
    · exact ⟨(k, 1), ho, hp, hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩
  · rintro ⟨e, ho, hp, h₁, h₂⟩
    exact or_reaches h hp (hom_and_add h ho e.2 (hom_pure_x.mpr h₁) (hom_pure_y.mpr h₂))

private lemma mixed21 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w : ℕ} {X Y : Set (Fin N)} (hw : OHom N C s w 2 1 X Y) :
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C s (fromWire e) 2 X ∧ oneSide N C (!s) (otherWire e) 1 Y) ∨
       (OHom N C s (fromWire e) 1 1 X Y ∧ oneSide N C s (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h s (by decide : 0 < 2) (by decide : 0 < 1) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (ohom_and h ho).mp hk
  have hpos₁ := ohom_pos h h₁
  have hpos₂ := ohom_pos h h₂
  have hs : (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 0) ∨
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 1) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨(k, 0), ho, hp, Or.inl ⟨ohom_pure.mp h₁, ohom_pure_other.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inl ⟨ohom_pure.mp h₂, ohom_pure_other.mp h₁⟩⟩
  · exact ⟨(k, 0), ho, hp, Or.inr ⟨h₁, ohom_pure.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inr ⟨h₂, ohom_pure.mp h₁⟩⟩

private lemma mixed22 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} (hw : Hom N C w 2 2 X Y) :
    (∃ k : Fin C.size, (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) w ∧
      Hom N C (operand C k 0) 1 1 X Y ∧ Hom N C (operand C k 1) 1 1 X Y) ∨
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C false (fromWire e) 2 X ∧ oneSide N C true (otherWire e) 2 Y) ∨
       (Hom N C (fromWire e) 2 1 X Y ∧ oneSide N C true (otherWire e) 1 Y) ∨
       (Hom N C (fromWire e) 1 2 X Y ∧ oneSide N C false (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 2) (by decide : 0 < 2) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
  have hpos₁ := hom_pos h h₁
  have hpos₂ := hom_pos h h₂
  have hs : (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 0) ∨
      (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
      (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 2) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨k, ho, hp, h₁, h₂⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inl ⟨hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inl ⟨hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inl ⟨h₁, hom_pure_y.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inl ⟨h₂, hom_pure_y.mp h₁⟩)⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inr ⟨h₁, hom_pure_x.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inr ⟨h₂, hom_pure_x.mp h₁⟩)⟩

private def backOne (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X : Set (Fin N)) : Prop :=
  ∃ e : Occ C, andAt e ∧ orPath N C w (fromWire e) ∧ orPath N C (atWire N e) C.output ∧
    oneSide N C s (otherWire e) 1 X

private lemma backOne_mono (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) :
    Monotone (backOne N C s w) :=
  fun _ _ hx ⟨e, ha, hp, ht, hh⟩ => ⟨e, ha, hp, ht, one_mono N C s _ _ hx hh⟩

private lemma backOne_head {N : ℕ} {C : Circuit} {s : Bool} {w : ℕ} {X : Set (Fin N)} :
    backOne N C s w X ↔ ∃ e : Occ C, fromWire e = w ∧
      ((orAt e ∧ backOne N C s (atWire N e) X) ∨
       (andAt e ∧ orPath N C (atWire N e) C.output ∧ oneSide N C s (otherWire e) 1 X)) := by
  constructor
  · rintro ⟨e, ha, hp, ht, hh⟩
    rcases orPath_head.mp hp with he | ⟨e', ho, he, hp'⟩
    · exact ⟨e, he.symm, Or.inr ⟨ha, ht, hh⟩⟩
    · exact ⟨e', he, Or.inl ⟨ho, e, ha, hp', ht, hh⟩⟩
  · rintro ⟨e, rfl, ⟨ho, e', ha, hp, ht, hh⟩ | ⟨ha, ht, hh⟩⟩
    · exact ⟨e', ha, orPath_head.mpr (Or.inr ⟨e, ho, rfl, hp⟩), ht, hh⟩
    · exact ⟨e, ha, .refl, ht, hh⟩

private lemma backOne_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {a b w : ℕ} {X Y : Set (Fin N)}
    (hb : backOne N C s w X) (hh : OHom N C s w a b X Y) :
    OHom N C s C.output (a + 1) b X Y := by
  obtain ⟨e, ho, hp, ht, hx⟩ := hb
  exact ohom_or_reach h ht (ohom_add h ho (ohom_or_reach h hp hh) (ohom_pure.mpr hx))

end Shapes


section PureNetwork

-- Count shared forward selectors and selectors for one remaining leaf along the output path.

open Finset PEqualNP.CircuitLowerBounds

private lemma one_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    oneSide N C s w 1 X ↔ ∃ p ∈ single (oneSide N C s w 1), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => one_mono N C s w 1 (Set.singleton_subset_iff.mpr hx) hp⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases wire_cases (N + N) C.size w with hh | ⟨k, rfl⟩ | hm
    · obtain ⟨_, p, hp, hv⟩ := (one_input hh).mp hw
      exact ⟨p, (one_input hh).mpr ⟨rfl, p, by simp, hv⟩, hp⟩
    · rcases op_kind h k with ha | ho
      · have hbad := (one_and_small h ha (by decide)).mp hw
        omega
      · obtain ⟨i, hi⟩ := (one_or h ho).mp hw
        obtain ⟨p, hp, hx⟩ := ih _ (earlier h k i) hi
        exact ⟨p, (one_or h ho).mpr ⟨i, hp⟩, hx⟩
    · exact (ohom_void hm hw).elim

private lemma back_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    backOne N C s w X ↔ ∃ p ∈ single (backOne N C s w), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => backOne_mono N C s w (Set.singleton_subset_iff.mpr hx) hp⟩
  rintro ⟨e, ha, hp, ht, h1⟩
  obtain ⟨p, hm, hx⟩ := (one_linear h s (otherWire e) X).mp h1
  exact ⟨p, ⟨e, ha, hp, ht, (mem_single _ _).mp hm⟩, hx⟩

private abbrev PureNode (C : Circuit) := ((Fin 2 × ℕ) ⊕ ℕ) ⊕ Occ C
private abbrev PureArc (C : Circuit) := (Fin 2 × Occ C) ⊕ Occ C
private def pfwd {C : Circuit} (d : Fin 2) (w : ℕ) : PureNode C := .inl (.inl (d, w))
private def pbck {C : Circuit} (w : ℕ) : PureNode C := .inl (.inr w)
private def pjoin {C : Circuit} (e : Occ C) : PureNode C := .inr e

private def pureNode (N : ℕ) {C : Circuit} (s : Bool) : PureNode C → Set (Fin N) → Prop
  | .inl (.inl (d, w)) => oneSide N C s w (1 + d.val)
  | .inl (.inr w) => backOne N C s w
  | .inr e => fun X => oneSide N C s (fromWire e) 1 X ∧ backOne N C s (atWire N e) X

private def pureSimple {C : Circuit} : PureNode C → Prop
  | .inl (.inl (d, _)) => d = 0
  | .inl (.inr _) => True
  | .inr _ => False

private lemma pureNode_mono (N : ℕ) {C : Circuit} (s : Bool) (w : PureNode C) :
    Monotone (pureNode N s w) := by
  rcases w with (⟨d, w⟩ | w) | e
  · exact one_mono N C s w _
  · exact backOne_mono N C s w
  · exact fun X Y h hx => ⟨one_mono N C s _ _ h hx.1, backOne_mono N C s _ h hx.2⟩

private lemma pureNode_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : PureNode C) (hs : pureSimple w) (X : Set (Fin N)) :
    pureNode N s w X ↔ ∃ p ∈ single (pureNode N s w), p ∈ X := by
  rcases w with (⟨d, w⟩ | w) | e
  · obtain rfl : d = 0 := hs
    exact one_linear h s w X
  · exact back_linear h s w X
  · exact hs.elim

private def pureRank (N : ℕ) {C : Circuit} (w : PureNode C) : ℕ :=
  let m := N + N + C.size + 1
  match w with
  | .inl (.inl (_, w)) => w
  | .inl (.inr w) => m + (m - w)
  | .inr _ => 2 * m + 1

private def endAnd (N : ℕ) {C : Circuit} (e : Occ C) : Prop :=
  andAt e ∧ orPath N C (atWire N e) C.output

private noncomputable def pureArcs (N : ℕ) (C : Circuit) : Finset (PureArc C) := by
  classical
  exact univ.filter fun a => a.elim (fun e => orAt e.2) (fun e => orAt e ∨ endAnd N e)

private def pureSrc (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (atWire N e)
  | .inr e => pbck (fromWire e)

private noncomputable def pureDst (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (fromWire e)
  | .inr e => by
    classical
    exact if orAt e then pbck (atWire N e) else pfwd 0 (otherWire e)

private lemma pure_rule {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w : PureNode C) :
    (∀ c, ¬ approved J (pureSimple w) (pureNode N s w) c) ∨
    (∃ u v : PureNode C, pureRank N u < pureRank N w ∧ pureRank N v < pureRank N w ∧
      ¬ pureSimple w ∧ ∀ X, pureNode N s w X ↔ pureNode N s u X ∧ pureNode N s v X) ∨
    ((∀ e ∈ pureArcs N C, pureSrc N e = w → pureRank N (pureDst N e) < pureRank N w ∧
      (pureSimple w → pureSimple (pureDst N e))) ∧
      ∀ X, pureNode N s w X ↔
        ∃ e ∈ pureArcs N C, pureSrc N e = w ∧ pureNode N s (pureDst N e) X) := by
  classical
  rcases w with (⟨d, w⟩ | w) | e
  · rcases wire_cases (N + N) C.size w with hin | ⟨k, rfl⟩ | hmiss
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp hq
      obtain ⟨_, p', hp', hpt⟩ := (one_input hin).mp ((mem_single _ _).mp hp)
      obtain ⟨_, q', hq', hqt⟩ := (one_input hin).mp ((mem_single _ _).mp hq)
      obtain rfl : p' = p := hp'
      obtain rfl : q' = q := hq'
      exact tag_inj (hpt.trans hqt.symm)
    · rcases op_kind h k with ho | ho
      · fin_cases d
        · left
          apply no_approved_small
          apply Finset.card_le_one_iff.mpr
          intro p q hp _
          have hh := (one_and_small h ho (by decide)).mp ((mem_single _ _).mp hp)
          exact (by decide : (1 : ℕ) ≠ 2) hh.1 |>.elim
        · right; left
          exact ⟨pfwd 0 (operand C k 0), pfwd 0 (operand C k 1), earlier h k 0, earlier h k 1,
            by change (1 : Fin 2) ≠ 0; decide, fun X => by
              change oneSide N C s (outWire (N + N) k) 2 X ↔
                oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X
              simpa using (one_and_small h ho (by decide : (2 : ℕ) ≤ 2) (s := s) (X := X))⟩
      · right; right
        constructor
        · rintro (⟨i, e⟩ | e) _ he
          · change Sum.inl (Sum.inl (i, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at he
            obtain ⟨rfl, hw⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj he))
            exact ⟨by simpa [pureDst, pureRank, pfwd, hw] using earlier_occ h e, id⟩
          · simp [pureSrc, pbck] at he
        · intro X
          change oneSide N C s (outWire (N + N) k) (1 + d.val) X ↔ _
          rw [one_or h ho]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨.inl (d, (k, i)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, rfl, hi⟩
          · rintro ⟨(⟨j, e⟩ | e), _, hi, ht⟩
            · change Sum.inl (Sum.inl (j, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at hi
              obtain ⟨rfl, hh⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj hi))
              have heq := at_eq hh
              exact ⟨e.2, by simpa [pureNode, pureDst, pfwd, fromWire, heq] using ht⟩
            · simp [pureSrc, pbck] at hi
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp _
      have hh : oneSide N C s w (1 + d.val) {p} := (mem_single _ _).mp hp
      exact (ohom_void hmiss hh).elim
  · right; right
    constructor
    · rintro (⟨d, e⟩ | e) _ he
      · simp [pureSrc, pfwd] at he
      · have heq : fromWire e = w := by simpa [pureSrc, pbck] using he
        have hh := earlier_occ h e
        have hb := at_bound N e
        have hb' := earlier_other h e
        by_cases ho : orAt e
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pbck, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck]
          omega
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pfwd, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck, pfwd]
          omega
    · intro X
      change backOne N C s w X ↔ _
      rw [backOne_head]
      constructor
      · rintro ⟨e, he, ⟨ho, ht⟩ | ⟨ha, hp, ht⟩⟩
        · exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ho⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, ho, pbck] using ht⟩
        · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (ha.symm.trans ho)
          exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ha, hp⟩⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, hn, pfwd] using ht⟩
      · rintro ⟨(e | e), he, hp, ht⟩
        · obtain ⟨d, e⟩ := e
          simp [pureSrc, pfwd] at hp
        · have heq : fromWire e = w := by simpa [pureSrc, pbck] using hp
          by_cases ho : orAt e
          · exact ⟨e, heq, Or.inl ⟨ho, by simpa [pureNode, pureDst, ho, pbck] using ht⟩⟩
          · have hAnd : endAnd N e := ((Finset.mem_filter.mp he).2 : orAt e ∨ endAnd N e).resolve_left ho
            exact ⟨e, heq, Or.inr ⟨hAnd.1, hAnd.2, by simpa [pureNode, pureDst, ho, pfwd] using ht⟩⟩
  · right; left
    refine ⟨pfwd 0 (fromWire e), pbck (atWire N e), ?_, ?_, not_false, fun _ => Iff.rfl⟩
    · have := earlier_occ h e
      have := at_bound N e
      simp [pureRank, pfwd]
      omega
    · simp [pureRank, pbck]
      omega

private lemma pure_bound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (hf : fourFree J) (s : Bool) :
    (edgeCover J (pureNode N (C := C) s) pureSimple).card ≤ 12 * C.size := by
  classical
  have hh := cover_bound J hf (pureNode N (C := C) s) pureSimple (pureRank N)
    (pureArcs N C) (pureSrc N) (pureDst N) (pureNode_mono N s) (pureNode_linear h s) (pure_rule h J s)
  have ha : (pureArcs N C).card ≤ 6 * C.size := by
    apply (Finset.card_filter_le _ _).trans
    simp [Fintype.card_sum, Fintype.card_prod]
    omega
  omega

end PureNetwork


section Rectangles

-- In a sound product of two rectangle families, a pair of bad opposite centers must be incident.
-- Otherwise two choices of each bad neighbor give an independent input accepted by the product.

variable {A B R : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]
variable (f : R → Set A → Prop) (g : R → Set B → Prop)

private def mixHit (S : Set R) (X : Set A) (Y : Set B) : Prop :=
  ∃ r ∈ S, f r X ∧ g r Y

private def safe (U : Set A → Set B → Prop) : Prop :=
  ∀ X Y, U X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l

private def little (r : R) : Prop :=
  ((single (f r)).card ≤ 1 ∧ (single (g r)).card ≤ 3) ∨
    ((single (f r)).card ≤ 3 ∧ (single (g r)).card ≤ 1)

private def badL (S : Set R) (l : B) : Prop :=
  ∃ r ∈ S, single (g r) = {l} ∧ ¬ almost I (single (f r)) l

private def badP (S : Set R) (p : A) : Prop :=
  ∃ r ∈ S, single (f r) = {p} ∧ ¬ almost (fun l p => I p l) (single (g r)) p

private lemma swapped_free (hf : fourFree I) : fourFree (fun l p => I p l) := by
  intro p q hp a b hap haq hbp hbq
  by_contra hne
  exact hp (hf hne hap hbp haq hbq)

private lemma opposite_bad_adj (hf : fourFree I)
    (Sf : ∀ r X, f r X ↔ ∃ a ∈ single (f r), a ∈ X)
    (Sg : ∀ r Y, g r Y ↔ ∃ b ∈ single (g r), b ∈ Y)
    {U V : Set R} (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hl : badL I f g U l) (hp : badP I f g V p) : I p l := by
  classical
  obtain ⟨r, hr, hrl, hA⟩ := hl
  obtain ⟨s, hs, hsp, hB⟩ := hp
  let Ar := (single (f r)).filter (fun p' => ¬ I p' l)
  let Bs := (single (g s)).filter (fun l' => ¬ I p l')
  have hAr : 1 < Ar.card := Nat.lt_of_not_ge hA
  have hBs : 1 < Bs.card := Nat.lt_of_not_ge hB
  by_contra hpl
  have hfind : ∃ p' ∈ Ar, ∃ l' ∈ Bs, ¬ I p' l' := by
    by_contra! hall
    obtain ⟨p₁, p₂, ha₁, ha₂, hpp⟩ := Finset.one_lt_card_iff.mp hAr
    obtain ⟨l₁, l₂, hb₁, hb₂, hll⟩ := Finset.one_lt_card_iff.mp hBs
    exact hpp (hf hll (hall p₁ ha₁ l₁ hb₁) (hall p₁ ha₁ l₂ hb₂)
      (hall p₂ ha₂ l₁ hb₁) (hall p₂ ha₂ l₂ hb₂))
  obtain ⟨p', hpr, l', hls, hcross⟩ := hfind
  have hp' := Finset.mem_filter.mp hpr
  have hl' := Finset.mem_filter.mp hls
  have hr' : mixHit f g U ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨r, hr, (Sf _ _).mpr ⟨p', hp'.1, by simp⟩, (Sg _ _).mpr ⟨l, by simp [hrl], by simp⟩⟩
  have hs' : mixHit f g V ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨s, hs, (Sf _ _).mpr ⟨p, by simp [hsp], by simp⟩, (Sg _ _).mpr ⟨l', hl'.1, by simp⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hUV _ _ ⟨hr', hs'⟩
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hpl hab
    · obtain rfl : b = l' := hb
      exact hl'.2 hab
  · obtain rfl : a = p' := ha
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hp'.2 hab
    · obtain rfl : b = l' := hb
      exact hcross hab

private def pureGood (p : A) (l : B) : Prop :=
  (∃ r, p ∈ single (f r) ∧ approved I True (f r) l) ∨
    ∃ r, l ∈ single (g r) ∧ approved (fun l p => I p l) True (g r) p

private def smallGood (p : A) (l : B) : Prop :=
  ∃ r, little f g r ∧ p ∈ single (f r) ∧ l ∈ single (g r)

private lemma classify_same (p : A) (l : B) (r : R)
    (hp : p ∈ single (f r)) (hl : l ∈ single (g r))
    (hx : clean I (f r) l) (hy : clean (fun l p => I p l) (g r) p) :
    pureGood I f g p l ∨ smallGood f g p l := by
  by_cases h2 : 2 ≤ (single (f r)).card
  · exact Or.inl (Or.inl ⟨r, hp, Or.inl ⟨h2, hx⟩⟩)
  by_cases hg2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inr ⟨r, hl, Or.inl ⟨hg2, hy⟩⟩)
  exact Or.inr ⟨r, Or.inl ⟨by omega, by omega⟩, hp, hl⟩

private lemma singleton_of_small {T : Type*} [DecidableEq T] {s : Finset T}
    {a : T} (h : a ∈ s) (hc : s.card ≤ 1) : s = {a} := by
  ext b
  simp only [Finset.mem_singleton]
  exact ⟨fun hb => Finset.card_le_one_iff.mp hc hb h, fun e => e ▸ h⟩

private lemma classify_opposite {U V : Set R} {p : A} {l : B} {r s : R}
    (hr : r ∈ U) (hs : s ∈ V) (hpr : p ∈ single (f r)) (hlr : l ∈ single (g r))
    (hps : p ∈ single (f s)) (hls : l ∈ single (g s))
    (hY : clean (fun l p => I p l) (g r) p) (hX : clean I (f s) l) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨ (badL I f g U l ∧ badP I f g V p) := by
  classical
  by_cases hy2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inl (Or.inr ⟨r, hlr, Or.inl ⟨hy2, hY⟩⟩))
  by_cases hx2 : 2 ≤ (single (f s)).card
  · exact Or.inl (Or.inl (Or.inl ⟨s, hps, Or.inl ⟨hx2, hX⟩⟩))
  by_cases hRa : almost I (single (f r)) l
  · by_cases hR4 : 4 ≤ (single (f r)).card
    · exact Or.inl (Or.inl (Or.inl ⟨r, hpr, Or.inr ⟨trivial, hR4, hRa⟩⟩))
    · exact Or.inl (Or.inr ⟨r, Or.inr ⟨by omega, by omega⟩, hpr, hlr⟩)
  by_cases hSa : almost (fun l p => I p l) (single (g s)) p
  · by_cases hS4 : 4 ≤ (single (g s)).card
    · exact Or.inl (Or.inl (Or.inr ⟨s, hls, Or.inr ⟨trivial, hS4, hSa⟩⟩))
    · exact Or.inl (Or.inr ⟨s, Or.inl ⟨by omega, by omega⟩, hps, hls⟩)
  exact Or.inr ⟨⟨r, hr, singleton_of_small hlr (by omega), hRa⟩,
    ⟨s, hs, singleton_of_small hps (by omega), hSa⟩⟩

private lemma classify_product {U V : Set R}
    (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hU : mixHit f g U {p} {l}) (hV : mixHit f g V {p} {l}) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨
      (badL I f g U l ∧ badP I f g V p) ∨ (badL I f g V l ∧ badP I f g U p) := by
  classical
  obtain ⟨r, hr, hpr, hlr⟩ := hU
  obtain ⟨s, hs, hps, hls⟩ := hV
  let X := {a | ¬ I a l}
  let Y := {b | ¬ I p b}
  have hX : ¬ (mixHit f g U X {l} ∧ mixHit f g V X {l}) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : b = l := hb
    exact ha hi
  have hY : ¬ (mixHit f g U {p} Y ∧ mixHit f g V {p} Y) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : a = p := ha
    exact hb hi
  have hx : clean I (f r) l ∨ clean I (f s) l := by
    by_cases ha : f r X
    · exact Or.inr (fun hb => hX ⟨⟨r, hr, ha, hlr⟩, ⟨s, hs, hb, hls⟩⟩)
    · exact Or.inl ha
  have hy : clean (fun l p => I p l) (g r) p ∨ clean (fun l p => I p l) (g s) p := by
    by_cases ha : g r Y
    · exact Or.inr (fun hb => hY ⟨⟨r, hr, hpr, ha⟩, ⟨s, hs, hps, hb⟩⟩)
    · exact Or.inl ha
  have hpr' := (mem_single _ _).mpr hpr
  have hlr' := (mem_single _ _).mpr hlr
  have hps' := (mem_single _ _).mpr hps
  have hls' := (mem_single _ _).mpr hls
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (classify_same I f g p l r hpr' hlr' hx hy)
  · exact (classify_opposite I f g hs hr hps' hls' hpr' hlr' hy hx).imp id Or.inr
  · exact (classify_opposite I f g hr hs hpr' hlr' hps' hls' hy hx).imp id Or.inl
  · exact Or.inl (classify_same I f g p l s hps' hls' hx hy)

private lemma classify_direct
    (U : Set A → Prop) (V : Set B → Prop)
    (hUV : safe I (fun X Y => U X ∧ V Y))
    (p : A) (l : B) (hp : U {p}) (hl : V {l}) :
    (approved I False U l ∨ approved (fun l p => I p l) False V p) ∨
      ((single U).card ≤ 1 ∧ (single V).card ≤ 1) := by
  have hx : clean I U l := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hm, hl⟩
    obtain rfl : b = l := hb
    exact ha hi
  have hy : clean (fun l p => I p l) V p := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hp, hm⟩
    obtain rfl : a = p := ha
    exact hb hi
  by_cases ha : 2 ≤ (single U).card
  · exact Or.inl (Or.inl (Or.inl ⟨ha, hx⟩))
  by_cases hb : 2 ≤ (single V).card
  · exact Or.inl (Or.inr (Or.inl ⟨hb, hy⟩))
  exact Or.inr ⟨by omega, by omega⟩

end Rectangles


section MixedNetwork

open Finset Relation PEqualNP.CircuitLowerBounds

private abbrev Rect (C : Circuit) := Occ C ⊕ (Occ C × Fin 2)
private abbrev MixNode (C : Circuit) := (ℕ ⊕ ℕ) ⊕ Rect C

private def mfwd {C : Circuit} (w : ℕ) : MixNode C := .inl (.inl w)
private def mbck {C : Circuit} (w : ℕ) : MixNode C := .inl (.inr w)
private def mleaf {C : Circuit} (r : Rect C) : MixNode C := .inr r

private def rectPoint (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (fromWire e)
  | .inr (e, i) => if i = 0 then pfwd 0 (otherWire e) else pbck (atWire N e)

private def rectLine (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (otherWire e)
  | .inr (e, i) => if i = 0 then pbck (atWire N e) else pfwd 0 (otherWire e)

private def rpoint (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N false (rectPoint N r)

private def rline (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N true (rectLine N r)

private lemma rectPoint_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectPoint N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectPoint, pfwd, pbck, pureSimple]

private lemma rectLine_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectLine N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectLine, pfwd, pbck, pureSimple]

private def mixFamily (N : ℕ) {C : Circuit} : MixNode C → Set (Rect C)
  | .inl (.inl w) => {r | ∃ e : Occ C, r = .inl e ∧ andAt e ∧ orPath N C (atWire N e) w}
  | .inl (.inr w) => {r | ∃ e : Occ C, ∃ i : Fin 2, r = .inr (e, i) ∧ andAt e ∧
      orPath N C w (fromWire e)}
  | .inr r => {r}

private lemma mixFwd_spec {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mfwd (C := C) w)) X Y ↔ Hom N C w 1 1 X Y := by
  rw [mixed11 h]
  constructor
  · rintro ⟨_, ⟨e, rfl, he, hp⟩, hX, hY⟩
    exact ⟨e, he, hp, hX, hY⟩
  · rintro ⟨e, he, hp, hX, hY⟩
    exact ⟨.inl e, ⟨e, rfl, he, hp⟩, hX, hY⟩

private lemma mixBack_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)}
    (hb : mixHit (rpoint N) (rline N) (mixFamily N (mbck (C := C) w)) X Y)
    (hh : Hom N C w a b X Y) : Hom N C C.output (a + 1) (b + 1) X Y := by
  obtain ⟨_, ⟨e, i, rfl, he, hp⟩, hx, hy⟩ := hb
  fin_cases i
  · have hx' : oneSide N C false (otherWire e) 1 X := by
      simpa [rpoint, rectPoint, pureNode, pfwd] using hx
    have hy' : backOne N C true (atWire N e) Y := by
      simpa [rline, rectLine, pureNode, pbck] using hy
    have hj : Hom N C (atWire N e) (a + 1) b X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_x.mpr hx')
    exact backOne_apply (s := true) h hy' hj
  · have hx' : backOne N C false (atWire N e) X := by
      simpa [rpoint, rectPoint, pureNode, pbck] using hx
    have hy' : oneSide N C true (otherWire e) 1 Y := by
      simpa [rline, rectLine, pureNode, pfwd] using hy
    have hj : Hom N C (atWire N e) a (b + 1) X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_y.mpr hy')
    exact backOne_apply (s := false) h hx' hj

private lemma mixLeaf_spec (N : ℕ) {C : Circuit} (r : Rect C) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mleaf r)) X Y ↔ rpoint N r X ∧ rline N r Y := by
  simp [mixHit, mixFamily, mleaf]

private def mixRank (N : ℕ) {C : Circuit} : MixNode C → ℕ
  | .inl (.inl w) => w + 1
  | .inl (.inr w) => (N + N + C.size + 1 - w) + 1
  | .inr _ => 0

private def mixSrc (N : ℕ) {C : Circuit} : Rect C → MixNode C
  | .inl e => mfwd (atWire N e)
  | .inr (e, _) => mbck (fromWire e)

private noncomputable def mixDst (N : ℕ) {C : Circuit} (a : Rect C) : MixNode C := by
  classical
  exact match a with
  | .inl e => if orAt e then mfwd (fromWire e) else mleaf a
  | .inr (e, _) => if orAt e then mbck (atWire N e) else mleaf a

private lemma mixArc_rank {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (a : Rect C) : mixRank N (mixDst N a) < mixRank N (mixSrc N a) := by
  classical
  rcases a with e | ⟨e, i⟩
  · have := earlier_occ h e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mfwd, mleaf] <;> omega
  · have := earlier_occ h e
    have := at_bound N e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mbck, mleaf] <;> omega

private lemma mixFwd_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mfwd w) ↔
      ∃ a : Rect C, mixSrc N a = mfwd w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, rfl, he, hp⟩
    rcases hp.cases_tail with heq | ⟨_, hp', ⟨a, ha, hf, hw⟩⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inl e, by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inl a, by simp [mixSrc, hw], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, rfl, he, hf ▸ hp'⟩
  · rintro ⟨(a | a), hs, ht⟩
    · have hw : atWire N a = w := by simpa [mixSrc, mfwd] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, rfl, he, hp⟩ := ht
        exact ⟨e, rfl, he, hp.tail ⟨a, ha, rfl, hw⟩⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inl a := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, heq, hn, hw ▸ ReflTransGen.refl⟩
    · obtain ⟨a, i⟩ := a
      simp [mixSrc, mbck, mfwd] at hs

private lemma mixBack_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mbck w) ↔
      ∃ a : Rect C, mixSrc N a = mbck w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, i, rfl, he, hp⟩
    rcases orPath_head.mp hp with heq | ⟨a, ha, hf, ht⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inr (e, i), by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inr (a, 0), by simp [mixSrc, hf], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, i, rfl, he, ht⟩
  · rintro ⟨(a | ⟨a, i⟩), hs, ht⟩
    · simp [mixSrc, mfwd, mbck] at hs
    · have hw : fromWire a = w := by simpa [mixSrc, mbck] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, j, rfl, he, hp⟩ := ht
        exact ⟨e, j, rfl, he, orPath_head.mpr (Or.inr ⟨a, ha, hw, hp⟩)⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inr (a, i) := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, i, heq, hn, hw ▸ ReflTransGen.refl⟩

variable {N : ℕ} {C : Circuit}

private def centerLabel (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (r : Rect C) (v : Fin N) : Prop := by
  classical
  exact if s then single (rline N r) = {v} ∧ ¬ almost I (single (rpoint N r)) v
    else single (rpoint N r) = {v} ∧ ¬ almost (fun l p => I p l) (single (rline N r)) v

private def centerNode (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) : Prop :=
  ∃ r ∈ mixFamily N w, ∃ v ∈ X, centerLabel I s r v

private lemma center_mono (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) : Monotone (centerNode I s w) :=
  fun _ _ h ⟨r, hr, v, hv, hl⟩ => ⟨r, hr, v, h hv, hl⟩

private lemma center_member (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (v : Fin N) :
    v ∈ single (centerNode I s w) ↔ ∃ r ∈ mixFamily N w, centerLabel I s r v := by
  simp [centerNode, mem_single]

private lemma center_linear (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) :
    centerNode I s w X ↔ ∃ v ∈ single (centerNode I s w), v ∈ X := by
  simp only [center_member, centerNode]
  exact ⟨fun ⟨r, hr, v, hv, hl⟩ => ⟨v, ⟨r, hr, hl⟩, hv⟩,
    fun ⟨v, ⟨r, hr, hl⟩, hv⟩ => ⟨r, hr, v, hv, hl⟩⟩

private lemma center_rule (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (w : MixNode C) :
    (∀ c, ¬ approved J True (centerNode I s w) c) ∨
    (∃ u v : MixNode C, mixRank N u < mixRank N w ∧ mixRank N v < mixRank N w ∧
      ¬ True ∧ ∀ X, centerNode I s w X ↔ centerNode I s u X ∧ centerNode I s v X) ∨
    ((∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
      mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X) := by
  classical
  have go (w : MixNode C) (hw : ∀ r, r ∈ mixFamily N w ↔
      ∃ a : Rect C, mixSrc N a = w ∧ r ∈ mixFamily N (mixDst N a)) :
      (∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
        mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X := by
    refine ⟨fun a _ he => ⟨he ▸ mixArc_rank h a, id⟩, ?_⟩
    intro X
    constructor
    · rintro ⟨r, hr, v, hv, ht⟩
      obtain ⟨a, he, ha⟩ := (hw r).mp hr
      exact ⟨a, Finset.mem_univ _, he, r, ha, v, hv, ht⟩
    · rintro ⟨a, _, he, r, ha, v, hv, ht⟩
      exact ⟨r, (hw r).mpr ⟨a, he, ha⟩, v, hv, ht⟩
  rcases w with (w | w) | r
  · exact Or.inr (Or.inr (go (mfwd w) (mixFwd_next h w)))
  · exact Or.inr (Or.inr (go (mbck w) (mixBack_next h w)))
  · left
    apply no_approved_small
    apply Finset.card_le_one_iff.mpr
    intro p q hp hq
    obtain ⟨r', hr, hpl⟩ := (center_member I s _ _).mp hp
    obtain ⟨r'', ht, hql⟩ := (center_member I s _ _).mp hq
    have he' : r' = r := hr
    have he'' : r'' = r := ht
    subst r'
    subst r''
    cases s
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)

private lemma center_bound (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (hf : fourFree J) :
    (edgeCover J (centerNode I (C := C) s) (fun _ => True)).card ≤ 12 * C.size := by
  classical
  have hh := cover_bound J hf (centerNode I (C := C) s) (fun _ => True) (mixRank N)
    (univ : Finset (Rect C)) (mixSrc N) (mixDst N) (center_mono I s)
    (fun w _ => center_linear I s w) (center_rule h I s J)
  simp [Fintype.card_sum, Fintype.card_prod] at hh
  omega

end MixedNetwork


section Products

-- Classify each word with two point leaves and two line leaves by its first mixed AND.
-- A path above that gate adds at most one leaf of each kind.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}

private abbrev MixProduct (C : Circuit) := Fin C.size ⊕ Occ C
private abbrev PureProduct (C : Circuit) := Fin 3 × Occ C

private def validMixed (N : ℕ) {C : Circuit} : MixProduct C → Prop
  | .inl k => (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) C.output
  | .inr e => andAt e

private def leftMix {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 0)
  | .inr e => mleaf (.inl e)

private def rightMix (N : ℕ) {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 1)
  | .inr e => mbck (atWire N e)

private def validPure (N : ℕ) {C : Circuit} (d : PureProduct C) : Prop :=
  andAt d.2 ∧ (d.1 = 0 → orPath N C (atWire N d.2) C.output)

private def purePoint {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 2 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private def pureLine {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 0 then pfwd 1 (otherWire d.2) else
    if d.1 = 1 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private lemma pjoin_spec (N : ℕ) {C : Circuit} (s : Bool) (e : Occ C) (X : Set (Fin N)) :
    pureNode N s (pjoin (flip e)) X ↔
      oneSide N C s (otherWire e) 1 X ∧ backOne N C s (atWire N e) X := Iff.rfl

private lemma mixed_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {t : MixProduct C}
    (ht : validMixed N t) {X Y : Set (Fin N)}
    (hl : mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y)
    (hr : mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y) :
    Hom N C C.output 2 2 X Y := by
  rcases t with k | e
  · have ha := (mixFwd_spec h _ _ _).mp hl
    have hb := (mixFwd_spec h _ _ _).mp hr
    exact or_reaches h ht.2 (hom_and_add h ht.1 0 ha hb)
  · have hs := (mixLeaf_spec N (.inl e) X Y).mp hl
    have hm := hom_and_add h ht e.2 (hom_pure_x.mpr hs.1) (hom_pure_y.mpr hs.2)
    exact mixBack_apply h hr hm

private lemma pure_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {d : PureProduct C}
    (hd : validPure N d) {X Y : Set (Fin N)}
    (hp : pureNode N false (purePoint d) X) (hl : pureNode N true (pureLine d) Y) :
    Hom N C C.output 2 2 X Y := by
  obtain ⟨t, e⟩ := d
  fin_cases t
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' : oneSide N C true (otherWire e) 2 Y := hl
    exact or_reaches h (hd.2 rfl) (hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'))
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' := (pjoin_spec N true e Y).mp hl
    have hh : Hom N C (atWire N e) 2 1 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'.1)
    exact backOne_apply (s := true) h hl'.2 hh
  · have hp' := (pjoin_spec N false e X).mp hp
    have hl' : oneSide N C true (fromWire e) 2 Y := hl
    have hh : Hom N C (atWire N e) 1 2 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_y.mpr hl') (hom_pure_x.mpr hp'.1)
    exact backOne_apply (s := false) h hp'.2 hh

private def mixedTerm (N : ℕ) {C : Circuit} (t : MixProduct C) (X Y : Set (Fin N)) : Prop :=
  mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y ∧
    mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y

private def pureTerm (N : ℕ) {C : Circuit} (d : PureProduct C) (X Y : Set (Fin N)) : Prop :=
  pureNode N false (purePoint d) X ∧ pureNode N true (pureLine d) Y

private lemma product_normal (h : PEqualNP.TopForm.IsAO2 (N + N) C) {X Y : Set (Fin N)}
    (hw : Hom N C C.output 2 2 X Y) :
    (∃ t : MixProduct C, validMixed N t ∧ mixedTerm N t X Y) ∨
    (∃ d : PureProduct C, validPure N d ∧ pureTerm N d X Y) := by
  rcases mixed22 h hw with ⟨k, ha, ht, h₁, h₂⟩ | ⟨e, ha, ht, (⟨hp, hl⟩ | ⟨hh, hl⟩ | ⟨hh, hp⟩)⟩
  · exact Or.inl ⟨.inl k, ⟨ha, ht⟩, (mixFwd_spec h _ _ _).mpr h₁, (mixFwd_spec h _ _ _).mpr h₂⟩
  · exact Or.inr ⟨(0, e), ⟨ha, fun _ => ht⟩, hp, hl⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := false) h hh
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      exact Or.inr ⟨(1, e'), ⟨he', fun hf => ((by decide : (1 : Fin 3) ≠ 0) hf).elim⟩,
        hy, (pjoin_spec N true e' Y).mpr ⟨hx, hb⟩⟩
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 0), ⟨e', 0, rfl, he', hpath⟩, hz, hb⟩⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := true) h hh
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      exact Or.inr ⟨(2, e'), ⟨he', fun hf => ((by decide : (2 : Fin 3) ≠ 0) hf).elim⟩,
        (pjoin_spec N false e' X).mpr ⟨hx, hb⟩, hy⟩
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 1), ⟨e', 1, rfl, he', hpath⟩, hb, hz⟩⟩

end Products


section Accounting

-- Count the incident pairs using selectors, small rectangles, and singleton products.

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma pay_bound {K T : Type*} [Fintype K] [DecidableEq T]
    (Pay : K → Finset T) (m : ℕ) (hp : ∀ k, (Pay k).card ≤ m) :
    (univ.biUnion Pay).card ≤ Fintype.card K * m := by
  calc
    _ ≤ ∑ k : K, (Pay k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k : K, m := Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by simp

private def exchange {N : ℕ} (S : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  S.map (Equiv.prodComm (Fin N) (Fin N)).toEmbedding

private lemma exchange_card {N : ℕ} (S : Finset (Fin N × Fin N)) :
    (exchange S).card = S.card := Finset.card_map _

private lemma exchange_mem {N : ℕ} {S : Finset (Fin N × Fin N)} {p l : Fin N}
    (h : (l, p) ∈ S) : (p, l) ∈ exchange S :=
  Finset.mem_map.mpr ⟨(l, p), h, rfl⟩

private lemma in_cover {A B W : Type*} [Fintype A] [Fintype B]
    (I : A → B → Prop) [DecidableRel I] {f : W → Set A → Prop} {s : W → Prop}
    {p : A} {l : B} (hi : I p l) (w : W) (ha : approved I (s w) (f w) l)
    (hp : p ∈ single (f w)) : (p, l) ∈ edgeCover I f s := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, w, ha, hp⟩

private noncomputable def singletonPay {N : ℕ} (f g : Set (Fin N) → Prop) :
    Finset (Fin N × Fin N) := by
  classical
  exact if (single f).card ≤ 1 ∧ (single g).card ≤ 1 then (single f) ×ˢ (single g) else ∅

private lemma singletonPay_card {N : ℕ} (f g : Set (Fin N) → Prop) :
    (singletonPay f g).card ≤ 1 := by
  classical
  by_cases h : (single f).card ≤ 1 ∧ (single g).card ≤ 1
  · simpa [singletonPay, h, Finset.card_product] using Nat.mul_le_mul h.1 h.2
  · simp [singletonPay, h]

private lemma singletonPay_mem {N : ℕ} {f g : Set (Fin N) → Prop} {p l : Fin N}
    (hp : p ∈ single f) (hl : l ∈ single g) (hs : (single f).card ≤ 1 ∧ (single g).card ≤ 1) :
    (p, l) ∈ singletonPay f g := by
  classical
  simp [singletonPay, hs, hp, hl]

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private noncomputable def rectPay (N : ℕ) {C : Circuit} (r : Rect C) : Finset (Fin N × Fin N) := by
  classical
  exact if little (rpoint N) (rline N) r then
    single (rpoint N r) ×ˢ single (rline N r) else ∅

private lemma rectPay_card (N : ℕ) {C : Circuit} (r : Rect C) : (rectPay N r).card ≤ 3 := by
  classical
  by_cases h : little (rpoint N) (rline N) r
  · rw [rectPay, ite_eq_left h, Finset.card_product]
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Nat.mul_le_mul ha hb
    · exact Nat.mul_le_mul ha hb
  · simp [rectPay, h]

private def centerPoint (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then leftMix t else rightMix N t

private def centerLine (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then rightMix N t else leftMix t

private noncomputable def mixedPay (t : MixProduct C × Bool) : Finset (Fin N × Fin N) :=
  singletonPay (centerNode I false (centerPoint N t.1 t.2)) (centerNode I true (centerLine N t.1 t.2))

private noncomputable def purePay (d : PureProduct C) : Finset (Fin N × Fin N) :=
  singletonPay (pureNode N false (purePoint d)) (pureNode N true (pureLine d))

private noncomputable def pureCover (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) :=
  edgeCover I (pureNode N (C := C) false) pureSimple ∪
  exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple)

private noncomputable def centerCover (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) :=
  edgeCover I (centerNode I (C := C) false) (fun _ => True) ∪
  exchange (edgeCover (fun l p => I p l) (centerNode I (C := C) true) (fun _ => True))

private lemma covered_by_pure {p l : Fin N} (hi : I p l)
    (h : pureGood I (rpoint N (C := C)) (rline N) p l) : (p, l) ∈ pureCover N C I := by
  rcases h with ⟨r, hp, ha⟩ | ⟨r, hl, ha⟩
  · apply Finset.mem_union_left
    apply in_cover I hi (rectPoint N r) _ hp
    change approved I (pureSimple (rectPoint N r)) (rpoint N r) l
    simpa only [rectPoint_simple] using ha
  · apply Finset.mem_union_right
    apply exchange_mem
    apply in_cover (fun l p => I p l) hi (rectLine N r) _ hl
    change approved (fun l p => I p l) (pureSimple (rectLine N r)) (rline N r) p
    simpa only [rectLine_simple] using ha

private lemma covered_by_center (t : MixProduct C) (rev : Bool)
    (p l : Fin N) (hp : p ∈ single (centerNode I false (centerPoint N t rev)))
    (hl : l ∈ single (centerNode I true (centerLine N t rev)))
    (hcross : ∀ a ∈ single (centerNode I false (centerPoint N t rev)),
      ∀ b ∈ single (centerNode I true (centerLine N t rev)), I a b) :
    (p, l) ∈ centerCover N C I ∨ (p, l) ∈ mixedPay I (t, rev) := by
  have hi := hcross p hp l hl
  by_cases hP : 2 ≤ (single (centerNode I false (centerPoint N t rev))).card
  · left
    apply Finset.mem_union_left
    apply in_cover I hi (centerPoint N t rev) _ hp
    apply Or.inl
    refine ⟨hP, ?_⟩
    intro hc
    obtain ⟨a, ha, hn⟩ := (center_linear I false _ _).mp hc
    exact hn (hcross a ha l hl)
  by_cases hL : 2 ≤ (single (centerNode I true (centerLine N t rev))).card
  · left
    apply Finset.mem_union_right
    apply exchange_mem
    apply in_cover (fun l p => I p l) hi (centerLine N t rev) _ hl
    apply Or.inl
    refine ⟨hL, ?_⟩
    intro hc
    obtain ⟨b, hb, hn⟩ := (center_linear I true _ _).mp hc
    exact hn (hcross p hp b hb)
  · right
    have hp' : (single (centerNode I false (centerPoint N t rev))).card ≤ 1 := by omega
    have hl' : (single (centerNode I true (centerLine N t rev))).card ≤ 1 := by omega
    exact singletonPay_mem hp hl ⟨hp', hl'⟩

private lemma mixed_charges (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hf : fourFree I) (t : MixProduct C) (hs : safe I (mixedTerm N t))
    (p l : Fin N) (hi : I p l) (hTerm : mixedTerm N t {p} {l}) :
    (p, l) ∈ pureCover N C I ∨ (p, l) ∈ univ.biUnion (rectPay N (C := C)) ∨
      (p, l) ∈ centerCover N C I ∨ (p, l) ∈ univ.biUnion (mixedPay (C := C) I) := by
  classical
  have sf (r : Rect C) (X : Set (Fin N)) := pureNode_linear h false (rectPoint N r) (rectPoint_simple N r) X
  have sg (r : Rect C) (Y : Set (Fin N)) := pureNode_linear h true (rectLine N r) (rectLine_simple N r) Y
  have badCover (rev : Bool)
      (ha : badP I (rpoint N) (rline N) (mixFamily N (centerPoint N t rev)) p)
      (hb : badL I (rpoint N) (rline N) (mixFamily N (centerLine N t rev)) l) :
      (p, l) ∈ centerCover N C I ∨ (p, l) ∈ univ.biUnion (mixedPay (C := C) I) := by
    have hpa : p ∈ single (centerNode I false (centerPoint N t rev)) :=
      (center_member I false _ _).mpr ha
    have hlb : l ∈ single (centerNode I true (centerLine N t rev)) :=
      (center_member I true _ _).mpr hb
    have hcross (a : Fin N) (ha : a ∈ single (centerNode I false (centerPoint N t rev)))
        (b : Fin N) (hb : b ∈ single (centerNode I true (centerLine N t rev))) : I a b := by
      have ha' := (center_member I false _ _).mp ha
      have hb' := (center_member I true _ _).mp hb
      cases rev
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg hs hb' ha'
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg (fun X Y hxy => hs X Y hxy.symm) hb' ha'
    exact (covered_by_center I t rev p l hpa hlb hcross).imp id
      (fun ht => Finset.mem_biUnion.mpr ⟨(t, rev), Finset.mem_univ _, ht⟩)
  rcases classify_product I (rpoint N) (rline N) hs hTerm.1 hTerm.2 with ((hx | hx) | hx | hx)
  · exact Or.inl (covered_by_pure I hi hx)
  · obtain ⟨r, hr, hp, hl⟩ := hx
    refine Or.inr (Or.inl (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, ?_⟩))
    simp [rectPay, hr, hp, hl]
  · exact Or.inr (Or.inr (badCover false hx.2 hx.1))
  · exact Or.inr (Or.inr (badCover true hx.2 hx.1))

private lemma pure_charges (d : PureProduct C) (hs : safe I (pureTerm N d))
    (p l : Fin N) (hi : I p l) (hTerm : pureTerm N d {p} {l}) :
    (p, l) ∈ pureCover N C I ∨ (p, l) ∈ purePay d := by
  have hp := (mem_single _ _).mpr hTerm.1
  have hl := (mem_single _ _).mpr hTerm.2
  rcases classify_direct I _ _ hs p l hTerm.1 hTerm.2 with (ha | ha) | ha
  · exact Or.inl (Finset.mem_union_left _ (in_cover I hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hp))
  · exact Or.inl (Finset.mem_union_right _ (exchange_mem
      (in_cover (fun l p => I p l) hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hl)))
  · exact Or.inr (singletonPay_mem hp hl ha)

private noncomputable def twiceEdges (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) := by
  classical
  exact univ.filter fun e => I e.1 e.2 ∧ Hom N C C.output 2 2 {e.1} {e.2}

private lemma twice_bound (h : PEqualNP.TopForm.IsAO2 (N + N) C) (hf : fourFree I)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false) :
    (twiceEdges N C I).card ≤ 78 * C.size := by
  classical
  let U := pureCover N C I
  let V := centerCover N C I
  let R := univ.biUnion (rectPay N (C := C))
  let M := univ.biUnion (mixedPay (C := C) I)
  let P := univ.biUnion (purePay (N := N) (C := C))
  have hU : U.card ≤ 24 * C.size := by
    have hc := Finset.card_union_le
      (edgeCover I (pureNode N (C := C) false) pureSimple)
      (exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple))
    rw [exchange_card] at hc
    have h1 := pure_bound h I hf false
    have h2 := pure_bound h (fun l p => I p l) (swapped_free I hf) true
    change (pureCover N C I).card ≤ _
    unfold pureCover
    omega
  have hV : V.card ≤ 24 * C.size := by
    have hc := Finset.card_union_le
      (edgeCover I (centerNode I (C := C) false) (fun _ => True))
      (exchange (edgeCover (fun l p => I p l) (centerNode I (C := C) true) (fun _ => True)))
    rw [exchange_card] at hc
    have h1 := center_bound h I false I hf
    have h2 := center_bound h I true (fun l p => I p l) (swapped_free I hf)
    change (centerCover N C I).card ≤ _
    unfold centerCover
    omega
  have hR : R.card ≤ 18 * C.size := by
    have hh := pay_bound (rectPay N (C := C)) 3 (rectPay_card N)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hh
    change (univ.biUnion (rectPay N (C := C))).card ≤ _
    omega
  have hM : M.card ≤ 6 * C.size := by
    have hh := pay_bound (mixedPay (C := C) I) 1 (fun _ => singletonPay_card _ _)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hh
    change (univ.biUnion (mixedPay (C := C) I)).card ≤ _
    omega
  have hP : P.card ≤ 6 * C.size := by
    have hh := pay_bound (purePay (N := N) (C := C)) 1 (fun _ => singletonPay_card _ _)
    simp only [Fintype.card_prod, Fintype.card_fin] at hh
    change (univ.biUnion (purePay (N := N) (C := C))).card ≤ _
    omega
  have hsub : twiceEdges N C I ⊆ U ∪ (V ∪ (R ∪ (M ∪ P))) := by
    intro e he
    obtain ⟨hi, ht⟩ := (Finset.mem_filter.mp he).2
    rcases product_normal h ht with ⟨t, ht, hv⟩ | ⟨d, hd, hv⟩
    · have hs : safe I (mixedTerm N t) := fun X Y hxy =>
        hom_output_safe2 I h hS (mixed_sound h ht hxy.1 hxy.2) le_rfl le_rfl
      rcases mixed_charges I h hf t hs e.1 e.2 hi hv with hu | hr | hh | hm
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hr))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hh)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_union_left _ hm)))
    · have hs : safe I (pureTerm N d) := fun X Y hxy =>
        hom_output_safe2 I h hS (pure_sound h hd hxy.1 hxy.2) le_rfl le_rfl
      rcases pure_charges I d hs e.1 e.2 hi hv with hu | hp
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, hp⟩))))
  have h0 := Finset.card_le_card hsub
  have h1 := Finset.card_union_le U (V ∪ (R ∪ (M ∪ P)))
  have h2 := Finset.card_union_le V (R ∪ (M ∪ P))
  have h3 := Finset.card_union_le R (M ∪ P)
  have h4 := Finset.card_union_le M P
  omega

end Accounting


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hT : ∀ p1 l1 : Fin N, I p1 l1 → circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true)
    (hS : ∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → circuitFun (N + N) C z = false)
    (hR : ∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) :
    N * q ≤ 100 * C.size := by
  classical
  have hf := plane_four_free I hU
  have hf' := swapped_free I hf
  have hS0 : ∀ X Y : Set (Fin N), ∀ a, a ≤ 2 → OHom N C false C.output a 1 X Y →
      ∃ p ∈ X, ∃ l ∈ Y, I p l := fun X Y a ha hh => hom_output_safe2 I h hS hh ha (by omega)
  have hS1 : ∀ X Y : Set (Fin N), ∀ a, a ≤ 2 → OHom N C true C.output a 1 X Y →
      ∃ p ∈ X, ∃ l ∈ Y, (fun l p => I p l) p l := by
    intro X Y a ha hh
    obtain ⟨p', hp', l', hl', hi⟩ := hom_output_safe2 I h hS hh (by omega) ha
    exact ⟨l', hl', p', hp', hi⟩
  let U := onceB C I false
  let V := exchange (onceB C (fun l p => I p l) true)
  let W := twiceEdges N C I
  have hUcard : U.card ≤ 8 * C.size + N := once_budget_bound h I hf false hS0
  have hVcard : V.card ≤ 8 * C.size + N := by
    unfold V
    rw [exchange_card]
    exact once_budget_bound h (fun l p => I p l) hf' true hS1
  have hWcard : W.card ≤ 78 * C.size := twice_bound I h hf hS
  have hsub : allEdges I ⊆ U ∪ (V ∪ W) := by
    rintro ⟨p, l⟩ he
    have hi : I p l := (Finset.mem_filter.mp he).2
    obtain ⟨a, b, ha₁, ha₂, hb₁, hb₂, hh⟩ := plane_read_cover I h hS hi (hR p l hi)
    by_cases hb : b = 1
    · subst b
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, a, ha₁, ha₂, hh⟩)
    by_cases ha : a = 1
    · subst a
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (exchange_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, b, hb₁, hb₂, hh⟩)))
    obtain rfl : a = 2 := by omega
    obtain rfl : b = 2 := by omega
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hh⟩))
  have hcard := Finset.card_le_card hsub
  rw [allEdges_card I q hL] at hcard
  have hcard₁ := Finset.card_union_le U (V ∪ W)
  have hcard₂ := Finset.card_union_le V W
  have hbase := plane_support q N I C hN hL hU h hT hS hq
  have hNpos : 0 < N := by nlinarith
  have hm : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (by omega)
  omega

end PEqualNP.Outside.L_meta_2673

theorem PEqualNP.Outside.L_meta_2673 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun p2 : Fin N => z (Fin.castAdd N p2) = true)).card ≤ 2 → (Finset.univ.filter (fun l2 : Fin N => z (Fin.natAdd N l2) = true)).card ≤ 2 → (¬ ∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → (∀ p4 l4 : Fin N, I p4 l4 → PEqualNP.ReadK.readsAtMost C (N + N) [p4.val, N + l4.val] 2 = true) → N * q ≤ 100 * C.size := by
  intro q N I _ C hq hN hL hU h hT hS hR
  exact PEqualNP.Outside.L_meta_2673.main q N I C hq hN hL hU h hT hS hR
