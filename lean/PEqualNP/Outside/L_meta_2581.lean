import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2581

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
    v ∈ andStep 3 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 3 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 4

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 3 (encode S t) (encode S u) = encode S (t ++ u) := by
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
  | .and => ins.foldl (andStep 3) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 3).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 3))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 3)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (3 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 3)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 3 (andStep 3 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
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
    (S : List ℕ) (r : readsAtMost C n S 3 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 3 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 4 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

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


private lemma words_in_range {n : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) :
    ∀ t ∈ words n C w, ∀ a ∈ t, a < n := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro t ht a ha
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have eqn : t = [w] := ht
      simpa [eqn] using (show a < n from (List.mem_singleton.mp (eqn ▸ ha)) ▸ hb)
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        exact (List.mem_append.mp ha).elim (ih _ (earlier h k 0) u hu a)
          (ih _ (earlier h k 1) v hv a)
      · rw [ho] at ht
        exact ht.elim (fun hu => ih _ (earlier h k 0) t hu a ha)
          (fun hv => ih _ (earlier h k 1) t hv a ha)
    · simp [words_missing n C hb] at ht

private lemma review_output_edge
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {t : List ℕ} (ht : t ∈ words (N + N) C C.output) :
    ∃ p l, I p l ∧ p.val ∈ t ∧ N + l.val ∈ t := by
  let z : Fin (N + N) → Bool := fun a => decide (a.val ∈ t)
  have hv : circuitFun (N + N) C z = true :=
    (value_eq_terms h z _).mpr ⟨t, ht, fun i hi =>
      ⟨⟨i, words_in_range h C.output t ht i hi⟩, rfl, decide_eq_true hi⟩⟩
  rw [hC, decide_eq_true_eq] at hv
  obtain ⟨p,l,he,hp,hl⟩ := hv
  exact ⟨p,l,he,of_decide_eq_true hp,of_decide_eq_true hl⟩

private lemma review_short
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hr : IsReadK (N + N) C 3) {p l : Fin N} (hi : I p l) :
    ∃ t ∈ words (N + N) C C.output, 1 ≤ t.length ∧ t.length ≤ 6 ∧
      ∀ a ∈ t, a = p.val ∨ a = N + l.val := by
  obtain ⟨t, ht, hs, counts⟩ := read_to_terms h _ (hr _ (pair_prime I hC hi))
  have hs' : ∀ a ∈ t, a = p.val ∨ a = N + l.val :=
    fun a ha => (setList_pair a).mp (hs a ha)
  have hne : p.val ≠ N + l.val := by have := p.isLt; omega
  have hlen (s : List ℕ) (mem : ∀ a ∈ s, a = p.val ∨ a = N + l.val) :
      s.length = s.count p.val + s.count (N + l.val) := by
    induction s with
    | nil => simp
    | cons a s ih =>
      have hi := ih (fun x hx => mem x (List.mem_cons_of_mem _ hx))
      rcases mem a (by simp) with ha | ha <;> subst a <;>
        simp [hne, Ne.symm hne] at * <;> omega
  have bound1 := counts _ ((setList_pair _).mpr (Or.inl rfl))
  have bound2 := counts _ ((setList_pair _).mpr (Or.inr rfl))
  have hp := words_nonempty h ht
  have hpos : 0 < t.length := List.length_pos_iff.mpr hp
  have total := hlen t hs'
  exact ⟨t, ht, hpos, by omega, hs'⟩


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


section Compression

private def limit (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + b * limit b d + b ^ 2 * (limit b d) ^ 2

private def uniqueCommon {α : Type} (G : α → α → Prop) :=
  ∀ {x z y v}, x ≠ z → G x y → G z y → G x v → G z v → y = v

private def cross {α : Type} (G : α → α → Prop) (S U : Finset α) :=
  ∀ x ∈ S, ∀ y ∈ U, ¬ G x y

private def represents {α : Type} (G : α → α → Prop) (d : ℕ)
    (A R : Finset (Finset α)) :=
  ∀ U : Finset α, U.card ≤ d → ∀ S ∈ A, cross G S U → ∃ T ∈ R, cross G T U

private lemma union_bound {α β : Type} [DecidableEq β] (A : Finset α)
    (F : α → Finset β) {m : ℕ} (h : ∀ a ∈ A, (F a).card ≤ m) :
    (A.biUnion F).card ≤ A.card * m := by
  calc
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, m := Finset.sum_le_sum h
    _ = _ := by simp

private lemma compression {α : Type} (G : α → α → Prop) (hu : uniqueCommon G)
    (b d : ℕ) (A : Finset (Finset α)) (hsize : ∀ S ∈ A, S.card ≤ b) :
    ∃ R ⊆ A, R.card ≤ limit b d ∧ represents G d A R := by
  classical
  induction d generalizing A with
  | zero =>
    by_cases ha : A.Nonempty
    · obtain ⟨S, hS⟩ := ha
      refine ⟨{S}, by simpa, by simp [limit], ?_⟩
      intro U hU _ _ _
      have he : U = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨S, by simp, by simp [he, cross]⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, fun _ _ S hS => (ha ⟨S,hS⟩).elim⟩
  | succ d ih =>
    by_cases ha : A.Nonempty
    swap
    · exact ⟨∅, Finset.empty_subset _, by simp, fun _ _ S hS => (ha ⟨S,hS⟩).elim⟩
    obtain ⟨S₀, h₀⟩ := ha
    have sub (P : Finset α → Prop) :
        ∃ R ⊆ A.filter P, R.card ≤ limit b d ∧ represents G d (A.filter P) R :=
      ih _ (fun S hS => hsize S (Finset.mem_filter.mp hS).1)
    have filterOut (P : Finset α → Prop) {S} (h : S ∈ A.filter P) : S ∈ A ∧ P S :=
      Finset.mem_filter.mp h
    have filterIn (P : Finset α → Prop) {S} (h : S ∈ A ∧ P S) : S ∈ A.filter P :=
      Finset.mem_filter.mpr h
    choose pick hsub hcard hrep using sub
    -- The first family omits x. A second conflict then identifies the context vertex.
    let B (x : α) := pick (fun S => x ∉ S)
    let V (x : α) := (B x).biUnion id
    let safe (x z : α) (S : Finset α) := ∀ y, G x y → G z y → ∀ a ∈ S, ¬ G a y
    let D (x z : α) := pick (safe x z)
    let R := insert S₀ ((S₀.biUnion B) ∪ S₀.biUnion (fun x => (V x).biUnion (D x)))
    have bsub {x S} (hr : S ∈ B x) := filterOut _ (hsub _ hr)
    have dsub {x z S} (hr : S ∈ D x z) := Finset.mem_filter.mp (hsub _ hr)
    have vcard (x : α) : (V x).card ≤ limit b d * b :=
      (union_bound (B x) id (fun S hS => hsize S (bsub hS).1)).trans
        (Nat.mul_le_mul_right _ (hcard _))
    refine ⟨R, ?_, ?_, ?_⟩
    · intro S hS
      rcases Finset.mem_insert.mp hS with rfl | h
      · exact h₀
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp h
        exact (bsub hx).1
      · obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp h
        obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hx
        exact (dsub hz).1
    · have h₁ := (union_bound S₀ B (fun x _ => hcard _)).trans
          (Nat.mul_le_mul_right _ (hsize S₀ h₀))
      have h₂ := (union_bound S₀ (fun x => (V x).biUnion (D x)) (fun x _ =>
          (union_bound (V x) (D x) (fun z _ => hcard _)).trans
            (Nat.mul_le_mul_right _ (vcard x)))).trans (Nat.mul_le_mul_right _ (hsize S₀ h₀))
      have hi := Finset.card_insert_le S₀ ((S₀.biUnion B) ∪ S₀.biUnion (fun x => (V x).biUnion (D x)))
      have hj := Finset.card_union_le (S₀.biUnion B) (S₀.biUnion (fun x => (V x).biUnion (D x)))
      change _ ≤ 1 + b * limit b d + b ^ 2 * (limit b d) ^ 2
      dsimp only [R]
      calc
        _ ≤ b * limit b d + b * (limit b d * b * limit b d) + 1 := by omega
        _ = _ := by ring
    · intro U hU S hS hs
      by_cases h₀u : cross G S₀ U
      · exact ⟨S₀, Finset.mem_insert_self .., h₀u⟩
      simp only [cross, not_forall] at h₀u
      obtain ⟨x, hx, y, hy, hxy⟩ := h₀u
      have hd : (U.erase y).card ≤ d := by have := Finset.card_erase_lt_of_mem hy; omega
      have hs' : cross G S (U.erase y) :=
        fun a ha v hv => hs a ha v (Finset.mem_of_mem_erase hv)
      obtain ⟨T,hT,ht⟩ := hrep (fun s => x ∉ s) _ hd S
        (filterIn _ ⟨hS, fun hh => hs x hh y hy (by simpa using hxy)⟩) hs'
      by_cases htu : cross G T U
      · exact ⟨T, Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨x,hx,hT⟩)), htu⟩
      simp only [cross, not_forall] at htu
      obtain ⟨z,hz,v,hv,hzv⟩ := htu
      have ev : v = y := by
        by_contra hn
        exact ht z hz v (Finset.mem_erase.mpr ⟨hn,hv⟩) (by simpa using hzv)
      subst v
      have hn : x ≠ z := fun eq => (bsub hT).2 (eq ▸ hz)
      have hxy' : G x y := by simpa using hxy
      have hzy : G z y := by simpa using hzv
      have hsafe : safe x z S := by
        intro a hxa hza
        have ea := hu hn hxa hza hxy' hzy
        exact fun u hu' => ea ▸ hs u hu' y hy
      obtain ⟨T',hT',ht'⟩ := hrep (safe x z) _ hd S (Finset.mem_filter.mpr ⟨hS,hsafe⟩) hs'
      refine ⟨T', Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_biUnion.mpr
          ⟨z,Finset.mem_biUnion.mpr ⟨T,hT,hz⟩,hT'⟩⟩)), ?_⟩
      intro a ha v hv
      by_cases ev : v = y
      · subst v
        exact (dsub hT').2 y hxy' hzy a ha
      · exact ht' a ha v (Finset.mem_erase.mpr ⟨ev,hv⟩)

end Compression

section Deletion

private noncomputable def common (G : ℕ → ℕ → Prop) (x z : ℕ) : ℕ := by
  classical
  exact if h : ∃ y, G x y ∧ G z y then h.choose else x

private lemma common_eq {G : ℕ → ℕ → Prop} (hu : uniqueCommon G) {x z y : ℕ}
    (hne : x ≠ z) (hx : G x y) (hz : G z y) : common G x z = y := by
  have hex : ∃ v, G x v ∧ G z v := ⟨y, hx, hz⟩
  simp only [common, dite_eq_left hex]
  exact hu hne hex.choose_spec.1 hex.choose_spec.2 hx hz

private def edge (x y : ℕ) : Finset ℕ := {x,y}

open Classical in
private noncomputable def charges (G : ℕ → ℕ → Prop) (V : Finset ℕ) :=
  (V ×ˢ V).image (fun p => edge p.1 p.2) ∪
    ((V ×ˢ V).filter (fun p => p.1 ≠ p.2 ∧ ∃ y, G p.1 y ∧ G p.2 y)).image
      (fun p => edge p.1 (common G p.1 p.2))

private lemma charges_bound (G : ℕ → ℕ → Prop) (V : Finset ℕ) :
    (charges G V).card ≤ 2 * V.card ^ 2 := by
  classical
  unfold charges
  apply Finset.card_union_le .. |>.trans
  calc
    _ ≤ (V ×ˢ V).card + (V ×ˢ V).card := Nat.add_le_add Finset.card_image_le
      (Finset.card_image_le.trans (Finset.card_filter_le ..))
    _ = _ := by simp [pow_two, two_mul]

private def deleted (G : ℕ → ℕ → Prop) (e : Finset ℕ) (x y : ℕ) :=
  G x y ∧ edge x y ≠ e

private lemma indep_mono {G : ℕ → ℕ → Prop} {A B : Finset ℕ} (h : cross G B B)
    (hs : A ⊆ B) : cross G A A := fun x hx y hy => h x (hs hx) y (hs hy)

private lemma indep_join {G : ℕ → ℕ → Prop} (sym : ∀ {x y}, G x y → G y x)
    {S U : Finset ℕ} (hs : cross G S S) (hu : cross G U U) (hh : cross G S U) :
    cross G (S ∪ U) (S ∪ U) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact hs x hx y hy
  · exact hh x hx y hy
  · exact fun h => hh y hy x hx (sym h)
  · exact hu x hx y hy

open Classical in
private lemma delete_replace {G : ℕ → ℕ → Prop} (sym : ∀ {x y}, G x y → G y x)
    (uniq : uniqueCommon G) {A R : Finset (Finset ℕ)} {V U e S : Finset ℕ}
    (coverV : ∀ T ∈ A, T ⊆ V)
    (sub : R ⊆ A.filter (fun T => cross G T T))
    (rep : represents G 6 (A.filter (fun T => cross G T T)) R)
    (he : e ∉ charges G V) (hS : S ∈ A) (hd : U.card ≤ 6)
    (h : cross (deleted G e) (S ∪ U) (S ∪ U)) :
    ∃ T ∈ R, cross (deleted G e) (T ∪ U) (T ∪ U) := by
  classical
  have internal {x y} (hx : x ∈ V) (hy : y ∈ V) : edge x y ≠ e := by
    rintro rfl
    exact he (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩))
  have hind : cross G S S := by
    intro x hx y hy hxy
    exact h x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)
      ⟨hxy,internal (coverV _ hS hx) (coverV _ hS hy)⟩
  have hA : S ∈ A.filter (fun T => cross G T T) := Finset.mem_filter.mpr ⟨hS,hind⟩
  have join {T} (hT : T ∈ R) (hc : cross (deleted G e) T U) :
      cross (deleted G e) (T ∪ U) (T ∪ U) := by
    apply indep_join (fun {x y} hv => ⟨sym hv.1, by simpa only [edge, Finset.pair_comm y x] using hv.2⟩)
    · exact fun x hx y hy hv => (Finset.mem_filter.mp (sub hT)).2 x hx y hy hv.1
    · exact indep_mono h Finset.subset_union_right
    · exact hc
  by_cases hc : cross G S U
  · obtain ⟨T,hT,ht⟩ := rep U hd S hA hc
    exact ⟨T,hT,join hT (fun x hx y hy hv => ht x hx y hy hv.1)⟩
  simp only [cross, not_forall, not_not] at hc
  obtain ⟨x,hx,y,hy,hxy⟩ := hc
  have same {a v} (ha : a ∈ S) (hv : v ∈ U) (hav : G a v) : edge a v = e := by
    by_contra ne
    exact h a (Finset.mem_union_left _ ha) v (Finset.mem_union_right _ hv) ⟨hav,ne⟩
  have exy := same hx hy hxy
  have yn : y ∉ S := fun hh => hind x hx y hh hxy
  -- Every conflict uses the deleted edge, oriented from the support toward y.
  have hc' : cross G S (U.erase y) := by
    intro a ha v hv hav
    have eqn := (same ha (Finset.mem_of_mem_erase hv) hav).trans exy.symm
    have mem : y ∈ edge a v := eqn ▸ (by simp [edge] : y ∈ edge x y)
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at mem
    exact mem.elim (fun eq => yn (eq ▸ ha)) (fun eq => (Finset.ne_of_mem_erase hv) eq.symm)
  obtain ⟨T,hT,ht⟩ := rep _ ((Finset.card_le_card (Finset.erase_subset _ _)).trans hd) S hA hc'
  refine ⟨T,hT,join hT ?_⟩
  intro z hz v hv hzv
  by_cases ev : v = y
  swap
  · exact ht z hz v (Finset.mem_erase.mpr ⟨ev,hv⟩) hzv.1
  subst v
  have ne : x ≠ z := fun eq => hzv.2 (eq ▸ exy)
  apply he
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(x,z), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨coverV _ hS hx, coverV _ (Finset.mem_filter.mp (sub hT)).1 hz⟩, ne, y, hxy, hzv.1⟩,
    by change edge x (common G x z) = e; rw [common_eq uniq ne hxy hzv.1, exy]⟩

end Deletion

section Incidence

private def directed {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  ∃ p l, x = p.val ∧ y = n + l.val ∧ I p l

private def adj {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  directed I x y ∨ directed I y x

private lemma adj_sym {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : adj I x y) :
    adj I y x := h.symm

private lemma sides {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : directed I x y) :
    x < n ∧ n ≤ y := by
  obtain ⟨p,l,rfl,rfl,_⟩ := h
  exact ⟨p.isLt, Nat.le_add_right ..⟩

private lemma adj_irrefl {n : ℕ} {I : Fin n → Fin n → Prop} (x : ℕ) : ¬ adj I x x := by
  intro h
  have h' := sides (h.elim id id)
  omega

private lemma rectangle {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l)
    {x z y v} (a : directed I x y) (b : directed I z y)
    (c : directed I x v) (d : directed I z v) : x = z ∨ y = v := by
  obtain ⟨p,l,rfl,rfl,ap⟩ := a
  obtain ⟨s,l',rfl,e,bs⟩ := b
  have el : l = l' := Fin.ext (Nat.add_left_cancel e)
  subst l'
  obtain ⟨p',k,f,rfl,cp⟩ := c
  have ep : p = p' := Fin.ext f
  subst p'
  obtain ⟨s',k',g,j,ds⟩ := d
  have es : s = s' := Fin.ext g
  have ek : k = k' := Fin.ext (Nat.add_left_cancel j)
  subst s'
  subst k'
  by_cases h : p = s
  · exact Or.inl (congrArg Fin.val h)
  · obtain ⟨_,_,uniq⟩ := hu p s h
    exact Or.inr (congrArg (fun t : Fin n => n + t.val)
      ((uniq l ⟨ap,bs⟩).trans (uniq k ⟨cp,ds⟩).symm))

private lemma adj_unique {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l) : uniqueCommon (adj I) := by
  intro x z y v hn a b c d
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d
  all_goals first
    | exact (rectangle hu a b c d).resolve_left hn
    | exact (rectangle hu a c b d).resolve_right hn
    | have := sides a; have := sides b; have := sides c; have := sides d; omega

end Incidence

section Summaries

private abbrev Family := Finset (Finset ℕ)
private abbrev Summary := ℕ → Family

private def small (A : Family) := A.filter (fun S => S.card ≤ 6)

open Classical in
private lemma reduce_exists (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) (A : Family) :
    ∃ R ⊆ (small A).filter (fun S => cross G S S),
      R.card ≤ limit 6 6 ∧ represents G 6 ((small A).filter (fun S => cross G S S)) R :=
  compression G uniq 6 6 _ (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2)

private noncomputable def reduce (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) (A : Family) :=
  (reduce_exists G uniq A).choose

private lemma reduce_mem {G : ℕ → ℕ → Prop} {uniq : uniqueCommon G} {A : Family} {S}
    (hr : S ∈ reduce G uniq A) : S ∈ A ∧ cross G S S := by
  classical
  have h := Finset.mem_filter.mp ((reduce_exists G uniq A).choose_spec.1 hr)
  exact ⟨(Finset.mem_filter.mp h.1).1, h.2⟩

private lemma reduce_card (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) (A : Family) :
    (reduce G uniq A).card ≤ limit 6 6 := (reduce_exists G uniq A).choose_spec.2.1

private def costs : Finset ℕ := (Finset.range 6).image (fun i => i + 1)

private lemma mem_costs {m} : m ∈ costs ↔ 1 ≤ m ∧ m ≤ 6 := by
  simp only [costs, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · intro h
    exact ⟨m-1,by omega,by omega⟩

private def products (A B : Summary) (m : ℕ) : Family :=
  costs.biUnion fun i => costs.biUnion fun j =>
    if i + j = m then ((A i) ×ˢ (B j)).image (fun p => p.1 ∪ p.2) else ∅

private lemma mem_products {A B : Summary} {m S} : S ∈ products A B m ↔
    ∃ i ∈ costs, ∃ j ∈ costs, i+j=m ∧ ∃ T ∈ A i, ∃ W ∈ B j, T ∪ W = S := by
  simp only [products, Finset.mem_biUnion]
  constructor
  · rintro ⟨i,hi,j,hj,h⟩
    split at h
    · obtain ⟨⟨t,w⟩,hp,eq⟩ := Finset.mem_image.mp h
      exact ⟨i,hi,j,hj,by assumption,t,(Finset.mem_product.mp hp).1,w,(Finset.mem_product.mp hp).2,eq⟩
    · simp at h
  · rintro ⟨i,hi,j,hj,hm,T,hT,W,hW,rfl⟩
    refine ⟨i,hi,j,hj,?_⟩
    simp only [hm, ite_true]
    exact Finset.mem_image.mpr ⟨(T,W),Finset.mem_product.mpr ⟨hT,hW⟩,rfl⟩

private noncomputable def summaryOp (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) :
    GateOp → List Summary → Summary
  | .or, [a,b] => fun m => reduce G uniq (a m ∪ b m)
  | .and, [a,b] => fun m => reduce G uniq (products a b m)
  | _, _ => fun _ => ∅

private def inputSummary (i : ℕ) : Summary := fun m => if m = 1 then {{i}} else ∅

private noncomputable def summaries (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) (n : ℕ)
    (C : Circuit) (w : ℕ) : Summary :=
  (evalFrom (fun _ => ∅) (summaryOp G uniq) C.gates
    (List.ofFn (fun i : Fin n => inputSummary i.val))).getD w (fun _ => ∅)

private lemma summary_input (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) {n : ℕ} (C : Circuit)
    {w : ℕ} (hw : w < n) : summaries G uniq n C w = inputSummary w := by
  unfold summaries
  have hi : w < (List.ofFn (fun i : Fin n => inputSummary i.val)).length := by simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma summary_gate (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) {n : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    summaries G uniq n C (outWire n k) = summaryOp G uniq (row C k).op
      [summaries G uniq n C (operand C k 0),summaries G uniq n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma summary_missing (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) {n : ℕ} (C : Circuit)
    {w : ℕ} (hw : n + C.size ≤ w) : summaries G uniq n C w = fun _ => ∅ :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma limit_pos (b d : ℕ) : 1 ≤ limit b d := by cases d <;> simp [limit]; omega

private lemma summary_card {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) {n : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 n C) (w m : ℕ) : (summaries G uniq n C w m).card ≤ limit 6 6 := by
  rcases wire_cases n C.size w with hb | ⟨k,rfl⟩ | hb
  · rw [summary_input G uniq C hb]
    by_cases hm : m = 1 <;> simp [inputSummary, hm, limit_pos]
  · rw [summary_gate G uniq h k]
    rcases op_kind h k with ho | ho <;> rw [ho] <;> exact reduce_card G uniq _
  · simp [summary_missing G uniq C hb]

private lemma realized {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (irr : ∀ x, ¬ G x x)
    {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) :
    ∀ m S, S ∈ summaries G uniq n C w m → cross G S S ∧
      ∃ t ∈ words n C w, t.length = m ∧ t.toFinset = S := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro m S hs
    rcases wire_cases n C.size w with hb | ⟨k,rfl⟩ | hb
    · rw [summary_input G uniq C hb] at hs
      by_cases hm : m = 1
      · subst m
        simp only [inputSummary, ite_true, Finset.mem_singleton] at hs
        subst S
        refine ⟨by simpa [cross] using irr w, [w], ?_, rfl, by simp⟩
        rw [words_input C hb]
        rfl
      · simp [inputSummary,hm] at hs
    · rw [summary_gate G uniq h k] at hs
      rw [words_gate h k]
      rcases op_kind h k with ho | ho <;> rw [ho] at hs ⊢
      · have hr := reduce_mem (uniq := uniq) hs
        obtain ⟨i,_,j,_,hm,T,hT,W,hW,rfl⟩ := mem_products.mp hr.1
        obtain ⟨_,u,hu,hlen,hsu⟩ := ih _ (earlier h k 0) _ _ hT
        obtain ⟨_,v,hv,vlen,hsv⟩ := ih _ (earlier h k 1) _ _ hW
        exact ⟨hr.2,u++v,⟨u,hu,v,hv,rfl⟩,by simp [hlen,vlen,hm],by simp [hsu,hsv]⟩
      · have hr := reduce_mem (uniq := uniq) hs
        rcases Finset.mem_union.mp hr.1 with hl | hl
        · obtain ⟨_,u,hu,hm,he⟩ := ih _ (earlier h k 0) _ _ hl
          exact ⟨hr.2,u,Or.inl hu,hm,he⟩
        · obtain ⟨_,u,hu,hm,he⟩ := ih _ (earlier h k 1) _ _ hl
          exact ⟨hr.2,u,Or.inr hu,hm,he⟩
    · simp [summary_missing G uniq C hb] at hs

private def vertices (A : Summary) := costs.biUnion fun m => (A m).biUnion id

private lemma vertices_cover {A : Summary} {m} (hm : m ∈ costs) {S} (hS : S ∈ A m) :
    S ⊆ vertices A := fun _ hx => Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_biUnion.mpr ⟨S,hS,hx⟩⟩

private lemma vertices_bound {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (irr : ∀ x, ¬ G x x)
    {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) :
    (vertices (summaries G uniq n C w)).card ≤ 36 * limit 6 6 := by
  have hc : costs.card ≤ 6 := Finset.card_image_le.trans_eq (Finset.card_range 6)
  calc
    _ ≤ costs.card * (limit 6 6 * 6) := union_bound _ _ (fun m hm =>
      (union_bound _ id (fun S hS => by
        obtain ⟨_,t,_,rfl,rfl⟩ := realized uniq irr h w m S hS
        exact t.toFinset_card_le.trans (mem_costs.mp hm).2)).trans
        (Nat.mul_le_mul_right 6 (summary_card uniq h w m)))
    _ ≤ 6 * (limit 6 6 * 6) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

end Summaries

section Propagation

private abbrev free (G : ℕ → ℕ → Prop) (S : Finset ℕ) := cross G S S

private noncomputable def gateVertices {n : ℕ} {C : Circuit} {G : ℕ → ℕ → Prop}
    (uniq : uniqueCommon G) (k : Fin C.size) :=
  vertices (summaries G uniq n C (operand C k 0)) ∪ vertices (summaries G uniq n C (operand C k 1))

private noncomputable def paid (G : ℕ → ℕ → Prop) (uniq : uniqueCommon G) (n : ℕ) (C : Circuit) :=
  Finset.univ.biUnion (fun k : Fin C.size => charges G (gateVertices (G := G) (n := n) uniq k))

private lemma paid_bound {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (irr : ∀ x, ¬ G x x)
    {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    (paid G uniq n C).card ≤ (2 * (72 * limit 6 6) ^ 2) * C.size := by
  have bound (k : Fin C.size) : (gateVertices (G := G) (n := n) uniq k).card ≤ 72 * limit 6 6 := by
    unfold gateVertices
    apply Finset.card_union_le .. |>.trans
    calc
      _ ≤ 36 * limit 6 6 + 36 * limit 6 6 :=
        Nat.add_le_add (vertices_bound uniq irr h _) (vertices_bound uniq irr h _)
      _ = _ := by ring
  calc
    _ ≤ Finset.univ.card * (2 * (72 * limit 6 6) ^ 2) := union_bound _ _ (fun k _ =>
      (charges_bound _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (bound k) _)))
    _ = _ := by simp [Nat.mul_comm]

private lemma apply_reduce {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (sym : ∀ {x y}, G x y → G y x)
    {A : Family} {V U e S : Finset ℕ} (hv : ∀ T ∈ A, T ⊆ V) (he : e ∉ charges G V)
    (hs : S ∈ A) (hb : S.card ≤ 6) (hd : U.card ≤ 6) (h : free (deleted G e) (S ∪ U)) :
    ∃ T ∈ reduce G uniq A, free (deleted G e) (T ∪ U) := by
  classical
  exact delete_replace sym uniq (fun T ht => hv T (Finset.mem_filter.mp ht).1)
    (reduce_exists G uniq A).choose_spec.1 (reduce_exists G uniq A).choose_spec.2.2 he
    (Finset.mem_filter.mpr ⟨hs,hb⟩) hd h

private lemma support_card {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (irr : ∀ x, ¬ G x x)
    {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {w m S} (hs : S ∈ summaries G uniq n C w m) :
    S.card ≤ m := by
  obtain ⟨_,t,_,rfl,rfl⟩ := realized uniq irr h w m S hs
  exact t.toFinset_card_le

private lemma propagate {G : ℕ → ℕ → Prop} (uniq : uniqueCommon G) (irr : ∀ x, ¬ G x x)
    (sym : ∀ {x y}, G x y → G y x) {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {e : Finset ℕ} (he : e ∉ paid G uniq n C) (w : ℕ) :
    ∀ t ∈ words n C w, ∀ U : Finset ℕ, t.length + U.card ≤ 6 →
      free (deleted G e) (t.toFinset ∪ U) →
      ∃ S ∈ summaries G uniq n C w t.length, free (deleted G e) (S ∪ U) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro t ht U budget hi
    have hm : t.length ∈ costs := mem_costs.mpr
      ⟨List.length_pos_iff.mpr (words_nonempty h ht),by omega⟩
    rcases wire_cases n C.size w with hb | ⟨k,rfl⟩ | hb
    · rw [words_input C hb] at ht
      have eqn : t = [w] := ht
      subst t
      exact ⟨[w].toFinset, by simp [summary_input G uniq C hb,inputSummary],hi⟩
    · let A := summaries G uniq n C (operand C k 0)
      let B := summaries G uniq n C (operand C k 1)
      let V := gateVertices (G := G) (n := n) uniq k
      have unpaid : e ∉ charges G V := fun hmem => he (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hmem⟩)
      have left {i S} (hc : i ∈ costs) (hs : S ∈ A i) : S ⊆ V :=
        (vertices_cover hc hs).trans Finset.subset_union_left
      have right {i S} (hc : i ∈ costs) (hs : S ∈ B i) : S ⊆ V :=
        (vertices_cover hc hs).trans Finset.subset_union_right
      rw [words_gate h k] at ht
      rw [summary_gate G uniq h k]
      rcases op_kind h k with ho | ho <;> rw [ho] at ht ⊢
      · obtain ⟨a,ha,b,hb,rfl⟩ := ht
        have ha' : a.length ∈ costs := mem_costs.mpr
          ⟨List.length_pos_iff.mpr (words_nonempty h ha),by simp only [List.length_append] at budget; omega⟩
        have hb' : b.length ∈ costs := mem_costs.mpr
          ⟨List.length_pos_iff.mpr (words_nonempty h hb),by simp only [List.length_append] at budget; omega⟩
        simp only [List.length_append] at budget
        -- Keep the other operand in the context while replacing each child in turn.
        have hab := Finset.card_union_le b.toFinset U
        obtain ⟨T,hT,hTU⟩ := ih _ (earlier h k 0) a ha (b.toFinset ∪ U)
          (by have := b.toFinset_card_le; omega)
          (by simpa only [List.toFinset_append,Finset.union_assoc] using hi)
        have hTcard := support_card uniq irr h hT
        have hTUcard := Finset.card_union_le T U
        obtain ⟨W,hW,hWU⟩ := ih _ (earlier h k 1) b hb (T ∪ U) (by omega)
          (by simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hTU)
        have hWcard := support_card uniq irr h hW
        apply apply_reduce uniq sym (V := V) (S := T ∪ W) _ unpaid
        · apply mem_products.mpr
          exact ⟨a.length,ha',b.length,hb',by simp,T,hT,W,hW,rfl⟩
        · have := Finset.card_union_le T W
          omega
        · omega
        · simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using hWU
        · intro S hS
          obtain ⟨i,hi,j,hj,_,T',hT',W',hW',rfl⟩ := mem_products.mp hS
          exact Finset.union_subset (left hi hT') (right hj hW')
      · change t ∈ words n C (operand C k 0) ∨ t ∈ words n C (operand C k 1) at ht
        have hv (S) (hs : S ∈ A t.length ∪ B t.length) : S ⊆ V :=
          (Finset.mem_union.mp hs).elim (left hm) (right hm)
        rcases ht with ht | ht
        · obtain ⟨T,hT,hTU⟩ := ih _ (earlier h k 0) t ht U budget hi
          exact apply_reduce uniq sym hv unpaid (Finset.mem_union_left _ hT)
            ((support_card uniq irr h hT).trans (mem_costs.mp hm).2) (by omega) hTU
        · obtain ⟨T,hT,hTU⟩ := ih _ (earlier h k 1) t ht U budget hi
          exact apply_reduce uniq sym hv unpaid (Finset.mem_union_right _ hT)
            ((support_card uniq irr h hT).trans (mem_costs.mp hm).2) (by omega) hTU
    · simp [words_missing n C hb] at ht

end Propagation

private def planeEdge {n : ℕ} (a : Fin n × Fin n) := edge a.1.val (n + a.2.val)

private lemma planeEdge_injective {n : ℕ} : Function.Injective (@planeEdge n) := by
  rintro ⟨p,l⟩ ⟨p',l'⟩ he
  change edge p.val (n + l.val) = edge p'.val (n + l'.val) at he
  have hp : p.val ∈ edge p'.val (n + l'.val) := he ▸ (by simp [edge] :
    p.val ∈ edge p.val (n+l.val))
  have hl : n+l.val ∈ edge p'.val (n+l'.val) := he ▸ (by simp [edge] :
    n+l.val ∈ edge p.val (n+l.val))
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hp hl
  apply Prod.ext
  · exact Fin.ext (show p.val = p'.val by have := p.isLt; omega)
  · exact Fin.ext (show l.val = l'.val by have := p'.isLt; omega)

private lemma plane_bound (q n : ℕ) (J : Fin n → Fin n → Prop) [DecidableRel J] (D : Circuit)
    (lines : ∀ l, (Finset.univ.filter (fun p => J p l)).card = q+1)
    (unique : ∀ p p' : Fin n, p ≠ p' → ∃! l, J p l ∧ J p' l)
    (h : PEqualNP.TopForm.IsAO2 (n+n) D)
    (correct : ∀ z : Fin (n+n) → Bool, circuitFun (n+n) D z =
      decide (∃ p l : Fin n, J p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true))
    (read : IsReadK (n+n) D 3) : n*q ≤ (2 * (72 * limit 6 6)^2) * D.size := by
  classical
  let G := adj J
  have uniq : uniqueCommon G := adj_unique unique
  let P := paid G uniq (n+n) D
  have sub : (allEdges J).image planeEdge ⊆ P := by
    intro e he
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp he
    have inc : J p l := (Finset.mem_filter.mp hp).2
    by_contra unpaid
    obtain ⟨t,ht,_,bound,letters⟩ := review_short J h correct read inc
    have good : free (deleted G (planeEdge (p,l))) (t.toFinset ∪ ∅) := by
      simp only [Finset.union_empty]
      intro x hx y hy bad
      rcases letters x (List.mem_toFinset.mp hx) with rfl | rfl <;>
        rcases letters y (List.mem_toFinset.mp hy) with rfl | rfl
      · exact adj_irrefl _ bad.1
      · exact bad.2 rfl
      · exact bad.2 (Finset.pair_comm ..)
      · exact adj_irrefl _ bad.1
    obtain ⟨S,hS,_⟩ := propagate (G := G) uniq (adj_irrefl (I := J)) (fun hv => adj_sym hv)
      h unpaid D.output t ht ∅ (by simpa using bound) good
    obtain ⟨safe,u,hu,_,rfl⟩ := realized (G := G) uniq (adj_irrefl (I := J)) h D.output _ _ hS
    obtain ⟨a,b,hab,ha,hb⟩ := review_output_edge J h correct hu
    exact safe _ (List.mem_toFinset.mpr ha) _ (List.mem_toFinset.mpr hb)
      (Or.inl ⟨a,b,rfl,rfl,hab⟩)
  calc
    n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (by omega)
    _ = (allEdges J).card := (allEdges_card J q lines).symm
    _ = ((allEdges J).image planeEdge).card := (Finset.card_image_of_injective _ planeEdge_injective).symm
    _ ≤ P.card := Finset.card_le_card sub
    _ ≤ _ := paid_bound (G := G) uniq (adj_irrefl (I := J)) h

end PEqualNP.Outside.L_meta_2581

theorem PEqualNP.Outside.L_meta_2581 :
  ∃ c : ℕ, ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 3 → N * q ≤ c * C.size := by
  refine ⟨2 * (72 * PEqualNP.Outside.L_meta_2581.limit 6 6) ^ 2, ?_⟩
  intro q N I _ C _ _ lines unique h correct read
  exact PEqualNP.Outside.L_meta_2581.plane_bound q N I C lines unique h correct read
