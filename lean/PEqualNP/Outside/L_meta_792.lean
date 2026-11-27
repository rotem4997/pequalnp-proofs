import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_792_aux

open PEqualNP.CircuitLowerBounds

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]
    simp

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht, List.length_append, hl]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ hi

private lemma wiresFrom_getD_take (gs : List Gate) (w : List Bool) (j i : ℕ)
    (hi : i < w.length + j) (hj : j ≤ gs.length) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  have h1 : wiresFrom gs w = wiresFrom (gs.drop j) (wiresFrom (gs.take j) w) := by
    rw [← wiresFrom_append, List.take_append_drop]
  rw [h1]
  symm
  exact wiresFrom_getD_lt _ _ _ (by rw [wiresFrom_length, List.length_take, Nat.min_eq_left hj]; exact hi)

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (wiresFrom gs w).getD i false else false) := by
  have hsp : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ (h := hj), List.take_append_drop]
  have h1 : (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
    conv_lhs => rw [hsp, wiresFrom_append, wiresFrom_cons]
    set pre := wiresFrom (gs.take j) w with hpre
    have hlen : pre.length = w.length + j := by
      rw [hpre, wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [wiresFrom_getD_lt _ _ _ (by rw [List.length_append, hlen]; simp)]
    rw [← hlen]
    simp
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hilt
  · exact wiresFrom_getD_take gs w j i hilt (Nat.le_of_lt hj)
  · exact List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega)

private def wireSet (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

private lemma wireSet_lt_n (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    (wireSet n C w).card ≤ 1 := by
  have hsub : wireSet n C w ⊆ {⟨w, hw⟩} := by
    intro p hp
    simp only [wireSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    change (wiresFrom C.gates (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true at hp
    rw [wiresFrom_getD_lt _ _ _ (by simp [hw])] at hp
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw, Option.getD_some,
      decide_eq_true_eq] at hp
    simp [hp]
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma wireSet_gate_val (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) (p : Fin n) :
    p ∈ wireSet n C (n + j) ↔
      g.op.eval (g.inputs.map fun w => if w < n + j then decide (p ∈ wireSet n C w) else false) = true := by
  have hjlt : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hget : C.gates[j]'hjlt = g := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  simp only [wireSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (wiresFrom C.gates (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true ↔ _
  have hlen : (List.ofFn (fun q : Fin n => decide (q = p))).length = n := by simp
  have hgate := wiresFrom_getD_gate C.gates (List.ofFn (fun q : Fin n => decide (q = p))) j hjlt
  rw [hlen, hget] at hgate
  rw [hgate]
  have hmap : (g.inputs.map fun w =>
        if w < n + j then (wiresFrom C.gates (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false else false) =
      (g.inputs.map fun w =>
        if w < n + j then decide ((C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true) else false) := by
    apply List.map_congr_left
    intro w _
    split_ifs
    · change (C.wires _).getD w false = _
      cases (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false <;> rfl
    · rfl
  rw [hmap]

theorem main
    (n r : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (_hrS : ∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S)
    (hrQ : r ∈ Q)
    (hQ : ∀ j ∈ Q, j < C.size ∧ wireSet n C (n + j) ⊆ S ∧ 2 ≤ (wireSet n C (n + j)).card)
    (hclosed : ∀ j ∈ Q, ∀ j' : ℕ, j' < j →
      (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
      wireSet n C (n + j') ⊆ S → 2 ≤ (wireSet n C (n + j')).card → j' ∈ Q)
    (hψQ : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false)))
    (hψOut : ∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → wireSet n C w ⊆ S)
    (hψr : ψ (n + r) = false) :
    (wireSet n C (n + r)).card ≤ Q.card + 1 := by
  classical
  set Q0 : Finset ℕ := Q.filter (fun j => ψ (n + j) = false) with hQ0
  have hQ0_sub : Q0 ⊆ Q := Finset.filter_subset _ _
  -- Helper: classify any false child `w` of `j ∈ Q0`
  have hchild : ∀ (j : ℕ), j ∈ Q0 → ∀ (g : Gate), C.gates[j]? = some g →
      ∀ (w : ℕ), w ∈ g.inputs → (if w < n + j then ψ w else false) = false →
      (∃ j' ∈ Q0, j' < j ∧ w = n + j') ∨
      ((if w < n + j then wireSet n C w else ∅).card ≤ 1) := by
    intro j hjQ0 g hg w hw_in hw_false
    have hjQ : j ∈ Q := hQ0_sub hjQ0
    by_cases hlt : w < n + j
    · simp only [hlt, ↓reduceIte] at hw_false ⊢
      by_cases hwn : w < n
      · exact Or.inr (wireSet_lt_n n C w hwn)
      · set j' := w - n
        have hwj' : w = n + j' := by omega
        have hj'lt : j' < j := by omega
        by_cases hj'Q : j' ∈ Q
        · left
          refine ⟨j', ?_, hj'lt, hwj'⟩
          rw [hQ0, Finset.mem_filter]
          exact ⟨hj'Q, hwj' ▸ hw_false⟩
        · right
          have hnotQ : ∀ k ∈ Q, w ≠ n + k := by
            intro k hk hwk
            apply hj'Q
            have : j' = k := by omega
            rwa [this]
          have hsubS : wireSet n C (n + j') ⊆ S := by
            rw [← hwj']
            exact hψOut w hnotQ hw_false
          have hnotge2 : ¬ (2 ≤ (wireSet n C (n + j')).card) := by
            intro hge2
            apply hj'Q
            exact hclosed j hjQ j' hj'lt ⟨g, hg, hwj' ▸ hw_in⟩ hsubS hge2
          rw [hwj']
          omega
    · simp only [hlt, ↓reduceIte, Finset.card_empty]
      exact Or.inr (Nat.zero_le 1)
  -- Helper: step a single child into (W, E)
  have haddChild : ∀ (m : ℕ), m ∈ Q0 → ∀ (g : Gate), C.gates[m]? = some g →
      ∀ (w : ℕ), w ∈ g.inputs → (if w < n + m then ψ w else false) = false →
      ∀ (W : Finset ℕ) (E : Finset (Fin n)),
      ∃ (W' : Finset ℕ) (E' : Finset (Fin n)),
        (∀ x ∈ W', x ∈ W ∨ (x ∈ Q0 ∧ x < m)) ∧
        (if w < n + m then wireSet n C w else ∅) ⊆ E' ∪ W'.biUnion (fun j => wireSet n C (n + j)) ∧
        E ⊆ E' ∧ W ⊆ W' ∧
        E'.card + W'.card ≤ E.card + W.card + 1 := by
    intro m hm g hg w hw_in hw_false W E
    rcases hchild m hm g hg w hw_in hw_false with ⟨j', hj'Q0, hj'lt, rfl⟩ | hcard1
    · refine ⟨insert j' W, E, ?_, ?_, Finset.Subset.refl _, Finset.subset_insert _ _, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hxW
        · exact Or.inr ⟨hj'Q0, hj'lt⟩
        · exact Or.inl hxW
      · intro p hp
        have hlt : n + j' < n + m := by omega
        simp only [hlt, ↓reduceIte] at hp
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j', Finset.mem_insert_self _ _, hp⟩)
      · have := Finset.card_insert_le j' W
        omega
    · set A := if w < n + m then wireSet n C w else ∅
      refine ⟨W, E ∪ A, fun x hx => Or.inl hx, Finset.subset_union_right.trans Finset.subset_union_left,
        Finset.subset_union_left, Finset.Subset.refl _, ?_⟩
      have := Finset.card_union_le E A
      omega
  -- Main DAG induction on upper bound `M`
  have hdag : ∀ (M : ℕ) (W : Finset ℕ) (E : Finset (Fin n)),
      (∀ j ∈ W, j ∈ Q0 ∧ j < M) →
      wireSet n C (n + r) ⊆ E ∪ W.biUnion (fun j => wireSet n C (n + j)) →
      (wireSet n C (n + r)).card ≤ E.card + W.card + (Q0.filter (· < M)).card := by
    intro M
    induction M using Nat.strong_induction_on with
    | ind M ih =>
      intro W E hWM hcov
      by_cases hW : W.Nonempty
      · set m := W.max' hW with hm_def
        have hmW : m ∈ W := Finset.max'_mem W hW
        have hmQ0 : m ∈ Q0 := (hWM m hmW).1
        have hmM : m < M := (hWM m hmW).2
        have hmQ : m ∈ Q := hQ0_sub hmQ0
        have hmlt : m < C.gates.length := (hQ m hmQ).1
        set g := C.gates[m]'hmlt with hg_def
        have hg_get : C.gates[m]? = some g := List.getElem?_eq_getElem hmlt
        have hg_mem : g ∈ C.gates := List.getElem_mem hmlt
        obtain ⟨hg_op, hg_len⟩ := hfan g hg_mem
        obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := by
          cases hin : g.inputs with
          | nil => rw [hin] at hg_len; simp at hg_len
          | cons a t =>
            cases t with
            | nil => rw [hin] at hg_len; simp at hg_len
            | cons b t2 =>
              cases t2 with
              | nil => exact ⟨a, b, rfl⟩
              | cons _ _ => rw [hin] at hg_len; simp at hg_len
        have hψm : ψ (n + m) = false := (Finset.mem_filter.1 hmQ0).2
        have heval_ψ := hψQ m hmQ g hg_get
        rw [hψm, hab] at heval_ψ
        set W0 := W.erase m with hW0_def
        have hW0_card : W0.card + 1 = W.card := Finset.card_erase_add_one hmW
        have hW0_lt : ∀ x ∈ W0, x ∈ Q0 ∧ x < m := by
          intro x hx
          have hxW : x ∈ W := Finset.mem_of_mem_erase hx
          have hne : x ≠ m := Finset.ne_of_mem_erase hx
          have hle : x ≤ m := Finset.le_max' W x hxW
          exact ⟨(hWM x hxW).1, lt_of_le_of_ne hle hne⟩
        have hQ0_drop : (Q0.filter (· < m)).card + 1 ≤ (Q0.filter (· < M)).card := by
          have hsub : insert m (Q0.filter (· < m)) ⊆ Q0.filter (· < M) := by
            intro x hx
            rcases Finset.mem_insert.1 hx with rfl | hx'
            · exact Finset.mem_filter.2 ⟨hmQ0, hmM⟩
            · obtain ⟨hxQ, hxm⟩ := Finset.mem_filter.1 hx'
              exact Finset.mem_filter.2 ⟨hxQ, lt_trans hxm hmM⟩
          have hnot : m ∉ Q0.filter (· < m) := by simp
          have hle := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hnot] at hle
          exact hle
        rcases hg_op with hop_and | hop_or
        · -- AND gate: at least one operand is ψ-false and covers wireSet (n + m)
          rw [hop_and] at heval_ψ
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id_eq, Bool.and_true] at heval_ψ
          have hchoice : (if a < n + m then ψ a else false) = false ∨
              (if b < n + m then ψ b else false) = false := by
            cases ha : (if a < n + m then ψ a else false)
            · exact Or.inl rfl
            · rw [ha, Bool.true_and] at heval_ψ
              exact Or.inr heval_ψ.symm
          have hstep_one : ∀ u : ℕ, u ∈ g.inputs →
              (if u < n + m then ψ u else false) = false →
              wireSet n C (n + m) ⊆ (if u < n + m then wireSet n C u else ∅) →
              (wireSet n C (n + r)).card ≤ E.card + W.card + (Q0.filter (· < M)).card := by
            intro u hu_in hu_false hu_cov
            obtain ⟨W1, E1, hW1_mem, hW1_cov, hEE1, hW0W1, hcard1⟩ :=
              haddChild m hmQ0 g hg_get u hu_in hu_false W0 E
            have hW1m : ∀ x ∈ W1, x ∈ Q0 ∧ x < m := by
              intro x hx
              rcases hW1_mem x hx with hx0 | hxm
              · exact hW0_lt x hx0
              · exact hxm
            have hcov1 : wireSet n C (n + r) ⊆ E1 ∪ W1.biUnion (fun j => wireSet n C (n + j)) := by
              intro p hp
              rcases Finset.mem_union.1 (hcov hp) with hpE | hpW
              · exact Finset.mem_union_left _ (hEE1 hpE)
              · obtain ⟨j, hjW, hpj⟩ := Finset.mem_biUnion.1 hpW
                by_cases hjm : j = m
                · subst hjm
                  exact hW1_cov (hu_cov hpj)
                · exact Finset.mem_union_right _
                    (Finset.mem_biUnion.2 ⟨j, hW0W1 (Finset.mem_erase.2 ⟨hjm, hjW⟩), hpj⟩)
            have hrec := ih m hmM W1 E1 hW1m hcov1
            omega
          rcases hchoice with ha_false | hb_false
          · apply hstep_one a (by rw [hab]; simp) ha_false
            intro p hp
            have hv := (wireSet_gate_val n C m g hg_get p).1 hp
            rw [hop_and, hab] at hv
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hv
            split_ifs with ha_lt
            · simp only [ha_lt, ↓reduceIte, decide_eq_true_eq] at hv
              exact hv.1
            · simp only [ha_lt, ↓reduceIte] at hv
              exact absurd hv.1 (by decide)
          · apply hstep_one b (by rw [hab]; simp) hb_false
            intro p hp
            have hv := (wireSet_gate_val n C m g hg_get p).1 hp
            rw [hop_and, hab] at hv
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hv
            split_ifs with hb_lt
            · simp only [hb_lt, ↓reduceIte, decide_eq_true_eq] at hv
              exact hv.2
            · simp only [hb_lt, ↓reduceIte] at hv
              exact absurd hv.2 (by decide)
        · -- OR gate: both operands are ψ-false and their union covers wireSet (n + m)
          rw [hop_or] at heval_ψ
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            id_eq, Bool.or_false] at heval_ψ
          have ha_false : (if a < n + m then ψ a else false) = false := by
            cases h : (if a < n + m then ψ a else false)
            · rfl
            · rw [h, Bool.true_or] at heval_ψ; cases heval_ψ
          have hb_false : (if b < n + m then ψ b else false) = false := by
            cases h : (if b < n + m then ψ b else false)
            · rfl
            · rw [h, Bool.or_true] at heval_ψ; cases heval_ψ
          obtain ⟨W1, E1, hW1_mem, hW1_cov, hEE1, hW0W1, hcard1⟩ :=
            haddChild m hmQ0 g hg_get a (by rw [hab]; simp) ha_false W0 E
          obtain ⟨W2, E2, hW2_mem, hW2_cov, hE1E2, hW1W2, hcard2⟩ :=
            haddChild m hmQ0 g hg_get b (by rw [hab]; simp) hb_false W1 E1
          have hW2m : ∀ x ∈ W2, x ∈ Q0 ∧ x < m := by
            intro x hx
            rcases hW2_mem x hx with hx1 | hxm
            · rcases hW1_mem x hx1 with hx0 | hxm'
              · exact hW0_lt x hx0
              · exact hxm'
            · exact hxm
          have hcov2 : wireSet n C (n + r) ⊆ E2 ∪ W2.biUnion (fun j => wireSet n C (n + j)) := by
            intro p hp
            rcases Finset.mem_union.1 (hcov hp) with hpE | hpW
            · exact Finset.mem_union_left _ (hE1E2 (hEE1 hpE))
            · obtain ⟨j, hjW, hpj⟩ := Finset.mem_biUnion.1 hpW
              by_cases hjm : j = m
              · subst hjm
                have hv := (wireSet_gate_val n C m g hg_get p).1 hpj
                rw [hop_or, hab] at hv
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, Bool.or_eq_true] at hv
                rcases hv with hva | hvb
                · have hpa : p ∈ (if a < n + m then wireSet n C a else ∅) := by
                    split_ifs with ha_lt
                    · simp only [ha_lt, ↓reduceIte, decide_eq_true_eq] at hva; exact hva
                    · simp only [ha_lt, ↓reduceIte] at hva; exact absurd hva (by decide)
                  rcases Finset.mem_union.1 (hW1_cov hpa) with hpE1 | hpW1
                  · exact Finset.mem_union_left _ (hE1E2 hpE1)
                  · obtain ⟨k, hk1, hpk⟩ := Finset.mem_biUnion.1 hpW1
                    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, hW1W2 hk1, hpk⟩)
                · have hpb : p ∈ (if b < n + m then wireSet n C b else ∅) := by
                    split_ifs with hb_lt
                    · simp only [hb_lt, ↓reduceIte, decide_eq_true_eq] at hvb; exact hvb
                    · simp only [hb_lt, ↓reduceIte] at hvb; exact absurd hvb (by decide)
                  exact hW2_cov hpb
              · exact Finset.mem_union_right _
                  (Finset.mem_biUnion.2 ⟨j, hW1W2 (hW0W1 (Finset.mem_erase.2 ⟨hjm, hjW⟩)), hpj⟩)
          have hrec := ih m hmM W2 E2 hW2m hcov2
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hW
        subst hW
        simp only [Finset.biUnion_empty, Finset.union_empty] at hcov
        have hle := Finset.card_le_card hcov
        omega
  have hrQ0 : r ∈ Q0 := Finset.mem_filter.2 ⟨hrQ, hψr⟩
  have hres := hdag (r + 1) {r} ∅
    (fun j hj => by rw [Finset.mem_singleton.1 hj]; exact ⟨hrQ0, Nat.lt_succ_self r⟩)
    (by simp)
  have hle1 : (Q0.filter (· < r + 1)).card ≤ Q.card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_card hQ0_sub)
  simp only [Finset.card_empty, Finset.card_singleton, zero_add] at hres
  omega

end PEqualNP.Outside.L_meta_792_aux

theorem PEqualNP.Outside.L_meta_792 :
    ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool),
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) →
      r ∈ Q →
      (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) →
      (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) →
      (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) →
      (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) →
      ψ (n + r) = false →
      (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 :=
  PEqualNP.Outside.L_meta_792_aux.main
