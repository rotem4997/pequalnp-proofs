import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11187

open PEqualNP.CircuitLowerBounds

-- The wire-frontier argument follows the accepted proof of L-meta-11131.
-- This circuit groups the vertices by part before taking a majority.
private def IsAO (g : Gate) : Prop := g.op = .and ∨ g.op = .or

private def IsAllowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def isOrdinary (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

private def eraseNot (gs : List Gate) : List Gate :=
  gs.map fun g => if isOrdinary g then g else ⟨.or, []⟩

private theorem eraseNot_length (gs : List Gate) : (eraseNot gs).length = gs.length := by
  simp [eraseNot]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wires (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

private theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = step (wires gs x) g := by
  simp [wires]

private theorem wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [wires_snoc, step]; simp [ih, Nat.add_assoc]

private theorem wire_before (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (h : i < x.length + gs.length) :
    (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
  rw [wires_snoc, step]
  have h' : i < (wires gs x).length := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h']

private theorem wire_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wires_snoc, step, ← wires_length]
  simp [List.getD_eq_getElem?_getD]

private theorem wire_outside (gs : List Gate) (x : List Bool) {i : ℕ}
    (h : x.length + gs.length ≤ i) : (wires gs x).getD i false = false := by
  have h' : (wires gs x).length ≤ i := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']

private theorem evalAO {g : Gate} (hg : IsAO g) {a b : ℕ → Bool}
    (le : ∀ i ∈ g.inputs, a i ≤ b i) :
    g.op.eval (g.inputs.map a) ≤ g.op.eval (g.inputs.map b) := by
  apply Bool.le_iff_imp.2
  rcases hg with h | h
  · simp only [h, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    exact fun ha i hi => Bool.le_iff_imp.1 (le i hi) (ha i hi)
  · simp only [h, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, Bool.le_iff_imp.1 (le i hi) ha⟩

private theorem wires_le (gs : List Gate) (hgs : ∀ g ∈ gs, IsAO g)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false ≤ y.getD i false) :
    ∀ i, (wires gs x).getD i false ≤ (wires gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [wires] using hxy
  | append_singleton gs g ih =>
    have hr := ih (fun a ha => hgs a (by simp [ha]))
    intro i
    by_cases hi : i < x.length + gs.length
    · rw [wire_before gs g x hi, wire_before gs g y (by omega)]
      exact hr i
    by_cases he : i = x.length + gs.length
    · have he' : i = y.length + gs.length := by omega
      rw [he, wire_last, ← he, he', wire_last]
      exact evalAO (hgs g (by simp)) (fun j _ => hr j)
    · have hx : x.length + (gs ++ [g]).length ≤ i := by simp; omega
      have hy : y.length + (gs ++ [g]).length ≤ i := by simp; omega
      rw [wire_outside _ _ hx, wire_outside _ _ hy]

private def OneNot (gs : List Gate) : Prop :=
  gs.Pairwise fun a b => a.op ≠ .not ∨ b.op ≠ .not

private theorem earlier_AO (gs : List Gate) (g : Gate)
    (hgs : ∀ a ∈ gs, IsAllowed a) (uniq : OneNot (gs ++ [g])) (hn : g.op = .not) :
    ∀ a ∈ gs, IsAO a := by
  intro a ha
  rcases (hgs a ha).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim ((List.pairwise_append.1 uniq).2.2 a ha g (by simp) |>.elim
      (fun F => F h) (fun F => F hn))

private theorem not_eval_le {g : Gate} (hn : g.op = .not) {a b : ℕ → Bool}
    (le : ∀ i, a i ≤ b i) : g.op.eval (g.inputs.map b) ≤ g.op.eval (g.inputs.map a) := by
  cases h : g.inputs with
  | nil => simp [hn, GateOp.eval]
  | cons i _ =>
    have hi := le i
    simp only [hn, GateOp.eval, List.map_cons, List.headD_cons]
    cases ha : a i <;> cases hb : b i <;> simp_all

private def next (k : ℕ) (P : Finset ℕ) (g : Gate) : Finset ℕ :=
  P.erase k ∪ (g.inputs.filter fun i => i < k).toFinset

private theorem next_card (k : ℕ) (P : Finset ℕ) (g : Gate)
    (hk : k ∈ P) (hlen : g.inputs.length ≤ 2) : (next k P g).card ≤ P.card + 1 := by
  have h₁ := Finset.card_union_le (P.erase k) (g.inputs.filter fun i => i < k).toFinset
  have h₂ := List.toFinset_card_le (g.inputs.filter fun i => i < k)
  have h₃ := List.length_filter_le (fun i : ℕ => decide (i < k)) g.inputs
  have h₄ := Finset.card_erase_add_one hk
  unfold next
  omega

private theorem next_include {k i : ℕ} {P : Finset ℕ} {g : Gate} (hi : i ∈ g.inputs)
    (hk : i < k) : i ∈ next k P g := by
  exact Finset.mem_union_right _ (List.mem_toFinset.2 (by simp [hi, hk]))

-- Track the wires needed before each gate. A reached NOT consumes one frontier wire.
-- Increasing the inputs can only decrease the value supplied by this gate.
private theorem frontier (n : ℕ) (gs : List Gate)
    (allowed : ∀ g ∈ gs, IsAllowed g) (uniq : OneNot gs)
    (P : Finset ℕ) (bounded : ∀ i ∈ P, i < n + gs.length) :
    ∃ (D : Finset ℕ) (usedNot : Bool),
      (∀ i ∈ D, i < n) ∧ D.card + usedNot.toNat ≤ P.card + (gs.filter isOrdinary).length ∧
      (∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i, x.getD i false ≤ y.getD i false) →
        (∀ i ∈ D, x.getD i false = y.getD i false) →
        ∀ i ∈ P, (wires gs y).getD i false ≤ (wires gs x).getD i false) ∧
      (usedNot = false → ∀ x : List Bool, x.length = n → ∀ i ∈ P,
        (wires gs x).getD i false = (wires (eraseNot gs) x).getD i false) := by
  induction gs using List.reverseRecOn generalizing P with
  | nil =>
    have hD : ∀ i ∈ P, i < n := by simpa using bounded
    refine ⟨P, false, hD, by simp, ?_, ?_⟩
    · intro x y _ _ _ hagree i hi
      exact le_of_eq (hagree i hi).symm
    · simp [wires, eraseNot]
  | append_singleton gs g ih =>
    have hpre : ∀ h ∈ gs, IsAllowed h := fun h hh => allowed h (by simp [hh])
    have hg := allowed g (by simp)
    have hu : OneNot gs := (List.pairwise_append.1 uniq).1
    let k := n + gs.length
    have hp : ∀ i ∈ P, i ≠ k → i < k := by
      intro i hi hne
      have h := bounded i hi
      simp at h
      dsimp [k] at hne ⊢
      omega
    have he : ∀ i ∈ P.erase k, i < k := fun i hi =>
      hp i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    have sameBefore : ∀ x : List Bool, x.length = n → ∀ i < k,
        (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
      intro x hx i hi
      apply wire_before
      simpa [k, hx] using hi
    have erasedBefore : ∀ x : List Bool, x.length = n → ∀ i < k,
        (wires (eraseNot (gs ++ [g])) x).getD i false =
          (wires (eraseNot gs) x).getD i false := by
      intro x hx i hi
      rw [show eraseNot (gs ++ [g]) = eraseNot gs ++ eraseNot [g] from by
        simp [eraseNot, List.map_append]]
      change (wires (eraseNot gs ++ [ _ ]) x).getD i false = _
      apply wire_before
      simpa [k, hx, eraseNot_length] using hi
    have last : ∀ x : List Bool, x.length = n →
        (wires (gs ++ [g]) x).getD k false =
          g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
      intro x hx
      simpa [k, hx] using wire_last gs g x
    by_cases hk : k ∈ P
    · by_cases hn : g.op = .not
      · obtain ⟨D, u, hD, hc, hcmp, _⟩ := ih hpre hu (P.erase k) he
        have count := Finset.card_erase_add_one hk
        refine ⟨D, true, hD, ?_, ?_, by simp⟩
        · simp [List.filter_append, isOrdinary, hn]
          omega
        · intro x y hx hy hxy heq i hi
          by_cases hi' : i = k
          · rw [hi', last x hx, last y hy]
            exact not_eval_le hn (wires_le gs (earlier_AO gs g hpre uniq hn) x y
              (hx.trans hy.symm) hxy)
          · have hiE : i ∈ P.erase k := Finset.mem_erase.2 ⟨hi', hi⟩
            rw [sameBefore x hx i (he i hiE), sameBefore y hy i (he i hiE)]
            exact hcmp x y hx hy hxy heq i hiE
      · have ha : IsAO g := by
          rcases hg.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hn h).elim
        have ho : isOrdinary g = true := by
          rcases ha with h | h <;> simp [isOrdinary, h]
        have he' : ∀ i ∈ next k P g, i < k := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact he i hi
          · exact (List.mem_filter.1 (List.mem_toFinset.1 hi)).2 |> of_decide_eq_true
        obtain ⟨D, u, hD, hc, hcmp, hsame⟩ := ih hpre hu (next k P g) he'
        have count := next_card k P g hk hg.2
        refine ⟨D, u, hD, ?_, ?_, ?_⟩
        · simp [List.filter_append, ho]
          omega
        · intro x y hx hy hxy heq i hi
          by_cases hi' : i = k
          · rw [hi', last x hx, last y hy]
            apply evalAO ha
            intro j hj
            by_cases hj' : j < k
            · exact hcmp x y hx hy hxy heq j (next_include hj hj')
            · rw [wire_outside gs x (by simpa [hx, k] using Nat.le_of_not_gt hj'),
                wire_outside gs y (by simpa [hy, k] using Nat.le_of_not_gt hj')]
          · have hiE : i ∈ P.erase k := Finset.mem_erase.2 ⟨hi', hi⟩
            rw [sameBefore x hx i (he i hiE), sameBefore y hy i (he i hiE)]
            exact hcmp x y hx hy hxy heq i (Finset.mem_union_left _ hiE)
        · intro hu' x hx i hi
          by_cases hi' : i = k
          · have hs : eraseNot (gs ++ [g]) = eraseNot gs ++ [g] := by
              simp [eraseNot, ho, List.map_append]
            rw [hi', last x hx, hs, show k = x.length + (eraseNot gs).length by
              simp [k, hx, eraseNot_length], wire_last]
            apply congrArg (g.op.eval)
            apply List.map_congr_left
            intro j hj
            by_cases hj' : j < k
            · exact hsame hu' x hx j (next_include hj hj')
            · rw [wire_outside gs x (by simpa [hx, k] using Nat.le_of_not_gt hj'),
                wire_outside (eraseNot gs) x
                  (by simpa [hx, k, eraseNot_length] using Nat.le_of_not_gt hj')]
          · rw [sameBefore x hx i (hp i hi hi'), erasedBefore x hx i (hp i hi hi')]
            exact hsame hu' x hx i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hi', hi⟩))
    · have hp' : ∀ i ∈ P, i < k := fun i hi => hp i hi (fun h => hk (h ▸ hi))
      obtain ⟨D, u, hD, hc, hcmp, hsame⟩ := ih hpre hu P hp'
      refine ⟨D, u, hD, ?_, ?_, ?_⟩
      · simp [List.filter_append]
        omega
      · intro x y hx hy hxy heq i hi
        rw [sameBefore x hx i (hp' i hi), sameBefore y hy i (hp' i hi)]
        exact hcmp x y hx hy hxy heq i hi
      · intro hu' x hx i hi
        rw [sameBefore x hx i (hp' i hi), erasedBefore x hx i (hp' i hi)]
        exact hsame hu' x hx i hi

private def witness : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [3, 4]⟩,
   ⟨.or, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [8, 9]⟩,
   ⟨.and, [10, 11]⟩, ⟨.or, [12, 13]⟩]

private def target (x : Fin 7 → Bool) : Bool :=
  (⟨witness, 14⟩ : Circuit).eval (List.ofFn x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem target_spec : ∀ x : Fin 7 → Bool, target x = decide (∃ i < ([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

private def neighbor (i : Fin 7) : Fin 7 := if i.val < 3 then 3 else 0

private def low (i j : Fin 7) : Bool := decide (j = neighbor i)

private def high (i j : Fin 7) : Bool := decide (j = neighbor i ∨ j = i)

set_option maxRecDepth 100000 in
private theorem pair_raises : ∀ i : Fin 7, target (low i) = false ∧ target (high i) = true := by
  decide +kernel

private theorem input_value {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

private theorem compare_pair (i : Fin 7) (j : ℕ) :
    (List.ofFn (low i)).getD j false ≤ (List.ofFn (high i)).getD j false := by
  rw [input_value, input_value]
  by_cases hj : j < 7
  · simp only [dite_eq_left hj, low, high, Bool.le_iff_imp, decide_eq_true_eq]
    exact Or.inl
  · simp [hj]

private theorem same_pair (i : Fin 7) (j : ℕ) (h : j ≠ i.val) :
    (List.ofFn (low i)).getD j false = (List.ofFn (high i)).getD j false := by
  rw [input_value, input_value]
  by_cases hj : j < 7
  · have hn : (⟨j, hj⟩ : Fin 7) ≠ i := fun eq => h (congrArg Fin.val eq)
    simp [hj, low, high, hn]
  · simp [hj]

private theorem erased_AO (gs : List Gate) (hgs : ∀ g ∈ gs, IsAllowed g) :
    ∀ g ∈ eraseNot gs, IsAO g ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨g', hm, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hop, hlen⟩ := hgs g' hm
  rcases hop with ha | ho | hn
  · simpa [isOrdinary, ha, IsAO] using hlen
  · simpa [isOrdinary, ho, IsAO] using hlen
  · simp [isOrdinary, hn, IsAO]

-- Six binary gates can trace at most seven frontier wires. All seven inputs
-- already occupy these slots, so a reached NOT would exceed the budget.
private theorem replacement :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal unique evaluates
  by_cases enough : 8 ≤ gates.length
  · refine ⟨witness, 14, by simp [witness], enough, target_spec⟩
  by_cases hn : ∃ g ∈ gates, g.op = .not
  swap
  · refine ⟨gates, o, ?_, le_rfl, evaluates⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with ha | ho | hb
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g, hg, hb⟩).elim
  have hu : OneNot gates := List.pairwise_iff_get.2 (by
    intro i j hij
    by_cases hi : (gates.get i).op = .not
    · exact Or.inr (fun hj => (ne_of_lt hij) (unique i j hi hj))
    · exact Or.inl hi)
  have hf : ∀ x : Fin 7 → Bool, (⟨gates, o⟩ : Circuit).eval (List.ofFn x) = target x :=
    fun x => (evaluates x).trans (target_spec x).symm
  have ho : o < 7 + gates.length := by
    by_contra h
    have eq := hf (high 0)
    change (wires gates (List.ofFn (high 0))).getD o false = _ at eq
    rw [wire_outside gates _ (by simpa using Nat.le_of_not_gt h), (pair_raises 0).2] at eq
    cases eq
  obtain ⟨D, u, _, hc, hcmp, hsame⟩ := frontier 7 gates legal hu {o} (by simpa using ho)
  have all : Finset.range 7 ⊆ D := by
    intro j hj
    by_contra hmiss
    let i : Fin 7 := ⟨j, Finset.mem_range.1 hj⟩
    have h := hcmp (List.ofFn (low i)) (List.ofFn (high i)) (by simp) (by simp)
      (compare_pair i) (fun k hk => same_pair i k (by rintro rfl; exact hmiss hk)) o (by simp)
    change (⟨gates, o⟩ : Circuit).eval (List.ofFn (high i)) ≤
      (⟨gates, o⟩ : Circuit).eval (List.ofFn (low i)) at h
    rw [hf, hf, (pair_raises i).2, (pair_raises i).1] at h
    exact Bool.le_iff_imp.1 h rfl |> Bool.noConfusion
  have hD : 7 ≤ D.card := by simpa using Finset.card_le_card all
  obtain ⟨g, hg, hgNot⟩ := hn
  have strict : (gates.filter isOrdinary).length < gates.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨g, hg, by simp [isOrdinary, hgNot]⟩
  have uFalse : u = false := by
    cases u with
    | false => rfl
    | true => simp at hc; omega
  refine ⟨eraseNot gates, o, erased_AO gates legal, by simp [eraseNot_length], ?_⟩
  intro x
  have eq := hsame uFalse (List.ofFn x) (by simp) o (by simp)
  change (⟨gates, o⟩ : Circuit).eval (List.ofFn x) =
    (⟨eraseNot gates, o⟩ : Circuit).eval (List.ofFn x) at eq
  exact eq.symm.trans (evaluates x)

end PEqualNP.Outside.L_meta_11187

theorem PEqualNP.Outside.L_meta_11187 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_11187.replacement
