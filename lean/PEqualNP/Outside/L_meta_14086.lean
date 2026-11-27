import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14086

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def eff (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def cost (g : Gate) : ℕ := (eff g).length - 1

theorem eff_length_le (g : Gate) : (eff g).length ≤ g.inputs.length := by
  unfold eff
  split <;> simp

theorem eff_le_cost (g : Gate) : (eff g).length ≤ cost g + 1 := by
  unfold cost; omega

theorem cost_le (g : Gate) (h : g.inputs.length ≤ 2) : cost g ≤ 1 := by
  have := eff_length_le g
  unfold cost; omega

theorem cost_not (g : Gate) (h : g.op = GateOp.not) : cost g = 0 := by
  have : (eff g).length ≤ 1 := by
    unfold eff
    rw [h]
    simp
  unfold cost; omega

theorem eval_congr (g : Gate) (F F' : ℕ → Bool) (h : ∀ a ∈ eff g, F a = F' a) :
    g.op.eval (g.inputs.map F) = g.op.eval (g.inputs.map F') := by
  obtain ⟨op, ins⟩ := g
  cases op
  case not =>
    simp only [eff] at h
    show GateOp.eval .not (ins.map F) = GateOp.eval .not (ins.map F')
    cases ins with
    | nil => rfl
    | cons a l =>
      have := h a (by simp)
      simp [GateOp.eval, this]
  all_goals
    simp only [eff] at h
    show GateOp.eval _ (ins.map F) = GateOp.eval _ (ins.map F')
    rw [List.map_congr_left h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  ((eff g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ eff g, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply eval_congr
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate)
    (h : Cnt t L) : Cnt (t + cost g) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (eff g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (eff g).toFinset).card ≤ (W.card - 1) + (cost g + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (eff_le_cost g)) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (eff g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    Cnt t L → Cnt (t + (gs.map cost).sum) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L h; simp only [List.map_nil, List.sum_nil, add_zero]; exact h
  | cons g gs ih =>
    intro t L h
    have := ih (t + cost g) (L ++ [gateSupp L g]) (cnt_step t L g h)
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact this

theorem sum_le (gs : List Gate) (h : ∀ g ∈ gs, cost g ≤ 1) : (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h g List.mem_cons_self
    have h2 := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    omega

theorem sum_lt (gs : List Gate) (h : ∀ g ∈ gs, cost g ≤ 1) (h0 : ∃ g ∈ gs, cost g = 0) :
    (gs.map cost).sum + 1 ≤ gs.length := by
  induction gs with
  | nil =>
    obtain ⟨g, hg, _⟩ := h0
    simp at hg
  | cons g gs ih =>
    obtain ⟨g', hg', h0'⟩ := h0
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hrest : ∀ g'' ∈ gs, cost g'' ≤ 1 := fun g'' hg'' => h g'' (List.mem_cons_of_mem _ hg'')
    rcases List.mem_cons.1 hg' with he | hm
    · rw [he] at h0'
      have := sum_le gs hrest
      omega
    · have h1 := h g List.mem_cons_self
      have := ih hrest ⟨g', hm, h0'⟩
      omega

def graph (x : Fin 8 → Bool) : Bool :=
  (x 6 && (x 0 || x 1 || x 2 || x 3)) || (x 7 && (x 0 || x 1 || x 4 || x 5))

theorem graph_dep : ∀ i : Fin 8, ∃ x : Fin 8 → Bool,
    graph (Function.update x i (!x i)) ≠ graph x := by
  intro i
  fin_cases i
  · exact ⟨fun j => decide (j = 6), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 6), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 6), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 6), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 7), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 7), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 0), by decide +kernel⟩
  · exact ⟨fun j => decide (j = 0), by decide +kernel⟩

theorem lower (gates : List Gate) (o : ℕ)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x) :
    8 ≤ (gates.map cost).sum + 1 := by
  set S := (suppsFrom gates (inputSupps 8)).getD o ∅ with hS
  have hall : (Finset.univ : Finset (Fin 8)) ⊆ S := by
    intro i _
    by_contra hi
    obtain ⟨x, hx⟩ := graph_dep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x gates _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom gates 0 (inputSupps 8) cnt_inputs {o}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  have hu : (Finset.univ : Finset (Fin 8)).card = 8 := by decide
  omega

def witness : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [6, 10]⟩,
   ⟨.or, [4, 5]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [11, 14]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 15⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph x = decide (∃ i < ([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14086

open PEqualNP.Outside.L_meta_14086 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_14086 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x :=
    fun x => (computes x).trans (graph_correct x).symm
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hn
    have hl := lower gates o hev
    have hs := sum_lt gates (fun g' hg' => cost_le g' (legal g' hg').2) ⟨g, hg, cost_not g hgn⟩
    have hw : witness.length = 8 := rfl
    exact ⟨witness, 15, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn
