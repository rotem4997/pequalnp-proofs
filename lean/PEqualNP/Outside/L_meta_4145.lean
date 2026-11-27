import PEqualNP.Defs

-- SPDX-License-Identifier: Apache-2.0
-- Adapted from the local NormalizedExtraction proof documented by WH3EL5 in pull request 5091.
-- The flat-circuit count and clean-gate contraction adapt willakone's proofs in pull requests 4283 and 4314.

-- Flat-circuit counting from L-meta-2059.
namespace PEqualNP.Outside.L_meta_4145_aux.Flat

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring


open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem disj {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 (fun v => decide (v ∉ L1)) (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

def MJ {n m : ℕ} (gates : List Gate) (L A : Fin m → Finset (Fin n)) (j : Fin m)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y)) g

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
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


def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def mk (f g : Fin 13 → Bool) (u : Fin 26) : Bool :=
  if h : u.val < 13 then f ⟨u.val, h⟩ else g ⟨u.val - 13, by omega⟩

theorem mk_eq (f g : Fin 13 → Bool) : List.ofFn f ++ List.ofFn g = List.ofFn (mk f g) := by
  have hl : (List.ofFn f).length = 13 := List.length_ofFn
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases h : i < 13
    · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_ofFn]
      unfold mk
      rw [dif_pos h]
    · rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_ofFn]
      unfold mk
      rw [dif_neg h]
      congr 2

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

theorem mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

def qin (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  mk (fun u => decide (u ∈ Q)) (fun v => decide (∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

def ein (p l : Fin 13) : Fin 26 → Bool :=
  mk (fun x => decide (x = p)) (fun x => decide (x = l))

def Pp (s t : Fin 26) : Fin 13 := ⟨(min s.val t.val) % 13, Nat.mod_lt _ (by norm_num)⟩

def Ll (s t : Fin 26) : Fin 13 := ⟨(max s.val t.val - 13) % 13, Nat.mod_lt _ (by norm_num)⟩

def tab : List (List ℕ) := [[0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 5], [0, 2, 3, 4], [0, 1, 4, 6], [0, 1, 2, 5], [0, 1, 2, 6], [0, 1, 2, 7], [0, 1, 4, 8], [0, 2, 4, 9], [0, 1, 5, 10], [0, 1, 2, 11], [0, 1, 4, 12], [], [0, 3, 5, 6], [0, 1, 4, 6], [0, 1, 2, 5], [], [0, 2, 3, 4], [0, 1, 4, 8], [0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 6], [], [0, 2, 3, 4], [], [], [], [2, 4, 5, 6], [], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 7, 8], [2, 4, 5, 8], [], [2, 5, 6, 10], [2, 4, 6, 11], [2, 4, 5, 12], [2, 4, 5, 6], [5, 6, 7, 11], [4, 6, 7, 8], [2, 5, 7, 8], [2, 6, 8, 10], [2, 4, 7, 11], [4, 5, 8, 10], [2, 4, 5, 6], [2, 5, 6, 10], [2, 4, 6, 8], [2, 4, 5, 8], [2, 4, 5, 6], [4, 5, 6, 10]]

def sh (s : Fin 26) : ℕ := if s.val < 13 then s.val else s.val - 13

def tidx (s t : Fin 26) : ℕ :=
  (if s.val < 13 then 0 else 26) +
    (if t.val < 13 then (t.val + 13 - sh s) % 13 else 13 + (t.val - 13 + 13 - sh s) % 13)

def Wt (s t : Fin 26) : Finset (Fin 13) :=
  ((tab.getD (tidx s t) []).map
    (fun a => (⟨(a + sh s) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13))).toFinset

theorem adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

theorem adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

theorem hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by decide +kernel

theorem degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

theorem adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

theorem accwit : ∀ s t : Fin 26, adjb s t = true →
    (Pp s t - Ll s t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧
      ∀ u : Fin 26, ein (Pp s t) (Ll s t) u = true → (u = s ∨ u = t) := by
  decide +kernel

theorem wit : ∀ s t : Fin 26, adjb s t = false →
    (Wt s t).card = 4 ∧
    (∀ l : Fin 13, ({x ∈ Wt s t | x - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) ∧
    qin (Wt s t) s = true ∧ qin (Wt s t) t = true := by
  decide +kernel

theorem k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem hin_of (C : Circuit) (n : ℕ) (hrb : ReadsBack n C) :
    ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + (i : ℕ) := by
  intro i a ha
  apply hrb i i.2 a
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ i.2]
  exact ha

def Lin (gs : List Gate) (w : ℕ) : Prop :=
  ∀ x : Fin 26 → Bool, val gs w x = true →
    ∃ u : Fin 26, x u = true ∧ val gs w (fun v => decide (v = u)) = true

open PEqualNP.EdgeOwnership in
theorem lin_ind (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ)) :
    ∀ w, (26 ≤ w → w - 26 < C.gates.length → (gateAt C (w - 26)).op = GateOp.or ∧
      ∀ i, InCone 26 C i (w - 26) → (gateAt C i).op ≠ GateOp.and) → Lin C.gates w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hwn : w < 26
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_input C.gates _ w hwn] at hx
        exact hx
      · rw [val_input C.gates _ w hwn]
        simp
    · by_cases hbig : 26 + C.gates.length ≤ w
      · rw [val_big C.gates x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < C.gates.length := by omega
        have he : 26 + (w - 26) = w := by omega
        obtain ⟨hor, hcone⟩ := hw (by omega) hi
        rw [gateAt_eq C _ hi] at hor
        have hx' : val C.gates (26 + (w - 26)) x = true := by rw [he]; exact hx
        obtain ⟨a, ha, halt, hav⟩ := (val_or C.gates x (w - 26) hi hor).1 hx'
        have hga : a ∈ (gateAt C (w - 26)).inputs := by rw [gateAt_eq C _ hi]; exact ha
        have hla : Lin C.gates a := by
          apply ih a (by omega)
          intro ha26 hai
          have hic : InCone 26 C (a - 26) (w - 26) :=
            (inCone_iff 26 C (a - 26) (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
          have hna := hcone _ hic
          refine ⟨?_, ?_⟩
          · rw [gateAt_eq C _ hai] at hna ⊢
            rcases (legal _ (List.getElem_mem hai)).1 with h | h
            · exact absurd h hna
            · exact h
          · intro i hi2
            exact hcone i ((inCone_iff 26 C i (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩)
        obtain ⟨u, hu, huv⟩ := hla x hav
        refine ⟨u, hu, ?_⟩
        rw [← he]
        exact (val_or C.gates _ (w - 26) hi hor).2 ⟨a, ha, halt, huv⟩

open PEqualNP.EdgeOwnership in
theorem lin_and (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ))
    (hflat : ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) (a : ℕ)
    (ha : a ∈ C.gates[j].inputs) : Lin C.gates a := by
  have halt : a < 26 + j := hin ⟨j, hj⟩ a ha
  have hgj : (gateAt C j).op = GateOp.and := by rw [gateAt_eq C j hj]; exact hop
  have hga : a ∈ (gateAt C j).inputs := by rw [gateAt_eq C j hj]; exact ha
  apply lin_ind C legal hin a
  intro ha26 hai
  have hic : InCone 26 C (a - 26) j :=
    (inCone_iff 26 C (a - 26) j hj).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
  refine ⟨?_, ?_⟩
  · rcases (legal _ (List.getElem_mem hai)).1 with h | h
    · exact absurd ⟨a - 26, j, by rw [gateAt_eq C _ hai]; exact h, hgj, hic⟩ hflat
    · rw [gateAt_eq C _ hai]; exact h
  · intro i hi2 hand
    exact hflat ⟨i, j, hand, hgj,
      (inCone_iff 26 C i j hj).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩⟩

def Reach (gs : List Gate) (o : ℕ) (w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o →
    (∀ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or → S (26 + k) →
      ∀ a ∈ gs[k].inputs, S a) → S w

theorem reach_out (gs : List Gate) (o : ℕ) : Reach gs o o := fun _ h _ => h

theorem reach_step (gs : List Gate) (o : ℕ) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hr : Reach gs o (26 + k)) (a : ℕ) (ha : a ∈ gs[k].inputs) :
    Reach gs o a :=
  fun S h0 hs => hs k hk hop (hr S h0 hs) a ha

theorem reach_imp (gs : List Gate) (o : ℕ)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ))
    (w : ℕ) (hr : Reach gs o w) :
    ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true := by
  apply hr (fun w => ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true)
  · intro x h
    exact h
  · intro k hk hop hS a ha x hx
    exact hS x ((val_or gs x k hk hop).2 ⟨a, ha, hin ⟨k, hk⟩ a ha, hx⟩)

theorem reach_down (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 26 → Bool) :
    ∀ w, Reach gs o w → val gs w x = true →
      ∃ w', Reach gs o w' ∧ val gs w' x = true ∧
        (w' < 26 ∨ ∃ (j : ℕ) (hj : j < gs.length), w' = 26 + j ∧ gs[j].op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr hx
    by_cases hwn : w < 26
    · exact ⟨w, hr, hx, Or.inl hwn⟩
    · by_cases hbig : 26 + gs.length ≤ w
      · rw [val_big gs x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < gs.length := by omega
        have he : 26 + (w - 26) = w := by omega
        rcases (legal gs[w - 26] (List.getElem_mem hi)).1 with ha | ho
        · exact ⟨w, hr, hx, Or.inr ⟨w - 26, hi, he.symm, ha⟩⟩
        · have hx' : val gs (26 + (w - 26)) x = true := by rw [he]; exact hx
          have hr' : Reach gs o (26 + (w - 26)) := by rw [he]; exact hr
          obtain ⟨a, ha, halt, hav⟩ := (val_or gs x (w - 26) hi ho).1 hx'
          exact ih a (by omega) (reach_step gs o (w - 26) hi ho hr' a ha) hav

theorem reach_parent (gs : List Gate) (o : ℕ) (w : ℕ) (hr : Reach gs o w) :
    w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧ Reach gs o (26 + k) ∧
      w ∈ gs[k].inputs := by
  apply hr (fun w => w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧
    Reach gs o (26 + k) ∧ w ∈ gs[k].inputs)
  · exact Or.inl rfl
  · intro k hk hop hS a ha
    right
    refine ⟨k, hk, hop, ?_, ha⟩
    rcases hS with h | ⟨k', hk', hop', hr', hmem⟩
    · rw [h]
      exact reach_out gs o
    · exact reach_step gs o k' hk' hop' hr' _ hmem

open Classical in
theorem top_count (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (U RO : Finset (Fin gs.length))
    (hU : ∀ j ∈ U, (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)))
    (hRO : ∀ j, j ∈ RO ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))) :
    U.card ≤ RO.card + 1 := by
  have hdisj : Disjoint U RO := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (hU j h1).1
    have a2 := ((hRO j).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hsub : (U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ)) ⊆
      insert o (RO.biUnion (fun k => (gs.get k).inputs.toFinset)) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hr : Reach gs o (26 + (j : ℕ)) := by
      rcases Finset.mem_union.1 hj with h | h
      · exact (hU j h).2
      · exact ((hRO j).1 h).2
    rcases reach_parent gs o _ hr with h | ⟨k, hk, hop, hrk, hmem⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      exact ⟨⟨k, hk⟩, (hRO ⟨k, hk⟩).2 ⟨hop, hrk⟩, List.mem_toFinset.2 hmem⟩
  have hinj : Function.Injective (fun j : Fin gs.length => 26 + (j : ℕ)) := by
    intro a b h
    apply Fin.ext
    simpa using h
  have hc1 : ((U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ))).card
      = U.card + RO.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint hdisj]
  have hc2 : (RO.biUnion (fun k => (gs.get k).inputs.toFinset)).card ≤ RO.card * 2 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans (by simp)
    intro k _
    exact (List.toFinset_card_le _).trans (legal _ (List.getElem_mem k.2)).2
  have hc3 := Finset.card_le_card hsub
  have hc4 := Finset.card_insert_le o (RO.biUnion (fun k => (gs.get k).inputs.toFinset))
  omega

open Classical in
theorem mrg_count {n m : ℕ} (L A : Fin m → Finset (Fin n)) (gates : List Gate) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hA : ∀ j : Fin m, A j ⊆ L j)
    (hot : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      val gates (o j) (fun i : Fin n => decide (i = p)) = true)
    (hoc : ∀ j : Fin m, 1 ≤ (A j).card →
      val gates (o j) (fun i : Fin n => decide (i ∉ L j)) = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤
      (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
  have h1 : ∀ j : Fin m, (A j).card - 1 ≤
      ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) := by
    intro j
    by_cases hc : 1 ≤ (A j).card
    · exact le_of_eq (mcount gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y))
        (fun p _ v hv => of_decide_eq_true hv) legal hin hc (o j) (hoc j hc)
        (fun p hp => hot j p hp)).symm
    · have hz : (A j).card - 1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  have h2 : ∀ g : Fin gates.length,
      (∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0)) ≤
        (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) := by
    intro g
    by_cases hex : ∃ j0 : Fin m, MJ gates L A j0 g
    · rw [if_pos hex]
      obtain ⟨j0, hj0⟩ := hex
      have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) ≤ (if j = j0 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : MJ gates L A j g
        · have e : j = j0 := by
            by_contra hne
            exact disj gates legal hin (L j) (L j0) (A j) (A j0) (hA j) (hL j j0 hne) g hj hj0
          rw [if_pos hj, if_pos e]
        · rw [if_neg hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (fun h => hex ⟨j, h⟩)
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  calc ∑ j : Fin m, ((A j).card - 1)
      ≤ ∑ j : Fin m, ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ∑ g : Fin gates.length, ∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ g : Fin gates.length, (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun g _ => h2 g)
    _ = (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
        rw [Finset.card_filter]

def Hy (gs : List Gate) (o : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ)) ∧
  (∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and → ∀ a ∈ gs[j].inputs, Lin gs a) ∧
  (∀ s t : Fin 26, adjb s t = true → val gs o (pr s t) = true) ∧
  (∀ s t : Fin 26, adjb s t = false → val gs o (pr s t) = false)

theorem reach_adj (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s t : Fin 26) (h : val gs w (pr s t) = true) : adjb s t = true := by
  have h2 := reach_imp gs o H.2.1 w hr _ h
  cases hb : adjb s t with
  | true => rfl
  | false =>
    rw [H.2.2.2.2 s t hb] at h2
    exact Bool.noConfusion h2

theorem val_e_pr (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (s t u : Fin 26) (hu : u = s ∨ u = t)
    (h : val gs w (fun v : Fin 26 => decide (v = u)) = true) : val gs w (pr s t) = true :=
  val_mono gs legal _ _ (by
    intro v hv
    have e : v = u := of_decide_eq_true hv
    rw [e]
    exact decide_eq_true hu) w h

theorem reach_single (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s : Fin 26) (h : val gs w (fun v : Fin 26 => decide (v = s)) = true) : False := by
  have h2 := reach_adj gs o H w hr s s (val_e_pr gs H.1 w s s s (Or.inl rfl) h)
  rw [adj_irr s] at h2
  exact Bool.noConfusion h2

theorem and_struct (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) : ∃ a b : ℕ, gs[j].inputs = [a, b] := by
  have hlen := (H.1 gs[j] (List.getElem_mem hj)).2
  have hall := (val_and gs (pr s0 t0) j hj hop).1 h0
  have hlinj := H.2.2.1 j hj hop
  rcases hinp : gs[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · exfalso
    apply reach_single gs o H _ hr s0
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    simp at hi
  · exfalso
    have ha : a ∈ gs[j].inputs := by rw [hinp]; simp
    obtain ⟨halt, hav⟩ := hall a ha
    obtain ⟨u, hu, huv⟩ := hlinj a ha _ hav
    apply reach_single gs o H _ hr u
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    have e : i = a := by simpa using hi
    rw [e]
    exact ⟨halt, huv⟩
  · exact ⟨a, b, rfl⟩
  · rw [hinp] at hlen
    simp at hlen

theorem star (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) :
    ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ), A ⊆ N z ∧
      (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
      ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true → (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A) := by
  obtain ⟨a, b, hab⟩ := and_struct gs o H j hj hop hr s0 t0 h0
  have ha : a ∈ gs[j].inputs := by rw [hab]; simp
  have hb : b ∈ gs[j].inputs := by rw [hab]; simp
  have halt : a < 26 + j := H.2.1 ⟨j, hj⟩ a ha
  have hblt : b < 26 + j := H.2.1 ⟨j, hj⟩ b hb
  have la : Lin gs a := H.2.2.1 j hj hop a ha
  have lb : Lin gs b := H.2.2.1 j hj hop b hb
  have hST : ∀ s t : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true →
      val gs b (fun v : Fin 26 => decide (v = t)) = true → adjb s t = true := by
    intro s t hs ht
    apply reach_adj gs o H _ hr s t
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hab] at hi
    rcases List.mem_pair.1 hi with e | e
    · rw [e]
      exact ⟨halt, val_e_pr gs H.1 a s t s (Or.inl rfl) hs⟩
    · rw [e]
      exact ⟨hblt, val_e_pr gs H.1 b s t t (Or.inr rfl) ht⟩
  have hcov : ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true →
      (val gs a (fun v : Fin 26 => decide (v = s)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = t)) = true) ∨
      (val gs a (fun v : Fin 26 => decide (v = t)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = s)) = true) := by
    intro s t h
    have hall := (val_and gs (pr s t) j hj hop).1 h
    obtain ⟨u1, hu1, hv1⟩ := la _ (hall a ha).2
    obtain ⟨u2, hu2, hv2⟩ := lb _ (hall b hb).2
    have hadj := hST u1 u2 hv1 hv2
    have e1 : u1 = s ∨ u1 = t := of_decide_eq_true hu1
    have e2 : u2 = s ∨ u2 = t := of_decide_eq_true hu2
    have hne : u1 ≠ u2 := by
      intro e
      rw [e, adj_irr] at hadj
      exact Bool.noConfusion hadj
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · right
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · exact absurd (e1.trans e2.symm) hne
  have hne : ∃ sa tb : Fin 26, val gs a (fun v : Fin 26 => decide (v = sa)) = true ∧
      val gs b (fun v : Fin 26 => decide (v = tb)) = true := by
    rcases hcov s0 t0 h0 with h | h
    · exact ⟨s0, t0, h⟩
    · exact ⟨t0, s0, h⟩
  obtain ⟨sa, tb, hsa, htb⟩ := hne
  by_cases hT : ∀ t : Fin 26, val gs b (fun v : Fin 26 => decide (v = t)) = true → t = tb
  · refine ⟨tb, Finset.univ.filter
      (fun s : Fin 26 => val gs a (fun v : Fin 26 => decide (v = s)) = true), a, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [mem_N, adj_symm]
      exact hST s tb hs.2 htb
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs a (fun v : Fin 26 => decide (v ∉ N tb)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := la _ hv
        have hu' : u ∉ N tb := of_decide_eq_true hu
        apply hu'
        rw [mem_N, adj_symm]
        exact hST u tb huv htb
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        exact ⟨hT t h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
      · left
        exact ⟨hT s h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
  · push_neg at hT
    obtain ⟨t1, ht1, hne1⟩ := hT
    have hS : ∀ s : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true → s = sa := by
      intro s hs
      by_contra hne2
      exact hne1 (k22 s sa t1 tb (hST s t1 hs ht1) (hST s tb hs htb) (hST sa t1 hsa ht1)
        (hST sa tb hsa htb) hne2)
    refine ⟨sa, Finset.univ.filter
      (fun t : Fin 26 => val gs b (fun v : Fin 26 => decide (v = t)) = true), b, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_filter] at ht
      rw [mem_N]
      exact hST sa t hsa ht.2
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs b (fun v : Fin 26 => decide (v ∉ N sa)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := lb _ hv
        have hu' : u ∉ N sa := of_decide_eq_true hu
        apply hu'
        rw [mem_N]
        exact hST sa u hsa huv
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨hS s h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
      · right
        exact ⟨hS t h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩

open Classical in
noncomputable def US (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
    ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true)

open Classical in
noncomputable def ROS (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))

open Classical in
noncomputable def MGS (gs : List Gate) (A' : Fin 26 → Finset (Fin 26)) :
    Finset (Fin gs.length) :=
  Finset.univ.filter (fun g : Fin gs.length => ∃ j, MJ gs N A' j g)

open Classical in
theorem mem_US (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ US gs o ↔ ((gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
      ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) := by
  unfold US
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
theorem mem_ROS (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ ROS gs o ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ))) := by
  unfold ROS
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem cover (gs : List Gate) (o : ℕ) (H : Hy gs o) (v y : Fin 26) (hadj : adjb v y = true) :
    ∃ j : Fin gs.length, j ∈ US gs o ∧ val gs (26 + (j : ℕ)) (pr v y) = true := by
  have hout := H.2.2.2.1 v y hadj
  obtain ⟨w, hr, hx, hw⟩ := reach_down gs o H.1 (pr v y) o (reach_out gs o) hout
  rcases hw with hw | ⟨j, hj, e, hop⟩
  · exfalso
    apply reach_single gs o H w hr ⟨w, hw⟩
    rw [val_input gs _ w hw]
    simp
  · rw [e] at hr hx
    exact ⟨⟨j, hj⟩, (mem_US gs o _).2 ⟨hop, hr, v, y, hx⟩, hx⟩

theorem arith (b c m : ℕ) (h4 : b ≤ 4) (hm : b ≤ c * m) :
    5 * b ≤ 4 * (2 * c + (m - 1)) := by
  rcases c with _ | _ | _ | c
  · simp at hm
    omega
  · simp at hm
    omega
  · omega
  · clear hm
    omega

theorem tally {ι : Type} (U : Finset ι) (z : ι → Fin 26) (A : ι → Finset (Fin 26))
    (A' : Fin 26 → Finset (Fin 26))
    (h1 : ∀ j ∈ U, A j ⊆ N (z j)) (h2 : ∀ j ∈ U, (A j).card ≤ (A' (z j)).card)
    (h3 : ∀ v y : Fin 26, adjb v y = true →
      ∃ j ∈ U, (v = z j ∧ y ∈ A j) ∨ (y = z j ∧ v ∈ A j)) :
    260 ≤ 8 * U.card + 4 * ∑ v : Fin 26, ((A' v).card - 1) := by
  obtain ⟨B, hB⟩ : ∃ B : Fin 26 → Finset (Fin 26),
      ∀ v, B v = (U.filter (fun j => z j = v)).biUnion A := ⟨_, fun _ => rfl⟩
  have hB4 : ∀ v, (B v).card ≤ 4 := by
    intro v
    rw [← degN v, hB v]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h1 j hj.1 hyj
  have hBm : ∀ v, (B v).card ≤ (U.filter (fun j => z j = v)).card * (A' v).card := by
    intro v
    rw [hB v]
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((A' v).card) ?_).trans (by simp)
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h2 j hj.1
  have hv : ∀ v, 5 * (B v).card ≤
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    fun v => arith _ _ _ (hB4 v) (hBm v)
  have hpt : ∀ v y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) ≤
      (if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0) := by
    intro v y
    by_cases hadj : adjb v y = true
    · obtain ⟨j, hj, h | h⟩ := h3 v y hadj
      · have hm : y ∈ B v := by
          rw [hB v]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
      · have hm : v ∈ B y := by
          rw [hB y]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
    · rw [if_neg hadj]
      exact Nat.zero_le _
  have hsumB : ∀ v : Fin 26, ∑ y : Fin 26, (if y ∈ B v then (1 : ℕ) else 0) = (B v).card := by
    intro v
    simp
  have hsumB' : ∑ v : Fin 26, ∑ y : Fin 26, (if v ∈ B y then (1 : ℕ) else 0)
      = ∑ y : Fin 26, (B y).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => hsumB y)
  have h104 : 104 ≤ 2 * ∑ v : Fin 26, (B v).card := by
    calc 104 = ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) :=
          adj_total.symm
      _ ≤ ∑ v : Fin 26, ∑ y : Fin 26,
            ((if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0)) :=
          Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun y _ => hpt v y))
      _ = (∑ v : Fin 26, (B v).card) + ∑ y : Fin 26, (B y).card := by
          simp only [Finset.sum_add_distrib]
          rw [hsumB', Finset.sum_congr rfl (fun v _ => hsumB v)]
      _ = 2 * ∑ v : Fin 26, (B v).card := by ring
  have hU : U.card = ∑ v : Fin 26, (U.filter (fun j => z j = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (z j))
  have hfin : ∑ v : Fin 26, 5 * (B v).card ≤ ∑ v : Fin 26,
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    Finset.sum_le_sum (fun v _ => hv v)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← hU]
    at hfin
  omega

open Classical in
theorem core2 (gs : List Gate) (o : ℕ) (H : Hy gs o) : 64 ≤ gs.length := by
  have hstar : ∀ j : Fin gs.length, ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ),
      ((gs.get j).op = GateOp.and → Reach gs o (26 + (j : ℕ)) →
        (∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) →
        A ⊆ N z ∧ (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
        val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
        ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
          (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A)) := by
    intro j
    by_cases h : (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
        ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true
    · obtain ⟨h1, h2, s, t, h3⟩ := h
      obtain ⟨z, A, lw, hh⟩ := star gs o H j j.2 h1 h2 s t h3
      exact ⟨z, A, lw, fun _ _ _ => hh⟩
    · exact ⟨0, ∅, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z A lw hst using hstar
  have hst' : ∀ j ∈ US gs o, A j ⊆ N (z j) ∧
      (∀ p ∈ A j, val gs (lw j) (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs (lw j) (fun v : Fin 26 => decide (v ∉ N (z j))) = false ∧
      ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
        (s = z j ∧ t ∈ A j) ∨ (t = z j ∧ s ∈ A j) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (mem_US gs o j).1 hj
    exact hst j h1 h2 h3
  have hmax : ∀ v : Fin 26, ∃ (A' : Finset (Fin 26)) (o' : ℕ), A' ⊆ N v ∧
      (∀ p : Fin 26, p ∈ A' → val gs o' (fun i : Fin 26 => decide (i = p)) = true) ∧
      (1 ≤ A'.card → val gs o' (fun i : Fin 26 => decide (i ∉ N v)) = false) ∧
      (∀ j ∈ US gs o, z j = v → (A j).card ≤ A'.card) := by
    intro v
    by_cases hne : ((US gs o).filter (fun j => z j = v)).Nonempty
    · obtain ⟨j0, hj0, hmx⟩ := Finset.exists_max_image _ (fun j => (A j).card) hne
      rw [Finset.mem_filter] at hj0
      obtain ⟨hA1, hA2, hA3, _⟩ := hst' j0 hj0.1
      rw [hj0.2] at hA1 hA3
      exact ⟨A j0, lw j0, hA1, hA2, fun _ => hA3,
        fun j hj hz => hmx j (Finset.mem_filter.2 ⟨hj, hz⟩)⟩
    · refine ⟨∅, 0, Finset.empty_subset _, ?_, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro h
        simp at h
      · intro j hj hz
        exact absurd ⟨j, Finset.mem_filter.2 ⟨hj, hz⟩⟩ hne
  choose A' o' hA1 hA2 hA3 hA4 using hmax
  have hmc : ∑ v : Fin 26, ((A' v).card - 1) ≤ (MGS gs A').card :=
    mrg_count N A' gs o' hLN H.1 H.2.1 hA1 hA2 hA3
  have htl := tally (US gs o) z A A' (fun j hj => (hst' j hj).1)
    (fun j hj => hA4 (z j) j hj rfl) (by
      intro v y hadj
      obtain ⟨j, hj, hval⟩ := cover gs o H v y hadj
      exact ⟨j, hj, (hst' j hj).2.2.2 v y hval⟩)
  have htop := top_count gs o H.1 (US gs o) (ROS gs o)
    (fun j hj => ⟨((mem_US gs o j).1 hj).1, ((mem_US gs o j).1 hj).2.1⟩) (mem_ROS gs o)
  have hd1 : Disjoint (US gs o) (ROS gs o) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    have a1 := ((mem_US gs o g).1 h1).1
    have a2 := ((mem_ROS gs o g).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hd2 : Disjoint (US gs o ∪ ROS gs o) (MGS gs A') := by
    rw [Finset.disjoint_left]
    intro g hg hm
    obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 hm
    obtain ⟨ho, _, w1, w2, hab, r, _, r', _, hv1, _⟩ := hmj
    rcases Finset.mem_union.1 hg with h | h
    · have a1 := ((mem_US gs o g).1 h).1
      rw [a1] at ho
      exact GateOp.noConfusion ho
    · have hr := ((mem_ROS gs o g).1 h).2
      have hm1 : w1 ∈ (gs.get g).inputs := by rw [hab]; simp
      exact reach_single gs o H _ hr r
        ((val_or gs _ g g.2 ho).2 ⟨w1, hm1, H.2.1 g w1 hm1, hv1⟩)
  have hcard : (US gs o ∪ ROS gs o ∪ MGS gs A').card ≤ gs.length := by
    simpa using Finset.card_le_univ (US gs o ∪ ROS gs o ∪ MGS gs A')
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hcard
  omega

open PEqualNP.EdgeOwnership in
theorem core (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ (x3 x4 : Fin 13), x3 - x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 = x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (x6 = x4)) = true)
    (hrej : ∀ (x3 : Finset (Fin 13)), x3.card = 4 →
      (∀ (x5 : Fin 13), ({x6 ∈ x3 | x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 ∈ x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (∀ x7 ∈ x3, x7 - x6 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) = false)
    (hflat : ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j) : 64 ≤ C.size := by
  have legal := legal_of C hmono
  have hin := hin_of C 26 hrb
  have H : Hy C.gates C.output := by
    refine ⟨legal, hin, ?_, ?_, ?_⟩
    · intro j hj hop a ha
      exact lin_and C legal hin hflat j hj hop a ha
    · intro s t hadj
      obtain ⟨hD, hsub⟩ := accwit s t hadj
      have h : val C.gates C.output (ein (Pp s t) (Ll s t)) = true := by
        have h := hacc _ _ hD
        rw [mk_eq] at h
        exact h
      exact val_mono C.gates legal _ _ (fun u hu => decide_eq_true (hsub u hu)) C.output h
    · intro s t hadj
      obtain ⟨hc, hq, hs, ht⟩ := wit s t hadj
      have h : val C.gates C.output (qin (Wt s t)) = false := by
        have h := hrej _ hc hq
        rw [mk_eq] at h
        exact h
      cases hv : val C.gates C.output (pr s t) with
      | false => rfl
      | true =>
        have h2 := val_mono C.gates legal (pr s t) (qin (Wt s t)) (by
          intro u hu
          have e : u = s ∨ u = t := of_decide_eq_true hu
          rcases e with e | e
          · rw [e]
            exact hs
          · rw [e]
            exact ht) C.output hv
        rw [h] at h2
        exact Bool.noConfusion h2
  exact core2 C.gates C.output H

end PEqualNP.Outside.L_meta_4145_aux.Flat

-- Clean-gate contraction from L-meta-2061.
namespace PEqualNP.Outside.L_meta_4145_aux.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

def Tt (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.and => ⟨GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.and, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

def Tf (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.or => ⟨GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.or, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

theorem Tt_and (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.and, ins⟩
    = ⟨GateOp.and, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tt_or (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.or, ins⟩
    = if N ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (sk N)⟩ := rfl

theorem Tf_or (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.or, ins⟩
    = ⟨GateOp.or, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tf_and (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.and, ins⟩
    = if N ∈ ins then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ins.map (sk N)⟩ := rfl

theorem map_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (ins : List ℕ)
    (hni : N ∉ ins) :
    (ins.map (sk N)).map (fun i => (A ++ E).getD i false)
      = ins.map (fun i => (A ++ b :: E).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact getD_sk A E b N hN i (fun e => hni (by rw [← e]; exact hi))

theorem all_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = true) : ∀ ins : List ℕ,
    (ins.map f).all id = ((ins.filter (fun i => decide (i ≠ N))).map f).all id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.all_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.all_cons, ih]

theorem any_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = false) : ∀ ins : List ℕ,
    (ins.map f).any id = ((ins.filter (fun i => decide (i ≠ N))).map f).any id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.any_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.any_cons, ih]

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem sound_t (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ true :: E).getD i false)
      = (Tt N h).op.eval ((Tt N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ true :: E).getD N false = true := getD_mid A E true N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    show (ins.map fun i => (A ++ true :: E).getD i false).all id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).all id
    rw [map_sk A E true N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact all_drop _ N hf ins
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id = true
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨N, hm, rfl⟩, hf⟩
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).any id
      rw [map_sk A E true N hN ins hm]

theorem sound_f (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ false :: E).getD i false)
      = (Tf N h).op.eval ((Tf N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ false :: E).getD N false = false := getD_mid A E false N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id = false
      cases hall : (ins.map fun i => (A ++ false :: E).getD i false).all id with
      | false => rfl
      | true =>
        have t := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨N, hm, rfl⟩)
        have t2 : (A ++ false :: E).getD N false = true := t
        rw [hf] at t2
        exact Bool.noConfusion t2
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).all id
      rw [map_sk A E false N hN ins hm]
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    show (ins.map fun i => (A ++ false :: E).getD i false).any id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).any id
    rw [map_sk A E false N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact any_drop _ N hf ins

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem Tt_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tt N h).op = GateOp.and ∨ (Tt N h).op = GateOp.or) ∧ (Tt N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    refine ⟨Or.inl rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inl rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inr rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'

theorem Tf_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tf N h).op = GateOp.and ∨ (Tf N h).op = GateOp.or) ∧ (Tf N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inr rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inl rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    refine ⟨Or.inr rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'

theorem Tt_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tt N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)

theorem Tf_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tf N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)

theorem assemble (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hev : ∀ x : List Bool, x.length = 26 →
      Circuit.eval ⟨pre ++ post.map T, o'⟩ x = C.eval x) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  refine ⟨⟨pre ++ post.map T, o'⟩, ?_, ?_, hev, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (26 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (26 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem copy_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (a : ℕ)
    (ha : a < 26 + pre.length)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = A.getD a false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  apply assemble C pre post g hC (Tc (26 + pre.length) a) (rn (26 + pre.length) a C.output)
    hmono hrb
  · intro h hl
    exact Tc_legal _ _ h hl
  · intro h _ M hM hi
    exact Tc_rb _ _ ha h M hM hi
  · intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    obtain ⟨E2, h1, h2⟩ := ev pre post g (Tc (26 + pre.length) a) x _ (hb (wf pre x))
      (fun h _ E' => sound_c (wf pre x) E' _ (26 + pre.length) hlen a ha rfl h)
    show (wf (pre ++ post.map (Tc (26 + pre.length) a)) x).getD
        (rn (26 + pre.length) a C.output) false = (wf C.gates x).getD C.output false
    rw [h2, hC, h1]
    exact getD_rn (wf pre x) E2 _ (26 + pre.length) hlen a ha rfl C.output

theorem const_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (T : Gate → Gate)
    (b : Bool)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = b)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hs : ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) → ∀ (A E : List Bool),
      A.length = 26 + pre.length →
      h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
        = (T h).op.eval ((T h).inputs.map fun i => (A ++ E).getD i false))
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  have key : ∀ x : List Bool, x.length = 26 → ∃ E2 : List Bool,
      wf C.gates x = wf pre x ++ b :: E2 ∧ wf (pre ++ post.map T) x = wf pre x ++ E2 := by
    intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
    rw [hC]
    exact ev pre post g T x b (hb (wf pre x))
      (fun h hh E' => hs h (hpost h hh) (wf pre x) E' hlen)
  have hout : C.output ≠ 26 + pre.length := by
    intro ho
    obtain ⟨x, y, hx, hy, ex, ey⟩ := hne
    obtain ⟨E2, h1, _⟩ := key x hx
    obtain ⟨E3, h3, _⟩ := key y hy
    have vx : C.eval x = b := by
      show (wf C.gates x).getD C.output false = b
      rw [h1, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hx])
    have vy : C.eval y = b := by
      show (wf C.gates y).getD C.output false = b
      rw [h3, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hy])
    rw [vx] at ex
    rw [vy, ex] at ey
    exact Bool.noConfusion ey
  apply assemble C pre post g hC T (sk (26 + pre.length) C.output) hmono hrb hTm hTr
  intro x hx
  obtain ⟨E2, h1, h2⟩ := key x hx
  show (wf (pre ++ post.map T) x).getD (sk (26 + pre.length) C.output) false
    = (wf C.gates x).getD C.output false
  rw [h2, h1]
  exact getD_sk _ _ _ _ (by rw [wf_len, hx]) _ hout

theorem copy_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (v : Bool) :
    op.eval [v] = v ∧ op.eval [v, v] = v := by
  rcases hop with rfl | rfl <;> cases v <;> exact ⟨rfl, rfl⟩

theorem len26 (f g : Fin 13 → Bool) : (List.ofFn f ++ List.ofFn g).length = 26 := by
  simp

theorem short_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false)
    (hdeg : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
    obtain ⟨g, hg, hd⟩ := hdeg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := split_gates C.gates k hk
    have hgg : gj = g := by rw [← hgj, hgk]
    rw [hgg] at hC
    have hl := legal_of C hmono g hg
    have hin : ∀ i ∈ g.inputs, i < 26 + pre.length := by
      intro i hi
      have := hrb k hk i (by rw [gateAt_eq C k hk, hgk]; exact hi)
      omega
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or := hl.1
    have hlen : ins.length ≤ 2 := hl.2
    have hd' : ins.length < 2 ∨ ins.getD 0 0 = ins.getD 1 0 := hd
    have hin' : ∀ i ∈ ins, i < 26 + pre.length := hin
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, r⟩⟩⟩
    · rcases hop with hop | hop
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tt (26 + pre.length)) true (fun _ => rfl)
          (fun h hl => Tt_legal _ h hl)
          (fun h hl M hM hi => Tt_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_t A E _ hA h hop) hne
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tf (26 + pre.length)) false (fun _ => rfl)
          (fun h hl => Tf_legal _ h hl)
          (fun h hl M hM hi => Tf_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_f A E _ hA h hop) hne
    · exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).1)
    · have hac : a = c := by simpa using hd'
      subst hac
      exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).2)
    · have h3 : (a :: c :: d :: r).length ≤ 2 := hlen
      simp only [List.length_cons] at h3
      omega

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma reader_or (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hC r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hC) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x hb => V1_fun n C r (n + i) x hC hr hir hout hb (key x)
  have hle := hmin _ (V1_AO2 n C r (n + i) hC hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hC hout i r1 hr1 hmin hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hC hout i r2 hr2 hmin hin2
  have hir1 : i < r1 := by have := (hC r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hC hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x hb => V2_out n C r2 c2 i x hC hr2 hc2lt hir2 hout hb (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x hb =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x hb)
  have hle := hmin _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma step3_core (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hC hout i r hr hmin hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hC hout i k r h hr hmin hkin hrin).elim
    · exact h
    · exact (reader_unique n C hC hout i r k h hk hmin hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hC) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma lift_abs (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ D : Circuit, AO2 n D ∧ D.gates.length = C.gates.length ∧
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) ∧
      PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C := by
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hC hout i j hmin hcone
  refine ⟨V2 n C r c i, V2_AO2 n C r c i hC hr hclt hir hout, V2_len n C r c i,
    fun x hb => V2_out n C r c i x hC hr hclt hir hout hb (h0 x), ?_⟩
  unfold PEqualNP.TopForm.andPairs
  refine pairs_lt2 n C (V2 n C r c i) r i j hr hir (V2_len n C r c i) ?_ ?_ ?_ ?_ hi hj hcone
    _ _ ?_ ?_
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro a' b' hb' h
    exact V2_cone n C r c i hC hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma AO2_mono {n : ℕ} {C : Circuit} (h : AO2 n C) : Monotone2 C := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e := gateAt_eq C k hk
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h k hk
  rw [e] at h1 h2
  refine ⟨?_, by rw [h2]; simp⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

lemma to_AO2 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (h2 : ∀ g ∈ C.gates, ¬ g.inputs.length < 2) : AO2 26 C := by
  intro k hk
  have e := gateAt_eq C k hk
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  have hl := legal_of C hmono _ hmem
  have h3 := h2 _ hmem
  refine ⟨by rw [e]; exact hl.1, ?_, hrb k hk⟩
  rw [e]
  have h4 : (C.gates[k]).inputs.length = 2 := by
    have := hl.2
    omega
  exact List.length_eq_two.mp h4

theorem main26 (A R : List Bool → Prop) (hA : ∀ L, A L → L.length = 26)
    (hR : ∀ L, R L → L.length = 26) (hAne : ∃ L, A L) (hRne : ∃ L, R L)
    (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ L, A L → C.eval L = true) (hrej : ∀ L, R L → C.eval L = false)
    (i j : ℕ) (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone 26 C i j)
    (hB : ∀ L, R L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ((∀ L, A L → D.eval L = true) ∧
      ∀ L, R L → D.eval L = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  by_cases hsm : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) ∧ D.size < C.size
  · obtain ⟨D, h1, h2, h3, h4⟩ := hsm
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
        C.eval y = false := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨Lr, hr⟩ := hRne
      exact ⟨La, Lr, hA _ ha, hR _ hr, hacc _ ha, hrej _ hr⟩
    have hC : AO2 26 C := by
      apply to_AO2 C hmono hrb
      intro g hg hlt
      obtain ⟨C', m1, m2, heq, hsz⟩ := short_case C hmono hrb hne ⟨g, hg, Or.inl hlt⟩
      apply hsm
      refine ⟨C', m1, m2, ⟨?_, ?_⟩, hsz⟩
      · intro L hL
        rw [heq L (hA L hL)]
        exact hacc L hL
      · intro L hL
        rw [heq L (hR L hL)]
        exact hrej L hL
    have hbelA : ∀ x : Fin 26 → Bool, A (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL _
      exact hacc _ hL
    have hbelR : ∀ x : Fin 26 → Bool, R (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL hv
      have h1 : wv 26 C x (26 + i) = false := hB _ hL
      rw [h1] at hv
      exact absurd hv (by simp)
    have tg : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) →
        ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) := by
      intro D _ hf
      constructor
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hA L hL)
        subst hx
        have h1 := hf x (hbelA x hL)
        have h2 : wv 26 C x C.output = true := hacc _ hL
        show wv 26 D x D.output = true
        rw [h1]
        exact h2
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hR L hL)
        subst hx
        have h1 := hf x (hbelR x hL)
        have h2 : wv 26 C x C.output = false := hrej _ hL
        show wv 26 D x D.output = false
        rw [h1]
        exact h2
    have hmin : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) → C.gates.length ≤ D.gates.length := by
      intro D hD hf
      by_contra hlt
      apply hsm
      refine ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, ?_⟩
      show D.gates.length < C.gates.length
      omega
    have hout : C.output < 26 + C.gates.length := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨x, hx⟩ := ofFn_of_len La 26 (hA La ha)
      subst hx
      exact out_lt 26 C x (hacc _ ha)
    obtain ⟨D, hD, hlen, hf, hp⟩ := lift_abs 26 C hC hout i j hmin hi hj hij
    exact ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, Or.inr ⟨hlen, hp⟩⟩

end PEqualNP.Outside.L_meta_4145_aux.Lift

namespace PEqualNP.Outside.L_meta_4145_aux

open Flat
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

theorem commonInputs (p l : Fin 13) (inc : p-l ∈ ({0,1,3,9} : Finset (Fin 13)))
    (Q : Finset (Fin 13)) {a b : Fin 26}
    (pa : ein p l a = true) (pb : ein p l b = true)
    (na : qin Q a = true) (nb : qin Q b = true) : a = b := by
  by_cases ha : a.val < 13 <;> by_cases hb : b.val < 13
  · simp [ein,mk,ha,hb] at pa pb
    apply Fin.ext
    have ia := congrArg Fin.val pa
    have ib := congrArg Fin.val pb
    simp at ia ib
    omega
  · simp [ein,mk,ha,hb] at pa pb
    simp only [qin,mk,dite_eq_left ha,decide_eq_true_eq] at na
    simp only [qin,mk,dite_eq_right hb,decide_eq_true_eq] at nb
    rw [pa] at na
    rw [pb] at nb
    exact False.elim (nb p na inc)
  · simp [ein,mk,ha,hb] at pa pb
    simp only [qin,mk,dite_eq_right ha,decide_eq_true_eq] at na
    simp only [qin,mk,dite_eq_left hb,decide_eq_true_eq] at nb
    rw [pa] at na
    rw [pb] at nb
    exact False.elim (na p nb inc)
  · simp [ein,mk,ha,hb] at pa pb
    apply Fin.ext
    have ia := congrArg Fin.val pa
    have ib := congrArg Fin.val pb
    simp at ia ib
    omega

-- One changed wire can only increase the output if it increases on that input.
theorem compareWire {n : ℕ} (a b : List Gate) (len : a.length = b.length)
    (j : ℕ) (away : ∀ k (h : k < a.length), k ≠ j → a[k] = b[k]'(by omega))
    (legal : ∀ g ∈ a, g.op = .and ∨ g.op = .or)
    (x : Fin n → Bool) (changed : val a (n+j) x = true → val b (n+j) x = true) :
    ∀ i, val a i x = true → val b i x = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro h
    by_cases small : i<n
    · simpa only [val_input a _ i small,val_input b _ i small] using h
    by_cases big : n+a.length ≤ i
    · rw [val_big a x i big] at h
      contradiction
    let k := i-n
    have hk : k < a.length := by dsimp [k]; omega
    have hk' : k < b.length := by omega
    have eq : i=n+k := by dsimp [k]; omega
    by_cases same : k=j
    · rw [eq,same] at h ⊢
      exact changed h
    have gates := away k hk same
    rw [eq] at h ⊢
    rcases legal a[k] (List.getElem_mem hk) with ho | ho
    · apply (val_and b x k hk' (gates ▸ ho)).mpr
      intro w hw
      obtain ⟨hw',hv⟩ := (val_and a x k hk ho).mp h w (gates.symm ▸ hw)
      exact ⟨hw',ih w (by omega) hv⟩
    · obtain ⟨w,hw,hw',hv⟩ := (val_or a x k hk ho).mp h
      exact (val_or b x k hk' (gates ▸ ho)).mpr ⟨w,gates ▸ hw,hw',ih w (by omega) hv⟩

private def off (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨.or,[]⟩, C.output⟩

private lemma legalOff (C : Circuit) (j : ℕ) (hm : Monotone2 C) (hr : ReadsBack 26 C) :
    Monotone2 (off C j) ∧ ReadsBack 26 (off C j) := by
  constructor
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hg
    change k < (C.gates.set j _).length at hk
    change ((C.gates.set j _)[k].op ∈ _ ∧ (C.gates.set j _)[k].inputs.length ≤ _)
    rw [List.getElem_set]
    split
    · simp
    · exact hm _ (List.getElem_mem (by simpa using hk))
  · intro k hk w hw
    have hk' : k < C.gates.length := by simpa [off] using hk
    rw [gateAt_eq _ _ hk] at hw
    change k < (C.gates.set j ⟨.or,[]⟩).length at hk
    change w ∈ ((C.gates.set j _)[k]).inputs at hw
    rw [List.getElem_set] at hw
    split at hw
    · simp at hw
    · exact hr k hk' w (by rwa [gateAt_eq _ _ hk'])

lemma rawPairVal (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (a b : Fin 26)
    (kind : C.gates[j].op = .and) (pins : C.gates[j].inputs = [↑a,↑b]) (x : Fin 26 → Bool) :
    val C.gates (26+j) x = true ↔ x a = true ∧ x b = true := by
  rw [val_and C.gates x j hj kind, pins]
  have av : val C.gates a x = x a := val_input _ _ _ a.isLt
  have bv : val C.gates b x = x b := val_input _ _ _ b.isLt
  constructor
  · intro h
    exact ⟨av ▸ (h a (by simp)).2, bv ▸ (h b (by simp)).2⟩
  · rintro ⟨ha,hb⟩ w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨by have := a.isLt; omega, av.trans ha⟩
    · exact ⟨by have := b.isLt; omega, bv.trans hb⟩

abbrev Incident (p l : Fin 13) := p-l ∈ ({0,1,3,9} : Finset (Fin 13))
def positiveRows : Set (Fin 26 → Bool) := {x | ∃ p l, Incident p l ∧ x = ein p l}
def negativeRows (test : Finset (Fin 13) → Prop) : Set (Fin 26 → Bool) :=
  {x | ∃ Q, test Q ∧ x = qin Q}

def fits (test : Finset (Fin 13) → Prop) (C : Circuit) :=
  (∀ x ∈ positiveRows, C.eval (List.ofFn x) = true) ∧
  (∀ x ∈ negativeRows test, C.eval (List.ofFn x) = false)

abbrev NestedPair (C : Circuit) (i j : ℕ) : Prop :=
  (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j

private def setPair (C : Circuit) (i : ℕ) (a b : Fin 26) : Circuit :=
  ⟨C.gates.set i ⟨.and,[a.val,b.val]⟩, C.output⟩

private lemma setPairLegal (C : Circuit) (i : ℕ) (a b : Fin 26) (hm : Monotone2 C)
    (hr : ReadsBack 26 C) : Monotone2 (setPair C i a b) ∧ ReadsBack 26 (setPair C i a b) := by
  constructor
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hg
    change k < (C.gates.set i _).length at hk
    change ((C.gates.set i _)[k].op ∈ _ ∧ (C.gates.set i _)[k].inputs.length ≤ _)
    rw [List.getElem_set]
    split
    · simp
    · exact hm _ (List.getElem_mem (by simpa using hk))
  · intro k hk w hw
    have hk' : k < C.gates.length := by simpa [setPair] using hk
    rw [gateAt_eq _ _ hk] at hw
    change k < (C.gates.set i ⟨.and,[a.val,b.val]⟩).length at hk
    change w ∈ ((C.gates.set i _)[k]).inputs at hw
    rw [List.getElem_set] at hw
    split at hw
    · have ha := a.isLt
      have hb := b.isLt
      simp at hw
      omega
    · exact hr k hk' w (by rwa [gateAt_eq _ _ hk'])

private theorem rewireCones (C Z : Circuit) (i : ℕ) (zl : Z.gates.length = C.gates.length)
    (away : ∀ k, k < Z.gates.length → k ≠ i → gateAt Z k = gateAt C k)
    (raw : ∀ w ∈ (gateAt Z i).inputs, w < 26) :
    (∀ u v, InCone 26 Z u v → InCone 26 C u v) ∧
    (∀ v, InCone 26 C i v → InCone 26 Z i v) := by
  constructor
  · intro u v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro h
      rw [PEqualNP.Outside.L_meta_4145_aux.Lift.inCone_iff] at h ⊢
      obtain ⟨hv,k,kv,mem,h⟩ := h
      have ne : v ≠ i := by rintro rfl; have := raw _ mem; omega
      rw [away v hv ne] at mem
      exact ⟨by omega,k,kv,mem,h.imp_right (ih k kv)⟩
  · intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro h
      have iv := (PEqualNP.Outside.L_meta_4145_aux.Lift.inCone_lt 26 C i v h).1
      rw [PEqualNP.Outside.L_meta_4145_aux.Lift.inCone_iff] at h ⊢
      obtain ⟨hv,k,kv,mem,h⟩ := h
      rw [← away v (by omega) (by omega)] at mem
      exact ⟨by omega,k,kv,mem,h.imp_right (ih k kv)⟩

private theorem pairsSubset (C Z : Circuit) (zl : Z.gates.length = C.gates.length)
    (ops : ∀ k, k < Z.gates.length → (gateAt Z k).op = (gateAt C k).op)
    (cones : ∀ u v, InCone 26 Z u v → InCone 26 C u v) :
    PEqualNP.TopForm.andPairs 26 Z ≤ PEqualNP.TopForm.andPairs 26 C := by
  unfold PEqualNP.TopForm.andPairs
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp ⊢
  obtain ⟨⟨h1,h2⟩,o1,o2,co⟩ := hp
  exact ⟨⟨by omega,by omega⟩,(ops _ h1) ▸ o1,(ops _ h2) ▸ o2,cones _ _ co⟩

private def listRows (P : Set (Fin 26 → Bool)) (L : List Bool) := ∃ x ∈ P, L = List.ofFn x

private lemma shrinkClean (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (test : Finset (Fin 13) → Prop) (neg : ∃ Q, test Q) (hf : fits test C)
    (i j : ℕ) (nested : NestedPair C i j)
    (clean : ∀ Q, test Q → val C.gates (26+i) (qin Q) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ fits test D ∧
      (D.size < C.size ∨ D.size = C.size ∧ PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  obtain ⟨Q,hQ⟩ := neg
  obtain ⟨D,hmD,hrD,hfD,decr⟩ := PEqualNP.Outside.L_meta_4145_aux.Lift.main26
    (listRows positiveRows) (listRows (negativeRows test)) (by rintro L ⟨x,hx,rfl⟩; simp)
    (by rintro L ⟨x,hx,rfl⟩; simp)
    ⟨_,ein 0 0,⟨0,0,by decide,rfl⟩,rfl⟩ ⟨_,qin Q,⟨Q,hQ,rfl⟩,rfl⟩ C hm hr
    (by rintro _ ⟨x,hx,rfl⟩; exact hf.1 _ hx)
    (by rintro _ ⟨x,hx,rfl⟩; exact hf.2 _ hx)
    i j nested.1 nested.2.1 nested.2.2 (by rintro _ ⟨x,⟨U,hU,rfl⟩,rfl⟩; exact clean U hU)
  exact ⟨D,hmD,hrD,⟨fun x hx => hfD.1 _ ⟨x,hx,rfl⟩,fun x hx => hfD.2 _ ⟨x,hx,rfl⟩⟩,decr⟩

def needsGate (C : Circuit) (i : ℕ) (x : Fin 26 → Bool) : Prop :=
  (off C i).eval (List.ofFn x) = false

private lemma preservedWhenOff (C Z : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (i : ℕ) (hi : i < C.gates.length) (zl : C.gates.length = Z.gates.length)
    (away : ∀ k (hk : k < C.gates.length), k ≠ i → C.gates[k] = Z.gates[k]'(by omega))
    (out : C.output = Z.output) (x : Fin 26 → Bool) (hx : ¬ needsGate C i x) :
    Z.eval (List.ofFn x) = true := by
  let F := off C i
  obtain ⟨fm,fr⟩ := legalOff C i hm hr
  have lf : F.gates.length = C.gates.length := by simp [F,off]
  have fi : i < F.gates.length := by omega
  have fs : F.gates[i] = ⟨.or,[]⟩ := by simp [F,off]
  have foff : val F.gates (26+i) x ≠ true := by
    intro h
    obtain ⟨w,hw,_⟩ := (val_or F.gates x i fi (by simp [fs])).mp h
    simp [fs] at hw
  have forward (k) (hk : k < F.gates.length) (ne : k ≠ i) :
      F.gates[k] = Z.gates[k]'(by omega) := by
    change (C.gates.set i _)[k] = _
    exact (List.getElem_set_ne ne.symm _).trans (away k (by omega) ne)
  have evalF : F.eval (List.ofFn x) = true := by
    cases e : F.eval (List.ofFn x)
    · exact False.elim (hx e)
    · rfl
  change val Z.gates Z.output x = true
  rw [← out]
  exact compareWire F.gates Z.gates (lf.trans zl) i forward (fun g hg => (legal_of F fm g hg).1)
    x (fun h => (foff h).elim) C.output evalF

theorem cleanNeededByPair (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (test : Finset (Fin 13) → Prop) (neg : ∃ Q, test Q) (hf : fits test C)
    (i j : ℕ) (nested : NestedPair C i j) (a b : Fin 26)
    (pos : ∀ x ∈ positiveRows, needsGate C i x → val C.gates (26+i) x = true → x a = true ∧ x b = true)
    (clean : ∀ Q, test Q → ¬(qin Q a = true ∧ qin Q b = true)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ fits test D ∧
      (D.size < C.size ∨ D.size = C.size ∧ PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  let Z := setPair C i a b
  obtain ⟨hmZ,hrZ⟩ := setPairLegal C i a b hm hr
  have zl : Z.gates.length = C.gates.length := by simp [Z,setPair]
  have range := PEqualNP.Outside.L_meta_4145_aux.Lift.inCone_lt 26 C i j nested.2.2
  have hi : i < Z.gates.length := by omega
  have self : Z.gates[i] = ⟨.and,[a.val,b.val]⟩ := by simp [Z,setPair]
  have selfAt : gateAt Z i = ⟨.and,[a.val,b.val]⟩ := (gateAt_eq _ _ hi).trans self
  have away : ∀ k (hk : k < Z.gates.length), k ≠ i → Z.gates[k] = C.gates[k]'(by omega) := by
    intro k hk ne
    change (C.gates.set i _)[k] = _
    exact List.getElem_set_ne ne.symm _
  have awayAt (k) (hk : k < Z.gates.length) (ne : k ≠ i) : gateAt Z k = gateAt C k := by
    rw [gateAt_eq _ _ hk,gateAt_eq _ _ (show k < C.gates.length by omega)]
    exact away k hk ne
  have ops (k) (hk : k < Z.gates.length) : (gateAt Z k).op = (gateAt C k).op := by
    by_cases eq : k = i
    · subst k; rw [selfAt,nested.1]
    · rw [awayAt k hk eq]
  obtain ⟨subset,above⟩ := rewireCones C Z i zl awayAt (by
    intro w hw
    rw [selfAt] at hw
    have ha := a.isLt
    have hb := b.isLt
    simp at hw
    omega)
  have valZ := rawPairVal Z i hi a b (by simp [self]) (by simp [self])
  have cleanZ (Q) (hQ : test Q) : val Z.gates (26+i) (qin Q) = false :=
    Bool.eq_false_iff.mpr (fun h => clean _ hQ ((valZ _).mp h))
  have fitZ : fits test Z := by
    constructor
    · intro x hx
      by_cases need : needsGate C i x
      · exact compareWire C.gates Z.gates zl.symm i (fun k hk ne => (away k (by omega) ne).symm)
          (fun g hg => (legal_of C hm g hg).1) x (fun h => (valZ x).mpr (pos x hx need h)) C.output (hf.1 _ hx)
      · exact preservedWhenOff C Z hm hr i (by omega) zl.symm
          (fun k hk ne => (away k (by omega) ne).symm) rfl x need
    · intro x hx
      obtain ⟨Q,hQ,rfl⟩ := hx
      apply Bool.eq_false_iff.mpr
      intro bad
      have h := compareWire Z.gates C.gates zl i away (fun g hg => (legal_of Z hmZ g hg).1)
        (qin Q) (fun h => by rw [cleanZ _ hQ] at h; contradiction) C.output bad
      change C.eval (List.ofFn (qin Q)) = true at h
      rw [hf.2 _ ⟨Q,hQ,rfl⟩] at h
      contradiction
  have pairZ : NestedPair Z i j :=
    ⟨(ops i hi).trans nested.1,(ops j (by omega)).trans nested.2.1,above j nested.2.2⟩
  obtain ⟨D,hD,rD,fD,dec⟩ := shrinkClean Z hmZ hrZ test neg fitZ i j pairZ cleanZ
  have sizeZ : Z.size = C.size := zl
  have bound := pairsSubset C Z zl ops subset
  exact ⟨D,hD,rD,fD,by rcases dec with h | ⟨h,k⟩ <;> omega⟩

theorem oneRequiredEdge (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (test : Finset (Fin 13) → Prop) (neg : ∃ Q, test Q) (hf : fits test C)
    (i j : ℕ) (nested : NestedPair C i j)
    (unique : ∀ x ∈ positiveRows, ∀ y ∈ positiveRows,
      needsGate C i x → needsGate C i y → x = y) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ fits test D ∧
      (D.size < C.size ∨ D.size = C.size ∧ PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  obtain ⟨p,l,inc,cover⟩ : ∃ p l, Incident p l ∧
      ∀ x ∈ positiveRows, needsGate C i x → x = ein p l := by
    by_cases h : ∃ x ∈ positiveRows, needsGate C i x
    · obtain ⟨_,⟨p,l,inc,rfl⟩,need⟩ := h
      exact ⟨p,l,inc,fun x hx nx => unique x hx _ ⟨p,l,inc,rfl⟩ nx need⟩
    · exact ⟨0,0,by decide,fun x hx nx => (h ⟨x,hx,nx⟩).elim⟩
  let a : Fin 26 := ⟨p.val, by have := p.isLt; omega⟩
  let b : Fin 26 := ⟨13+l.val, by have := l.isLt; omega⟩
  have pa : ein p l a = true := by simp [a,ein,mk,p.isLt]
  have pb : ein p l b = true := by simp [b,ein,mk]
  have ab : a ≠ b := by
    intro eq
    have := congrArg Fin.val eq
    dsimp [a,b] at this
    have := p.isLt
    omega
  exact cleanNeededByPair C hm hr test neg hf i j nested a b
    (fun x hx nx _ => cover x hx nx ▸ ⟨pa,pb⟩)
    (fun Q _ h => ab (commonInputs p l inc Q pa pb h.1 h.2))

abbrev reduces (test : Finset (Fin 13) → Prop) (C : Circuit) : Prop :=
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ fits test D ∧
      (D.size < C.size ∨ D.size = C.size ∧ PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C)

def Quad (Q : Finset (Fin 13)) := Q.card = 4 ∧ ∀ l, (Q.filter fun p => Incident p l).card ≤ 2

private theorem leastWitness {α : Type*} (P : α → Prop) (cost : α → ℕ) (exist : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → cost x ≤ cost y := by
  classical
  have ex : ∃ n, ∃ x, P x ∧ cost x = n := by obtain ⟨x,h⟩ := exist; exact ⟨_,x,h,rfl⟩
  obtain ⟨w,hw,eq⟩ := Nat.find_spec ex
  exact ⟨w,hw,fun y hy => eq ▸ Nat.find_min' ex ⟨y,hy,rfl⟩⟩

theorem normalizedFirstChild :
    let S := singerLines3
    let row := fun Q => incidenceInput Q (missLines S Q)
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
      ∀ Q, IsQuadrangle S Q → C.eval (row Q) = false
    let inner := fun (C : Circuit) i => (gateAt C i).op = .and ∧
      ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
    let hard := fun C : Circuit => (∃ i, inner C i) ∧ ∀ i, inner C i →
      (∃ Q, IsQuadrangle S Q ∧ (C.wires (row Q)).getD (26+i) false = true) ∧
      2 ≤ ((incidences S).filter fun e =>
        ({C with gates := C.gates.set i ⟨.or,[]⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false).card
    ∀ C, valid C → C.size < 64 → ∃ D, valid D ∧ D.size ≤ C.size ∧ hard D := by
  classical
  intro S row valid inner hard C ok small
  have geom : ∀ p l : Fin 13, p ∈ S l ↔ Incident p l := by decide +kernel
  have qiff (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔ Quad Q := by
    have eq (l : Fin 13) : Q ∩ S l = Q.filter fun p => Incident p l := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ S l).card ≤ 2) ↔ (_ ∧ ∀ l, (Q.filter fun p => Incident p l).card ≤ 2)
    simp only [eq]
  have rowQ (Q : Finset (Fin 13)) : row Q = List.ofFn (qin Q) := by
    change List.ofFn _ ++ List.ofFn _ = _
    change _ = List.ofFn (mk _ _)
    rw [← mk_eq]
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    simp only [missLines,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right]
    exact forall₂_congr fun p _ => not_congr (geom p l)
  have rowP (p l : Fin 13) : incidenceInput {p} {l} = List.ofFn (ein p l) := by
    rw [incidenceInput]
    simp only [Finset.mem_singleton]
    exact mk_eq _ _
  have fit (E : Circuit) : valid E ↔ Monotone2 E ∧ ReadsBack 26 E ∧ fits Quad E := by
    constructor
    · rintro ⟨em,er,ep,en⟩
      refine ⟨em,er,?_,?_⟩
      · rintro _ ⟨p,l,inc,rfl⟩
        rw [←rowP]; exact ep l p ((geom p l).mpr inc)
      · rintro _ ⟨Q,hQ,rfl⟩
        rw [←rowQ]; exact en Q ((qiff Q).mpr hQ)
    · rintro ⟨em,er,ep,en⟩
      refine ⟨em,er,?_,?_⟩
      · intro l p hp
        rw [rowP]; exact ep _ ⟨p,l,(geom p l).mp hp,rfl⟩
      · intro Q hQ
        rw [rowQ]; exact en _ ⟨Q,(qiff Q).mp hQ,rfl⟩
  obtain ⟨M,vm,minS⟩ := leastWitness valid Circuit.size ⟨C,ok⟩
  obtain ⟨E,⟨ve,es⟩,minK⟩ := leastWitness (fun D => valid D ∧ D.size = M.size)
    (PEqualNP.TopForm.andPairs 26) ⟨M,vm,rfl⟩
  have bound : E.size ≤ C.size := es ▸ minS _ ok
  have esmall : E.size < 64 := lt_of_le_of_lt bound small
  obtain ⟨em,er,ef⟩ := (fit E).mp ve
  have nomove : ¬ reduces Quad E := by
    rintro ⟨D,dm,dr,df,dd⟩
    have vd := (fit D).mpr ⟨dm,dr,df⟩
    rcases dd with smaller | ⟨same,k⟩
    · have h := minS D vd; omega
    · exact (Nat.not_lt_of_ge (minK _ ⟨vd,same.trans es⟩)) k
  have ex : ∃ i j, NestedPair E i j := by
    by_contra flat
    have sz : 64 ≤ E.size := core E em er (by
      intro p l inc
      rw [mk_eq]
      exact ef.1 _ ⟨p,l,inc,rfl⟩) (by
      intro Q card lines
      rw [mk_eq]
      exact ef.2 _ ⟨Q,⟨card,lines⟩,rfl⟩) flat
    omega
  obtain ⟨i₀,j₀,h₀⟩ := ex
  refine ⟨E,ve,bound,⟨i₀,h₀.1,j₀,h₀.2⟩,?_⟩
  intro i hi
  obtain ⟨io,j,jo,ij⟩ := hi
  have pair : NestedPair E i j := ⟨io,jo,ij⟩
  have neg : ∃ Q, Quad Q := ⟨{0,1,2,5},by unfold Quad; decide⟩
  constructor
  · by_contra no
    apply nomove
    apply shrinkClean E em er Quad neg ef i j pair
    intro Q hQ
    apply Bool.eq_false_iff.mpr
    intro h
    exact no ⟨Q,(qiff Q).mpr hQ,by rw [rowQ]; exact h⟩
  · by_contra few
    apply nomove
    apply oneRequiredEdge E em er Quad neg ef i j pair
    rintro _ ⟨p,l,inc,rfl⟩ _ ⟨p',l',inc',rfl⟩ hx hy
    let F : Circuit := ⟨E.gates.set i ⟨.or,[]⟩, E.output⟩
    let K := (incidences S).filter fun e => F.eval (incidenceInput {e.1} {e.2}) = false
    have mem (u v : Fin 13) (uv : Incident u v) (need : needsGate E i (ein u v)) : (u,v) ∈ K := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(geom u v).mpr uv⟩,?_⟩
      change F.eval (incidenceInput {u} {v}) = false
      rw [rowP]
      exact need
    have kl : K.card ≤ 1 := by change ¬2 ≤ K.card at few; omega
    have eq := Finset.card_le_one.mp kl (p,l) (mem p l inc hx) (p',l') (mem p' l' inc' hy)
    cases eq
    rfl

end PEqualNP.Outside.L_meta_4145_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_4145 : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x6.size < (64 : ℕ) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x3 x9 ∧ x9.size ≤ x6.size ∧ x5 x9 :=
  PEqualNP.Outside.L_meta_4145_aux.normalizedFirstChild
