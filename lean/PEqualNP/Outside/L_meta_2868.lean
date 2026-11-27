import PEqualNP.Defs

-- Circuit evaluation and counting lemmas are adapted from L-meta-2051 by willakone.
namespace PEqualNP.Outside.L_meta_2868

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

open Classical in
theorem mcount_ge {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (J : Finset (Fin gates.length)) (o : Fin gates.length → ℕ)
    (hoc : ∀ i ∈ J, val gates (o i) c = false)
    (hot : ∀ p ∈ M, ∃ i ∈ J, val gates (o i) (τ p) = true) :
    M.card ≤ J.card + ∑ g : Fin gates.length, (if Mrg gates M c τ g then 1 else 0) := by
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have key : ∀ (Y Y2 : Finset (Fin n)), Y ⊆ M → Con gates M c τ gates.length Y2 →
      J.filter (fun i => ∃ p ∈ M, p ∈ Y ∧ val gates (o i) (τ p) = true) =
        J.filter (fun i => ∃ p ∈ M, p ∈ Y2 ∧ val gates (o i) (τ p) = true) → Y ⊆ Y2 := by
    intro Y Y2 hY hY2 he p hp
    obtain ⟨i, hi, hv⟩ := hot p (hY hp)
    have hm : i ∈ J.filter (fun i => ∃ p ∈ M, p ∈ Y ∧ val gates (o i) (τ p) = true) :=
      Finset.mem_filter.2 ⟨hi, p, hY hp, hp, hv⟩
    rw [he] at hm
    obtain ⟨_, q, hqM, hqY, hvq⟩ := Finset.mem_filter.1 hm
    have holt : o i < n + gates.length := by
      by_contra h
      have hb := val_big gates (τ p) (o i) (by omega)
      rw [hv] at hb
      exact Bool.noConfusion hb
    exact (single gates M c τ hτ legal hin gates.length le_rfl Y2 hY2 (o i) holt (hoc i hi)
      q hqM p (hY hp) hvq hv).1 hqY
  have hP : (P gates M c τ gates.length).card ≤ 2 ^ J.card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card_of_injOn
      (fun X => J.filter (fun i => ∃ p ∈ M, p ∈ X ∧ val gates (o i) (τ p) = true))
    · intro X _
      exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
    · intro X hX X2 hX2 heq
      have hX1 : X ∈ P gates M c τ gates.length := hX
      have hX3 : X2 ∈ P gates M c τ gates.length := hX2
      rw [P, Finset.mem_filter, Finset.mem_powerset] at hX1 hX3
      exact Finset.Subset.antisymm (key X X2 hX1.1 hX3.2 heq) (key X2 X hX3.1 hX1.2 heq.symm)
  have h2 : 2 ^ M.card ≤
      2 ^ (J.card + ∑ g : Fin gates.length, (if Mrg gates M c τ g then 1 else 0)) := by
    rw [← hcnt, pow_add]
    exact Nat.mul_le_mul_right _ hP
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

open Classical in
theorem mrg_count {n : ℕ} (L B : Fin n → Finset (Fin n)) (gates : List Gate)
    (z : Fin gates.length → Fin n) (U : Finset (Fin gates.length)) (o : Fin gates.length → ℕ)
    (hL : ∀ i j : Fin n, i ≠ j → (L i ∩ L j).card ≤ 1)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hB : ∀ v : Fin n, B v ⊆ L v)
    (hot : ∀ (v p : Fin n), p ∈ B v →
      ∃ i ∈ U, z i = v ∧ val gates (o i) (fun u : Fin n => decide (u = p)) = true)
    (hoc : ∀ i ∈ U, val gates (o i) (fun u : Fin n => decide (u ∉ L (z i))) = false) :
    ∑ v : Fin n, (B v).card ≤ U.card +
      (Finset.univ.filter (fun g : Fin gates.length => ∃ v, MJ gates L B v g)).card := by
  have h1 : ∀ v : Fin n, (B v).card ≤ (U.filter (fun i => z i = v)).card +
      ∑ g : Fin gates.length, (if MJ gates L B v g then (1 : ℕ) else 0) := by
    intro v
    apply mcount_ge gates (B v) (fun u => decide (u ∉ L v)) (fun y u => decide (u = y))
      (fun p _ u hu => of_decide_eq_true hu) legal hin (U.filter (fun i => z i = v)) o
    · intro i hi
      obtain ⟨hiU, hz⟩ := Finset.mem_filter.1 hi
      have h := hoc i hiU
      rw [hz] at h
      exact h
    · intro p hp
      obtain ⟨i, hi, hz, hv⟩ := hot v p hp
      exact ⟨i, Finset.mem_filter.2 ⟨hi, hz⟩, hv⟩
  have h2 : ∀ g : Fin gates.length,
      (∑ j : Fin n, (if MJ gates L B j g then (1 : ℕ) else 0)) ≤
        (if ∃ j, MJ gates L B j g then (1 : ℕ) else 0) := by
    intro g
    by_cases hex : ∃ j0 : Fin n, MJ gates L B j0 g
    · rw [if_pos hex]
      obtain ⟨j0, hj0⟩ := hex
      have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (if MJ gates L B j g then (1 : ℕ) else 0) ≤ (if j = j0 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : MJ gates L B j g
        · have e : j = j0 := by
            by_contra hne
            exact disj gates legal hin (L j) (L j0) (B j) (B j0) (hB j) (hL j j0 hne) g hj hj0
          rw [if_pos hj, if_pos e]
        · rw [if_neg hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (if MJ gates L B j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (fun h => hex ⟨j, h⟩)
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  have hU : U.card = ∑ v : Fin n, (U.filter (fun i => z i = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (z j))
  calc ∑ v : Fin n, (B v).card
      ≤ ∑ v : Fin n, ((U.filter (fun i => z i = v)).card +
          ∑ g : Fin gates.length, (if MJ gates L B v g then (1 : ℕ) else 0)) :=
        Finset.sum_le_sum (fun v _ => h1 v)
    _ = U.card + ∑ v : Fin n, ∑ g : Fin gates.length,
          (if MJ gates L B v g then (1 : ℕ) else 0) := by
        rw [Finset.sum_add_distrib, ← hU]
    _ = U.card + ∑ g : Fin gates.length, ∑ v : Fin n,
          (if MJ gates L B v g then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm]
    _ ≤ U.card + ∑ g : Fin gates.length, (if ∃ v, MJ gates L B v g then (1 : ℕ) else 0) :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun g _ => h2 g)) _
    _ = U.card +
        (Finset.univ.filter (fun g : Fin gates.length => ∃ v, MJ gates L B v g)).card := by
        rw [Finset.card_filter]

def pr {n : ℕ} (s t : Fin n) : Fin n → Bool := fun u => decide (u = s ∨ u = t)

theorem pr_true {n : ℕ} (s t u : Fin n) (h : u = s ∨ u = t) : pr s t u = true := by
  unfold pr
  exact decide_eq_true h

theorem pr_of {n : ℕ} (s t u : Fin n) (h : pr s t u = true) : u = s ∨ u = t := by
  unfold pr at h
  exact of_decide_eq_true h

def Lin (n : ℕ) (gs : List Gate) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val gs w x = true →
    ∃ u : Fin n, x u = true ∧ val gs w (fun v : Fin n => decide (v = u)) = true

def Good (n : ℕ) (gs : List Gate) (o w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val gs w x = true → val gs o x = true

theorem good_down (n : ℕ) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∀ w, Good n gs o w → val gs w x = true →
      ∃ w2, Good n gs o w2 ∧ val gs w2 x = true ∧
        (w2 < n ∨ ∃ (j : ℕ) (hj : j < gs.length), w2 = n + j ∧ gs[j].op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr hx
    by_cases hwn : w < n
    · exact ⟨w, hr, hx, Or.inl hwn⟩
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - n < gs.length := by omega
        have he : n + (w - n) = w := by omega
        rcases (legal gs[w - n] (List.getElem_mem hi)).1 with ha | ho
        · exact ⟨w, hr, hx, Or.inr ⟨w - n, hi, he.symm, ha⟩⟩
        · have hx1 : val gs (n + (w - n)) x = true := by rw [he]; exact hx
          obtain ⟨a, ha, halt, hav⟩ := (val_or gs x (w - n) hi ho).1 hx1
          refine ih a (by omega) ?_ hav
          intro x2 hx2
          apply hr x2
          rw [← he]
          exact (val_or gs x2 (w - n) hi ho).2 ⟨a, ha, halt, hx2⟩

open Classical in
noncomputable def Nb {n : ℕ} (adj : Fin n → Fin n → Prop) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => adj v y)

theorem mem_Nb {n : ℕ} (adj : Fin n → Fin n → Prop) (v y : Fin n) :
    y ∈ Nb adj v ↔ adj v y := by
  unfold Nb
  simp

def Hy (n : ℕ) (adj : Fin n → Fin n → Prop) (gs : List Gate) (o : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < n + (i : ℕ)) ∧
  (∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
    ∃ a b : ℕ, gs[j].inputs = [a, b] ∧ Lin n gs a ∧ Lin n gs b) ∧
  (∀ s t : Fin n, adj s t → val gs o (pr s t) = true) ∧
  (∀ s t : Fin n, ¬ adj s t → val gs o (pr s t) = false)

theorem good_adj (n : ℕ) (adj : Fin n → Fin n → Prop) (gs : List Gate) (o : ℕ)
    (H : Hy n adj gs o) (w : ℕ) (hr : Good n gs o w)
    (s t : Fin n) (h : val gs w (pr s t) = true) : adj s t := by
  have h2 := hr _ h
  by_contra hb
  rw [H.2.2.2.2 s t hb] at h2
  exact Bool.noConfusion h2

theorem val_e_pr {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (s t u : Fin n) (hu : u = s ∨ u = t)
    (h : val gs w (fun v : Fin n => decide (v = u)) = true) : val gs w (pr s t) = true :=
  val_mono gs legal _ _ (by
    intro v hv
    have e : v = u := of_decide_eq_true hv
    rw [e]
    exact pr_true s t u hu) w h

theorem good_single (n : ℕ) (adj : Fin n → Fin n → Prop) (hirr : ∀ s, ¬ adj s s)
    (gs : List Gate) (o : ℕ) (H : Hy n adj gs o) (w : ℕ) (hr : Good n gs o w)
    (s : Fin n) (h : val gs w (fun v : Fin n => decide (v = s)) = true) : False :=
  hirr s (good_adj n adj gs o H w hr s s (val_e_pr gs H.1 w s s s (Or.inl rfl) h))

theorem star (n : ℕ) (adj : Fin n → Fin n → Prop) (hirr : ∀ s, ¬ adj s s)
    (hsym : ∀ s t, adj s t → adj t s)
    (hk : ∀ s1 s2 t1 t2 : Fin n, adj s1 t1 → adj s1 t2 → adj s2 t1 → adj s2 t2 →
      s1 ≠ s2 → t1 = t2)
    (gs : List Gate) (o : ℕ) (H : Hy n adj gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Good n gs o (n + j)) (s0 t0 : Fin n)
    (h0 : val gs (n + j) (pr s0 t0) = true) :
    ∃ (z : Fin n) (A : Finset (Fin n)) (lw : ℕ), A ⊆ Nb adj z ∧
      (∀ p ∈ A, val gs lw (fun v : Fin n => decide (v = p)) = true) ∧
      val gs lw (fun v : Fin n => decide (v ∉ Nb adj z)) = false ∧
      ∀ s t : Fin n, val gs (n + j) (pr s t) = true → (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A) := by
  obtain ⟨a, b, hab, la, lb⟩ := H.2.2.1 j hj hop
  have ha : a ∈ gs[j].inputs := by rw [hab]; simp
  have hb : b ∈ gs[j].inputs := by rw [hab]; simp
  have halt : a < n + j := H.2.1 ⟨j, hj⟩ a ha
  have hblt : b < n + j := H.2.1 ⟨j, hj⟩ b hb
  have hST : ∀ s t : Fin n, val gs a (fun v : Fin n => decide (v = s)) = true →
      val gs b (fun v : Fin n => decide (v = t)) = true → adj s t := by
    intro s t hs ht
    apply good_adj n adj gs o H _ hr s t
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hab] at hi
    rcases List.mem_pair.1 hi with e | e
    · rw [e]
      exact ⟨halt, val_e_pr gs H.1 a s t s (Or.inl rfl) hs⟩
    · rw [e]
      exact ⟨hblt, val_e_pr gs H.1 b s t t (Or.inr rfl) ht⟩
  have hcov : ∀ s t : Fin n, val gs (n + j) (pr s t) = true →
      (val gs a (fun v : Fin n => decide (v = s)) = true ∧
        val gs b (fun v : Fin n => decide (v = t)) = true) ∨
      (val gs a (fun v : Fin n => decide (v = t)) = true ∧
        val gs b (fun v : Fin n => decide (v = s)) = true) := by
    intro s t h
    have hall := (val_and gs (pr s t) j hj hop).1 h
    obtain ⟨u1, hu1, hv1⟩ := la _ (hall a ha).2
    obtain ⟨u2, hu2, hv2⟩ := lb _ (hall b hb).2
    have hadj := hST u1 u2 hv1 hv2
    have e1 : u1 = s ∨ u1 = t := pr_of s t u1 hu1
    have e2 : u2 = s ∨ u2 = t := pr_of s t u2 hu2
    have hne : u1 ≠ u2 := by
      intro e
      rw [e] at hadj
      exact hirr _ hadj
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · right
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · exact absurd (e1.trans e2.symm) hne
  have hne : ∃ sa tb : Fin n, val gs a (fun v : Fin n => decide (v = sa)) = true ∧
      val gs b (fun v : Fin n => decide (v = tb)) = true := by
    rcases hcov s0 t0 h0 with h | h
    · exact ⟨s0, t0, h⟩
    · exact ⟨t0, s0, h⟩
  obtain ⟨sa, tb, hsa, htb⟩ := hne
  by_cases hT : ∀ t : Fin n, val gs b (fun v : Fin n => decide (v = t)) = true → t = tb
  · refine ⟨tb, Finset.univ.filter
      (fun s : Fin n => val gs a (fun v : Fin n => decide (v = s)) = true), a, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [mem_Nb]
      exact hsym _ _ (hST s tb hs.2 htb)
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs a (fun v : Fin n => decide (v ∉ Nb adj tb)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := la _ hv
        have hu2 : u ∉ Nb adj tb := of_decide_eq_true hu
        apply hu2
        rw [mem_Nb]
        exact hsym _ _ (hST u tb huv htb)
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        exact ⟨hT t h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
      · left
        exact ⟨hT s h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
  · push_neg at hT
    obtain ⟨t1, ht1, hne1⟩ := hT
    have hS : ∀ s : Fin n, val gs a (fun v : Fin n => decide (v = s)) = true → s = sa := by
      intro s hs
      by_contra hne2
      exact hne1 (hk s sa t1 tb (hST s t1 hs ht1) (hST s tb hs htb) (hST sa t1 hsa ht1)
        (hST sa tb hsa htb) hne2)
    refine ⟨sa, Finset.univ.filter
      (fun t : Fin n => val gs b (fun v : Fin n => decide (v = t)) = true), b, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_filter] at ht
      rw [mem_Nb]
      exact hST sa t hsa ht.2
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs b (fun v : Fin n => decide (v ∉ Nb adj sa)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := lb _ hv
        have hu2 : u ∉ Nb adj sa := of_decide_eq_true hu
        apply hu2
        rw [mem_Nb]
        exact hST sa u hsa huv
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨hS s h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
      · right
        exact ⟨hS t h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩

open Classical in
theorem core2 (n : ℕ) (adj : Fin n → Fin n → Prop) (hirr : ∀ s, ¬ adj s s)
    (hsym : ∀ s t, adj s t → adj t s)
    (hk : ∀ s1 s2 t1 t2 : Fin n, adj s1 t1 → adj s1 t2 → adj s2 t1 → adj s2 t2 →
      s1 ≠ s2 → t1 = t2)
    (gs : List Gate) (o : ℕ) (H : Hy n adj gs o) :
    ∃ B : Fin n → Finset (Fin n), (∀ s t : Fin n, adj s t → t ∈ B s ∨ s ∈ B t) ∧
      ∑ v : Fin n, (B v).card ≤ gs.length := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact ⟨fun _ => ∅, fun s => s.elim0, by simp⟩
  have hstar : ∀ j : Fin gs.length, ∃ (z : Fin n) (A : Finset (Fin n)) (lw : ℕ),
      ((gs.get j).op = GateOp.and → Good n gs o (n + (j : ℕ)) →
        (∃ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true) →
        A ⊆ Nb adj z ∧ (∀ p ∈ A, val gs lw (fun v : Fin n => decide (v = p)) = true) ∧
        val gs lw (fun v : Fin n => decide (v ∉ Nb adj z)) = false ∧
        ∀ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true →
          (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A)) := by
    intro j
    by_cases h : (gs.get j).op = GateOp.and ∧ Good n gs o (n + (j : ℕ)) ∧
        ∃ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true
    · obtain ⟨h1, h2, s, t, h3⟩ := h
      obtain ⟨z, A, lw, hh⟩ := star n adj hirr hsym hk gs o H j j.2 h1 h2 s t h3
      exact ⟨z, A, lw, fun _ _ _ => hh⟩
    · exact ⟨⟨0, hnpos⟩, ∅, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z A lw hst using hstar
  obtain ⟨US, hUS⟩ : ∃ US : Finset (Fin gs.length), ∀ j, j ∈ US ↔
      ((gs.get j).op = GateOp.and ∧ Good n gs o (n + (j : ℕ)) ∧
        ∃ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true) :=
    ⟨Finset.univ.filter (fun j => (gs.get j).op = GateOp.and ∧ Good n gs o (n + (j : ℕ)) ∧
      ∃ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true),
      fun j => ⟨fun h => (Finset.mem_filter.1 h).2,
        fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩⟩
  have hst2 : ∀ j ∈ US, A j ⊆ Nb adj (z j) ∧
      (∀ p ∈ A j, val gs (lw j) (fun v : Fin n => decide (v = p)) = true) ∧
      val gs (lw j) (fun v : Fin n => decide (v ∉ Nb adj (z j))) = false ∧
      ∀ s t : Fin n, val gs (n + (j : ℕ)) (pr s t) = true →
        (s = z j ∧ t ∈ A j) ∨ (t = z j ∧ s ∈ A j) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (hUS j).1 hj
    exact hst j h1 h2 h3
  obtain ⟨B, hB⟩ : ∃ B : Fin n → Finset (Fin n),
      ∀ v, B v = (US.filter (fun j => z j = v)).biUnion A := ⟨_, fun _ => rfl⟩
  refine ⟨B, ?_, ?_⟩
  · intro s t hadj
    have hout := H.2.2.2.1 s t hadj
    obtain ⟨w, hr, hx, hw⟩ := good_down n gs o H.1 (pr s t) o (fun _ h => h) hout
    rcases hw with hw | ⟨j, hj, e, hop⟩
    · exfalso
      apply good_single n adj hirr gs o H w hr ⟨w, hw⟩
      rw [val_input gs _ w hw]
      simp
    · rw [e] at hr hx
      have hjU : (⟨j, hj⟩ : Fin gs.length) ∈ US := (hUS _).2 ⟨hop, hr, s, t, hx⟩
      rcases (hst2 _ hjU).2.2.2 s t hx with h | h
      · left
        rw [hB s]
        exact Finset.mem_biUnion.2 ⟨⟨j, hj⟩, Finset.mem_filter.2 ⟨hjU, h.1.symm⟩, h.2⟩
      · right
        rw [hB t]
        exact Finset.mem_biUnion.2 ⟨⟨j, hj⟩, Finset.mem_filter.2 ⟨hjU, h.1.symm⟩, h.2⟩
  · have hLN : ∀ i j : Fin n, i ≠ j → (Nb adj i ∩ Nb adj j).card ≤ 1 := by
      intro i j hij
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_inter, mem_Nb, mem_Nb] at ha hb
      exact hk i j a b ha.1 hb.1 ha.2 hb.2 hij
    have hBsub : ∀ v : Fin n, B v ⊆ Nb adj v := by
      intro v y hy
      rw [hB v] at hy
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
      rw [Finset.mem_filter] at hj
      rw [← hj.2]
      exact (hst2 j hj.1).1 hyj
    have hot : ∀ (v p : Fin n), p ∈ B v →
        ∃ i ∈ US, z i = v ∧ val gs (lw i) (fun u : Fin n => decide (u = p)) = true := by
      intro v p hp
      rw [hB v] at hp
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.1 hp
      rw [Finset.mem_filter] at hj
      exact ⟨j, hj.1, hj.2, (hst2 j hj.1).2.1 p hpj⟩
    have hoc : ∀ i ∈ US,
        val gs (lw i) (fun u : Fin n => decide (u ∉ Nb adj (z i))) = false :=
      fun i hi => (hst2 i hi).2.2.1
    have hmc := mrg_count (Nb adj) B gs z US lw hLN H.1 H.2.1 hBsub hot hoc
    have hd : Disjoint US
        (Finset.univ.filter (fun g : Fin gs.length => ∃ v, MJ gs (Nb adj) B v g)) := by
      rw [Finset.disjoint_left]
      intro g h1 h2
      obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 h2
      obtain ⟨a2, _⟩ := hmj
      have a1 := ((hUS g).1 h1).1
      rw [a1] at a2
      exact GateOp.noConfusion a2
    have hcard : (US ∪
        Finset.univ.filter (fun g : Fin gs.length => ∃ v, MJ gs (Nb adj) B v g)).card
          ≤ gs.length := by
      simpa using Finset.card_le_univ (US ∪
        Finset.univ.filter (fun g : Fin gs.length => ∃ v, MJ gs (Nb adj) B v g))
    rw [Finset.card_union_of_disjoint hd] at hcard
    omega

def adj (N : ℕ) (I : Fin N → Fin N → Prop) (s t : Fin (N + N)) : Prop :=
  ∃ p l : Fin N, I p l ∧
    (((s : ℕ) = (p : ℕ) ∧ (t : ℕ) = N + (l : ℕ)) ∨ ((t : ℕ) = (p : ℕ) ∧ (s : ℕ) = N + (l : ℕ)))

theorem adj_irr (N : ℕ) (I : Fin N → Fin N → Prop) (s : Fin (N + N)) : ¬ adj N I s s := by
  rintro ⟨p, l, _, h⟩
  have := p.isLt
  omega

theorem adj_symm (N : ℕ) (I : Fin N → Fin N → Prop) (s t : Fin (N + N))
    (h : adj N I s t) : adj N I t s := by
  obtain ⟨p, l, hI, h | h⟩ := h
  · exact ⟨p, l, hI, Or.inr h⟩
  · exact ⟨p, l, hI, Or.inl h⟩

theorem k22 (N : ℕ) (I : Fin N → Fin N → Prop)
    (hC4 : ∀ p q l m : Fin N, p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m))
    (s1 s2 t1 t2 : Fin (N + N)) (h11 : adj N I s1 t1) (h12 : adj N I s1 t2)
    (h21 : adj N I s2 t1) (h22 : adj N I s2 t2) (hne : s1 ≠ s2) : t1 = t2 := by
  obtain ⟨p11, l11, i11, h11⟩ := h11
  obtain ⟨p12, l12, i12, h12⟩ := h12
  obtain ⟨p21, l21, i21, h21⟩ := h21
  obtain ⟨p22, l22, i22, h22⟩ := h22
  have b11 := p11.isLt
  have b12 := p12.isLt
  have b21 := p21.isLt
  have b22 := p22.isLt
  have hnv : (s1 : ℕ) ≠ (s2 : ℕ) := fun h => hne (Fin.ext h)
  by_contra hne2
  have hnt : (t1 : ℕ) ≠ (t2 : ℕ) := fun h => hne2 (Fin.ext h)
  by_cases hs : (s1 : ℕ) < N
  · have e1 : p12 = p11 := Fin.ext (by omega)
    have e2 : p22 = p21 := Fin.ext (by omega)
    have e3 : l21 = l11 := Fin.ext (by omega)
    have e4 : l22 = l12 := Fin.ext (by omega)
    rw [e1] at i12
    rw [e2, e4] at i22
    rw [e3] at i21
    have hv : (p11 : ℕ) ≠ (p21 : ℕ) := by omega
    have hpp : p11 ≠ p21 := fun e => hv (by rw [e])
    have hw : (l11 : ℕ) ≠ (l12 : ℕ) := by omega
    have hll : l11 ≠ l12 := fun e => hw (by rw [e])
    exact hC4 p11 p21 l11 l12 hpp hll ⟨i11, i12, i21, i22⟩
  · have e1 : l12 = l11 := Fin.ext (by omega)
    have e2 : p21 = p11 := Fin.ext (by omega)
    have e3 : p22 = p12 := Fin.ext (by omega)
    have e4 : l22 = l21 := Fin.ext (by omega)
    rw [e1] at i12
    rw [e2] at i21
    rw [e3, e4] at i22
    have hv : (p11 : ℕ) ≠ (p12 : ℕ) := by omega
    have hpp : p11 ≠ p12 := fun e => hv (by rw [e])
    have hw : (l11 : ℕ) ≠ (l21 : ℕ) := by omega
    have hll : l11 ≠ l21 := fun e => hw (by rw [e])
    exact hC4 p11 p12 l11 l21 hpp hll ⟨i11, i21, i12, i22⟩

theorem cA_inj (N : ℕ) (a b : Fin N) (h : Fin.castAdd N a = Fin.castAdd N b) : a = b := by
  have h2 := congrArg Fin.val h
  rw [Fin.coe_castAdd, Fin.coe_castAdd] at h2
  exact Fin.ext h2

theorem nA_inj (N : ℕ) (a b : Fin N) (h : Fin.natAdd N a = Fin.natAdd N b) : a = b := by
  have h2 := congrArg Fin.val h
  rw [Fin.coe_natAdd, Fin.coe_natAdd] at h2
  exact Fin.ext (by omega)

theorem cA_ne_nA (N : ℕ) (a b : Fin N) (h : Fin.castAdd N a = Fin.natAdd N b) : False := by
  have h2 := congrArg Fin.val h
  rw [Fin.coe_castAdd, Fin.coe_natAdd] at h2
  have := a.isLt
  omega

def enc (N : ℕ) (B : Fin (N + N) → Finset (Fin (N + N))) (e : Fin N × Fin N) :
    Fin (N + N) × Fin (N + N) :=
  if Fin.natAdd N e.2 ∈ B (Fin.castAdd N e.1) then (Fin.castAdd N e.1, Fin.natAdd N e.2)
  else (Fin.natAdd N e.2, Fin.castAdd N e.1)

theorem enc_inj (N : ℕ) (B : Fin (N + N) → Finset (Fin (N + N))) (e f : Fin N × Fin N)
    (hf : enc N B e = enc N B f) : e = f := by
  unfold enc at hf
  by_cases c1 : Fin.natAdd N e.2 ∈ B (Fin.castAdd N e.1) <;>
    by_cases c2 : Fin.natAdd N f.2 ∈ B (Fin.castAdd N f.1)
  · rw [if_pos c1, if_pos c2] at hf
    have h := Prod.mk.inj hf
    exact Prod.ext (cA_inj N _ _ h.1) (nA_inj N _ _ h.2)
  · rw [if_pos c1, if_neg c2] at hf
    exact (cA_ne_nA N _ _ (Prod.mk.inj hf).1).elim
  · rw [if_neg c1, if_pos c2] at hf
    exact (cA_ne_nA N _ _ (Prod.mk.inj hf).1.symm).elim
  · rw [if_neg c1, if_neg c2] at hf
    have h := Prod.mk.inj hf
    exact Prod.ext (cA_inj N _ _ h.2) (nA_inj N _ _ h.1)

theorem legal_of (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def junk2868 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false)

-- Restrict one side to zero and extract singleton witnesses on the retained side.
private def keep2868 {N : ℕ} (p : Bool) (x : Fin (N+N) → Bool) : Fin (N+N) → Bool :=
  fun i => if decide (i.val < N) = p then x i else false

private def pure2868 {N : ℕ} (gs : List Gate) (p : Bool) (w : ℕ) : Prop :=
  ∀ x : Fin (N+N) → Bool, val gs w x = val gs w (keep2868 p x)

private theorem ext2868 (n : ℕ) (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hb : ∀ j (hj : j < gs.length), ∃ a b, gs[j].inputs = [a,b] ∧ a < b ∧ b < n+j)
    (w : ℕ) (hw : w < n+gs.length) (z : Bool) : val gs w (fun _ : Fin n => z) = z := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · exact val_input gs _ w hn
    have hj : w-n < gs.length := by omega
    have e : n+(w-n)=w := by omega
    obtain ⟨a,b,hab,ha,hb'⟩ := hb _ hj
    have va := ih a (by omega) (by omega)
    have vb := ih b (by omega) (by omega)
    have op := (legal _ (List.getElem_mem hj)).1
    rw [← e]
    rcases op with hop|hop
    · have h := val_and gs (fun _ : Fin n => z) _ hj hop
      rw [hab] at h
      cases z <;> simp_all <;> omega
    · have h := val_or gs (fun _ : Fin n => z) _ hj hop
      rw [hab] at h
      cases z <;> simp_all <;> omega

private theorem kill2868 {N : ℕ} (gs : List Gate) (w : ℕ) (p : Bool)
    (pure : pure2868 (N:=N) gs (!p) w)
    (hz : val gs w (fun _ : Fin (N+N) => false) = false) (x : Fin (N+N) → Bool) :
    val gs w (keep2868 p x) = false := by
  rw [pure]
  have h : keep2868 (!p) (keep2868 p x) = fun _ => false := by
    funext i
    cases p <;> by_cases hi : i.val < N <;> simp [keep2868, hi]
  rw [h, hz]

private theorem linProj2868 {N : ℕ} (gs : List Gate) (p : Bool)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hkill : ∀ j (hj : j < gs.length), gs[j].op = GateOp.and →
      ∀ x : Fin (N+N) → Bool, val gs (N+N+j) (keep2868 p x) = false)
    (w : ℕ) (hw : pure2868 (N:=N) gs p w) : Lin (N+N) gs w := by
  have gen : ∀ (v : ℕ) (x : Fin (N+N) → Bool), val gs v (keep2868 p x) = true →
      ∃ u : Fin (N+N), x u = true ∧ val gs v (fun t : Fin (N+N) => decide (t=u)) = true := by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro x hv
      by_cases hi : v < N+N
      · rw [val_input _ _ _ hi] at hv
        refine ⟨⟨v, hi⟩, ?_, ?_⟩
        · unfold keep2868 at hv
          split at hv <;> simp_all
        · rw [val_input _ _ _ hi]; simp
      by_cases big : N+N+gs.length ≤ v
      · rw [val_big _ _ _ big] at hv; contradiction
      have hj : v-(N+N) < gs.length := by omega
      have e : N+N+(v-(N+N))=v := by omega
      rcases (legal _ (List.getElem_mem hj)).1 with hop|hop
      · rw [← e, hkill _ hj hop] at hv; contradiction
      · rw [← e, val_or gs _ _ hj hop] at hv
        obtain ⟨a,ha,hal,ht⟩ := hv
        obtain ⟨u,hu,hv'⟩ := ih a (by omega) x ht
        exact ⟨u,hu,by rw [← e]; exact (val_or gs _ _ hj hop).2 ⟨a,ha,hal,hv'⟩⟩
  intro x hx
  exact gen w x (by rw [← hw]; exact hx)

-- Monotonicity turns equality at the two constant endpoints into independence from that side.
private def fill2868 {N : ℕ} (p z : Bool) (x : Fin (N+N) → Bool) : Fin (N+N) → Bool :=
  fun i => if decide (i.val < N) = p then x i else z

private theorem sandwich2868 {N : ℕ} (C : Circuit) (w : ℕ) (p : Bool)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ends : ∀ x : Fin (N+N) → Bool,
      val C.gates w (fill2868 p false x) = val C.gates w (fill2868 p true x)) :
    pure2868 (N:=N) C.gates p w := by
  intro x
  have a := val_mono C.gates legal (fill2868 p false x) x (by
    intro i hi
    unfold fill2868 at hi
    split at hi <;> simp_all) w
  have b := val_mono C.gates legal x (fill2868 p true x) (by
    intro i hi
    simp [fill2868, hi]) w
  change val C.gates w x = val C.gates w (fill2868 p false x)
  rw [← ends x] at b
  cases hx : val C.gates w x <;> cases hy : val C.gates w (fill2868 p false x) <;> simp_all

private theorem pureLeft2868 {N : ℕ} (C : Circuit) (w : ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h : ∀ x : Fin N → Bool, (C.wires (List.ofFn x ++ List.replicate N false)).getD w false =
      (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) :
    pure2868 (N:=N) C.gates true w := by
  apply sandwich2868 C w true legal
  intro x
  have eqn (z : Bool) : List.ofFn (fill2868 true z x) =
      List.ofFn (fun i => x (Fin.castAdd N i)) ++ List.replicate N z := by
    rw [List.ofFn_add]
    congr 1
    all_goals try rw [← List.ofFn_const]
    all_goals apply congrArg List.ofFn; funext i; simp [fill2868, i.isLt] <;> rfl
  change (C.wires (List.ofFn (fill2868 true false x))).getD w false =
    (C.wires (List.ofFn (fill2868 true true x))).getD w false
  rw [eqn, eqn]
  exact h _

private theorem pureRight2868 {N : ℕ} (C : Circuit) (w : ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h : ∀ x : Fin N → Bool, (C.wires (List.replicate N false ++ List.ofFn x)).getD w false =
      (C.wires (List.replicate N true ++ List.ofFn x)).getD w false) :
    pure2868 (N:=N) C.gates false w := by
  apply sandwich2868 C w false legal
  intro x
  have eqn (z : Bool) : List.ofFn (fill2868 false z x) =
      List.replicate N z ++ List.ofFn (fun i => x (Fin.natAdd N i)) := by
    rw [List.ofFn_add]
    congr 1
    all_goals try rw [← List.ofFn_const]
    all_goals apply congrArg List.ofFn; funext i; simp [fill2868, i.isLt] <;> rfl
  change (C.wires (List.ofFn (fill2868 false false x))).getD w false =
    (C.wires (List.ofFn (fill2868 false true x))).getD w false
  rw [eqn, eqn]
  exact h _

-- Each binary AND gate has a point-pure and a line-pure input. Both inputs have singleton witnesses.
theorem pureLin2868 (N : ℕ) (D : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 D)
    (hb : ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a < b ∧ b < N+N+j)
    (hnb : ∀ j (hj : j < D.gates.length), ¬ junk2868 N D D.gates[j]) :
    ∀ j (hj : j < D.gates.length), D.gates[j].op = GateOp.and →
    ∃ a b : ℕ, D.gates[j].inputs = [a,b] ∧ Lin (N+N) D.gates a ∧ Lin (N+N) D.gates b := by
  classical
  have legal := legal_of D hm
  have bins : ∀ j (hj : j < D.gates.length), ∃ a b : ℕ, D.gates[j].inputs = [a,b] ∧ a < b ∧ b < N+N+j :=
    fun j hj => hb j D.gates[j] (by simp [hj])
  have ex := ext2868 (N+N) D.gates legal bins
  have exclusive (w : ℕ) (hw : w < N+N+D.gates.length) (pa : pure2868 (N:=N) D.gates true w)
      (la : pure2868 (N:=N) D.gates false w) : False := by
    have h := pa (fun _ => true)
    rw [ex w hw true, kill2868 D.gates w true la (ex w hw false)] at h
    contradiction
  have sides : ∀ j (hj : j < D.gates.length), D.gates[j].op = GateOp.and →
      ∃ a b, D.gates[j].inputs = [a,b] ∧ a < b ∧ b < N+N+j ∧
        ((pure2868 (N:=N) D.gates true a ∧ pure2868 (N:=N) D.gates false b) ∨
         (pure2868 (N:=N) D.gates false a ∧ pure2868 (N:=N) D.gates true b)) := by
    intro j hj hop
    obtain ⟨a,b,hg,hab,hb'⟩ := bins j hj
    refine ⟨a,b,hg,hab,hb',?_⟩
    have hn := hnb j hj
    simp only [junk2868, hop, true_and, not_or] at hn
    obtain ⟨nl,nr⟩ := hn
    push Not at nl nr
    obtain ⟨l,hl,el⟩ := nl
    obtain ⟨r,hr,er⟩ := nr
    have pl := pureLeft2868 D l legal el
    have pr' := pureRight2868 D r legal er
    simp [hg] at hl hr
    rcases hl with h|h <;> subst l <;> rcases hr with h|h <;> subst r
    · exact (exclusive a (by omega) pl pr').elim
    · exact Or.inl ⟨pl,pr'⟩
    · exact Or.inr ⟨pr',pl⟩
    · exact (exclusive b (by omega) pl pr').elim
  have killed (p : Bool) (j : ℕ) (hj : j < D.gates.length) (hop : D.gates[j].op = GateOp.and)
      (x : Fin (N+N) → Bool) : val D.gates (N+N+j) (keep2868 p x) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hv
    obtain ⟨a,b,hg,hab,hb',sh⟩ := sides j hj hop
    have h := (val_and D.gates _ _ hj hop).1 hv
    have va := (h a (by simp [hg])).2
    have vb := (h b (by simp [hg])).2
    have ea := ex a (by omega) false
    have eb := ex b (by omega) false
    rcases sh with ⟨pa,lb⟩|⟨la,pb⟩
    · cases p
      · rw [kill2868 D.gates a false pa ea] at va; contradiction
      · rw [kill2868 D.gates b true lb eb] at vb; contradiction
    · cases p
      · rw [kill2868 D.gates b false pb eb] at vb; contradiction
      · rw [kill2868 D.gates a true la ea] at va; contradiction
  intro j hj hop
  obtain ⟨a,b,hab,_,_,s⟩ := sides j hj hop
  refine ⟨a,b,hab,?_⟩
  rcases s with ⟨pa,lb⟩|⟨la,pb⟩
  · exact ⟨linProj2868 D.gates true legal (killed true) a pa,
            linProj2868 D.gates false legal (killed false) b lb⟩
  · exact ⟨linProj2868 D.gates false legal (killed false) a la,
            linProj2868 D.gates true legal (killed true) b pb⟩

-- A two-input assignment uses at most two lines, so the negative tests determine all nonadjacent pairs.
theorem pairCount (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit)
    (hq : 100 < q)
    (hC4 : ∀ p q l m : Fin N, p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m))
    (hmono : PEqualNP.MetaComplexity.Monotone2 D)
    (hb : ∀ (i : ℕ) (g : Gate), D.gates[i]? = some g →
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a < b ∧ b < N+N+i)
    (hpos : ∀ p l : Fin N, I p l →
      PEqualNP.MetaComplexity.circuitFun (N+N) D (pr (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) D x = false)
    (hlin : ∀ j (hj : j < D.gates.length), D.gates[j].op = GateOp.and →
      ∃ a b, D.gates[j].inputs = [a,b] ∧ Lin (N+N) D.gates a ∧ Lin (N+N) D.gates b) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ D.gates.length + 1 := by
  classical
  have H : Hy (N + N) (adj N I) D.gates D.output := by
    refine ⟨legal_of D hmono, ?_, hlin, ?_, ?_⟩
    · intro i v hv
      obtain ⟨a,b,hab,hab',hlt⟩ := hb i (D.gates.get i) (by simp)
      rw [hab] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
    · intro s t hadj
      obtain ⟨p,l,hi, h | h⟩ := hadj
      · have hs : s = Fin.castAdd N p := Fin.ext (by simpa using h.1)
        have ht : t = Fin.natAdd N l := Fin.ext (by simpa only [Fin.val_natAdd] using h.2)
        subst s
        subst t
        exact hpos p l hi
      · have ht : t = Fin.castAdd N p := Fin.ext (by simpa using h.1)
        have hs : s = Fin.natAdd N l := Fin.ext (by simpa only [Fin.val_natAdd] using h.2)
        have he : pr s t = pr t s := by funext v; simp only [pr, or_comm]
        rw [he, ht, hs]
        exact hpos p l hi
    · intro s t hadj
      apply hneg
      · let P : Finset (Fin (N+N)) := {s,t}
        let f : {l : Fin N // pr s t (Fin.natAdd N l) = true} → ↥P :=
          fun l => ⟨Fin.natAdd N l.1, by
            simpa only [P, Finset.mem_insert, Finset.mem_singleton] using (pr_of s t _ l.2)⟩
        have hf : Function.Injective f := by
          intro a b h
          apply Subtype.ext
          exact nA_inj N _ _ (congrArg Subtype.val h)
        have hle := Fintype.card_le_of_injective f hf
        rw [Fintype.card_coe] at hle
        have h2 : P.card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
        omega
      · rintro ⟨p,l,hI,hp,hl⟩
        apply hadj
        have v1 := (pr_of s t _ hp).imp (congrArg Fin.val) (congrArg Fin.val)
        have v2 := (pr_of s t _ hl).imp (congrArg Fin.val) (congrArg Fin.val)
        rw [Fin.coe_castAdd] at v1
        rw [Fin.coe_natAdd] at v2
        have := p.isLt
        exact ⟨p,l,hI,by omega⟩
  obtain ⟨B, hcov, hsum⟩ := core2 (N + N) (adj N I) (adj_irr N I) (adj_symm N I)
    (k22 N I hC4) D.gates D.output H
  have hmem : ∀ e : Fin N × Fin N, I e.1 e.2 → enc N B e ∈
      (Finset.univ : Finset (Fin (N + N))).biUnion (fun v => (B v).image (fun y => (v, y))) := by
    intro e hI
    have hadj : adj N I (Fin.castAdd N e.1) (Fin.natAdd N e.2) :=
      ⟨e.1, e.2, hI, Or.inl ⟨Fin.coe_castAdd N e.1, Fin.coe_natAdd N e.2⟩⟩
    unfold enc
    by_cases hc : Fin.natAdd N e.2 ∈ B (Fin.castAdd N e.1)
    · rw [if_pos hc]
      exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, Finset.mem_image.2 ⟨_, hc, rfl⟩⟩
    · rw [if_neg hc]
      have hc2 := (hcov _ _ hadj).resolve_left hc
      exact Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, Finset.mem_image.2 ⟨_, hc2, rfl⟩⟩
  have hE : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤
      ((Finset.univ : Finset (Fin (N + N))).biUnion
        (fun v => (B v).image (fun y => (v, y)))).card := by
    apply Finset.card_le_card_of_injOn (enc N B)
    · intro e he
      exact hmem e (by simpa using he)
    · intro e _ f _ hf
      exact enc_inj N B e f hf
  have hT : ((Finset.univ : Finset (Fin (N + N))).biUnion
      (fun v => (B v).image (fun y => (v, y)))).card ≤ ∑ v : Fin (N + N), (B v).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun v _ => Finset.card_image_le))
  exact (hE.trans (hT.trans hsum)).trans (Nat.le_succ _)

-- Count incidences by lines, and use uniqueness of joins to exclude four-cycles.
theorem planeFinish2868 (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hq : 100 < q) (hN : N = q^2 + q + 1)
    (deg : ∀ l, Fintype.card {p : Fin N // I p l} = q + 1)
    (he : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ D.size + 1) :
    N * q ≤ 100 * D.size := by
  let f : {e : Fin N × Fin N // I e.1 e.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
    { toFun := fun e => ⟨e.1.2, e.1.1, e.2⟩
      invFun := fun z => ⟨⟨z.2.1, z.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have eqn := Fintype.card_congr f
  rw [Fintype.card_sigma] at eqn
  simp [deg, Fintype.card_subtype] at eqn
  have hb : N * (q + 1) ≤ D.size + 1 := by omega
  rw [Nat.mul_add, Nat.mul_one] at hb
  omega

theorem planeNoSquare2868 (N : ℕ) (I : Fin N → Fin N → Prop)
    (join : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) :
    ∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  intro p p' l l' hpp hll ⟨a,b,c,d⟩
  exact hll ((join p p' hpp).unique ⟨a,c⟩ ⟨b,d⟩)

end PEqualNP.Outside.L_meta_2868

theorem PEqualNP.Outside.L_meta_2868 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, x16.card = (0 : ℕ) → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  intro _ q N I inst D hq hN deg join hm _ hb hp hn T _ hT hbad _
  have hnb : ∀ j (hj : j < D.gates.length),
      ¬ PEqualNP.Outside.L_meta_2868.junk2868 N D D.gates[j] := by
    intro j hj h
    have hmem := (hbad j D.gates[j] (List.getElem?_eq_getElem hj)).2 h
    have hEmpty := Finset.card_eq_zero.mp hT
    simpa [hEmpty] using hmem
  have hlin := PEqualNP.Outside.L_meta_2868.pureLin2868 N D hm hb hnb
  have hC4 := PEqualNP.Outside.L_meta_2868.planeNoSquare2868 N I join
  have he := PEqualNP.Outside.L_meta_2868.pairCount q N I D hq hC4 hm hb hp hn hlin
  exact PEqualNP.Outside.L_meta_2868.planeFinish2868 q N I D hq hN deg he
