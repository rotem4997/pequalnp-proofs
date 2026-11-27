import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_7921

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this

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


lemma gv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) :=
  cval_gate n C (List.ofFn x) (by simp) hRB j hj

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  have h := run_getD C.gates (List.ofFn x) i (by simp; exact hi)
  show (run C.gates (List.ofFn x)).getD i false = _
  rw [h]
  simp [List.getD_eq_getElem?_getD, hi]

lemma or_true (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hv : (C.wires (List.ofFn x)).getD w false = true) : gateVal n C k x = true := by
  rw [gv n C hRB k hk x, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨w, hw, hv⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (m k : ℕ) (hmk : InCone n C m k) :
    ∀ g, InCone n C k g → InCone n C m g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro h
    obtain ⟨hg, k2, hk2, hin, hor⟩ := (inCone_iff n C k g).mp h
    rcases hor with e | hc
    · subst e
      exact (inCone_iff n C m g).mpr ⟨hg, k, hk2, hin, Or.inr hmk⟩
    · exact (inCone_iff n C m g).mpr ⟨hg, k2, hk2, hin, Or.inr (ih k2 hk2 hc)⟩

lemma op_cases (C : Circuit) (hA : AndOrOnly C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  apply hA
  rw [gateAt_eq C k hk]
  exact List.getElem_mem hk

lemma prop (n : ℕ) (C : Circuit) (hA : AndOrOnly C) (hRB : ReadsBack n C) (t t2 : ℕ)
    (hnt : ¬ InCone n C t t2) (x : Fin n → Bool) (ht : gateVal n C t x = true) :
    ∀ g, g < C.gates.length → (gateAt C g).op = GateOp.or → InCone n C t g →
      (∀ m, InCone n C m g → (gateAt C m).op = GateOp.and → m = t ∨ m = t2) →
      gateVal n C g x = true := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg hop hc hands
    obtain ⟨_, k, hk, hin, hor⟩ := (inCone_iff n C t g).mp hc
    rcases hor with e | htk
    · subst e
      exact or_true n C hRB g hg hop x (n + t) hin ht
    · have hkg : InCone n C k g := (inCone_iff n C k g).mpr ⟨hg, k, hk, hin, Or.inl rfl⟩
      have hklen : k < C.gates.length := by omega
      rcases op_cases C hA k hklen with hand | hor2
      · rcases hands k hkg hand with e | e
        · have := (inCone_lt n C t k htk).1
          omega
        · subst e
          exact absurd htk hnt
      · have hv := ih k hk hklen hor2 htk (fun m hm hmand =>
          hands m (inCone_trans n C m k hm g hkg) hmand)
        exact or_true n C hRB g hg hop x (n + k) hin hv

def Cov (n : ℕ) (C : Circuit) (t w : ℕ) : Prop := ∃ k, w = n + k ∧ (t = k ∨ InCone n C t k)

lemma cover (n : ℕ) (C : Circuit) (hA : AndOrOnly C) (hRB : ReadsBack n C) (t t2 g : ℕ)
    (hg : g < C.gates.length)
    (hnt : ¬ InCone n C t t2) (x : Fin n → Bool) (ht : gateVal n C t x = true)
    (hands : ∀ m, InCone n C m g → (gateAt C m).op = GateOp.and → m = t ∨ m = t2)
    (w : ℕ) (hw : w ∈ (gateAt C g).inputs) (hcov : Cov n C t w) :
    (C.wires (List.ofFn x)).getD w false = true := by
  obtain ⟨k, rfl, hor⟩ := hcov
  rcases hor with e | htk
  · subst e
    exact ht
  · have hlt := hRB g hg (n + k) hw
    have hkg : InCone n C k g := (inCone_iff n C k g).mpr ⟨hg, k, by omega, hw, Or.inl rfl⟩
    have hklen : k < C.gates.length := by omega
    rcases op_cases C hA k hklen with hand | hor2
    · rcases hands k hkg hand with e | e
      · have := (inCone_lt n C t k htk).1
        omega
      · subst e
        exact absurd htk hnt
    · exact prop n C hA hRB t t2 hnt x ht k hklen hor2 htk (fun m hm hmand =>
        hands m (inCone_trans n C m k hm g hkg) hmand)

lemma pureOr (n : ℕ) (C : Circuit) (hao : IsAO2 n C) :
    ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      (∀ m, InCone n C m k → (gateAt C m).op ≠ GateOp.and) →
      ∃ i : Fin n, ∀ x : Fin n → Bool, x i = true → gateVal n C k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hop hno
    have hlen : (gateAt C k).inputs.length = 2 := by
      apply hao.2.2
      rw [gateAt_eq C k hk]
      exact List.getElem_mem hk
    obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos (show 0 < (gateAt C k).inputs.length by omega)
    have hlt := hao.2.1 k hk u hu
    by_cases hun : u < n
    · refine ⟨⟨u, hun⟩, fun x hx => ?_⟩
      exact or_true n C hao.2.1 k hk hop x u hu (by rw [wires_input n C x u hun]; exact hx)
    · obtain ⟨k2, rfl⟩ : ∃ k2, u = n + k2 := ⟨u - n, by omega⟩
      have hkk : InCone n C k2 k := (inCone_iff n C k2 k).mpr ⟨hk, k2, by omega, hu, Or.inl rfl⟩
      have hk2len : k2 < C.gates.length := by omega
      have hor2 : (gateAt C k2).op = GateOp.or := by
        rcases op_cases C hao.1 k2 hk2len with h | h
        · exact absurd h (hno k2 hkk)
        · exact h
      obtain ⟨i, hi⟩ := ih k2 (by omega) hk2len hor2
        (fun m hm => hno m (inCone_trans n C m k2 hm k hkk))
      exact ⟨i, fun x hx => or_true n C hao.2.1 k hk hop x (n + k2) hu (hi x hx)⟩

lemma leaf (n : ℕ) (C : Circuit) (hao : IsAO2 n C) (x4 x5 g : ℕ) (hg : g < C.gates.length)
    (hands : ∀ m, InCone n C m g → (gateAt C m).op = GateOp.and → m = x4 ∨ m = x5)
    (b : ℕ) (hb : b ∈ (gateAt C g).inputs) (hnc : ¬ (Cov n C x4 b ∨ Cov n C x5 b)) :
    ∃ i : Fin n, ∀ x : Fin n → Bool, x i = true → (C.wires (List.ofFn x)).getD b false = true := by
  have hlt := hao.2.1 g hg b hb
  by_cases hbn : b < n
  · exact ⟨⟨b, hbn⟩, fun x hx => by rw [wires_input n C x b hbn]; exact hx⟩
  · obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    have hkg : InCone n C k g := (inCone_iff n C k g).mpr ⟨hg, k, by omega, hb, Or.inl rfl⟩
    have hklen : k < C.gates.length := by omega
    rcases op_cases C hao.1 k hklen with hand | hor
    · exfalso
      rcases hands k hkg hand with e | e
      · exact hnc (Or.inl ⟨k, rfl, Or.inl e.symm⟩)
      · exact hnc (Or.inr ⟨k, rfl, Or.inl e.symm⟩)
    · obtain ⟨i, hi⟩ := pureOr n C hao k hklen hor (fun m hm hmand => by
        rcases hands m (inCone_trans n C m k hm g hkg) hmand with e | e
        · subst e; exact hnc (Or.inl ⟨k, rfl, Or.inr hm⟩)
        · subst e; exact hnc (Or.inr ⟨k, rfl, Or.inr hm⟩))
      exact ⟨i, hi⟩

lemma cov_of_inCone (n : ℕ) (C : Circuit) (t g : ℕ) (h : InCone n C t g) (a b : ℕ)
    (hab : (gateAt C g).inputs = [a, b]) : Cov n C t a ∨ Cov n C t b := by
  obtain ⟨_, k, _, hin, hor⟩ := (inCone_iff n C t g).mp h
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with e | e
  · exact Or.inl ⟨k, e.symm, hor⟩
  · exact Or.inr ⟨k, e.symm, hor⟩

lemma main (n : ℕ) (L : List ℕ) (C : Circuit) (x4 x5 x6 : ℕ) (hao : IsAO2 n C)
    (hx6 : x6 < C.gates.length) (hand : (gateAt C x6).op = GateOp.and)
    (hands : ∀ m, InCone n C m x6 → (gateAt C m).op = GateOp.and → m = x4 ∨ m = x5)
    (hn45 : ¬ InCone n C x4 x5) (hn54 : ¬ InCone n C x5 x4)
    (h4 : InCone n C x4 x6) (h5 : InCone n C x5 x6)
    (hL : ∀ s ∈ L, gateVal n C x6 (fun j : Fin n => s.testBit ↑j) = false) :
    (∀ s ∈ L, gateVal n C x4 (fun j : Fin n => s.testBit ↑j) = true →
        gateVal n C x5 (fun j : Fin n => s.testBit ↑j) = false) ∨
      ∃ i : Fin n, ∀ s ∈ L, s.testBit ↑i = true →
        gateVal n C x4 (fun j : Fin n => s.testBit ↑j) = false ∧
          gateVal n C x5 (fun j : Fin n => s.testBit ↑j) = false := by
  have hA := hao.1
  have hRB := hao.2.1
  have hlen : (gateAt C x6).inputs.length = 2 := by
    apply hao.2.2
    rw [gateAt_eq C x6 hx6]
    exact List.getElem_mem hx6
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have hval : ∀ x : Fin n → Bool, gateVal n C x6 x =
      ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) := by
    intro x
    rw [gv n C hRB x6 hx6 x, hand, hab]
    simp [GateOp.eval]
  have ha_in : a ∈ (gateAt C x6).inputs := by rw [hab]; simp
  have hb_in : b ∈ (gateAt C x6).inputs := by rw [hab]; simp
  have hands2 : ∀ m, InCone n C m x6 → (gateAt C m).op = GateOp.and → m = x5 ∨ m = x4 :=
    fun m hm hmand => (hands m hm hmand).symm
  have wv : ∀ (x : Fin n → Bool) (w : ℕ), w ∈ (gateAt C x6).inputs →
      (Cov n C x4 w → gateVal n C x4 x = true → (C.wires (List.ofFn x)).getD w false = true) ∧
      (Cov n C x5 w → gateVal n C x5 x = true → (C.wires (List.ofFn x)).getD w false = true) :=
    fun x w hw => ⟨fun hc ht => cover n C hA hRB x4 x5 x6 hx6 hn45 x ht hands w hw hc,
      fun hc ht => cover n C hA hRB x5 x4 x6 hx6 hn54 x ht hands2 w hw hc⟩
  have c4 := cov_of_inCone n C x4 x6 h4 a b hab
  have c5 := cov_of_inCone n C x5 x6 h5 a b hab
  by_cases ha : Cov n C x4 a ∨ Cov n C x5 a
  · by_cases hb : Cov n C x4 b ∨ Cov n C x5 b
    · left
      intro s hs h4s
      have h0 := hL s hs
      cases h5s : gateVal n C x5 (fun j : Fin n => s.testBit ↑j)
      · rfl
      · exfalso
        have va : (C.wires (List.ofFn (fun j : Fin n => s.testBit ↑j))).getD a false = true := by
          rcases ha with h | h
          · exact (wv _ a ha_in).1 h h4s
          · exact (wv _ a ha_in).2 h h5s
        have vb : (C.wires (List.ofFn (fun j : Fin n => s.testBit ↑j))).getD b false = true := by
          rcases hb with h | h
          · exact (wv _ b hb_in).1 h h4s
          · exact (wv _ b hb_in).2 h h5s
        rw [hval, va, vb] at h0
        exact absurd h0 (by decide)
    · right
      have a4 : Cov n C x4 a := c4.resolve_right (fun h => hb (Or.inl h))
      have a5 : Cov n C x5 a := c5.resolve_right (fun h => hb (Or.inr h))
      obtain ⟨i, hi⟩ := leaf n C hao x4 x5 x6 hx6 hands b hb_in hb
      refine ⟨i, fun s hs hbit => ?_⟩
      have h0 := hL s hs
      have vb := hi (fun j : Fin n => s.testBit ↑j) hbit
      rw [hval, vb, Bool.and_true] at h0
      constructor
      · cases h2 : gateVal n C x4 (fun j : Fin n => s.testBit ↑j)
        · rfl
        · rw [(wv _ a ha_in).1 a4 h2] at h0; exact absurd h0 (by decide)
      · cases h2 : gateVal n C x5 (fun j : Fin n => s.testBit ↑j)
        · rfl
        · rw [(wv _ a ha_in).2 a5 h2] at h0; exact absurd h0 (by decide)
  · right
    have b4 : Cov n C x4 b := c4.resolve_left (fun h => ha (Or.inl h))
    have b5 : Cov n C x5 b := c5.resolve_left (fun h => ha (Or.inr h))
    obtain ⟨i, hi⟩ := leaf n C hao x4 x5 x6 hx6 hands a ha_in ha
    refine ⟨i, fun s hs hbit => ?_⟩
    have h0 := hL s hs
    have va := hi (fun j : Fin n => s.testBit ↑j) hbit
    rw [hval, va, Bool.true_and] at h0
    constructor
    · cases h2 : gateVal n C x4 (fun j : Fin n => s.testBit ↑j)
      · rfl
      · rw [(wv _ b hb_in).1 b4 h2] at h0; exact absurd h0 (by decide)
    · cases h2 : gateVal n C x5 (fun j : Fin n => s.testBit ↑j)
      · rfl
      · rw [(wv _ b hb_in).2 b5 h2] at h0; exact absurd h0 (by decide)

end PEqualNP.Outside.L_meta_7921

theorem PEqualNP.Outside.L_meta_7921 : ∀ (x1 : ℕ) (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x6 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x3 →     x6 < x3.gates.length →       (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →         (∀ (x10 : ℕ), PEqualNP.EdgeOwnership.InCone x1 x3 x10 x6 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 = x4 ∨ x10 = x5) →           ¬PEqualNP.EdgeOwnership.InCone x1 x3 x4 x5 →             ¬PEqualNP.EdgeOwnership.InCone x1 x3 x5 x4 →               PEqualNP.EdgeOwnership.InCone x1 x3 x4 x6 →                 PEqualNP.EdgeOwnership.InCone x1 x3 x5 x6 →                   (∀ x15 ∈ x2, (PEqualNP.EdgeOwnership.gateVal x1 x3 x6 fun (x17 : Fin x1) => x15.testBit ↑x17) = Bool.false) →                     have x16 : ℕ → ℕ → Bool := fun (x16 x17 : ℕ) => PEqualNP.EdgeOwnership.gateVal x1 x3 x16 fun (x18 : Fin x1) => x17.testBit ↑x18;                     (∀ x17 ∈ x2, x16 x4 x17 = Bool.true → x16 x5 x17 = Bool.false) ∨ ∃ (x17 : Fin x1), ∀ x18 ∈ x2, x18.testBit ↑x17 = Bool.true → x16 x4 x18 = Bool.false ∧ x16 x5 x18 = Bool.false := by
  intro n L C x4 x5 x6 hao hx6 hand hands hn45 hn54 h4 h5 hL
  exact PEqualNP.Outside.L_meta_7921.main n L C x4 x5 x6 hao hx6 hand hands hn45 hn54 h4 h5 hL
