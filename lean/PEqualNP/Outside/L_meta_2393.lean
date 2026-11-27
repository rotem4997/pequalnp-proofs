import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2393

section Sec1499

namespace P1499
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
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
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
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
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

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

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv

lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

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

lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

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

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    [DecidablePred (fun k : ℕ => (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)]
    [DecidablePred (fun k : ℕ => (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true)] :
    ((Finset.range C'.gates.length).filter (fun k : ℕ => (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true)).card =
    ((Finset.range C.gates.length).filter (fun k : ℕ => (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)).card := by
  rw [hlen]
  apply card_filter_rho C.gates.length r hr
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma two_elems {l : List ℕ} (hl : l.length ≤ 2) {p a : ℕ} (hp : p ∈ l) (ha : a ∈ l)
    (hne : a ≠ p) : ∀ u ∈ l, u = p ∨ u = a := by
  match l, hl with
  | [], _ => simp at hp
  | [u], _ =>
    simp only [List.mem_singleton] at hp ha
    omega
  | [u, v], _ =>
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ha hw
    omega
  | _ :: _ :: _ :: _, h => simp at h

lemma hxl {n : ℕ} (x : Fin n → Bool) : (List.ofFn x).length = n := List.length_ofFn

lemma h_and_dead {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hp : p ∈ (gateAt C k).inputs)
    (hdead : ∀ x : Fin n → Bool, ¬ (p < n + k ∧ val C (List.ofFn x) p = true)) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false := by
  intro x
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact hdead x ((val_and (hxl x) hk hop).mp hc p hp)

lemma h_or_live {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hp : p ∈ (gateAt C k).inputs)
    (hlive : ∀ x : Fin n → Bool, p < n + k ∧ val C (List.ofFn x) p = true) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true := by
  intro x
  exact (val_or (hxl x) hk hop).mpr ⟨p, hp, hlive x⟩

lemma h_or_dead {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hlen : (gateAt C k).inputs.length ≤ 2)
    (hop : (gateAt C k).op = GateOp.or) (hp : p ∈ (gateAt C k).inputs)
    (hdead : ∀ x : Fin n → Bool, ¬ (p < n + k ∧ val C (List.ofFn x) p = true)) :
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false) ∨
      ∃ b, b < n + k ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = val C (List.ofFn x) b := by
  by_cases hb : ∃ b ∈ (gateAt C k).inputs, b ≠ p ∧ b < n + k
  · obtain ⟨b, hbm, hbp, hbk⟩ := hb
    right
    refine ⟨b, hbk, fun x => ?_⟩
    have h2 := two_elems hlen hp hbm hbp
    rw [Bool.eq_iff_iff, val_or (hxl x) hk hop]
    constructor
    · rintro ⟨u, hu, hlt, hv⟩
      rcases h2 u hu with h3 | h3
      · rw [h3] at hlt hv
        exact absurd ⟨hlt, hv⟩ (hdead x)
      · rw [h3] at hv
        exact hv
    · intro hv; exact ⟨b, hbm, hbk, hv⟩
  · left
    intro x
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨u, hu, hlt, hv⟩ := (val_or (hxl x) hk hop).mp hc
    by_cases hup : u = p
    · rw [hup] at hlt hv
      exact hdead x ⟨hlt, hv⟩
    · exact hb ⟨u, hu, hup, hlt⟩

lemma h_and_live {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hlen : (gateAt C k).inputs.length ≤ 2)
    (hop : (gateAt C k).op = GateOp.and) (hp : p ∈ (gateAt C k).inputs)
    (hlive : ∀ x : Fin n → Bool, p < n + k ∧ val C (List.ofFn x) p = true) :
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true) ∨
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false) ∨
      ∃ b, b < n + k ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = val C (List.ofFn x) b := by
  by_cases hb : ∃ b ∈ (gateAt C k).inputs, b ≠ p
  · obtain ⟨b, hbm, hbp⟩ := hb
    have h2 := two_elems hlen hp hbm hbp
    right
    by_cases hbk : b < n + k
    · right
      refine ⟨b, hbk, fun x => ?_⟩
      rw [Bool.eq_iff_iff, val_and (hxl x) hk hop]
      constructor
      · intro h; exact (h b hbm).2
      · intro hv u hu
        rcases h2 u hu with h3 | h3
        · rw [h3]; exact hlive x
        · rw [h3]; exact ⟨hbk, hv⟩
    · left
      intro x
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact hbk ((val_and (hxl x) hk hop).mp hc b hbm).1
  · left
    intro x
    rw [val_and (hxl x) hk hop]
    intro u hu
    by_cases hup : u = p
    · rw [hup]; exact hlive x
    · exact absurd ⟨u, hu, hup⟩ hb

lemma normal (n : ℕ) (C : Circuit) (hn : 0 < n) (F : (Fin n → Bool) → Bool)
    (Good : Circuit → Prop)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hlen2 : ∀ k < C.gates.length, (gateAt C k).inputs.length ≤ 2)
    (hbyp : ∀ r i, r < C.gates.length → i < n + r → Good (bypass n C r i))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hF0 : ∃ x, F x = false) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D, Good D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.gates.length ≤ D.gates.length) :
    ∀ k < C.gates.length, (∃ a b, (gateAt C k).inputs = [a, b]) ∧
      ∀ u ∈ (gateAt C k).inputs, u < n + k := by
  have nodup : ∀ r i, r < C.gates.length → i < n + r →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i := by
    intro r i hr hi h
    have := hmin _ (hbyp r i hr hi)
      (fun x => bypass_eval_eq (hxl x) hAO hr (Or.inl hi) (h x))
    rw [bypass_length] at this; omega
  have unread : ∀ r, r < C.gates.length → C.output ≠ n + r →
      ¬ ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs := by
    intro r hr hout hno
    have := hmin _ (hbyp r 0 hr (by omega))
      (fun x => bypass_eval_unread (hxl x) hAO hr (Or.inl (by omega)) hout hno)
    rw [bypass_length] at this; omega
  have nofalse : ∀ m r, C.gates.length - r = m → r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = false := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r hm hr hP
      obtain ⟨x1, hx1⟩ := hF1
      have hout : C.output ≠ n + r := by
        intro h
        have h1 := hF x1
        rw [eval_eq_val, h, hP x1, hx1] at h1
        exact absurd h1 (by simp)
      apply unread r hr hout
      intro k hrk hk hmem
      have hdead : ∀ x : Fin n → Bool,
          ¬ (n + r < n + k ∧ val C (List.ofFn x) (n + r) = true) := by
        intro x h; rw [hP x] at h; exact absurd h.2 (by simp)
      rcases hAO k hk with hop | hop
      · exact ih (C.gates.length - k) (by omega) k rfl hk (h_and_dead hk hop hmem hdead)
      · rcases h_or_dead hk (hlen2 k hk) hop hmem hdead with h | ⟨b, hb, h⟩
        · exact ih (C.gates.length - k) (by omega) k rfl hk h
        · exact nodup k b hk hb h
  have nofalse' : ∀ r, r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = false :=
    fun r hr => nofalse _ r rfl hr
  have notrue : ∀ m r, C.gates.length - r = m → r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r hm hr hP
      obtain ⟨x0, hx0⟩ := hF0
      have hout : C.output ≠ n + r := by
        intro h
        have h1 := hF x0
        rw [eval_eq_val, h, hP x0, hx0] at h1
        exact absurd h1 (by simp)
      apply unread r hr hout
      intro k hrk hk hmem
      have hlive : ∀ x : Fin n → Bool,
          n + r < n + k ∧ val C (List.ofFn x) (n + r) = true :=
        fun x => ⟨by omega, hP x⟩
      rcases hAO k hk with hop | hop
      · rcases h_and_live hk (hlen2 k hk) hop hmem hlive with h | h | ⟨b, hb, h⟩
        · exact ih (C.gates.length - k) (by omega) k rfl hk h
        · exact nofalse' k hk h
        · exact nodup k b hk hb h
      · exact ih (C.gates.length - k) (by omega) k rfl hk (h_or_live hk hop hmem hlive)
  have notrue' : ∀ r, r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true :=
    fun r hr => notrue _ r rfl hr
  intro k hk
  have hback : ∀ u ∈ (gateAt C k).inputs, u < n + k := by
    intro u hu
    by_contra hlt
    have hdead : ∀ x : Fin n → Bool, ¬ (u < n + k ∧ val C (List.ofFn x) u = true) :=
      fun x h => hlt h.1
    rcases hAO k hk with hop | hop
    · exact nofalse' k hk (h_and_dead hk hop hu hdead)
    · rcases h_or_dead hk (hlen2 k hk) hop hu hdead with h | ⟨b, hb, h⟩
      · exact nofalse' k hk h
      · exact nodup k b hk hb h
  refine ⟨?_, hback⟩
  have h2 := hlen2 k hk
  rcases hl : (gateAt C k).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    rcases hAO k hk with hop | hop
    · apply notrue' k hk
      intro x
      rw [val_and (hxl x) hk hop, hl]
      intro u hu
      simp at hu
    · apply nofalse' k hk
      intro x
      by_contra hc
      rw [Bool.not_eq_false, val_or (hxl x) hk hop, hl] at hc
      obtain ⟨u, hu, _⟩ := hc
      simp at hu
  · exfalso
    have ha : a < n + k := hback a (by rw [hl]; simp)
    apply nodup k a hk ha
    intro x
    rw [Bool.eq_iff_iff]
    rcases hAO k hk with hop | hop
    · rw [val_and (hxl x) hk hop, hl]
      simp [ha]
    · rw [val_or (hxl x) hk hop, hl]
      simp [ha]
  · exact ⟨a, b, rfl⟩
  · rw [hl] at h2
    exact absurd h2 (by simp only [List.length_cons]; omega)

lemma wv_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    wv n C x w = val C (List.ofFn x) w := rfl

lemma eval_wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wv n C x C.output := rfl

lemma gateVal_wv (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wv n C x (n + j) := rfl

lemma mem_gates_iff (C : Circuit) (g : Gate) :
    g ∈ C.gates ↔ ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    exact ⟨j, hj, gateAt_eq hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact gateAt_mem hj

lemma AO2_mem {n : ℕ} {C : Circuit} (h : AO2 n C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := (mem_gates_iff C g).mp hg
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h j hj
  exact ⟨h1, by rw [h2]; rfl⟩

lemma AO2_readsBack {n : ℕ} {C : Circuit} (h : AO2 n C) : ReadsBack n C :=
  fun j hj => (h j hj).2.2

lemma to_AO2 (n : ℕ) (C : Circuit) (hn : 0 < n) (F : (Fin n → Bool) → Bool)
    (Good : Circuit → Prop)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hlen2 : ∀ k < C.gates.length, (gateAt C k).inputs.length ≤ 2)
    (hbyp : ∀ r i, r < C.gates.length → i < n + r → Good (bypass n C r i))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hF0 : ∃ x, F x = false) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D, Good D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.gates.length ≤ D.gates.length) : AO2 n C :=
  fun k hk => ⟨hAO k hk, normal n C hn F Good hAO hlen2 hbyp hF hF0 hF1 hmin k hk⟩

lemma graphFun_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphFun G ∅ (fun _ => false) = false := by
  simp [graphFun]

lemma graphFun_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : graphFun G ∅ (fun _ => true) = true := by
  obtain ⟨e, he⟩ := h
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [graphFun_iff]
    exact ⟨u, v, he, rfl, rfl⟩

lemma pos_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : 0 < n := by
  obtain ⟨e, _⟩ := h
  induction e using Sym2.ind with
  | _ u v => exact Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt

lemma main_abs (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hF : ∀ x, wv n C x C.output = F x) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = F x) →
      C.gates.length ≤ D.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hL : Least n C := ⟨hC, fun D hD hfun => hmin D hD (fun x => (hfun x).trans (hF x))⟩
  obtain ⟨x1, hx1⟩ := hF1
  have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF, hx1])
  exact step3_struct n C F hL hF hout i j hbel hcone

lemma junk_eq2 (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  classical
  have e : S = (Finset.range C.gates.length).filter (fun k : ℕ =>
      (gateAt C k).op = GateOp.and ∧ ¬ ∀ x, wv n C x (n + k) = true → F x = true) := by
    ext k; rw [hS, Finset.mem_filter, Finset.mem_range]
  have e' : S' = (Finset.range C'.gates.length).filter (fun k : ℕ =>
      (gateAt C' k).op = GateOp.and ∧ ¬ ∀ x, wv n C' x (n + k) = true → F x = true) := by
    ext k; rw [hS', Finset.mem_filter, Finset.mem_range]
  rw [e, e']
  exact junk_eq n C C' F r hr hlen hops htop hopr hbelow

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

lemma junk_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma to_real {n : ℕ} {D : Circuit} (hD : AO2 n D) : PEqualNP.TopForm.IsAO2 n D :=
  ⟨fun g hg => (AO2_mem hD g hg).1, AO2_readsBack hD, fun g hg => (AO2_mem hD g hg).2⟩

lemma of_real {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  exact ⟨h1 _ (gateAt_mem hk), List.length_eq_two.mp (h3 _ (gateAt_mem hk)), h2 k hk⟩

end P1499

end Sec1499

section Sec1491

namespace P1491
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

end S90

namespace S98

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega

lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp

lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega

lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp

lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)

lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem

lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp

theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

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

lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩

lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩

lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab

lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩

lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩

lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩

lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl

theorem main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]

end S98

theorem cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

theorem cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

theorem cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

theorem top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

theorem star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

theorem assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩

lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩

end P1491

theorem s1491 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact PEqualNP.Outside.L_meta_2393.P1491.main n G C h4 hne hL hTF

end Sec1491

section Sec2239

namespace Own
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

theorem ofFn_getD {α : Type} {n : ℕ} (x : Fin n → α) (dflt : α) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i dflt = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

theorem F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

theorem F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def blk (c h : ℕ) (t : List ℕ) (w : ℕ) : List Gate :=
  chain h w t ++ [⟨GateOp.and, [cfin h w t, c]⟩]

theorem blk_len (c h : ℕ) (t : List ℕ) (w : ℕ) : (blk c h t w).length = t.length + 1 := by
  simp [blk, chain_len]

theorem blk_shape (c h : ℕ) (t : List ℕ) (w : ℕ) :
    ∀ g ∈ blk c h t w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

theorem blk_val (c h : ℕ) (t : List ℕ) (w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w) (h3 : c < w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false =
      ((d.getD h false || t.any fun i => d.getD i false) && d.getD c false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

theorem blk_iff (n c h : ℕ) (t : List ℕ) (w : ℕ) (d x : List Bool)
    (hw : d.length = w) (hpre : ∀ i < n, d.getD i false = x.getD i false)
    (h1 : h < n) (h2 : ∀ i ∈ t, i < n) (hl : c < n) (hNw : n ≤ w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false = true ↔
      (x.getD c false = true ∧ ∃ i ∈ h :: t, x.getD i false = true) := by
  rw [blk_val c h t w d hw (by omega) (fun i hi => by have := h2 i hi; omega) (by omega),
    Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, hpre h (by omega),
    hpre c (by omega)]
  constructor
  · rintro ⟨hh | ⟨i, hi, hh⟩, hy⟩
    · exact ⟨hy, h, by simp, hh⟩
    · exact ⟨hy, i, by simp [hi], by rw [← hpre i (h2 i hi)]; exact hh⟩
  · rintro ⟨hy, i, hi, hh⟩
    refine ⟨?_, hy⟩
    rcases List.mem_cons.mp hi with e | hi2
    · rw [e] at hh; exact Or.inl hh
    · exact Or.inr ⟨i, hi2, by rw [hpre i (h2 i hi2)]; exact hh⟩

def G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : List (ℕ × ℕ × List ℕ) → List Gate
  | [] => blk s0.1 s0.2.1 s0.2.2 n
  | s :: r => G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length) ++
      [⟨GateOp.or, [n + (G n s0 r).length - 1, n + (G n s0 r).length + s.2.2.length]⟩]

theorem G_pos (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r, 0 < (G n s0 r).length
  | [] => by simp [G, blk_len]
  | s :: r => by simp [G]

theorem G_len (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    (G n s0 r).length + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum
  | [] => by simp [G, blk_len]
  | s :: r => by
    have ih := G_len n s0 r
    simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    omega

theorem G_shape (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    ∀ g ∈ G n s0 r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [] => by
    intro g hg
    simp only [G] at hg
    exact blk_shape _ _ _ _ g hg
  | s :: r => by
    intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact G_shape n s0 r g hg
    · exact blk_shape _ _ _ _ g hg
    · exact ⟨Or.inr rfl, rfl⟩

theorem G_val (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List Bool) (hx : x.length = n)
    (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ((F wstep (G n s0 r) x).getD (n + (G n s0 r).length - 1) false = true ↔
        ∃ s ∈ s0 :: r, x.getD s.1 false = true ∧ ∃ i ∈ s.2.1 :: s.2.2, x.getD i false = true)
  | [], _ => by
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    rw [blk_iff n s0.1 s0.2.1 s0.2.2 n x x hx (fun i _ => rfl) (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 (le_refl _)]
    constructor
    · intro a
      exact ⟨s0, by simp, a⟩
    · rintro ⟨s, hs, a⟩
      rw [List.mem_singleton.mp hs] at a
      exact a
  | s :: r, hr => by
    have ih := G_val n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F wstep (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F wstep (G n s0 r) x).getD i false = x.getD i false :=
      fun i hi => F_pre wstep false _ _ i (by omega)
    have hb := blk_iff n s.1 s.2.1 s.2.2 (n + (G n s0 r).length)
      (F wstep (G n s0 r) x) x hL hpre (hs.2 _ (by simp)) (fun i hi => hs.2 i (by simp [hi]))
      hs.1 (by omega)
    have hL2 : (F wstep (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, wstep_or, Bool.or_eq_true]
    rw [F_append, F_pre wstep false _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega), ih, hb]
    constructor
    · rintro (⟨s', hs', a⟩ | a)
      · refine ⟨s', ?_, a⟩
        simp only [List.mem_cons] at hs' ⊢
        tauto
      · exact ⟨s, by simp, a⟩
    · rintro ⟨s', hs', a⟩
      simp only [List.mem_cons] at hs'
      rcases hs' with h | h | h
      · exact Or.inl ⟨s', by simp [h], a⟩
      · rw [h] at a
        exact Or.inr a
      · exact Or.inl ⟨s', by simp [h], a⟩

def RB (w : ℕ) (b : List Gate) : Prop :=
  ∀ j < b.length, ∀ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, i < w + j

theorem RB_app (w : ℕ) (a b : List Gate) (ha : RB w a) (hb : RB (w + a.length) b) :
    RB w (a ++ b) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [List.getD_append _ _ _ _ h] at hi
    exact ha j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    have hj2 : j - a.length < b.length := by
      rw [List.length_append] at hj; omega
    have := hb (j - a.length) hj2 i hi
    omega

theorem RB_two (w : ℕ) (op : GateOp) (a b : ℕ) (ha : a < w) (hb : b < w) :
    RB w [⟨op, [a, b]⟩] := by
  intro j hj i hi
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hi' : i ∈ [a, b] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with hi' | hi' <;> omega

theorem cfin_lt : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → cfin acc w ins < w + ins.length
  | [], acc, w, h => by simpa [cfin] using h
  | i :: is, acc, w, h => by
    have := cfin_lt is w (w + 1) (by omega)
    simp only [cfin, List.length_cons]
    omega

theorem RB_chain : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → (∀ i ∈ ins, i < w) →
    RB w (chain acc w ins)
  | [], _, _, _, _ => by
    intro j hj
    simp [chain] at hj
  | i :: is, acc, w, hacc, hins => by
    have e : chain acc w (i :: is) = [⟨GateOp.or, [acc, i]⟩] ++ chain w (w + 1) is := rfl
    rw [e]
    apply RB_app
    · exact RB_two w GateOp.or acc i hacc (hins i (by simp))
    · exact RB_chain is w (w + 1) (by omega)
        (fun k hk => by have := hins k (by simp [hk]); omega)

theorem RB_blk (c h : ℕ) (t : List ℕ) (w : ℕ) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) : RB w (blk c h t w) := by
  unfold blk
  apply RB_app _ _ _ (RB_chain t h w h1 h2)
  rw [chain_len]
  exact RB_two _ GateOp.and _ _ (cfin_lt t h w h1) (by omega)

theorem RB_G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      RB n (G n s0 r)
  | [], _ => by
    simp only [G]
    exact RB_blk _ _ _ _ (h0.2 _ (by simp)) (fun i hi => h0.2 i (by simp [hi])) h0.1
  | s :: r, hr => by
    have ih := RB_G n s0 h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hpos := G_pos n s0 r
    simp only [G]
    apply RB_app
    · apply RB_app _ _ _ ih
      exact RB_blk _ _ _ _ (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
    · rw [List.length_append, blk_len]
      exact RB_two _ GateOp.or _ _ (by omega) (by omega)

def rstep (S : List ℕ) (k : ℕ) (g : Gate) (R : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or =>
    (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = F (rstep S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · rw [h1]; exact h
  · simp

theorem mem_foldl_insertNew (x : List ℕ) : ∀ (B A : List (List ℕ)),
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B
  | [], A => by simp
  | b :: B, A => by
    rw [List.foldl_cons, mem_foldl_insertNew x B, mem_insertNew, List.mem_cons]
    tauto

def orv (A B : List (List ℕ)) : List (List ℕ) := B.foldl insertNew (A.foldl insertNew [])

theorem mem_orv (x : List ℕ) (A B : List (List ℕ)) : x ∈ orv A B ↔ x ∈ A ∨ x ∈ B := by
  unfold orv
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

theorem rstep_or (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.or, [a, b]⟩ R = orv (R.getD a []) (R.getD b []) := rfl

theorem mem_andStep (k : ℕ) (x : List ℕ) (A B : List (List ℕ)) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd k u v = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap]

theorem rstep_and (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.and, [a, b]⟩ R =
      andStep k (andStep k [S.map fun _ => 0] (R.getD a [])) (R.getD b []) := rfl

theorem foldl_orv (x : List ℕ) (g : ℕ → List (List ℕ)) : ∀ (l : List ℕ) (a : List (List ℕ)),
    (x ∈ a ∨ ∃ i ∈ l, x ∈ g i) → x ∈ l.foldl (fun v i => orv v (g i)) a
  | [], a, h => by
    rcases h with h | ⟨i, hi, _⟩
    · exact h
    · simp at hi
  | i :: is, a, h => by
    rw [List.foldl_cons]
    apply foldl_orv x g is
    rcases h with h | ⟨j, hj, hx⟩
    · exact Or.inl ((mem_orv _ _ _).mpr (Or.inl h))
    · rcases List.mem_cons.mp hj with e | hj2
      · rw [e] at hx
        exact Or.inl ((mem_orv _ _ _).mpr (Or.inr hx))
      · exact Or.inr ⟨j, hj2, hx⟩

theorem blk_rv (S : List ℕ) (k : ℕ) (c h : ℕ) (t : List ℕ) (w : ℕ)
    (d : List (List (List ℕ))) (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) (i : ℕ) (hi : i ∈ h :: t) (u y : List ℕ) (hu : u ∈ d.getD i [])
    (hy : y ∈ d.getD c []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
      (F (rstep S k) (blk c h t w) d).getD (w + t.length) [] := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec (rstep S k) [] orv (rstep_or S k) t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, rstep_and, c3, c2 _ h3, mem_andStep]
  refine ⟨_, ?_, y, hy, rfl⟩
  rw [mem_andStep]
  refine ⟨_, by simp, u, ?_, rfl⟩
  apply foldl_orv u (fun i => d.getD i [])
  rcases List.mem_cons.mp hi with e | hi2
  · rw [e] at hu
    exact Or.inl hu
  · exact Or.inr ⟨i, hi2, hu⟩

theorem G_rv (S : List ℕ) (k : ℕ) (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List (List (List ℕ)))
    (hx : x.length = n) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ∀ s ∈ s0 :: r, ∀ i ∈ s.2.1 :: s.2.2, ∀ u ∈ x.getD i [], ∀ y ∈ x.getD s.1 [],
        capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
          (F (rstep S k) (G n s0 r) x).getD (n + (G n s0 r).length - 1) []
  | [], _ => by
    intro s hs i hi u hu y hy
    have hs2 := List.mem_singleton.mp hs
    rw [hs2] at hi hy
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    exact blk_rv S k s0.1 s0.2.1 s0.2.2 n x hx (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 i hi u y hu hy
  | s :: r, hr => by
    intro s' hs' i hi u hu y hy
    have ih := G_rv S k n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F (rstep S k) (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F (rstep S k) (G n s0 r) x).getD i [] = x.getD i [] :=
      fun i hi => F_pre (rstep S k) [] _ _ i (by omega)
    have hL2 : (F (rstep S k) (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, rstep_or, mem_orv]
    rw [F_append, F_pre (rstep S k) [] _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega)]
    simp only [List.mem_cons] at hs'
    rcases hs' with h | h | h
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)
    · rw [h] at hi hy
      refine Or.inr (blk_rv S k s.1 s.2.1 s.2.2 (n + (G n s0 r).length) _ hL
        (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
        i hi u y ?_ ?_)
      · rw [hpre i (hs.2 i hi)]
        exact hu
      · rw [hpre _ hs.1]
        exact hy
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)

theorem capAdd_map (k : ℕ) (f g : ℕ → ℕ) : ∀ S : List ℕ,
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1)
  | [] => rfl
  | a :: S => by
    have ih := capAdd_map k f g S
    unfold capAdd at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem read_ok (S : List ℕ) (k a b : ℕ) (hk : 1 ≤ k) (hab : a ≠ b) :
    ((capAdd k (capAdd k (S.map fun _ => 0)
        (S.map fun j => if j = a then min 1 (k + 1) else 0))
      (S.map fun j => if j = b then min 1 (k + 1) else 0)).all
        fun x => decide (x ≤ k)) = true := by
  rw [capAdd_map, capAdd_map, List.all_eq_true]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  rw [decide_eq_true_eq]
  split_ifs with h1 h2 <;> omega

theorem leaf_getD (S : List ℕ) (k n i : ℕ) (hi : i < n) (hS : i ∈ S) :
    (S.map fun j => if j = i then min 1 (k + 1) else 0) ∈
      ((List.range n).map (leafVectors S k)).getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [leafVectors, hS]

def pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : List ℕ :=
  ((List.finRange N).filter fun p => decide (I p l)).map Fin.val

def star {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : ℕ × ℕ × List ℕ :=
  (N + l.val, (pts I l).headD 0, (pts I l).tail)

theorem mem_pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) (i : ℕ) :
    i ∈ pts I l ↔ ∃ p : Fin N, I p l ∧ p.val = i := by
  simp [pts]

theorem pts_len {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    (pts I l).length = (Finset.univ.filter (fun p => I p l)).card := by
  have e : (Finset.univ.filter (fun p => I p l)) =
      ((List.finRange N).filter fun p => decide (I p l)).toFinset := by
    ext p
    simp
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
  simp [pts]

theorem hd_tl {α : Type} (d : α) : ∀ l : List α, l ≠ [] → l.headD d :: l.tail = l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z2 : Fin (N + N) → Bool, circuitFun (N + N) D z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true)) ∧
      IsReadK (N + N) D 1 ∧ D.size + 1 = N * (q + 2) := by
  have hall0 : (List.finRange N).map (star I) ≠ [] := by
    intro h
    have h2 := congrArg List.length h
    simp at h2
    omega
  have hall := hd_tl (0, 0, []) _ hall0
  generalize ((List.finRange N).map (star I)).headD (0, 0, []) = s0 at hall
  generalize ((List.finRange N).map (star I)).tail = r at hall
  have hmem : ∀ s ∈ s0 :: r, ∃ l : Fin N, s = star I l := by
    intro s hs
    rw [hall] at hs
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hs
    exact ⟨l, hl.symm⟩
  have hlen : ∀ l : Fin N, (pts I l).length = q + 1 := fun l => by rw [pts_len, hc]
  have hcons : ∀ l : Fin N, (star I l).2.1 :: (star I l).2.2 = pts I l := by
    intro l
    apply hd_tl
    intro h
    have := hlen l
    rw [h] at this
    simp at this
  have hbd : ∀ s ∈ s0 :: r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N := by
    intro s hs
    obtain ⟨l, rfl⟩ := hmem s hs
    refine ⟨?_, ?_⟩
    · show N + l.val < N + N
      have := l.isLt
      omega
    · intro i hi
      rw [hcons l] at hi
      obtain ⟨p, _, rfl⟩ := (mem_pts I l i).mp hi
      have := p.isLt
      omega
  have hb0 := hbd s0 (by simp)
  have hbr : ∀ s ∈ r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N :=
    fun s hs => hbd s (by simp [hs])
  have hzl : ∀ (z : Fin (N + N) → Bool) (l : Fin N),
      (List.ofFn z).getD (N + l.val) false = z (Fin.natAdd N l) :=
    fun z l => ofFn_getD z false (N + l.val) (by have := l.isLt; omega)
  have hzp : ∀ (z : Fin (N + N) → Bool) (p : Fin N),
      (List.ofFn z).getD p.val false = z (Fin.castAdd N p) :=
    fun z p => ofFn_getD z false p.val (by have := p.isLt; omega)
  have hval : ∀ z2 : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true) := by
    intro z
    have hv := G_val (N + N) s0 (List.ofFn z) (by simp) hb0 r hbr
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    refine Iff.trans hv ?_
    constructor
    · rintro ⟨s, hs, h1, i, hi, h2⟩
      obtain ⟨l, rfl⟩ := hmem s hs
      rw [hcons l] at hi
      obtain ⟨p, hp, rfl⟩ := (mem_pts I l i).mp hi
      refine ⟨p, l, hp, ?_, ?_⟩
      · rw [← hzp z p]
        exact h2
      · rw [← hzl z l]
        exact h1
    · rintro ⟨p, l, hp, h1, h2⟩
      refine ⟨star I l, ?_, ?_, p.val, ?_, ?_⟩
      · rw [hall]
        exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩
      · show (List.ofFn z).getD (N + l.val) false = true
        rw [hzl z l]
        exact h2
      · rw [hcons l]
        exact (mem_pts I l _).mpr ⟨p, hp, rfl⟩
      · rw [hzp z p]
        exact h1
  refine ⟨⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩, ?_, hval, ?_, ?_⟩
  · refine And.intro ?_ (And.intro ?_ ?_)
    · intro g hg
      exact (G_shape _ _ _ g hg).1
    · exact RB_G (N + N) s0 hb0 r hbr
    · intro g hg
      exact (G_shape _ _ _ g hg).2
  · intro S hS
    have ht := hS.1
    rw [hval, decide_eq_true_iff] at ht
    obtain ⟨p, l, hpl, h1, h2⟩ := ht
    have h1' : Fin.castAdd N p ∈ S := of_decide_eq_true h1
    have h2' : Fin.natAdd N l ∈ S := of_decide_eq_true h2
    have hpL : p.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.castAdd N p,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h1'⟩, rfl⟩
    have hlL : N + l.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.natAdd N l,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h2'⟩, rfl⟩
    have hpn : p.val < N + N := by have := p.isLt; omega
    have hln : N + l.val < N + N := by have := l.isLt; omega
    have hmemv := G_rv (setList S) 1 (N + N) s0
      ((List.range (N + N)).map (leafVectors (setList S) 1)) (by simp) hb0 r hbr
      (star I l) (by rw [hall]; exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)
      p.val (by rw [hcons l]; exact (mem_pts I l _).mpr ⟨p, hpl, rfl⟩)
      _ (leaf_getD (setList S) 1 (N + N) p.val hpn hpL)
      _ (leaf_getD (setList S) 1 (N + N) (N + l.val) hln hlL)
    show ((readVectors ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ (N + N)
      (setList S) 1).getD (N + N + (G (N + N) s0 r).length - 1) []).any
        (fun v => v.all fun a => decide (a ≤ 1)) = true
    rw [rv_eq, List.any_eq_true]
    exact ⟨_, hmemv, read_ok (setList S) 1 p.val (N + l.val) (le_refl 1)
      (by have := p.isLt; omega)⟩
  · show (G (N + N) s0 r).length + 1 = N * (q + 2)
    rw [G_len]
    have hq2 : ∀ s ∈ s0 :: r, s.2.2.length + 2 = q + 2 := by
      intro s hs
      obtain ⟨l, rfl⟩ := hmem s hs
      have := hlen l
      show (pts I l).tail.length + 2 = q + 2
      rw [List.length_tail]
      omega
    have e : (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum =
        ((s0 :: r).map fun s => s.2.2.length + 2).sum := by
      simp only [List.map_cons, List.sum_cons]
    have e2 : ((s0 :: r).map fun s => s.2.2.length + 2) = List.replicate N (q + 2) := by
      apply List.eq_replicate_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [List.length_map, hall]
        simp
      · intro b hb
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        exact hq2 s hs
    rw [e, e2, List.sum_replicate, smul_eq_mul]

theorem lines_through {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p0 : Fin N) : (Finset.univ.filter (fun l => I p0 l)).card = q + 1 := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
      ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card = 1 := by
    intro p hp
    have hne : p0 ≠ p := (Finset.ne_of_mem_erase hp).symm
    obtain ⟨l, hl, hu⟩ := huniq p0 p hne
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      exact hu x hx
    · intro hx
      rw [hx]
      exact hl
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card = q := by
    intro l hl
    have hl' := (Finset.mem_filter.mp hl).2
    have e : ((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)
        = (Finset.univ.filter (fun p => I p l)).erase p0 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    have hmem : p0 ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
    rw [e, Finset.card_erase_of_mem hmem, hline l]
    rfl
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).erase p0,
        ((Finset.univ.filter (fun l => I p0 l)).filter (fun l => I p l)).card
      = ∑ l ∈ Finset.univ.filter (fun l => I p0 l),
        (((Finset.univ : Finset (Fin N)).erase p0).filter (fun p => I p l)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h3
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p0),
    Finset.card_univ, Fintype.card_fin] at h3
  have e : N - 1 = (q + 1) * q := by
    have : (q + 1) * q = q ^ 2 + q := by ring
    omega
  rw [e] at h3
  exact (Nat.eq_of_mul_eq_mul_right hq h3).symm

theorem cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
  have := p.isLt
  omega

theorem cast_inj {N : ℕ} {p p' : Fin N} (h : Fin.castAdd N p = Fin.castAdd N p') : p = p' := by
  have h2 := congrArg Fin.val h
  simp only [Fin.val_castAdd] at h2
  exact Fin.ext h2

theorem nat_inj {N : ℕ} {l l' : Fin N} (h : Fin.natAdd N l = Fin.natAdd N l') : l = l' := by
  have h2 := congrArg Fin.val h
  simp only [Fin.val_natAdd] at h2
  exact Fin.ext (by omega)

theorem fin_split {N : ℕ} (u : Fin (N + N)) :
    (∃ p : Fin N, u = Fin.castAdd N p) ∨ (∃ l : Fin N, u = Fin.natAdd N l) := by
  rcases Nat.lt_or_ge u.val N with h | h
  · exact Or.inl ⟨⟨u.val, h⟩, Fin.ext rfl⟩
  · have := u.isLt
    exact Or.inr ⟨⟨u.val - N, by omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩

def PG {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧
    ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))
  symm := ⟨by
    rintro u v ⟨p, l, h, h2⟩
    exact ⟨p, l, h, h2.symm.imp And.symm And.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact cast_ne_nat p l (h1.symm.trans h2)
    · exact cast_ne_nat p l (h2.symm.trans h1)⟩

theorem adj_cast {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (v : Fin (N + N)) :
    (PG I).Adj (Fin.castAdd N p) v ↔ ∃ l : Fin N, I p l ∧ v = Fin.natAdd N l := by
  constructor
  · rintro ⟨p', l, h, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
    · have := cast_inj h1
      subst this
      exact ⟨l, h, h2⟩
    · exact absurd h1 (cast_ne_nat p l)
  · rintro ⟨l, h, rfl⟩
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

theorem adj_nat {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (v : Fin (N + N)) :
    (PG I).Adj (Fin.natAdd N l) v ↔ ∃ p : Fin N, I p l ∧ v = Fin.castAdd N p := by
  constructor
  · rintro ⟨p, l', h, ⟨h1, _⟩ | ⟨h1, h2⟩⟩
    · exact absurd h1.symm (cast_ne_nat p l)
    · have := nat_inj h1
      subst this
      exact ⟨p, h, h2⟩
  · rintro ⟨p, h, rfl⟩
    exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩

theorem pg_nfc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel (PG I).Adj]
    (hU : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) :
    PEqualNP.TopForm.NoFourCycle (PG I) := by
  intro a b hab
  rw [Finset.card_le_one]
  intro w1 h1 w2 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  rcases fin_split a with ⟨pa, rfl⟩ | ⟨la, rfl⟩
  · obtain ⟨l1, i1, rfl⟩ := (adj_cast I pa w1).mp h1.1
    obtain ⟨l2, i2, rfl⟩ := (adj_cast I pa w2).mp h2.1
    obtain ⟨pb, j1, rfl⟩ := (adj_nat I l1 b).mp h1.2.symm
    obtain ⟨l3, j2, e⟩ := (adj_cast I pb _).mp h2.2
    have := nat_inj e
    subst this
    have hne : pa ≠ pb := fun h => hab (by rw [h])
    rw [(hU pa pb hne).unique ⟨i1, j1⟩ ⟨i2, j2⟩]
  · obtain ⟨p1, i1, rfl⟩ := (adj_nat I la w1).mp h1.1
    obtain ⟨p2, i2, rfl⟩ := (adj_nat I la w2).mp h2.1
    obtain ⟨lb, j1, rfl⟩ := (adj_cast I p1 b).mp h1.2.symm
    obtain ⟨p3, j2, e⟩ := (adj_nat I lb _).mp h2.2
    have := cast_inj e
    subst this
    by_contra hne
    have hp : p1 ≠ p2 := fun h => hne (by rw [h])
    exact hab (by rw [(hU p1 p2 hp).unique ⟨i1, i2⟩ ⟨j1, j2⟩])

def Inc {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    Finset (Fin N × Fin N) := (A ×ˢ B).filter (fun pl => I pl.1 pl.2)

theorem Inc_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ l ∈ B, (A.filter (fun p => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem Inc_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    (Inc I A B).card = ∑ p ∈ A, (B.filter (fun l => I p l)).card := by
  unfold Inc
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem pg_edges {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    [DecidableRel (PG I).Adj]
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    N * (q + 1) ≤ (PG I).edgeFinset.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  rw [← h0]
  refine Finset.card_le_card_of_injOn
    (fun pl => s(Fin.castAdd N pl.1, Fin.natAdd N pl.2)) ?_ ?_
  · intro pl hpl
    have hpl' : pl ∈ Inc I Finset.univ Finset.univ := hpl
    have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hpl').2
    have hadj : (PG I).Adj (Fin.castAdd N pl.1) (Fin.natAdd N pl.2) :=
      (adj_cast I pl.1 _).mpr ⟨pl.2, hI, rfl⟩
    exact SimpleGraph.mem_edgeFinset.mpr hadj
  · intro a _ b _ hab
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have hab' : s(Fin.castAdd N a1, Fin.natAdd N a2) = s(Fin.castAdd N b1, Fin.natAdd N b2) :=
      hab
    rcases Sym2.eq_iff.mp hab' with ⟨e1, e2⟩ | ⟨e1, _⟩
    · rw [cast_inj e1, nat_inj e2]
    · exact absurd e1 (cast_ne_nat a1 b2)

theorem cover_ge {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hd : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (T : Finset (Fin (N + N)))
    (hT : ∀ p l : Fin N, I p l → Fin.castAdd N p ∈ T ∨ Fin.natAdd N l ∈ T) :
    N ≤ T.card := by
  have h0 : (Inc I Finset.univ Finset.univ).card = N * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  have h1 : (Inc I (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T))
      Finset.univ).card =
      (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)).card * (q + 1) := by
    rw [Inc_left, Finset.sum_congr rfl (fun p _ => hd p)]
    simp
  have h2 : (Inc I Finset.univ
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T))).card =
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)).card * (q + 1) := by
    rw [Inc_right, Finset.sum_congr rfl (fun l _ => hc l)]
    simp
  have hsub : Inc I Finset.univ Finset.univ ⊆
      Inc I (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)) Finset.univ ∪
        Inc I Finset.univ (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)) := by
    intro pl hpl
    have hI : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
    rw [Finset.mem_union]
    rcases hT pl.1 pl.2 hI with h | h
    · left
      unfold Inc
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
      exact ⟨h, hI⟩
    · right
      unfold Inc
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨h, hI⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [h0, h1, h2] at hle
  have e1 : T.card = ∑ i : Fin (N + N), (if i ∈ T then 1 else 0) := by
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp
  have hTT : (Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)).card +
      (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)).card = T.card := by
    rw [e1, Fin.sum_univ_add, Finset.card_filter, Finset.card_filter]
  rw [← hTT]
  rw [← Nat.add_mul] at hle
  exact Nat.le_of_mul_le_mul_right hle (Nat.succ_pos q)

end Own

end Sec2239

section SecNew

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open P1499

def sg {n : ℕ} (u : Fin n) : Fin n → Bool := fun w => decide (w = u)

lemma wv_and {n : ℕ} {C : Circuit} (hC : AO2 n C) (x : Fin n → Bool) {k a b : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    (hab : (gateAt C k).inputs = [a, b]) :
    wv n C x (n + k) = (wv n C x a && wv n C x b) := by
  rw [wv_rec n C x (aob hC) k hk, hop, hab, eval_and_pair]

lemma wv_or {n : ℕ} {C : Circuit} (hC : AO2 n C) (x : Fin n → Bool) {k a b : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hab : (gateAt C k).inputs = [a, b]) :
    wv n C x (n + k) = (wv n C x a || wv n C x b) := by
  rw [wv_rec n C x (aob hC) k hk, hop, hab, eval_or_pair]

lemma mono {n : ℕ} {C : Circuit} (hC : AO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, w < n + C.gates.length → wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at h
      rw [wv_input n C y w hwn]
      exact hxy _ h
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, ⟨a, b, hab⟩, hlt⟩ := hC k hk
      have ha : a < n + k := hlt a (by rw [hab]; simp)
      have hb : b < n + k := hlt b (by rw [hab]; simp)
      rcases hop with hop | hop
      · rw [wv_and hC x hk hop hab, Bool.and_eq_true] at h
        rw [wv_and hC y hk hop hab, Bool.and_eq_true]
        exact ⟨ih a ha (by omega) h.1, ih b hb (by omega) h.2⟩
      · rw [wv_or hC x hk hop hab, Bool.or_eq_true] at h
        rw [wv_or hC y hk hop hab, Bool.or_eq_true]
        exact h.imp (ih a ha (by omega)) (ih b hb (by omega))

def Lin (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wv n C x w = true → ∃ u : Fin n, x u = true ∧ wv n C (sg u) w = true

lemma inp_cone (n : ℕ) (C : Circuit) (k a : ℕ) (hk : k < C.gates.length)
    (ha : a ∈ (gateAt C k).inputs) (hlt : a < n + k) :
    a < n ∨ ∃ k', a = n + k' ∧ InCone n C k' k := by
  by_cases h : a < n
  · exact Or.inl h
  · refine Or.inr ⟨a - n, by omega, ?_⟩
    rw [inCone_iff]
    refine ⟨hk, a - n, by omega, ?_, Or.inl rfl⟩
    have : n + (a - n) = a := by omega
    rw [this]; exact ha

lemma lin_cone {n : ℕ} {C : Circuit} (hC : AO2 n C) (j : ℕ)
    (hflat : ∀ a, (gateAt C a).op = GateOp.and → ¬ InCone n C a j) :
    ∀ w, (w < n ∨ ∃ k, w = n + k ∧ InCone n C k j) →
      Lin n C w ∧ ∃ u : Fin n, wv n C (sg u) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · have hs : wv n C (sg (⟨w, hwn⟩ : Fin n)) w = true := by
        rw [wv_input n C _ w hwn]; simp [sg]
      refine ⟨fun x h => ⟨⟨w, hwn⟩, ?_, hs⟩, ⟨⟨w, hwn⟩, hs⟩⟩
      rw [wv_input n C x w hwn] at h
      exact h
    · rcases hw with hw | ⟨k, rfl, hkj⟩
      · exact absurd hw hwn
      · have hk : k < C.gates.length := by
          have := inCone_lt n C k j hkj
          omega
        obtain ⟨hop, ⟨a, b, hab⟩, hlt⟩ := hC k hk
        have hop' : (gateAt C k).op = GateOp.or := by
          rcases hop with hop | hop
          · exact absurd hkj (hflat k hop)
          · exact hop
        have hain : a ∈ (gateAt C k).inputs := by rw [hab]; simp
        have hbin : b ∈ (gateAt C k).inputs := by rw [hab]; simp
        have ha : a < n + k := hlt a hain
        have hb : b < n + k := hlt b hbin
        have hca : a < n ∨ ∃ k', a = n + k' ∧ InCone n C k' j := by
          rcases inp_cone n C k a hk hain ha with h | ⟨k', h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨k', h1, inCone_trans n C k' k h2 j hkj⟩
        have hcb : b < n ∨ ∃ k', b = n + k' ∧ InCone n C k' j := by
          rcases inp_cone n C k b hk hbin hb with h | ⟨k', h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨k', h1, inCone_trans n C k' k h2 j hkj⟩
        obtain ⟨hla, ua, hua⟩ := ih a ha hca
        obtain ⟨hlb, _, _⟩ := ih b hb hcb
        refine ⟨fun x h => ?_, ⟨ua, ?_⟩⟩
        · rw [wv_or hC x hk hop' hab, Bool.or_eq_true] at h
          rcases h with h | h
          · obtain ⟨u, hu, hu2⟩ := hla x h
            exact ⟨u, hu, by rw [wv_or hC _ hk hop' hab, hu2]; rfl⟩
          · obtain ⟨u, hu, hu2⟩ := hlb x h
            exact ⟨u, hu, by rw [wv_or hC _ hk hop' hab, hu2]; simp⟩
        · rw [wv_or hC _ hk hop' hab, hua]; rfl

lemma gf_sg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (sg u) = true → False := by
  intro h
  rw [graphFun_iff] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [sg, decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma gf_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma nfc_use {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) {a b w w' : Fin n} (hab : a ≠ b)
    (h1 : G.Adj a w) (h2 : G.Adj b w) (h3 : G.Adj a w') (h4' : G.Adj b w') : w = w' := by
  have h := h4 a b hab
  rw [Finset.card_le_one] at h
  exact h w (by simp [h1, h2]) w' (by simp [h3, h4'])

lemma and_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {D : Circuit}
    (hD : AO2 n D) (T : ℕ) (hT : T < D.gates.length) (hop : (gateAt D T).op = GateOp.and)
    (hs : ∀ x, wv n D x (n + T) = true → graphFun G ∅ x = true)
    (hflat : ∀ a, (gateAt D a).op = GateOp.and → ¬ InCone n D a T) :
    ∃ A B, (gateAt D T).inputs = [A, B] ∧ Lin n D A ∧ Lin n D B ∧
      (∀ x, wv n D x (n + T) = (wv n D x A && wv n D x B)) ∧
      (∀ u v, wv n D (sg u) A = true → wv n D (sg v) B = true → G.Adj u v) := by
  obtain ⟨_, ⟨A, B, hab⟩, hlt⟩ := hD T hT
  have hain : A ∈ (gateAt D T).inputs := by rw [hab]; simp
  have hbin : B ∈ (gateAt D T).inputs := by rw [hab]; simp
  have ha : A < n + T := hlt A hain
  have hb : B < n + T := hlt B hbin
  have hla := (lin_cone hD T hflat A (inp_cone n D T A hT hain ha)).1
  have hlb := (lin_cone hD T hflat B (inp_cone n D T B hT hbin hb)).1
  refine ⟨A, B, hab, hla, hlb, fun x => wv_and hD x hT hop hab, fun u v hu hv => ?_⟩
  rw [← gf_pair]
  apply hs
  rw [wv_and hD _ hT hop hab, Bool.and_eq_true]
  constructor
  · exact mono hD (sg u) _ (fun w hw => by simp only [sg, decide_eq_true_eq] at hw; simp [pairInput, hw]) A (by omega) hu
  · exact mono hD (sg v) _ (fun w hw => by simp only [sg, decide_eq_true_eq] at hw; simp [pairInput, hw]) B (by omega) hv

lemma ctr_side {α : Type} (SA SB : α → Prop) (u0 : α)
    (hstar : (∀ u u', SA u → SA u' → u = u') ∨ (∀ v v', SB v → SB v' → v = v'))
    (hdis : SA u0 → SB u0 → False) :
    ∃ z, ((∀ u, SA u → u = z) ∨ (∀ v, SB v → v = z)) ∧
      (SA u0 → (∀ v, SB v → v = z) ∨ z = u0) ∧
      (SB u0 → (∀ u, SA u → u = z) ∨ z = u0) := by
  by_cases hA : SA u0
  · have hB : ¬ SB u0 := fun h => hdis hA h
    by_cases hsb : ∀ v v', SB v → SB v' → v = v'
    · by_cases he : ∃ v, SB v
      · obtain ⟨v1, hv1⟩ := he
        exact ⟨v1, Or.inr (fun v hv => hsb v v1 hv hv1),
          fun _ => Or.inl (fun v hv => hsb v v1 hv hv1), fun h => absurd h hB⟩
      · exact ⟨u0, Or.inr (fun v hv => absurd ⟨v, hv⟩ he), fun _ => Or.inr rfl,
          fun h => absurd h hB⟩
    · have hsa := hstar.resolve_right hsb
      exact ⟨u0, Or.inl (fun u hu => hsa u u0 hu hA), fun _ => Or.inr rfl, fun h => absurd h hB⟩
  · by_cases hB : SB u0
    · by_cases hsa : ∀ u u', SA u → SA u' → u = u'
      · by_cases he : ∃ u, SA u
        · obtain ⟨u1, hu1⟩ := he
          exact ⟨u1, Or.inl (fun u hu => hsa u u1 hu hu1), fun h => absurd h hA,
            fun _ => Or.inl (fun u hu => hsa u u1 hu hu1)⟩
        · exact ⟨u0, Or.inl (fun u hu => absurd ⟨u, hu⟩ he), fun h => absurd h hA,
            fun _ => Or.inr rfl⟩
      · have hsb := hstar.resolve_left hsa
        exact ⟨u0, Or.inr (fun v hv => hsb v u0 hv hB), fun h => absurd h hA, fun _ => Or.inr rfl⟩
    · rcases hstar with hsa | hsb
      · by_cases he : ∃ u, SA u
        · obtain ⟨u1, hu1⟩ := he
          exact ⟨u1, Or.inl (fun u hu => hsa u u1 hu hu1), fun h => absurd h hA,
            fun h => absurd h hB⟩
        · exact ⟨u0, Or.inl (fun u hu => absurd ⟨u, hu⟩ he), fun h => absurd h hA,
            fun h => absurd h hB⟩
      · by_cases he : ∃ v, SB v
        · obtain ⟨v1, hv1⟩ := he
          exact ⟨v1, Or.inr (fun v hv => hsb v v1 hv hv1), fun h => absurd h hA,
            fun h => absurd h hB⟩
        · exact ⟨u0, Or.inr (fun v hv => absurd ⟨v, hv⟩ he), fun h => absurd h hA,
            fun h => absurd h hB⟩

def Ctr (n : ℕ) (D : Circuit) (u0 : Fin n) (T : ℕ) (z : Fin n) : Prop :=
  ∃ A B, (gateAt D T).inputs = [A, B] ∧
    ((∀ u, wv n D (sg u) A = true → u = z) ∨ (∀ v, wv n D (sg v) B = true → v = z)) ∧
    (wv n D (sg u0) A = true → (∀ v, wv n D (sg v) B = true → v = z) ∨ z = u0) ∧
    (wv n D (sg u0) B = true → (∀ u, wv n D (sg u) A = true → u = z) ∨ z = u0)

lemma ctr_exists {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) {D : Circuit}
    (hD : AO2 n D) (u0 : Fin n) (T : ℕ) (hT : T < D.gates.length)
    (hop : (gateAt D T).op = GateOp.and)
    (hs : ∀ x, wv n D x (n + T) = true → graphFun G ∅ x = true)
    (hflat : ∀ a, (gateAt D a).op = GateOp.and → ¬ InCone n D a T) :
    ∃ z, Ctr n D u0 T z := by
  obtain ⟨A, B, hab, _, _, _, hcross⟩ := and_facts G hD T hT hop hs hflat
  have hstar : (∀ u u', wv n D (sg u) A = true → wv n D (sg u') A = true → u = u') ∨
      (∀ v v', wv n D (sg v) B = true → wv n D (sg v') B = true → v = v') := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [not_forall] at h1 h2
    obtain ⟨u, u', hu, hu', huu⟩ := h1
    obtain ⟨v, v', hv, hv', hvv⟩ := h2
    exact hvv (nfc_use G h4 huu (hcross u v hu hv) (hcross u' v hu' hv) (hcross u v' hu hv')
      (hcross u' v' hu' hv'))
  obtain ⟨z, hz1, hz2, hz3⟩ := ctr_side (fun u => wv n D (sg u) A = true)
    (fun v => wv n D (sg v) B = true) u0 hstar
    (fun h1 h2 => G.loopless.irrefl _ (hcross u0 u0 h1 h2))
  exact ⟨z, A, B, hab, hz1, hz2, hz3⟩

lemma descent {n : ℕ} {D : Circuit} (hD : AO2 n D) (x : Fin n → Bool) (i m : ℕ)
    (hm : m ≤ D.gates.length) :
    ∀ w, w < n + m → wv n D x w = true →
      (∃ T, T < m ∧ T ≠ i ∧ (gateAt D T).op = GateOp.and ∧ wv n D x (n + T) = true) ∨
      (∃ u, x u = true ∧ ∀ y : Fin n → Bool, y u = true → wv n D y w = true) ∨
      (∀ y : Fin n → Bool, wv n D y (n + i) = true → wv n D y w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hwn : w < n
    · right; left
      refine ⟨⟨w, hwn⟩, ?_, fun y hy => ?_⟩
      · rw [wv_input n D x w hwn] at h
        exact h
      · rw [wv_input n D y w hwn]
        exact hy
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < D.gates.length := by omega
      obtain ⟨hop, ⟨a, b, hab⟩, hlt⟩ := hD k hk
      have ha : a < n + k := hlt a (by rw [hab]; simp)
      have hb : b < n + k := hlt b (by rw [hab]; simp)
      rcases hop with hop | hop
      · by_cases hki : k = i
        · right; right
          subst hki
          exact fun y hy => hy
        · left
          exact ⟨k, by omega, hki, hop, h⟩
      · rw [wv_or hD x hk hop hab, Bool.or_eq_true] at h
        rcases h with h | h
        · rcases ih a ha (by omega) h with h1 | ⟨u, hu, h2⟩ | h3
          · exact Or.inl h1
          · exact Or.inr (Or.inl ⟨u, hu, fun y hy => by rw [wv_or hD y hk hop hab, h2 y hy]; rfl⟩)
          · exact Or.inr (Or.inr (fun y hy => by rw [wv_or hD y hk hop hab, h3 y hy]; rfl))
        · rcases ih b hb (by omega) h with h1 | ⟨u, hu, h2⟩ | h3
          · exact Or.inl h1
          · exact Or.inr (Or.inl ⟨u, hu, fun y hy => by rw [wv_or hD y hk hop hab, h2 y hy]; simp⟩)
          · exact Or.inr (Or.inr (fun y hy => by rw [wv_or hD y hk hop hab, h3 y hy]; simp))

end SecNew

section SecKey

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open P1499

lemma rho_gt (r k : ℕ) (hk : r < k) : rho r (k - 1) = k := by
  unfold rho; split_ifs <;> omega

lemma tau_gt (n r b k : ℕ) (hk : r < k) : tau n r b (n + k) = n + (k - 1) := by
  unfold tau; split_ifs <;> omega

lemma tau_r (n r b : ℕ) : tau n r b (n + r) = b := by
  unfold tau; split_ifs <;> first | rfl | omega

lemma V2_gate_gt (n : ℕ) (C : Circuit) (r c i k : ℕ) (hk : r < k) (hkl : k < C.gates.length) :
    gateAt (V2 n C r c i) (k - 1) = ⟨(gateAt C k).op, (gateAt C k).inputs.map (tau n r c)⟩ := by
  rw [V2_gate n C r c i (k - 1) (by omega), rho_gt r k hk]

lemma st (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hc : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + C.gates.length → wv n C x w = true →
      wv n (V2 n C r c i) x (tau n r c w) = true ∨
      (∀ y : Fin n → Bool, wv n (V2 n C r c i) y c = true →
        wv n (V2 n C r c i) y (tau n r c w) = true) ∨
      (∃ T X Y, T < C.gates.length - 1 ∧ r ≤ T ∧
        (gateAt (V2 n C r c i) T).op = GateOp.and ∧
        ((gateAt (V2 n C r c i) T).inputs = [X, Y] ∨ (gateAt (V2 n C r c i) T).inputs = [Y, X]) ∧
        (∀ y : Fin n → Bool, wv n (V2 n C r c i) y c = true → wv n (V2 n C r c i) y X = true) ∧
        wv n (V2 n C r c i) x Y = true) := by
  have hD := V2_AO2 n C r c i hC hr hc hi hout
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hwr : w < n + r
    · left
      rw [tau_low n r c w hwr, V2_low n C r c i x hC hr hc hi hout w hwr]
      exact h
    · by_cases hwe : w = n + r
      · right; left
        subst hwe
        rw [tau_r]
        exact fun y hy => hy
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hrk : r < k := by omega
        have hk : k < C.gates.length := by omega
        obtain ⟨hop, ⟨a, b, hab⟩, hlt⟩ := hC k hk
        have ha : a < n + k := hlt a (by rw [hab]; simp)
        have hb : b < n + k := hlt b (by rw [hab]; simp)
        have hg := V2_gate_gt n C r c i k hrk hk
        have hkD : k - 1 < (V2 n C r c i).gates.length := by rw [V2_len]; omega
        have hinD : (gateAt (V2 n C r c i) (k - 1)).inputs = [tau n r c a, tau n r c b] := by
          rw [hg, hab]; rfl
        have hopD : (gateAt (V2 n C r c i) (k - 1)).op = (gateAt C k).op := by rw [hg]
        rw [tau_gt n r c k hrk]
        rcases hop with hop | hop
        · rw [wv_and hC x hk hop hab, Bool.and_eq_true] at h
          have hopD' : (gateAt (V2 n C r c i) (k - 1)).op = GateOp.and := by rw [hopD, hop]
          rcases ih a ha (by omega) h.1 with h1 | h2 | h3
          · rcases ih b hb (by omega) h.2 with g1 | g2 | g3
            · left; rw [wv_and hD x hkD hopD' hinD, h1, g1]; rfl
            · right; right
              exact ⟨k - 1, tau n r c b, tau n r c a, by omega, by omega, hopD', Or.inr hinD, g2, h1⟩
            · exact Or.inr (Or.inr g3)
          · rcases ih b hb (by omega) h.2 with g1 | g2 | g3
            · right; right
              exact ⟨k - 1, tau n r c a, tau n r c b, by omega, by omega, hopD', Or.inl hinD, h2, g1⟩
            · right; left
              intro y hy
              rw [wv_and hD y hkD hopD' hinD, h2 y hy, g2 y hy]; rfl
            · exact Or.inr (Or.inr g3)
          · exact Or.inr (Or.inr h3)
        · rw [wv_or hC x hk hop hab, Bool.or_eq_true] at h
          have hopD' : (gateAt (V2 n C r c i) (k - 1)).op = GateOp.or := by rw [hopD, hop]
          rcases h with h | h
          · rcases ih a ha (by omega) h with h1 | h2 | h3
            · left; rw [wv_or hD x hkD hopD' hinD, h1]; rfl
            · right; left
              intro y hy
              rw [wv_or hD y hkD hopD' hinD, h2 y hy]; rfl
            · exact Or.inr (Or.inr h3)
          · rcases ih b hb (by omega) h with h1 | h2 | h3
            · left; rw [wv_or hD x hkD hopD' hinD, h1]; simp
            · right; left
              intro y hy
              rw [wv_or hD y hkD hopD' hinD, h2 y hy]; simp
            · exact Or.inr (Or.inr h3)

lemma cone_CD (n : ℕ) (C : Circuit) (r c i c0 : ℕ)
    (hc : c < n + r) (hc0 : c = n + c0) :
    ∀ j, InCone n C r j → InCone n (V2 n C r c i) c0 (j - 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have hlt := inCone_lt n C r j h
    rw [inCone_iff] at h
    obtain ⟨hj, k, hkj, hin, h3⟩ := h
    have hg := V2_gate_gt n C r c i j hlt.1 hj
    rw [inCone_iff]
    refine ⟨by rw [V2_len]; omega, ?_⟩
    rcases h3 with h3 | h3
    · refine ⟨c0, by omega, ?_, Or.inl rfl⟩
      rw [hg]
      show n + c0 ∈ List.map (tau n r c) (gateAt C j).inputs
      rw [List.mem_map]
      refine ⟨n + k, hin, ?_⟩
      rw [← h3, tau_r]; exact hc0
    · have hrk := (inCone_lt n C r k h3).1
      refine ⟨k - 1, by omega, ?_, Or.inr (ih k hkj h3)⟩
      rw [hg]
      show n + (k - 1) ∈ List.map (tau n r c) (gateAt C j).inputs
      rw [List.mem_map]
      exact ⟨n + k, hin, tau_gt n r c k hrk⟩

lemma exch (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧
      (gateAt C r).op = GateOp.or ∧ c ∈ (gateAt C r).inputs ∧
      InCone n C r j ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, hr, hir, hrin, hrj⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel' hrin
  refine ⟨r, c, hr, hir, hclt, hc, hop, ?_, ?_, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · rcases hrj with h | h
    · rw [h, hj] at hop
      cases hop
    · exact h
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel' hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel' hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma memP {n : ℕ} (p q z : Fin n) (hz : pairInput p q z = true) : z = p ∨ z = q := by
  simpa [pairInput] using hz

lemma key {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (r c i j : ℕ)
    (hC : AO2 n C) (hr : r < C.gates.length) (hir : i < r) (hc : c < n + r)
    (hout : C.output < n + C.gates.length)
    (hFC : ∀ x, wv n C x C.output = graphFun G ∅ x)
    (hFD : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = graphFun G ∅ x)
    (hrj : InCone n C r j) (hjop : (gateAt C j).op = GateOp.and)
    (hmin : ∀ E : Circuit, AO2 n E → (∀ x, wv n E x E.output = graphFun G ∅ x) →
      C.gates.length ≤ E.gates.length)
    (hsD : ∀ k, k < C.gates.length - 1 → (gateAt (V2 n C r c i) k).op = GateOp.and →
      ∀ x, wv n (V2 n C r c i) x (n + k) = true → graphFun G ∅ x = true)
    (hflat : ∀ a b, b < C.gates.length - 1 → (gateAt (V2 n C r c i) a).op = GateOp.and →
      (gateAt (V2 n C r c i) b).op = GateOp.and → ¬ InCone n (V2 n C r c i) a b)
    (hiD : (gateAt (V2 n C r c i) i).op = GateOp.and)
    (S : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length - 1 ∧ (gateAt (V2 n C r c i) k).op = GateOp.and) :
    ∃ K : Finset (Fin n), K.card < S.card ∧
      ((∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∨
        ∃ u0 w0, u0 ∈ K ∧ G.Adj u0 w0 ∧ ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K ∨ u = w0 ∨ v = w0) := by
  have hpos : 0 < C.gates.length := by omega
  have hD := V2_AO2 n C r c i hC hr hc hir hout
  have hlen := V2_len n C r c i
  have hgtop := V2_top n C r c i hpos
  have hoD : (V2 n C r c i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hst := fun x => st n C r c i x hC hr hc hir hout
  have hcone := fun c0 (h : c = n + c0) => cone_CD n C r c i c0 hc h j hrj
  have hjlt := inCone_lt n C r j hrj
  have hgj := V2_gate_gt n C r c i j hjlt.1 hjlt.2
  have hto : tau n r c C.output < n + (C.gates.length - 1) := by
    apply tau_lt n r c C.output (C.gates.length - 1) hc
    have : rho r (C.gates.length - 1) = C.gates.length := by unfold rho; split_ifs <;> omega
    rw [this]; exact hout
  have htopD : ∀ y, wv n (V2 n C r c i) y (V2 n C r c i).output =
      (wv n (V2 n C r c i) y (tau n r c C.output) || wv n (V2 n C r c i) y (n + i)) := by
    intro y
    rw [hoD]
    exact wv_or hD y (by rw [hlen]; omega) (by rw [hgtop]) (by rw [hgtop])
  have hsmall : (∀ y, wv n (V2 n C r c i) y (n + i) = true →
      wv n (V2 n C r c i) y (tau n r c C.output) = true) → False := by
    intro hdom
    have hE := V1_AO2 n C r c hC hr hc
    have hEl := V1_len n C r c
    have hpre : ∀ (y : Fin n → Bool) u, u < n + (C.gates.length - 1) →
        wv n (V1 n C r c) y u = wv n (V2 n C r c i) y u := by
      intro y
      exact val_prefix (C := V2 n C r c i) (D := V1 n C r c) (hxl y) (by rw [V2_len]; omega)
        (by rw [V1_len]) (fun k hk => by rw [V1_gate n C r c k hk, V2_gate n C r c i k hk])
    have hfun : ∀ x, wv n (V1 n C r c) x (V1 n C r c).output = graphFun G ∅ x := by
      intro x
      show wv n (V1 n C r c) x (tau n r c C.output) = _
      rw [hpre x _ hto, ← hFD x, htopD x]
      cases h1 : wv n (V2 n C r c i) x (n + i)
      · simp
      · rw [hdom x h1]; rfl
    have := hmin _ hE hfun
    rw [hEl] at this
    omega
  generalize V2 n C r c i = D at *
  obtain ⟨u0, hu0⟩ : ∃ u0 : Fin n, wv n D (sg u0) c = true := by
    have hjD : (gateAt D (j - 1)).op = GateOp.and := by rw [hgj]; exact hjop
    have hfl : ∀ a, (gateAt D a).op = GateOp.and → ¬ InCone n D a (j - 1) :=
      fun a ha => hflat a (j - 1) (by omega) ha hjD
    have hcw : c < n ∨ ∃ k, c = n + k ∧ InCone n D k (j - 1) := by
      by_cases hcn : c < n
      · exact Or.inl hcn
      · exact Or.inr ⟨c - n, by omega, hcone (c - n) (by omega)⟩
    exact (lin_cone hD (j - 1) hfl c hcw).2
  have hex : ∀ T, T < C.gates.length - 1 → (gateAt D T).op = GateOp.and →
      ∃ z, Ctr n D u0 T z :=
    fun T hT hop => ctr_exists G h4 hD u0 T (by rw [hlen]; omega) hop (hsD T hT hop)
      (fun a ha => hflat a T hT ha hop)
  have : Nonempty (Fin n) := ⟨u0⟩
  choose! zf hzf using hex
  have hfacts := fun T (hT : T < C.gates.length - 1) (hop : (gateAt D T).op = GateOp.and) =>
    and_facts G hD T (by rw [hlen]; omega) hop (hsD T hT hop) (fun a ha => hflat a T hT ha hop)
  have hC1 : ∀ T, T < C.gates.length - 1 → (gateAt D T).op = GateOp.and →
      ∀ x : Fin n → Bool, wv n D x (n + T) = true → x (zf T) = true := by
    intro T hT hop x hx
    obtain ⟨A, B, hab, hla, hlb, hval, _⟩ := hfacts T hT hop
    obtain ⟨A', B', hab', hz1, _, _⟩ := hzf T hT hop
    obtain ⟨rfl, rfl⟩ : A' = A ∧ B' = B := by simpa using hab'.symm.trans hab
    rw [hval, Bool.and_eq_true] at hx
    rcases hz1 with hz1 | hz1
    · obtain ⟨u, hu, hu2⟩ := hla x hx.1
      rw [← hz1 u hu2]; exact hu
    · obtain ⟨v, hv, hv2⟩ := hlb x hx.2
      rw [← hz1 v hv2]; exact hv
  have hiS : i ∈ S := (hS i).2 ⟨by omega, hiD⟩
  have hK : ∀ T, T < C.gates.length - 1 → (gateAt D T).op = GateOp.and → T ≠ i →
      zf T ∈ (S.erase i).image zf :=
    fun T hT hop hne => Finset.mem_image.mpr ⟨T, Finset.mem_erase.mpr ⟨hne, (hS T).2 ⟨hT, hop⟩⟩, rfl⟩
  refine ⟨(S.erase i).image zf, ?_, ?_⟩
  · calc ((S.erase i).image zf).card ≤ (S.erase i).card := Finset.card_image_le
      _ < S.card := Finset.card_erase_lt_of_mem hiS
  · have hedge : ∀ p q, G.Adj p q →
        (p ∈ (S.erase i).image zf ∨ q ∈ (S.erase i).image zf) ∨
        (wv n D (pairInput p q) (n + i) = true ∧ u0 ∈ (S.erase i).image zf ∧
          ∃ w, (w = p ∨ w = q) ∧ G.Adj u0 w) := by
      intro p q hpq
      have hFx : graphFun G ∅ (pairInput p q) = true := (gf_pair G p q).2 hpq
      have hdesc : wv n D (pairInput p q) (tau n r c C.output) = true →
          (p ∈ (S.erase i).image zf ∨ q ∈ (S.erase i).image zf) := by
        intro h
        rcases descent hD (pairInput p q) i (C.gates.length - 1) (by rw [hlen]; omega) _ hto h
          with ⟨T, hT, hTi, hop, hTv⟩ | ⟨u, hu, hdom⟩ | hdom
        · have hz := hC1 T hT hop _ hTv
          have hzK := hK T hT hop hTi
          rcases memP p q _ hz with e | e
          · left; rw [← e]; exact hzK
          · right; rw [← e]; exact hzK
        · exfalso
          apply gf_sg G u
          rw [← hFD, htopD, hdom (sg u) (by simp [sg])]; rfl
        · exact (hsmall hdom).elim
      by_cases hi1 : wv n D (pairInput p q) (n + i) = true
      · have hCx : wv n C (pairInput p q) C.output = true := by rw [hFC]; exact hFx
        rcases hst (pairInput p q) C.output hout hCx with h1 | h2 |
          ⟨T, X, Y, hT, hrT, hop, hin, hdomX, hY⟩
        · exact Or.inl (hdesc h1)
        · exfalso
          apply gf_sg G u0
          rw [← hFD, htopD, h2 (sg u0) hu0]; rfl
        · have hX0 : wv n D (sg u0) X = true := hdomX _ hu0
          obtain ⟨A, B, hab, hla, hlb, hval, hcross⟩ := hfacts T hT hop
          obtain ⟨A', B', hab', hz1, hz2, hz3⟩ := hzf T hT hop
          obtain ⟨rfl, rfl⟩ : A' = A ∧ B' = B := by simpa using hab'.symm.trans hab
          have hzK := hK T hT hop (by omega)
          rcases hin with hin | hin
          · obtain ⟨rfl, rfl⟩ : A' = X ∧ B' = Y := by simpa using hab.symm.trans hin
            obtain ⟨w, hw, hw2⟩ := hlb _ hY
            rcases hz2 hX0 with hz | hz
            · left
              have e := hz w hw2
              rcases memP p q _ hw with f | f
              · left; rw [← f, e]; exact hzK
              · right; rw [← f, e]; exact hzK
            · right
              exact ⟨hi1, by rw [← hz]; exact hzK, w, memP p q _ hw, hcross u0 w hX0 hw2⟩
          · obtain ⟨rfl, rfl⟩ : A' = Y ∧ B' = X := by simpa using hab.symm.trans hin
            obtain ⟨w, hw, hw2⟩ := hla _ hY
            rcases hz3 hX0 with hz | hz
            · left
              have e := hz w hw2
              rcases memP p q _ hw with f | f
              · left; rw [← f, e]; exact hzK
              · right; rw [← f, e]; exact hzK
            · right
              exact ⟨hi1, by rw [← hz]; exact hzK, w, memP p q _ hw, (hcross w u0 hw2 hX0).symm⟩
      · left
        apply hdesc
        have := hFD (pairInput p q)
        rw [htopD, hFx] at this
        rw [Bool.not_eq_true] at hi1
        rw [hi1] at this
        simpa using this
    by_cases hall : ∀ u v, G.Adj u v → u ∈ (S.erase i).image zf ∨ v ∈ (S.erase i).image zf
    · exact Or.inl hall
    · right
      simp only [not_forall, not_or] at hall
      obtain ⟨p0, q0, hpq0, hnp, hnq⟩ := hall
      rcases hedge p0 q0 hpq0 with h | ⟨hi0, hu0K, w0, hw0, hadj0⟩
      · rcases h with h | h
        · exact absurd h hnp
        · exact absurd h hnq
      · have ha0 := memP p0 q0 _ (hC1 i (by omega) hiD _ hi0)
        have haK : zf i ∉ (S.erase i).image zf := by
          rcases ha0 with e | e
          · rw [e]; exact hnp
          · rw [e]; exact hnq
        by_cases hadja : G.Adj u0 (zf i)
        · refine ⟨u0, zf i, hu0K, hadja, fun u v huv => ?_⟩
          rcases hedge u v huv with h | ⟨hi1, _, _⟩
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rcases memP u v _ (hC1 i (by omega) hiD _ hi1) with e | e
            · exact Or.inr (Or.inr (Or.inl e.symm))
            · exact Or.inr (Or.inr (Or.inr e.symm))
        · refine ⟨u0, w0, hu0K, hadj0, fun u v huv => ?_⟩
          rcases hedge u v huv with h | ⟨hi1, _, w1, hw1, hadj1⟩
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · have ha1 := memP u v _ (hC1 i (by omega) hiD _ hi1)
            have hne1 : w1 ≠ zf i := fun e => hadja (by rw [← e]; exact hadj1)
            have hne0 : w0 ≠ zf i := fun e => hadja (by rw [← e]; exact hadj0)
            have hau : zf i ≠ u0 := fun e => haK (by rw [e]; exact hu0K)
            have hA1 : G.Adj (zf i) w1 := by
              rcases ha1 with e | e <;> rcases hw1 with f | f
              · exact absurd (f.trans e.symm) hne1
              · rw [e, f]; exact huv
              · rw [e, f]; exact huv.symm
              · exact absurd (f.trans e.symm) hne1
            have hA0 : G.Adj (zf i) w0 := by
              rcases ha0 with e | e <;> rcases hw0 with f | f
              · exact absurd (f.trans e.symm) hne0
              · rw [e, f]; exact hpq0
              · rw [e, f]; exact hpq0.symm
              · exact absurd (f.trans e.symm) hne0
            have hww : w0 = w1 := nfc_use G h4 hau hA0 hadj0 hA1 hadj1
            rcases hw1 with f | f
            · exact Or.inr (Or.inr (Or.inl (f.symm.trans hww.symm)))
            · exact Or.inr (Or.inr (Or.inr (f.symm.trans hww.symm)))

end SecKey

section SecMain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open P1499

def I13 (p l : Fin 13) : Prop :=
  p = l ∨ p = l + (1 : Fin 13) ∨ p = l + (3 : Fin 13) ∨ p = l + (9 : Fin 13)

instance : DecidableRel I13 := fun p l => by unfold I13; infer_instance

lemma r4d (d : Fin 13) (hd : ∀ m : Fin 13, I13 (m + d) m) (K : Finset (Fin 26))
    (hK : K.card ≤ 13)
    (hcov : ∀ p l : Fin 13, I13 p l → Fin.castAdd 13 p ∈ K ∨ Fin.natAdd 13 l ∈ K) :
    13 ≤ K.card ∧ ∀ l : Fin 13, Fin.castAdd 13 (l + d) ∈ K → Fin.natAdd 13 l ∈ K → False := by
  classical
  let f : Fin 13 → Fin 26 := fun m =>
    if Fin.castAdd 13 (m + d) ∈ K then Fin.castAdd 13 (m + d) else Fin.natAdd 13 m
  have hf : Function.Injective f := by
    intro m m' h
    simp only [f] at h
    split_ifs at h with h1 h2 h2
    · exact add_right_cancel (Own.cast_inj h)
    · exact absurd h (Own.cast_ne_nat _ _)
    · exact absurd h.symm (Own.cast_ne_nat _ _)
    · exact Own.nat_inj h
  have hsub : Finset.univ.image f ⊆ K := by
    intro z hz
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hz
    simp only [f]
    split_ifs with h1
    · exact h1
    · exact (hcov (m + d) m (hd m)).resolve_left h1
  have hcard : (Finset.univ.image f).card = 13 := by
    rw [Finset.card_image_of_injective _ hf]; simp
  have h13 : 13 ≤ K.card := by rw [← hcard]; exact Finset.card_le_card hsub
  refine ⟨h13, fun l h1 h2 => ?_⟩
  have heq : Finset.univ.image f = K :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hK)
  rw [← heq] at h2
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp h2
  simp only [f] at hm
  split_ifs at hm with h3
  · exact Own.cast_ne_nat _ _ hm
  · have := Own.nat_inj hm
    subst this
    exact h3 h1

lemma hU13 : ∀ pa pb : Fin 13, pa ≠ pb → ∃! lb : Fin 13, I13 pa lb ∧ I13 pb lb := by
  have hk : ∀ pa pb : Fin 13, pa ≠ pb → ∃ lb : Fin 13, (I13 pa lb ∧ I13 pb lb) ∧
      ∀ y : Fin 13, I13 pa y ∧ I13 pb y → y = lb := by
    unfold I13
    decide +kernel
  exact fun pa pb h => hk pa pb h

lemma hc13 : ∀ l : Fin 13, (Finset.univ.filter (fun p => I13 p l)).card = 3 + 1 := by
  unfold I13
  decide

lemma g_eq (G : SimpleGraph (Fin 26))
    (hG : ∀ (a b : Fin 26), G.Adj a b ↔ ∃ (p : Fin 13) (l : Fin 13), I13 p l ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) :
    G = Own.PG I13 := by
  ext a b
  rw [hG]
  constructor
  · rintro ⟨p, l, h, h1 | h1⟩
    · exact ⟨p, l, h, Or.inl h1⟩
    · exact ⟨p, l, h, Or.inr ⟨h1.2, h1.1⟩⟩
  · rintro ⟨p, l, h, h1 | h1⟩
    · exact ⟨p, l, h, Or.inl h1⟩
    · exact ⟨p, l, h, Or.inr ⟨h1.2, h1.1⟩⟩

lemma g_nfc (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hG : ∀ (a b : Fin 26), G.Adj a b ↔ ∃ (p : Fin 13) (l : Fin 13), I13 p l ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) :
    PEqualNP.TopForm.NoFourCycle G := by
  obtain rfl := g_eq G hG
  exact Own.pg_nfc I13 hU13

lemma g_edges (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hG : ∀ (a b : Fin 26), G.Adj a b ↔ ∃ (p : Fin 13) (l : Fin 13), I13 p l ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) :
    52 ≤ G.edgeFinset.card := by
  obtain rfl := g_eq G hG
  exact Own.pg_edges 3 I13 hc13

lemma main_ind (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hG : ∀ (a b : Fin 26), G.Adj a b ↔ ∃ (p : Fin 13) (l : Fin 13), I13 p l ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) :
    ∀ m (C : Circuit), PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.junk G C = ∅ →
      PEqualNP.TopForm.andPairs 26 C = m → m = 0 := by
  have h4 : PEqualNP.TopForm.NoFourCycle G := g_nfc G hG
  have hE : 52 ≤ G.edgeFinset.card := g_edges G hG
  have hne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨W, hWA, hWf, _, hWs⟩ := Own.upper 3 13 I13 (by omega) hc13
  have hWF : circuitFun 26 W = graphFun G ∅ := by
    funext z
    have h1 := hWf z
    rw [Bool.eq_iff_iff, graphFun_iff]
    rw [show circuitFun 26 W z = circuitFun (13 + 13) W z from rfl, h1, decide_eq_true_iff]
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, (hG _ _).2 ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hG _ _).1 huv
      · exact ⟨p, l, h, hu, hv⟩
      · exact ⟨p, l, h, hv, hu⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hL hJ hm
    by_contra hm0
    have hposm : 0 < PEqualNP.TopForm.andPairs 26 C := by omega
    unfold PEqualNP.TopForm.andPairs at hposm
    rw [Finset.card_pos] at hposm
    obtain ⟨⟨i, j⟩, hp⟩ := hposm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨hi, hj⟩, hiand, hjand, hcone⟩ := hp
    obtain ⟨hAO, hfun, hmin⟩ := hL
    have hF : ∀ x : Fin 26 → Bool, wv 26 C x C.output = graphFun G ∅ x :=
      fun x => congrFun hfun x
    have hC : AO2 26 C := of_real hAO
    have hLC : Least 26 C :=
      ⟨hC, fun D hD hfunD => hmin D (to_real hD) (funext fun x => (hfunD x).trans (hF x))⟩
    have hout : C.output < 26 + C.gates.length :=
      out_lt 26 C (fun _ => true) (by rw [hF]; exact graphFun_true G hne)
    have hsC : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
        ∀ x, wv 26 C x (26 + k) = true → graphFun G ∅ x = true := by
      intro k hk hop
      by_contra hcon
      have hmem : k ∈ PEqualNP.TopForm.junk G C := (junk_mem G C k).2 ⟨hk, hop, hcon⟩
      rw [hJ] at hmem
      simp at hmem
    obtain ⟨r, c, hr, hir, hc, hci, hopr, hcin, hrj, huniq, h0⟩ :=
      exch 26 C (graphFun G ∅) hLC hF hout i j (hsC i hi hiand) hjand hcone
    have hbel' : ∀ x, wv 26 C x (26 + i) = true → wv 26 C x C.output = true :=
      fun x h => by rw [hF]; exact hsC i hi hiand x h
    have hD := V2_AO2 26 C r c i hC hr hc hir hout
    have hfunD : ∀ x, wv 26 (V2 26 C r c i) x (V2 26 C r c i).output = wv 26 C x C.output :=
      fun x => V2_out 26 C r c i x hC hr hc hir hout (hbel' x) (h0 x)
    have hFD : ∀ x, wv 26 (V2 26 C r c i) x (V2 26 C r c i).output = graphFun G ∅ x :=
      fun x => (hfunD x).trans (hF x)
    have hlen := V2_len 26 C r c i
    have hops : ∀ k', k' < C.gates.length - 1 →
        (gateAt (V2 26 C r c i) k').op = (gateAt C (rho r k')).op := by
      intro k' hk'
      rw [V2_gate 26 C r c i k' hk']
    have htop : (gateAt (V2 26 C r c i) (C.gates.length - 1)).op = GateOp.or := by
      rw [V2_top 26 C r c i (by omega)]
    have hbelow := fun k' hk' => V2_below 26 C r c i (graphFun G ∅) hC hr hc hir hout
      (hsC i hi hiand) h0 k' hk'
    have hcone' := fun a' b' hb' h => V2_cone 26 C r c i hC hr hc hcin a' b' hb' h
    have hno := V2_no_cone 26 C r c i hr hir hci huniq
    have hsD : ∀ k, k < C.gates.length - 1 → (gateAt (V2 26 C r c i) k).op = GateOp.and →
        ∀ x, wv 26 (V2 26 C r c i) x (26 + k) = true → graphFun G ∅ x = true := by
      intro k hk hop
      rw [hops k hk] at hop
      exact (hbelow k hk).2 (hsC _ (rho_lt r k _ hr hk) hop)
    have hLD : PEqualNP.TopForm.IsLeastAO G (V2 26 C r c i) :=
      ⟨to_real hD, funext hFD, fun E hE hEf => by
        show (V2 26 C r c i).gates.length ≤ E.gates.length
        rw [hlen]; exact hmin E hE hEf⟩
    have hJD : PEqualNP.TopForm.junk G (V2 26 C r c i) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [junk_mem] at hk
      obtain ⟨hk1, hk2, hk3⟩ := hk
      rw [hlen] at hk1
      by_cases hkl : k < C.gates.length - 1
      · exact hk3 (hsD k hkl hk2)
      · have hke : k = C.gates.length - 1 := by omega
        rw [hke, htop] at hk2
        cases hk2
    have hlt : PEqualNP.TopForm.andPairs 26 (V2 26 C r c i) < PEqualNP.TopForm.andPairs 26 C := by
      unfold PEqualNP.TopForm.andPairs
      apply pairs_lt2 26 C (V2 26 C r c i) r i j hr hir hlen hops htop hcone' hno hiand hjand hcone
      · intro p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      · intro p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have hD0 := ih _ (by rw [← hm]; exact hlt) (V2 26 C r c i) hLD hJD rfl
    have hnest : ∀ a b, (gateAt (V2 26 C r c i) a).op = GateOp.and →
        (gateAt (V2 26 C r c i) b).op = GateOp.and → ¬ InCone 26 (V2 26 C r c i) a b := by
      intro a b ha hbo hab
      have hab' := inCone_lt 26 _ a b hab
      unfold PEqualNP.TopForm.andPairs at hD0
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hD0
      apply hD0 (a, b)
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, ha, hbo, hab⟩
    have hTF : PEqualNP.TopForm.TopForm G (V2 26 C r c i) :=
      fun a _ b _ hao _ hbo hab => hnest a b hao hbo hab
    have hUs : PEqualNP.TopForm.Ustar G (V2 26 C r c i) = ∅ := by
      by_contra hne'
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro huv
        obtain ⟨_, _, _, h, hh, _⟩ := P1491.S90.off_star G (V2 26 C r c i) hLD hTF u v huv
        rw [hJD] at hh
        simp at hh
    have htc : (PEqualNP.TopForm.tops G (V2 26 C r c i)).card ≤ 13 := by
      obtain ⟨hineq, _⟩ := s1491 26 G (V2 26 C r c i) h4 hne hLD hTF
      have h1 : (PEqualNP.TopForm.tops G (V2 26 C r c i) \
          PEqualNP.TopForm.centreless G (V2 26 C r c i)).card +
          (PEqualNP.TopForm.centreless G (V2 26 C r c i)).card =
          (PEqualNP.TopForm.tops G (V2 26 C r c i)).card :=
        Finset.card_sdiff_add_card_eq_card (by
          unfold PEqualNP.TopForm.centreless
          exact Finset.filter_subset _ _)
      have hsz : (V2 26 C r c i).size ≤ W.size := hLD.2.2 W hWA hWF
      rw [hUs, hJD] at hineq
      simp only [Finset.card_empty] at hineq
      omega
    have hS : ∀ k, k ∈ PEqualNP.TopForm.tops G (V2 26 C r c i) ↔
        k < C.gates.length - 1 ∧ (gateAt (V2 26 C r c i) k).op = GateOp.and := by
      intro k
      unfold PEqualNP.TopForm.tops PEqualNP.TopForm.gatesWhere
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, _⟩
        rw [hlen] at h1
        refine ⟨?_, h2⟩
        by_contra hk
        have hke : k = C.gates.length - 1 := by omega
        rw [hke, htop] at h2
        cases h2
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [hlen]; omega, h2, fun x hx => hsD k h1 h2 x hx⟩
    have hiD : (gateAt (V2 26 C r c i) i).op = GateOp.and := by
      rw [hops i (by omega)]
      have : rho r i = i := by unfold rho; rw [if_pos hir]
      rw [this]; exact hiand
    obtain ⟨K, hKc, hKcov⟩ := key G h4 C r c i j hC hr hir hc hout hF hFD hrj hjand
      (fun E hE hEf => hmin E (to_real hE) (funext hEf)) hsD
      (fun a b _ ha hb => hnest a b ha hb) hiD _ hS
    have hflag : ∀ (K' : Finset (Fin 26)), (∀ u v, G.Adj u v → u ∈ K' ∨ v ∈ K') →
        ∀ p l : Fin 13, I13 p l → Fin.castAdd 13 p ∈ K' ∨ Fin.natAdd 13 l ∈ K' :=
      fun K' hc' p l h => hc' _ _ ((hG _ _).2 ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩)
    have hd0 : ∀ m : Fin 13, I13 (m + 0) m := fun m => Or.inl (add_zero m)
    have hd1 : ∀ m : Fin 13, I13 (m + 1) m := fun m => Or.inr (Or.inl rfl)
    have hd3 : ∀ m : Fin 13, I13 (m + 3) m := fun m => Or.inr (Or.inr (Or.inl rfl))
    have hd9 : ∀ m : Fin 13, I13 (m + 9) m := fun m => Or.inr (Or.inr (Or.inr rfl))
    rcases hKcov with hcov | ⟨u0, w0, hu0K, hadj, hcov⟩
    · have := (r4d 0 hd0 K (by omega) (hflag K hcov)).1
      omega
    · have hK' : (insert w0 K).card ≤ 13 := by
        have := Finset.card_insert_le w0 K
        omega
      have hcov' : ∀ u v, G.Adj u v → u ∈ insert w0 K ∨ v ∈ insert w0 K := by
        intro u v huv
        rcases hcov u v huv with h | h | h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr (Finset.mem_insert_of_mem h)
        · exact Or.inl (by rw [h]; exact Finset.mem_insert_self _ _)
        · exact Or.inr (by rw [h]; exact Finset.mem_insert_self _ _)
      have hfl := hflag _ hcov'
      have hu0 : u0 ∈ insert w0 K := Finset.mem_insert_of_mem hu0K
      have hw0 : w0 ∈ insert w0 K := Finset.mem_insert_self _ _
      obtain ⟨p, l, hI, hpl⟩ := (hG _ _).1 hadj
      have hboth : Fin.castAdd 13 p ∈ insert w0 K ∧ Fin.natAdd 13 l ∈ insert w0 K := by
        rcases hpl with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact ⟨by rw [← e1]; exact hu0, by rw [← e2]; exact hw0⟩
        · exact ⟨by rw [← e1]; exact hw0, by rw [← e2]; exact hu0⟩
      rcases hI with e | e | e | e
      · exact (r4d 0 hd0 _ hK' hfl).2 l (by rw [add_zero, ← e]; exact hboth.1) hboth.2
      · exact (r4d 1 hd1 _ hK' hfl).2 l (by rw [← e]; exact hboth.1) hboth.2
      · exact (r4d 3 hd3 _ hK' hfl).2 l (by rw [← e]; exact hboth.1) hboth.2
      · exact (r4d 9 hd9 _ hK' hfl).2 l (by rw [← e]; exact hboth.1) hboth.2

end SecMain

end PEqualNP.Outside.L_meta_2393

theorem PEqualNP.Outside.L_meta_2393 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (0 : ℕ) := by
  intro x1 x2 x3 hG hL hJ
  exact PEqualNP.Outside.L_meta_2393.main_ind x1 hG _ x3 hL hJ rfl
