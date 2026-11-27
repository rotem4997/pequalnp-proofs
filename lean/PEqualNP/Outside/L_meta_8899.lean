import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8899

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.GenericRejection

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


-- Wire evaluation and cone recursion adapted from L_meta_2061.
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
  rw [ite_eq_left ((hC j hj).2 i hi)]

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
    · have ht : tau n r b w = w := by unfold tau; rw [ite_eq_left (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [ite_eq_left hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_left (by omega)]
            · unfold rho; rw [ite_eq_left hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
            · unfold rho; rw [ite_eq_right (by omega)]; omega
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
  rw [ite_eq_left hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_left hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_right (by omega)]

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
  unfold tau; rw [ite_eq_left hw]

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

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma ao2_iff (n : ℕ) (C : Circuit) : AO2 n C ↔ PEqualNP.TopForm.IsAO2 n C := by
  have mem (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  constructor
  · intro h
    refine ⟨?_, fun j hj => (h j hj).2.2, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      simpa only [gateAt_eq C j hj] using (h j hj).1
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a, b, hab⟩ := (h j hj).2.1
      rw [gateAt_eq C j hj] at hab
      simp [hab]
  · intro h j hj
    refine ⟨h.1 _ (mem j hj), ?_, h.2.1 j hj⟩
    exact List.length_eq_two.mp (h.2.2 _ (mem j hj))

lemma reader_pair (n : ℕ) (C : Circuit) (hC : AO2 n C) (i r : ℕ)
    (hr : r < C.gates.length) (hin : n + i ∈ (gateAt C r).inputs) :
    ∃ p < n + r, (gateAt C r).inputs = [n + i, p] ∨ (gateAt C r).inputs = [p, n + i] := by
  obtain ⟨a, b, hab⟩ := (hC r hr).2.1
  have ha := (hC r hr).2.2 a (by simp [hab])
  have hb := (hC r hr).2.2 b (by simp [hab])
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · exact ⟨b, hb, Or.inl hab⟩
  · exact ⟨a, ha, Or.inr hab⟩

lemma and_reader (n : ℕ) (C : Circuit) (hC : AO2 n C) (i r p : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and)
    (hin : (gateAt C r).inputs = [n + i, p] ∨ (gateAt C r).inputs = [p, n + i])
    (x : Fin n → Bool) :
    wv n C x (n + r) = (wv n C x (n + i) && wv n C x p) := by
  rw [wv_rec n C x (aob hC) r hr, hop]
  rcases hin with hin | hin
  · rw [hin, eval_and_pair]
  · rw [hin, eval_and_pair, Bool.and_comm]

lemma or_reader (n : ℕ) (C : Circuit) (hC : AO2 n C) (i r p : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hin : (gateAt C r).inputs = [n + i, p] ∨ (gateAt C r).inputs = [p, n + i])
    (x : Fin n → Bool) :
    wv n C x (n + r) = (wv n C x (n + i) || wv n C x p) := by
  rw [wv_rec n C x (aob hC) r hr, hop]
  rcases hin with hin | hin
  · rw [hin, eval_or_pair]
  · rw [hin, eval_or_pair, Bool.or_comm]

def Accepts (n : ℕ) (P : (Fin n → Bool) → Prop) (C : Circuit) : Prop :=
  ∀ x, P x → wv n C x C.output = true

def Clean (n : ℕ) (Q : (Fin n → Bool) → Prop) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x, Q x → wv n C x w = false

def AndBound (C : Circuit) (t : ℕ) : Prop :=
  ∀ k < C.size, (gateAt C k).op = GateOp.and → k < t

def Separated (n : ℕ) (Q : (Fin n → Bool) → Prop) (C : Circuit) : Prop :=
  ∀ i < C.size, ∀ j < C.size, (gateAt C i).op = GateOp.and →
    Clean n Q C (n + i) → (gateAt C j).op = GateOp.and → ¬ InCone n C i j

lemma delete_and (n : ℕ) (P Q : (Fin n → Bool) → Prop) (C : Circuit) (t i r p : ℕ)
    (hC : AO2 n C) (hout : C.output < n + C.size) (ha : Accepts n P C)
    (hq : Clean n Q C C.output) (hi : Clean n Q C (n + i)) (ht : AndBound C t)
    (hr : r < C.size) (hir : i < r) (hop : (gateAt C r).op = GateOp.and)
    (hin : (gateAt C r).inputs = [n + i, p] ∨ (gateAt C r).inputs = [p, n + i]) :
    ∃ D : Circuit, D.size < C.size ∧ AO2 n D ∧ D.output < n + D.size ∧
      Accepts n P D ∧ Clean n Q D D.output ∧ AndBound D t := by
  let D := V1 n C r (n + i)
  have hD := V1_AO2 n C r (n + i) hC hr (by omega)
  have hlen : D.size = C.size - 1 := V1_len n C r (n + i)
  have houtD : D.output < n + D.size := by
    change tau n r (n + i) C.output < n + D.size
    rw [hlen]
    unfold tau
    split_ifs <;> omega
  refine ⟨D, by omega, hD, houtD, ?_, ?_, ?_⟩
  · intro x hx
    exact transfer_le n C D r (n + i) x (aob hC) (aob hD) hr (by omega)
      (by exact hlen.ge) (V1_red n C r (n + i)) C.output hout
      (fun _ h => by
        rw [and_reader n C hC i r p hr hop hin x] at h
        exact (Bool.and_eq_true_iff.mp h).1) (ha x hx)
  · intro x hx
    have heq := transfer_eq n C D r (n + i) x (aob hC) (aob hD) hr (by omega)
      (by exact hlen.ge) (V1_red n C r (n + i)) C.output hout
      (fun _ => by rw [and_reader n C hC i r p hr hop hin x, hi x hx]; rfl)
    exact heq.symm.trans (hq x hx)
  · intro k hk hkAnd
    have hk' : k < C.size - 1 := by omega
    rw [V1_gate n C r (n + i) k hk'] at hkAnd
    have h := ht _ (rho_lt r k _ hr hk') hkAnd
    unfold rho at h
    split_ifs at h <;> omega

lemma move_or (n : ℕ) (P Q : (Fin n → Bool) → Prop) (C : Circuit) (t i r p : ℕ)
    (hC : AO2 n C) (hout : C.output < n + C.size) (ha : Accepts n P C)
    (hq : Clean n Q C C.output) (hi : Clean n Q C (n + i)) (ht : AndBound C t)
    (hr : r < C.size) (hir : i < r) (hp : p < n + r) (hrt : r < t)
    (hop : (gateAt C r).op = GateOp.or)
    (hin : (gateAt C r).inputs = [n + i, p] ∨ (gateAt C r).inputs = [p, n + i]) :
    ∃ D : Circuit, D.size = C.size ∧ AO2 n D ∧ D.output < n + D.size ∧
      Accepts n P D ∧ Clean n Q D D.output ∧ AndBound D (t - 1) := by
  let D := V2 n C r p i
  have hD := V2_AO2 n C r p i hC hr hp hir hout
  have hlen : D.size = C.size := V2_len n C r p i
  have houtD : D.output < n + D.size := by
    change n + C.size - 1 < n + D.size
    omega
  have heq (x : Fin n → Bool) :
      (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n D x D.output = wv n C x C.output := by
    intro hx
    apply V2_out n C r p i x hC hr hp hir hout hx
    intro hv
    rw [or_reader n C hC i r p hr hop hin x, hv]
    rfl
  refine ⟨D, hlen, hD, houtD, ?_, ?_, ?_⟩
  · intro x hx
    exact (heq x (fun _ => ha x hx)).trans (ha x hx)
  · intro x hx
    exact (heq x (by simp [hi x hx])).trans (hq x hx)
  · intro k hk hkAnd
    by_cases hk' : k < C.size - 1
    · have hs : k < C.gates.length - 1 := hk'
      rw [V2_gate n C r p i k hs] at hkAnd
      have h := ht _ (rho_lt r k _ hr hs) hkAnd
      unfold rho at h
      split_ifs at h <;> omega
    · have he : k = C.gates.length - 1 := by change k = C.size - 1; omega
      rw [he, V2_top n C r p i (Nat.zero_lt_of_lt hr)] at hkAnd
      cases hkAnd

lemma normalize (n : ℕ) (P Q : (Fin n → Bool) → Prop) (m : ℕ) :
    ∀ (C : Circuit) (t : ℕ), C.size + t = m → AO2 n C →
      C.output < n + C.size → Accepts n P C → Clean n Q C C.output → AndBound C t →
      ∃ D : Circuit, D.size ≤ C.size ∧ AO2 n D ∧ D.output < n + D.size ∧
        Accepts n P D ∧ Clean n Q D D.output ∧ Separated n Q D := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C t hm hC hout ha hq ht
    classical
    by_cases hs : Separated n Q C
    · exact ⟨C, le_rfl, hC, hout, ha, hq, hs⟩
    simp only [Separated, not_forall, not_not] at hs
    obtain ⟨i, hi, j, hj, hiAnd, hiClean, hjAnd, hc⟩ := hs
    obtain ⟨r, hr, hir, hin, hpath⟩ := inCone_reader n C i j hc
    obtain ⟨p, hp, hpair⟩ := reader_pair n C hC i r hr hin
    have reduced : ∃ (D : Circuit) (u : ℕ), D.size ≤ C.size ∧ D.size + u < m ∧
        AO2 n D ∧ D.output < n + D.size ∧ Accepts n P D ∧ Clean n Q D D.output ∧
        AndBound D u := by
      rcases (hC r hr).1 with hAnd | hOr
      · obtain ⟨D, hd, h1, h2, h3, h4, h5⟩ :=
          delete_and n P Q C t i r p hC hout ha hq hiClean ht hr hir hAnd hpair
        exact ⟨D, t, hd.le, by omega, h1, h2, h3, h4, h5⟩
      · have hrj : r ≤ j := by
          rcases hpath with h | h
          · exact h.le
          · exact (inCone_lt n C r j h).1.le
        have htj := ht j hj hjAnd
        obtain ⟨D, hd, h1, h2, h3, h4, h5⟩ :=
          move_or n P Q C t i r p hC hout ha hq hiClean ht hr hir hp (by omega) hOr hpair
        exact ⟨D, t - 1, hd.le, by omega, h1, h2, h3, h4, h5⟩
    obtain ⟨D, u, hd, hlt, h1, h2, h3, h4, h5⟩ := reduced
    obtain ⟨E, he, e1, e2, e3, e4, e5⟩ :=
      ih (D.size + u) hlt D u rfl h1 h2 h3 h4 h5
    exact ⟨E, he.trans hd, e1, e2, e3, e4, e5⟩

end PEqualNP.Outside.L_meta_8899

theorem PEqualNP.Outside.L_meta_8899 :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) => ∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → PEqualNP.CircuitLowerBounds.wireValue x5 (PEqualNP.GenericRejection.incidenceInput x7 x8) x6 = Bool.false;   PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → x5 x4 x4.output → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size ≤ x4.size ∧ PEqualNP.TopForm.IsAO2 (x2 + x2) x10 ∧ x10.output < x2 + x2 + x10.size ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x3 x10 ∧ x5 x10 x10.output ∧ ∀ x11 < x10.size, ∀ x13 < x10.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 x10 (x2 + x2 + x11) → (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬PEqualNP.EdgeOwnership.InCone (x2 + x2) x10 x11 x13 := by
  open PEqualNP.Outside.L_meta_8899 PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection in
  intro q v S C
  dsimp only
  intro hC hout ha hq
  let P (x : Fin (v + v) → Bool) := ∃ (l p : Fin v), p ∈ S l ∧
    List.ofFn x = incidenceInput {p} {l}
  let Q (x : Fin (v + v) → Bool) := ∃ (X Y : Finset (Fin v)), Y.card ≤ q ∧
    IsFalseInput S X Y ∧ List.ofFn x = incidenceInput X Y
  have hAccept : Accepts (v + v) P C := by
    rintro x ⟨l, p, hp, hx⟩
    unfold wv
    rw [hx]
    exact ha l p hp
  have hClean : Clean (v + v) Q C C.output := by
    rintro x ⟨X, Y, hy, hf, hx⟩
    unfold wv
    rw [hx]
    exact hq X Y hy hf
  obtain ⟨D, hD, hAO, hOut, hA, hQ, hSep⟩ :=
    normalize (v + v) P Q (C.size + C.size) C C.size rfl
      ((ao2_iff _ _).mpr hC) hout hAccept hClean (fun _ hk _ => hk)
  have inputOfFn (X Y : Finset (Fin v)) :
      ∃ x : Fin (v + v) → Bool, List.ofFn x = incidenceInput X Y :=
    ofFn_of_len _ _ (by simp [incidenceInput])
  refine ⟨D, hD, (ao2_iff _ _).mp hAO, hOut, ?_, ?_, ?_⟩
  · intro l p hp
    obtain ⟨x, hx⟩ := inputOfFn {p} {l}
    exact hx ▸ hA x ⟨l, p, hp, hx⟩
  · intro X Y hy hf
    obtain ⟨x, hx⟩ := inputOfFn X Y
    exact hx ▸ hQ x ⟨X, Y, hy, hf, hx⟩
  · intro i hi j hj hiAnd hiClean hjAnd
    apply hSep i hi j hj hiAnd _ hjAnd
    rintro x ⟨X, Y, hy, hf, hx⟩
    unfold wv
    rw [hx]
    exact hiClean X Y hy hf
