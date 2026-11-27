import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2067

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

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma gateAt_some {C : Circuit} {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) :
    gateAt C k = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma no_pair (C : Circuit) (h : PEqualNP.TopForm.andPairs 26 C = 0) (i j : ℕ)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hc : InCone 26 C i j) : False := by
  have hlt := inCone_lt 26 C i j hc
  unfold PEqualNP.TopForm.andPairs at h
  rw [Finset.card_eq_zero] at h
  have hm := Finset.eq_empty_iff_forall_notMem.mp h (i, j)
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
  exact hm ⟨⟨by omega, by omega⟩, hi, hj, hc⟩

def NoAnd (C : Circuit) (k : ℕ) : Prop :=
  (gateAt C k).op ≠ GateOp.and ∧ ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and

def AF (C : Circuit) (w : ℕ) : Prop := ∀ k, w = 26 + k → NoAnd C k

lemma af_opnd (C : Circuit) (k a : ℕ) (hk : k < C.gates.length)
    (ha : a ∈ (gateAt C k).inputs) (halt : a < 26 + k)
    (hno : ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and) : AF C a := by
  intro i hi
  subst hi
  have hc : InCone 26 C i k := (inCone_iff 26 C i k).2 ⟨hk, i, by omega, ha, Or.inl rfl⟩
  exact ⟨hno i hc, fun i2 hc2 => hno i2 (inCone_trans 26 C i2 i hc2 k hc)⟩

def xP (p : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p)
def xL (l : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l)
def xPL (p l : Fin 13) : Fin 26 → Bool :=
  fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

lemma base (p l : Fin 13) (f : ℕ → Bool) (C : Circuit)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (w : ℕ) (hw : w < 26) :
    (wv 26 C (xPL p l) w = true → wv 26 C (xP p) w = true ∨ f w = true) ∧
    (f w = true → wv 26 C (xL l) w = true) := by
  rw [wv_input _ _ _ _ hw, wv_input _ _ _ _ hw, wv_input _ _ _ _ hw]
  simp only [xPL, xP, xL, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have hp := p.isLt
  have hl := l.isLt
  rcases Nat.lt_or_ge w 13 with h | h
  · have h5 : f w = false := (H5 ⟨w, h⟩).1
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · omega
    · intro h1
      rw [h5] at h1
      exact absurd h1 (by simp)
  · have h5 := (H5 ⟨w - 13, by omega⟩).2
    have e : 13 + (w - 13) = w := by omega
    simp only [e, Fin.ext_iff] at h5
    constructor
    · rintro (h1 | h1)
      · omega
      · right
        rw [h5]
        simp only [decide_eq_true_eq]
        omega
    · intro h1
      rw [h5] at h1
      simp only [decide_eq_true_eq] at h1
      omega

lemma gate_val (C : Circuit) (hC : AOB 26 C) (x : Fin 26 → Bool) (k : ℕ) (g : Gate)
    (hg : C.gates[k]? = some g) (a b : ℕ) (hin : g.inputs = [a, b]) :
    (g.op = GateOp.and → wv 26 C x (26 + k) = (wv 26 C x a && wv 26 C x b)) ∧
    (g.op = GateOp.or → wv 26 C x (26 + k) = (wv 26 C x a || wv 26 C x b)) := by
  have hk : k < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hg
    exact absurd hg (by simp)
  have h := wv_rec 26 C x hC k hk
  rw [gateAt_some hg, hin] at h
  constructor
  · intro hop
    rw [h, hop]
    simp [GateOp.eval]
  · intro hop
    rw [h, hop]
    simp [GateOp.eval]

lemma and_case (va vb pa pb fa fb la lb : Bool)
    (qa : (va = true → pa = true ∨ fa = true) ∧ (fa = true → la = true))
    (qb : (vb = true → pb = true ∨ fb = true) ∧ (fb = true → lb = true)) :
    (va && vb) = true →
      (pa && pb) = true ∨ (pa && fb || fa && pb) = true ∨ (la && lb) = true := by
  intro h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rcases qa.1 h1 with x | x <;> rcases qb.1 h2 with y | y
  · left; simp [x, y]
  · right; left; simp [x, y]
  · right; left; simp [x, y]
  · right; right; simp [qa.2 x, qb.2 y]

lemma or_case1 (va vb pa pb fa fb la lb : Bool)
    (qa : (va = true → pa = true ∨ fa = true) ∧ (fa = true → la = true))
    (qb : (vb = true → pb = true ∨ fb = true) ∧ (fb = true → lb = true)) :
    ((va || vb) = true → (pa || pb) = true ∨ (fa || fb) = true) ∧
      ((fa || fb) = true → (la || lb) = true) := by
  constructor
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rcases qa.1 h with x | x
      · left; simp [x]
      · right; simp [x]
    · rcases qb.1 h with x | x
      · left; simp [x]
      · right; simp [x]
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simp [qa.2 h]
    · simp [qb.2 h]

lemma or_case2 (va vb pa pb fa fb la lb : Bool)
    (qa : va = true → pa = true ∨ fa = true ∨ la = true)
    (qb : vb = true → pb = true ∨ fb = true ∨ lb = true) :
    (va || vb) = true →
      (pa || pb) = true ∨ (fa || fb) = true ∨ (la || lb) = true := by
  intro h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rcases qa h with x | x | x
    · left; simp [x]
    · right; left; simp [x]
    · right; right; simp [x]
  · rcases qb h with x | x | x
    · left; simp [x]
    · right; left; simp [x]
    · right; right; simp [x]

lemma main (C : Circuit) (p l : Fin 13) (f : ℕ → Bool)
    (H1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k)
    (H3 : PEqualNP.TopForm.andPairs 26 C = 0)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (H6 : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → f (26 + k) =
        (wv 26 C (xP p) a && f b || f a && wv 26 C (xP p) b)) ∧
      (g.op = GateOp.or → f (26 + k) = (f a || f b))) :
    ∀ w, w < 26 + C.gates.length →
      (AF C w → (wv 26 C (xPL p l) w = true → wv 26 C (xP p) w = true ∨ f w = true) ∧
        (f w = true → wv 26 C (xL l) w = true)) ∧
      (wv 26 C (xPL p l) w = true →
        wv 26 C (xP p) w = true ∨ f w = true ∨ wv 26 C (xL l) w = true) := by
  have hC : AOB 26 C := by
    intro j hj
    have hg : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
    obtain ⟨hop, a, b, hin, _, ha, hb⟩ := H1 j _ hg
    rw [gateAt_some hg]
    refine ⟨hop, ?_⟩
    intro i hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · omega
    · omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases Nat.lt_or_ge w 26 with h | h
    · have hb := base p l f C H5 w h
      exact ⟨fun _ => hb, fun hv => by
        rcases hb.1 hv with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < C.gates.length := by omega
      have hg : C.gates[k]? = some (C.gates[k]) := List.getElem?_eq_getElem hk
      obtain ⟨hop, a, b, hin, _, ha, hb⟩ := H1 k _ hg
      have hgk := gateAt_some hg
      have hain : a ∈ (gateAt C k).inputs := by rw [hgk, hin]; simp
      have hbin : b ∈ (gateAt C k).inputs := by rw [hgk, hin]; simp
      have iha := ih a ha (by omega)
      have ihb := ih b hb (by omega)
      have e1 := gate_val C hC (xPL p l) k _ hg a b hin
      have e2 := gate_val C hC (xP p) k _ hg a b hin
      have e3 := gate_val C hC (xL l) k _ hg a b hin
      have e4 := H6 k _ a b hg hin
      rcases hop with hop | hop
      · have hno : ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and := by
          intro i hc hi
          exact no_pair C H3 i k hi (by rw [hgk]; exact hop) hc
        have qa := iha.1 (af_opnd C k a hk hain ha hno)
        have qb := ihb.1 (af_opnd C k b hk hbin hb hno)
        rw [e1.1 hop, e2.1 hop, e3.1 hop, e4.1 hop]
        constructor
        · intro haf
          exact absurd (by rw [hgk]; exact hop) (haf k rfl).1
        · exact and_case _ _ _ _ _ _ _ _ qa qb
      · rw [e1.2 hop, e2.2 hop, e3.2 hop, e4.2 hop]
        constructor
        · intro haf
          have hno := (haf k rfl).2
          have qa := iha.1 (af_opnd C k a hk hain ha hno)
          have qb := ihb.1 (af_opnd C k b hk hbin hb hno)
          exact or_case1 _ _ _ _ _ _ _ _ qa qb
        · exact or_case2 _ _ _ _ _ _ _ _ iha.2 ihb.2

lemma core (S : Finset (Fin 13)) (C : Circuit) (p l : Fin 13) (f : ℕ → Bool)
    (H1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k)
    (H2 : ∀ (x : Fin 26 → Bool), C.eval (List.ofFn x) = true ↔
      ∃ (u : Fin 13) (v : Fin 13), u - v ∈ S ∧ x (Fin.castAdd 13 u) = true ∧
        x (Fin.natAdd 13 v) = true)
    (H3 : PEqualNP.TopForm.andPairs 26 C = 0)
    (H4 : p - l ∈ S)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (H6 : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → f (26 + k) =
        (wv 26 C (xP p) a && f b || f a && wv 26 C (xP p) b)) ∧
      (g.op = GateOp.or → f (26 + k) = (f a || f b))) :
    f C.output = true := by
  have hV : wv 26 C (xPL p l) C.output = true := by
    have := (H2 (xPL p l)).2 ⟨p, l, H4, by simp [xPL], by simp [xPL]⟩
    exact this
  have hV0 : ¬ wv 26 C (xP p) C.output = true := by
    intro h
    obtain ⟨u, v, _, _, hv⟩ := (H2 (xP p)).1 h
    simp only [xP, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hv
    have := p.isLt
    omega
  have hVL : ¬ wv 26 C (xL l) C.output = true := by
    intro h
    obtain ⟨u, v, _, hu, _⟩ := (H2 (xL l)).1 h
    simp only [xL, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hu
    have := u.isLt
    omega
  have hout := out_lt 26 C (xPL p l) hV
  rcases (main C p l f H1 H3 H5 H6 C.output hout).2 hV with h | h | h
  · exact absurd h hV0
  · exact h
  · exact absurd h hVL

end PEqualNP.Outside.L_meta_2067

theorem PEqualNP.Outside.L_meta_2067 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (13 : ℕ)) (x5 : ℕ → Bool),   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (26 : ℕ) + x6 ∧ x10 < (26 : ℕ) + x6) →     (∀ (x7 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →       PEqualNP.TopForm.andPairs (26 : ℕ) x2 = (0 : ℕ) →         x3 - x4 ∈ x1 →           (∀ (x10 : Fin (13 : ℕ)), x5 ↑x10 = Bool.false ∧ x5 ((13 : ℕ) + ↑x10) = Decidable.decide (x10 = x4)) →             (have x11 : List Bool := x2.wires (List.ofFn fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x3));               ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x2.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x12) = (x11.getD x14 Bool.false && x5 x15 || x5 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x12) = (x5 x14 || x5 x15))) →               x5 x2.output = Bool.true := by
  intro x1 C p l f H1 H2 H3 H4 H5 H6
  exact PEqualNP.Outside.L_meta_2067.core x1 C p l f H1 H2 H3 H4 H5 H6
