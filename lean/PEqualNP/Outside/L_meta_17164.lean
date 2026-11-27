import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17164

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents PEqualNP.EdgeOwnership

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dg : Gate := ⟨GateOp.or, []⟩

lemma fold_len (gs : List Gate) (x : List Bool) :
    (gs.foldl wstep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

lemma getD_app_left (x : List Bool) (v : Bool) (i : ℕ) (hi : i < x.length) :
    (x ++ [v]).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wstep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep x g) (by simp [wstep]; omega)]
    exact getD_app_left x _ i hi

lemma fold_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j) :
    (gs.foldl wstep x).getD (x.length + j) false =
      (gs.getD j dg).op.eval ((gs.getD j dg).inputs.map fun i => (gs.foldl wstep x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have hg : (g :: gs).getD 0 dg = g := rfl
      rw [hg] at hin ⊢
      rw [Nat.add_zero, fold_low gs (wstep x g) x.length (by simp [wstep])]
      have h1 : (wstep x g).getD x.length false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [wstep, List.getD_eq_getElem?_getD]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [fold_low gs (wstep x g) i (by simp [wstep]; omega)]
      exact (getD_app_left x _ i (by omega)).symm
    | succ j =>
      have hg : (g :: gs).getD (j + 1) dg = gs.getD j dg := rfl
      rw [hg] at hin ⊢
      have hl : (wstep x g).length = x.length + 1 := by simp [wstep]
      have := ih (wstep x g) j (by simpa using hj) (by intro i hi; have := hin i hi; omega)
      rw [hl] at this
      rw [show x.length + (j + 1) = x.length + 1 + j by omega]
      exact this

lemma cfold_len (N : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep N) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cfold_low (N : ℕ) (gs : List Gate) (cs : List (List ℕ)) (i : ℕ) (hi : i < cs.length) :
    (gs.foldl (coneStep N) cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (coneStep N cs g) (by simp [coneStep]; omega)]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cfold_mem (N : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
    i ∈ (gs.foldl (coneStep N) cs).getD (cs.length + j) [] ↔
      ∃ w ∈ (gs.getD j dg).inputs, N ≤ w ∧ w < N + (cs.length + j) ∧
        (i = w - N ∨ i ∈ (gs.foldl (coneStep N) cs).getD (w - N) []) := by
  induction gs generalizing cs j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have hg : (g :: gs).getD 0 dg = g := rfl
      rw [hg, Nat.add_zero, cfold_low N gs (coneStep N cs g) cs.length (by simp [coneStep])]
      have h1 : (coneStep N cs g).getD cs.length [] =
          (g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + cs.length))).flatMap
            (fun w => (w - N) :: cs.getD (w - N) []) := by
        simp [coneStep, List.getD_eq_getElem?_getD]
      rw [h1]
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨w, hw, h1, h2, ?_⟩
        rw [cfold_low N gs (coneStep N cs g) (w - N) (by simp [coneStep]; omega)]
        simpa [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show w - N < cs.length by omega)] using h3
      · rintro ⟨w, hw, h1, h2, h3⟩
        refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
        rw [cfold_low N gs (coneStep N cs g) (w - N) (by simp [coneStep]; omega)] at h3
        simpa [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show w - N < cs.length by omega)] using h3
    | succ j =>
      have hg : (g :: gs).getD (j + 1) dg = gs.getD j dg := rfl
      rw [hg]
      have hl : (coneStep N cs g).length = cs.length + 1 := by simp [coneStep]
      have := ih (coneStep N cs g) j (by simpa using hj)
      rw [hl] at this
      rw [show cs.length + (j + 1) = cs.length + 1 + j by omega]
      exact this

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

lemma val_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    val C x w = x.getD w false :=
  fold_low C.gates x w hw

lemma val_high (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    val C x w = false := by
  unfold val
  have hl : (C.wires x).length = x.length + C.gates.length := fold_len C.gates x
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (C.wires x).length ≤ w by omega)]

def GatesOk (N : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ j < C.gates.length, (gateAt C j).inputs.length = 2 ∧ (gateAt C j).inputs.Nodup ∧
    ∀ i ∈ (gateAt C j).inputs, i < N + j

lemma gate_form {N : ℕ} {C : Circuit} (h : GatesOk N C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ p q, (gateAt C j).inputs = [p, q] ∧ p ≠ q ∧ p < N + j ∧ q < N + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  obtain ⟨hm, hg⟩ := h
  obtain ⟨hlen, hnd, hlt⟩ := hg j hj
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop := (hm _ hmem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  match hi : (gateAt C j).inputs, hlen with
  | [p, q], _ =>
    rw [hi] at hnd hlt
    refine ⟨p, q, rfl, ?_, hlt p (by simp), hlt q (by simp), hop⟩
    intro e
    subst e
    simp at hnd

lemma val_and {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.and) :
    val C x (N + j) = (val C x p && val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.and := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma val_or {N : ℕ} {C : Circuit} (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) (p q : ℕ) (hi : (gateAt C j).inputs = [p, q]) (hp : p < N + j)
    (hq : q < N + j) (hop : (gateAt C j).op = GateOp.or) :
    val C x (N + j) = (val C x p || val C x q) := by
  have h := fold_val C.gates x j hj (by
    intro i hi'
    have : (C.gates.getD j dg).inputs = [p, q] := hi
    rw [this] at hi'
    simp at hi'
    rcases hi' with rfl | rfl <;> omega)
  have e1 : (C.gates.getD j dg).inputs = [p, q] := hi
  have e2 : (C.gates.getD j dg).op = GateOp.or := hop
  rw [e1, e2, hx] at h
  unfold val
  rw [show C.wires x = C.gates.foldl wstep x from rfl, h]
  simp [GateOp.eval]

lemma loc {N : ℕ} {C : Circuit} (h : GatesOk N C) (hid : ℕ → Prop) (P : ℕ)
    (hcl : ∀ k < C.gates.length, ∀ w ∈ (gateAt C k).inputs, hid w → hid (N + k) ∨ k = P)
    (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N)
    (hin : ∀ w < N, ¬ hid w → x.getD w false = true → x'.getD w false = true)
    (hP : val C x (N + P) = true → val C x' (N + P) = true) :
    ∀ w, ¬ hid w → val C x w = true → val C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hwN : w < N
    · rw [val_input C x w (by omega)] at hv
      rw [val_input C x' w (by omega)]
      exact hin w hwN hw hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      by_cases hj : j < C.gates.length
      · by_cases hjP : j = P
        · subst hjP; exact hP hv
        · obtain ⟨p, q, hi, -, hp, hq, hop⟩ := gate_form h j hj
          have hnp : ¬ hid p := fun hh => by
            rcases hcl j hj p (by simp [hi]) hh with h1 | h1
            · exact hw h1
            · exact hjP h1
          have hnq : ¬ hid q := fun hh => by
            rcases hcl j hj q (by simp [hi]) hh with h1 | h1
            · exact hw h1
            · exact hjP h1
          rcases hop with hop | hop
          · rw [val_and x hx j hj p q hi hp hq hop, Bool.and_eq_true] at hv
            rw [val_and x' hx' j hj p q hi hp hq hop, Bool.and_eq_true]
            exact ⟨ih p hp hnp hv.1, ih q hq hnq hv.2⟩
          · rw [val_or x hx j hj p q hi hp hq hop, Bool.or_eq_true] at hv
            rw [val_or x' hx' j hj p q hi hp hq hop, Bool.or_eq_true]
            exact hv.imp (ih p hp hnp) (ih q hq hnq)
      · rw [val_high C x (N + j) (by omega)] at hv
        cases hv

lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_get {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ w = u.val ∨ w = n + v.val := by
  unfold oneEach
  by_cases hw : w < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
    simp [hw, Fin.ext_iff]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hw)]
    by_cases hw2 : w - n < m
    · simp [hw2, Fin.ext_iff]
      omega
    · simp [hw2]
      omega

def AOk {n m : ℕ} (A : Fin n → Fin m → Bool) : Prop :=
  (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v ≠ A u' v) ∧ (∀ v v' : Fin m, v ≠ v' → ∃ u, A u v ≠ A u v') ∧
  (∀ u, (∃ v, A u v = true) ∧ ∃ v, A u v = false) ∧ (∀ v, (∃ u, A u v = true) ∧ ∃ u, A u v = false) ∧
  (∀ u v, A u v = true → (∃ v', v' ≠ v ∧ A u v' = true) ∨ ∃ u', u' ≠ u ∧ A u' v = true)

def Hyp {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hid : ℕ → Prop) (P : ℕ) : Prop :=
  GatesOk (n + m) C ∧ Represents A C ∧ AOk A ∧
  (∀ k < C.gates.length, ∀ w ∈ (gateAt C k).inputs, hid w → hid (n + m + k) ∨ k = P) ∧
  ¬ hid C.output

lemma star {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (u u' : Fin n) (v v' : Fin m)
    (hg : val C (oneEach u v) (n + m + P) = true → val C (oneEach u' v') (n + m + P) = true)
    (hu : u = u' ∨ hid u.val) (hv : v = v' ∨ hid (n + v.val)) :
    A u v = true → A u' v' = true := by
  obtain ⟨hG, hrep, -, hcl, hout⟩ := h
  rw [← hrep u v, ← hrep u' v']
  refine loc hG hid P hcl (oneEach u v) (oneEach u' v') (oneEach_len u v) (oneEach_len u' v') ?_ hg
    C.output hout
  intro w _ hnw hw
  rw [oneEach_get] at hw ⊢
  rcases hw with rfl | rfl
  · rcases hu with rfl | hh
    · exact Or.inl rfl
    · exact absurd hh hnw
  · rcases hv with rfl | hh
    · exact Or.inr rfl
    · exact absurd hh hnw

lemma emptyRow {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (a : Fin n) (ha : hid a.val)
    (hg : ∀ v : Fin m, val C (oneEach a v) (n + m + P) = true → False) : False := by
  obtain ⟨v, hv⟩ := (h.2.2.1.2.2.1 a).1
  obtain ⟨u, hu⟩ := (h.2.2.1.2.2.2.1 v).2
  have := star h a u v v (fun hh => (hg v hh).elim) (Or.inr ha) (Or.inl rfl) hv
  rw [hu] at this
  cases this

lemma emptyCol {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (b : Fin m) (hb : hid (n + b.val))
    (hg : ∀ u : Fin n, val C (oneEach u b) (n + m + P) = true → False) : False := by
  obtain ⟨u, hu⟩ := (h.2.2.1.2.2.2.1 b).1
  obtain ⟨v, hv⟩ := (h.2.2.1.2.2.1 u).2
  have := star h u u b v (fun hh => (hg u hh).elim) (Or.inl rfl) (Or.inr hb) hu
  rw [hv] at this
  cases this

lemma rowOnly {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (a : Fin n) (ha : hid a.val) (v : Fin m) (hA : A a v = true) :
    val C (oneEach a v) (n + m + P) = true := by
  by_contra hg
  obtain ⟨u, hu⟩ := (h.2.2.1.2.2.2.1 v).2
  have := star h a u v v (fun hh => (hg hh).elim) (Or.inr ha) (Or.inl rfl) hA
  rw [hu] at this
  cases this

lemma colOnly {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (b : Fin m) (hb : hid (n + b.val)) (u : Fin n) (hA : A u b = true) :
    val C (oneEach u b) (n + m + P) = true := by
  by_contra hg
  obtain ⟨v, hv⟩ := (h.2.2.1.2.2.1 u).2
  have := star h u u b v (fun hh => (hg hh).elim) (Or.inl rfl) (Or.inr hb) hA
  rw [hv] at this
  cases this

lemma iso {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (a : Fin n) (ha : hid a.val) (b : Fin m) (hb : hid (n + b.val))
    (hr : ∀ v : Fin m, val C (oneEach a v) (n + m + P) = true → v = b)
    (hc : ∀ u : Fin n, val C (oneEach u b) (n + m + P) = true → u = a) : False := by
  obtain ⟨v, hv⟩ := (h.2.2.1.2.2.1 a).1
  have e := hr v (rowOnly h a ha v hv)
  subst e
  rcases h.2.2.1.2.2.2.2 a v hv with ⟨v', hne, hv'⟩ | ⟨u', hne, hu'⟩
  · exact hne (hr v' (rowOnly h a ha v' hv'))
  · exact hne (hc u' (colOnly h v hb u' hu'))

lemma twinRow {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (a a' : Fin n) (ha : hid a.val) (ha' : hid a'.val) (hne : a ≠ a')
    (hg : ∀ v : Fin m, val C (oneEach a v) (n + m + P) = val C (oneEach a' v) (n + m + P)) : False := by
  obtain ⟨v, hv⟩ := h.2.2.1.1 a a' hne
  apply hv
  have h1 := star h a a' v v (fun hh => by rw [← hg v]; exact hh) (Or.inr ha) (Or.inl rfl)
  have h2 := star h a' a v v (fun hh => by rw [hg v]; exact hh) (Or.inr ha') (Or.inl rfl)
  cases e1 : A a v <;> cases e2 : A a' v <;> simp_all

lemma twinCol {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (b b' : Fin m) (hb : hid (n + b.val)) (hb' : hid (n + b'.val)) (hne : b ≠ b')
    (hg : ∀ u : Fin n, val C (oneEach u b) (n + m + P) = val C (oneEach u b') (n + m + P)) : False := by
  obtain ⟨u, hu⟩ := h.2.2.1.2.1 b b' hne
  apply hu
  have h1 := star h u u b b' (fun hh => by rw [← hg u]; exact hh) (Or.inl rfl) (Or.inr hb)
  have h2 := star h u u b' b (fun hh => by rw [hg u]; exact hh) (Or.inl rfl) (Or.inr hb')
  cases e1 : A u b <;> cases e2 : A u b' <;> simp_all

def Desc {n m : ℕ} (C : Circuit) (hid : ℕ → Prop) (w : ℕ) (r : Option (Fin n))
    (c : Option (Fin m)) : Prop :=
  (∀ u v, val C (oneEach u v) w = true ↔ (r = some u ∨ c = some v)) ∧
  (∀ a, r = some a → hid a.val) ∧ (∀ b, c = some b → hid (n + b.val)) ∧ (r ≠ none ∨ c ≠ none)

lemma notOut {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} (hrep : Represents A C)
    (hA : AOk A) (hid : ℕ → Prop) (r : Option (Fin n)) (c : Option (Fin m))
    (hd : Desc C hid C.output r c) : False := by
  obtain ⟨hv, -, -, hne⟩ := hd
  have key : ∀ u v, A u v = true ↔ (r = some u ∨ c = some v) := fun u v => by
    rw [← hrep u v]; exact hv u v
  cases r with
  | some a =>
    obtain ⟨v, hv'⟩ := (hA.2.2.1 a).2
    have := (key a v).2 (Or.inl rfl)
    rw [hv'] at this
    cases this
  | none =>
    cases c with
    | some b =>
      obtain ⟨u, hu'⟩ := (hA.2.2.2.1 b).2
      have := (key u b).2 (Or.inr rfl)
      rw [hu'] at this
      cases this
    | none => simp at hne

lemma comb {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {hid : ℕ → Prop} {P : ℕ}
    (h : Hyp A C hid P) (hP : P < C.gates.length) (w1 w2 : ℕ)
    (hi : (gateAt C P).inputs = [w1, w2])
    (r1 r2 : Option (Fin n)) (c1 c2 : Option (Fin m))
    (d1 : Desc C hid w1 r1 c1) (d2 : Desc C hid w2 r2 c2)
    (hr : ∀ a, r1 = some a → r2 ≠ some a) (hc : ∀ b, c1 = some b → c2 ≠ some b) :
    (gateAt C P).op = GateOp.or ∧
      ((∃ a b, r1 = some a ∧ c1 = none ∧ r2 = none ∧ c2 = some b) ∨
       (∃ a b, r1 = none ∧ c1 = some b ∧ r2 = some a ∧ c2 = none)) := by
  obtain ⟨p, q, hi', -, hp, hq, hop⟩ := gate_form h.1 P hP
  rw [hi] at hi'
  obtain ⟨rfl, rfl⟩ : w1 = p ∧ w2 = q := by simpa using hi'
  obtain ⟨v1, hr1, hc1, n1⟩ := d1
  obtain ⟨v2, hr2, hc2, n2⟩ := d2
  rcases hop with hop | hop
  · exfalso
    have g : ∀ u v, val C (oneEach u v) (n + m + P) = true ↔
        ((r1 = some u ∨ c1 = some v) ∧ (r2 = some u ∨ c2 = some v)) := fun u v => by
      rw [val_and _ (oneEach_len u v) P hP w1 w2 hi hp hq hop, Bool.and_eq_true, v1, v2]
    cases r1 with
    | some a =>
      have hra : r2 ≠ some a := hr a rfl
      cases c2 with
      | none =>
        refine emptyRow h a (hr1 a rfl) fun v hv => ?_
        have := (g a v).1 hv
        simp [hra] at this
      | some b' =>
        have hcb : c1 ≠ some b' := fun e => hc b' e rfl
        refine iso h a (hr1 a rfl) b' (hc2 b' rfl) (fun v hv => ?_) (fun u hu => ?_)
        · have := ((g a v).1 hv).2
          exact (by simpa [hra] using this : b' = v).symm
        · have := ((g u b').1 hu).1
          exact (by simpa [hcb] using this : a = u).symm
    | none =>
      cases c1 with
      | none => simp at n1
      | some b =>
        have hcb : c2 ≠ some b := hc b rfl
        cases r2 with
        | none =>
          refine emptyCol h b (hc1 b rfl) fun u hu => ?_
          have := (g u b).1 hu
          simp [hcb] at this
        | some a' =>
          refine iso h a' (hr2 a' rfl) b (hc1 b rfl) (fun v hv => ?_) (fun u hu => ?_)
          · have := ((g a' v).1 hv).1
            exact (by simpa using this : b = v).symm
          · have := ((g u b).1 hu).2
            exact (by simpa [hcb] using this : a' = u).symm
  · refine ⟨hop, ?_⟩
    have g : ∀ u v, val C (oneEach u v) (n + m + P) = true ↔
        ((r1 = some u ∨ c1 = some v) ∨ (r2 = some u ∨ c2 = some v)) := fun u v => by
      rw [val_or _ (oneEach_len u v) P hP w1 w2 hi hp hq hop, Bool.or_eq_true, v1, v2]
    have gb : ∀ (u : Fin n) (v : Fin m) (u' : Fin n) (v' : Fin m),
        (val C (oneEach u v) (n + m + P) = true ↔ val C (oneEach u' v') (n + m + P) = true) →
        val C (oneEach u v) (n + m + P) = val C (oneEach u' v') (n + m + P) := fun u v u' v' hh => by
      cases e1 : val C (oneEach u v) (n + m + P) <;> cases e2 : val C (oneEach u' v') (n + m + P) <;>
        simp_all
    cases r1 with
    | some a =>
      cases r2 with
      | some a' =>
        exfalso
        have hne : a ≠ a' := fun e => hr a rfl (by rw [e])
        exact twinRow h a a' (hr1 a rfl) (hr2 a' rfl) hne fun v => gb _ _ _ _ (by
          rw [g, g]; simp)
      | none =>
        cases c2 with
        | none => simp at n2
        | some b =>
          cases c1 with
          | none => exact Or.inl ⟨a, b, rfl, rfl, rfl, rfl⟩
          | some b0 =>
            exfalso
            have hne : b0 ≠ b := fun e => hc b0 rfl (by rw [e])
            exact twinCol h b0 b (hc1 b0 rfl) (hc2 b rfl) hne fun u => gb _ _ _ _ (by
              rw [g, g]; simp)
    | none =>
      cases c1 with
      | none => simp at n1
      | some b =>
        cases c2 with
        | some b' =>
          exfalso
          have hne : b ≠ b' := fun e => hc b rfl (by rw [e])
          exact twinCol h b b' (hc1 b rfl) (hc2 b' rfl) hne fun u => gb _ _ _ _ (by
            rw [g, g]; simp)
        | none =>
          cases r2 with
          | none => simp at n2
          | some a => exact Or.inr ⟨a, b, rfl, rfl, rfl, rfl⟩

def Once (C : Circuit) (w : ℕ) : Prop :=
  ((Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs).card = 1

lemma once_unique {C : Circuit} {w : ℕ} (h : Once C w) {k1 k2 : ℕ} (h1 : k1 < C.gates.length)
    (m1 : w ∈ (gateAt C k1).inputs) (h2 : k2 < C.gates.length) (m2 : w ∈ (gateAt C k2).inputs) :
    k1 = k2 := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  have a1 : k1 ∈ (Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs := by
    simp [h1, m1]
  have a2 : k2 ∈ (Finset.range C.gates.length).filter fun k => w ∈ (gateAt C k).inputs := by
    simp [h2, m2]
  rw [hx] at a1 a2
  simp only [Finset.mem_singleton] at a1 a2
  omega

lemma inCone_iff (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (i : ℕ) :
    InCone N C i j ↔ ∃ w ∈ (gateAt C j).inputs, N ≤ w ∧ w < N + j ∧
      (i = w - N ∨ InCone N C i (w - N)) := by
  have := cfold_mem N C.gates [] j hj i
  simpa [InCone, cones, gateAt, dg] using this

def HG (N : ℕ) (C : Circuit) (g : ℕ) : Prop :=
  ∀ w, (w ∈ (gateAt C g).inputs ∨ ∃ i, InCone N C i g ∧ w ∈ (gateAt C i).inputs) → Once C w

lemma HG_child {N : ℕ} {C : Circuit} {g : ℕ} (hg : g < C.gates.length) (h : HG N C g) (w : ℕ)
    (hw : w ∈ (gateAt C g).inputs) (h1 : N ≤ w) (h2 : w < N + g) : HG N C (w - N) := by
  intro w' hw'
  apply h w'
  right
  rcases hw' with hw' | ⟨i, hi, hw'⟩
  · exact ⟨w - N, (inCone_iff N C g hg _).2 ⟨w, hw, h1, h2, Or.inl rfl⟩, hw'⟩
  · exact ⟨i, (inCone_iff N C g hg _).2 ⟨w, hw, h1, h2, Or.inr hi⟩, hw'⟩

def Goal (n m : ℕ) (C : Circuit) (g : ℕ) : Prop :=
  (gateAt C g).op = GateOp.or ∧ ∃ a b, a < n ∧ n ≤ b ∧ b < n + m ∧
    (gateAt C g).inputs.toFinset = {a, b}

lemma desc_var {n m : ℕ} (C : Circuit) (hid : ℕ → Prop) (w : ℕ) (hw : w < n + m) (hh : hid w) :
    ∃ (r : Option (Fin n)) (c : Option (Fin m)), Desc C hid w r c ∧
      (c = none → ∃ a, r = some a ∧ w = a.val) ∧ (r = none → ∃ b, c = some b ∧ w = n + b.val) ∧
      (∀ a, r = some a → w = a.val) ∧ (∀ b, c = some b → w = n + b.val) := by
  by_cases hwn : w < n
  · refine ⟨some ⟨w, hwn⟩, none, ⟨fun u v => ?_, ?_, ?_, Or.inl (by simp)⟩, ?_, ?_, ?_, ?_⟩
    · rw [val_input C _ w (by rw [oneEach_len]; exact hw), oneEach_get]
      simp [Fin.ext_iff]
      omega
    · rintro a ⟨rfl⟩; exact hh
    · intro b hb; cases hb
    · intro _; exact ⟨⟨w, hwn⟩, rfl, rfl⟩
    · intro hb; cases hb
    · rintro a ⟨rfl⟩; rfl
    · intro b hb; cases hb
  · have hwm : w - n < m := by omega
    refine ⟨none, some ⟨w - n, hwm⟩, ⟨fun u v => ?_, ?_, ?_, Or.inr (by simp)⟩, ?_, ?_, ?_, ?_⟩
    · rw [val_input C _ w (by rw [oneEach_len]; exact hw), oneEach_get]
      simp [Fin.ext_iff]
      omega
    · intro a ha; cases ha
    · rintro b ⟨rfl⟩
      have : n + (w - n) = w := by omega
      simpa [this] using hh
    · intro hb; cases hb
    · intro _; exact ⟨⟨w - n, hwm⟩, rfl, by simp; omega⟩
    · intro a ha; cases ha
    · rintro b ⟨rfl⟩; simp; omega

lemma desc_gate {n m : ℕ} (C : Circuit) (hG : GatesOk (n + m) C) (hid : ℕ → Prop) (i : ℕ)
    (hi : i < C.gates.length) (hgoal : Goal n m C i)
    (hh : ∀ w ∈ (gateAt C i).inputs, hid w) :
    ∃ (r : Option (Fin n)) (c : Option (Fin m)), Desc C hid (n + m + i) r c ∧
      (c = none → False) ∧ (r = none → False) ∧
      (∀ a, r = some a → a.val ∈ (gateAt C i).inputs) ∧
      (∀ b, c = some b → n + b.val ∈ (gateAt C i).inputs) := by
  obtain ⟨hop, a, b, ha, hb1, hb2, hset⟩ := hgoal
  obtain ⟨p, q, hpq, hne, hp, hq, -⟩ := gate_form hG i hi
  rw [hpq] at hset
  have hmem : ∀ x, x ∈ [p, q] ↔ x = a ∨ x = b := fun x => by
    have := congrArg (fun S => x ∈ S) hset
    simpa using this
  have hpa := (hmem p).1 (by simp)
  have hqa := (hmem q).1 (by simp)
  have haIn := (hmem a).2 (Or.inl rfl)
  have hbIn := (hmem b).2 (Or.inr rfl)
  have hbm : b - n < m := by omega
  have hpN : p < n + m := by rcases hpa with rfl | rfl <;> omega
  have hqN : q < n + m := by rcases hqa with rfl | rfl <;> omega
  refine ⟨some ⟨a, ha⟩, some ⟨b - n, hbm⟩, ⟨fun u v => ?_, ?_, ?_, Or.inl (by simp)⟩, ?_, ?_, ?_, ?_⟩
  · rw [val_or _ (oneEach_len u v) i hi p q hpq hp hq hop, Bool.or_eq_true,
      val_input C _ p (by rw [oneEach_len]; exact hpN), val_input C _ q (by rw [oneEach_len]; exact hqN),
      oneEach_get, oneEach_get]
    simp only [Option.some.injEq, Fin.ext_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at haIn hbIn
    constructor
    · rintro (h | h)
      · rcases hpa with rfl | rfl <;> rcases h with h | h <;> first | (left; omega) | (right; omega)
      · rcases hqa with rfl | rfl <;> rcases h with h | h <;> first | (left; omega) | (right; omega)
    · rintro (h | h)
      · rcases haIn with e | e
        · left; left; omega
        · right; left; omega
      · rcases hbIn with e | e
        · left; right; omega
        · right; right; omega
  · rintro x ⟨rfl⟩
    exact hh a (by rw [hpq]; exact haIn)
  · rintro x ⟨rfl⟩
    have : n + (b - n) = b := by omega
    simpa [this] using hh b (by rw [hpq]; exact hbIn)
  · intro hc; cases hc
  · intro hc; cases hc
  · rintro x ⟨rfl⟩
    rw [hpq]; exact haIn
  · rintro x ⟨rfl⟩
    have : n + (b - n) = b := by omega
    rw [hpq]; simpa [this] using hbIn

theorem main {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hG : GatesOk (n + m) C)
    (hrep : Represents A C) (hA : AOk A) :
    ∀ g, g < C.gates.length → HG (n + m) C g → Goal n m C g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg hH
    obtain ⟨p, q, hpq, hne, hp, hq, -⟩ := gate_form hG g hg
    let hid : ℕ → Prop := fun w => w = p ∨ w = q ∨
      ∃ i, (n + m + i = p ∨ n + m + i = q) ∧ i < g ∧ w ∈ (gateAt C i).inputs
    have hpin : p ∈ (gateAt C g).inputs := by rw [hpq]; simp
    have hqin : q ∈ (gateAt C g).inputs := by rw [hpq]; simp
    have child : ∀ w, (w = p ∨ w = q) → n + m ≤ w →
        Goal n m C (w - (n + m)) ∧ w - (n + m) < g := by
      intro w hw hN
      have hwg : w < n + m + g := by rcases hw with rfl | rfl <;> assumption
      have hwin : w ∈ (gateAt C g).inputs := by rcases hw with rfl | rfl <;> assumption
      exact ⟨ih (w - (n + m)) (by omega) (by omega) (HG_child hg hH w hwin hN hwg), by omega⟩
    have D : ∀ w, (w = p ∨ w = q) → ∃ (r : Option (Fin n)) (c : Option (Fin m)),
        Desc C hid w r c ∧
        (c = none → ∃ a, r = some a ∧ w = a.val) ∧ (r = none → ∃ b, c = some b ∧ w = n + b.val) ∧
        (∀ a, r = some a → w = a.val ∨
          (n + m ≤ w ∧ a.val ∈ (gateAt C (w - (n + m))).inputs)) ∧
        (∀ b, c = some b → w = n + b.val ∨
          (n + m ≤ w ∧ n + b.val ∈ (gateAt C (w - (n + m))).inputs)) := by
      intro w hw
      have hhw : hid w := by
        rcases hw with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      by_cases hN : w < n + m
      · obtain ⟨r, c, d, h1, h2, h3, h4⟩ := desc_var (n := n) (m := m) C hid w hN hhw
        exact ⟨r, c, d, h1, h2, fun a ha => Or.inl (h3 a ha), fun b hb => Or.inl (h4 b hb)⟩
      · have hN' : n + m ≤ w := by omega
        obtain ⟨hgoal, hlt⟩ := child w hw hN'
        have hil : w - (n + m) < C.gates.length := by omega
        have e : n + m + (w - (n + m)) = w := by omega
        obtain ⟨r, c, d, h1, h2, h3, h4⟩ := desc_gate C hG hid (w - (n + m)) hil hgoal (by
          intro x hx
          refine Or.inr (Or.inr ⟨w - (n + m), ?_, hlt, hx⟩)
          rw [e]; exact hw)
        rw [e] at d
        exact ⟨r, c, d, fun hc => (h1 hc).elim, fun hr => (h2 hr).elim,
          fun a ha => Or.inr ⟨hN', h3 a ha⟩, fun b hb => Or.inr ⟨hN', h4 b hb⟩⟩
    have hcl : ∀ k < C.gates.length, ∀ w ∈ (gateAt C k).inputs, hid w →
        hid (n + m + k) ∨ k = g := by
      intro k hk w hwk hw
      rcases hw with rfl | rfl | ⟨i, hi, hig, hwi⟩
      · exact Or.inr (once_unique (hH _ (Or.inl hpin)) hk hwk hg hpin)
      · exact Or.inr (once_unique (hH _ (Or.inl hqin)) hk hwk hg hqin)
      · have hcone : InCone (n + m) C i g := by
          refine (inCone_iff (n + m) C g hg i).2
            ⟨n + m + i, ?_, by omega, by omega, Or.inl (by omega)⟩
          rcases hi with e | e <;> rw [e] <;> assumption
        have hik : k = i :=
          once_unique (hH w (Or.inr ⟨i, hcone, hwi⟩)) hk hwk (by omega) hwi
        subst hik
        left
        rcases hi with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
    have hout : ¬ hid C.output := by
      intro ho
      rcases ho with e | e | ⟨i, hi, hig, hwi⟩
      · obtain ⟨r, c, d, -⟩ := D p (Or.inl rfl)
        rw [← e] at d
        exact notOut hrep hA hid r c d
      · obtain ⟨r, c, d, -⟩ := D q (Or.inr rfl)
        rw [← e] at d
        exact notOut hrep hA hid r c d
      · obtain ⟨hgoal, -⟩ := child (n + m + i) (by
          rcases hi with e | e
          · exact Or.inl e
          · exact Or.inr e) (by omega)
        have e : n + m + i - (n + m) = i := by omega
        rw [e] at hgoal
        obtain ⟨-, a, b, ha, hb1, hb2, hset⟩ := hgoal
        have hmem : C.output ∈ ({a, b} : Finset ℕ) := by
          rw [← hset]; exact List.mem_toFinset.mpr hwi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        have hlt : C.output < n + m := by rcases hmem with e | e <;> omega
        obtain ⟨r, c, d, -⟩ := desc_var (n := n) (m := m) C hid C.output hlt
          (Or.inr (Or.inr ⟨i, hi, hig, hwi⟩))
        exact notOut hrep hA hid r c d
    have hyp : Hyp A C hid g := ⟨hG, hrep, hA, hcl, hout⟩
    have noShare : ∀ x, (p = x ∨ (n + m ≤ p ∧ x ∈ (gateAt C (p - (n + m))).inputs)) →
        (q = x ∨ (n + m ≤ q ∧ x ∈ (gateAt C (q - (n + m))).inputs)) → False := by
      intro x hp' hq'
      rcases hp' with e1 | ⟨hpN, hxp⟩ <;> rcases hq' with e2 | ⟨hqN, hxq⟩
      · exact hne (e1.trans e2.symm)
      · subst e1
        have := once_unique (hH p (Or.inl hpin)) hg hpin
          (show q - (n + m) < C.gates.length by omega) hxq
        omega
      · subst e2
        have := once_unique (hH q (Or.inl hqin)) hg hqin
          (show p - (n + m) < C.gates.length by omega) hxp
        omega
      · have hcone : InCone (n + m) C (p - (n + m)) g :=
          (inCone_iff _ C g hg _).2 ⟨p, hpin, hpN, hp, Or.inl rfl⟩
        have := once_unique (hH x (Or.inr ⟨_, hcone, hxp⟩))
          (show p - (n + m) < C.gates.length by omega) hxp
          (show q - (n + m) < C.gates.length by omega) hxq
        omega
    obtain ⟨r1, c1, d1, k1, k1', m1, m1'⟩ := D p (Or.inl rfl)
    obtain ⟨r2, c2, d2, k2, k2', m2, m2'⟩ := D q (Or.inr rfl)
    have hr : ∀ a, r1 = some a → r2 ≠ some a := fun a h1 h2 => noShare a.val (m1 a h1) (m2 a h2)
    have hc : ∀ b, c1 = some b → c2 ≠ some b := fun b h1 h2 =>
      noShare (n + b.val) (m1' b h1) (m2' b h2)
    obtain ⟨hop, hcase⟩ := comb hyp hg p q hpq r1 r2 c1 c2 d1 d2 hr hc
    refine ⟨hop, ?_⟩
    rcases hcase with ⟨a, b, e1, e2, e3, e4⟩ | ⟨a, b, e1, e2, e3, e4⟩
    · obtain ⟨a', -, hpa⟩ := k1 e2
      obtain ⟨b', -, hqb⟩ := k2' e3
      refine ⟨p, q, by omega, by omega, by omega, ?_⟩
      rw [hpq]; simp
    · obtain ⟨b', -, hpb⟩ := k1' e1
      obtain ⟨a', -, hqa⟩ := k2 e4
      refine ⟨q, p, by omega, by omega, by omega, ?_⟩
      rw [hpq]; simp [Finset.pair_comm]

end PEqualNP.Outside.L_meta_17164

theorem PEqualNP.Outside.L_meta_17164 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Nodup ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i < n + m + j) → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v ≠ A u' v) → (∀ v v' : Fin m, v ≠ v' → ∃ u, A u v ≠ A u v') → (∀ u, (∃ v, A u v = true) ∧ ∃ v, A u v = false) → (∀ v, (∃ u, A u v = true) ∧ ∃ u, A u v = false) → (∀ u v, A u v = true → (∃ v', v' ≠ v ∧ A u v' = true) ∨ ∃ u', u' ≠ u ∧ A u' v = true) → g < C.gates.length → (∀ w, (w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs ∨ ∃ i, PEqualNP.EdgeOwnership.InCone (n + m) C i g ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs) → ((Finset.range C.gates.length).filter fun k => w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs).card = 1) → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b, a < n ∧ n ≤ b ∧ b < n + m ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset = {a, b} := by
  intro n m A C g hm hrep hgates hrd hcd hrn hcn hiso hg hH
  exact PEqualNP.Outside.L_meta_17164.main A C ⟨hm, hgates⟩ hrep ⟨hrd, hcd, hrn, hcn, hiso⟩ g hg hH
