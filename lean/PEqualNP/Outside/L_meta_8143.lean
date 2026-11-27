import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8143

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The generators and orbit routing table come from L_meta_4059.

-- Points are 0..12, lines are 13..25. Point p lies on line l when p - l is in 0, 1, 3, 9 mod 13.
def inD (n : ℕ) : Bool := n == 0 || n == 1 || n == 3 || n == 9

def rel (u v : Fin 26) : Bool :=
  (decide (u.val < 13) && decide (13 ≤ v.val) && inD ((u.val + 26 - v.val) % 13)) ||
  (decide (v.val < 13) && decide (13 ≤ u.val) && inD ((v.val + 26 - u.val) % 13))

-- Three automorphisms: the shift by one, the polarity, and one collineation fixing point 0.
def fwd : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13], [13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25]]
def bwd : List (List ℕ) := [[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24], [13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25]]
def gf (i : ℕ) (u : Fin 26) : Fin 26 := Fin.ofNat 26 ((fwd.getD i []).getD u.val 0)
def gb (i : ℕ) (u : Fin 26) : Fin 26 := Fin.ofNat 26 ((bwd.getD i []).getD u.val 0)

-- For each ordered pair, which automorphism to apply next on the way to a base pair.
def tbl : List (List ℕ) := [
  [0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0],
  [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 2, 2, 2, 0, 0, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 0],
  [1, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 2, 1, 1, 0, 0, 1, 0, 1, 0, 2, 2, 1, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0],
  [0, 2, 1, 0, 2, 2, 0, 0, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1],
  [0, 0, 2, 1, 1, 2, 1, 0, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 2],
  [1, 0, 2, 2, 0, 1, 0, 0, 2, 1, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2],
  [1, 2, 0, 0, 1, 2, 2, 0, 0, 2, 1, 2, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0],
  [2, 0, 2, 0, 0, 0, 1, 2, 2, 0, 0, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0],
  [0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0, 2, 1, 0, 1, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0],
  [1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 0, 1, 1, 0, 1, 0, 2, 2, 0, 0, 2, 0, 0, 0, 2],
  [2, 2, 0, 1, 2, 0, 2, 2, 0, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0],
  [0, 2, 0, 2, 1, 0, 0, 2, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 1, 1, 2, 2, 0, 1, 2, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1],
  [1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 2, 0],
  [0, 1, 0, 0, 2, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2, 2, 1, 0, 1, 2, 0, 0, 2, 0],
  [2, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 1, 0, 2, 2, 0, 2],
  [0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 1, 1, 0, 0, 2, 2, 2, 1, 1, 1, 0],
  [1, 0, 0, 1, 2, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 0, 0],
  [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 1, 2, 1, 2, 2, 2, 0],
  [0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 2, 0, 0, 2, 1, 1],
  [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1],
  [2, 2, 1, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 1, 2, 1, 1, 1, 2, 2],
  [0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 2, 2, 0, 0, 1, 2],
  [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0, 1, 1, 1, 2, 0, 0, 2],
  [0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 2, 1, 1, 0, 0]]
def nxt (a b : Fin 26) : ℕ := (tbl.getD a.val []).getD b.val 0

def base (a b : Fin 26) : Bool := a == 0 && (b == 0 || b == 1 || b == 14)

def reach : ℕ → Fin 26 → Fin 26 → Bool
  | 0, a, b => base a b
  | n + 1, a, b => base a b || reach n (gf (nxt a b) a) (gf (nxt a b) b)

theorem left_ok : ∀ i : Fin 3, ∀ u : Fin 26, gb i.val (gf i.val u) = u := by decide +kernel
theorem right_ok : ∀ i : Fin 3, ∀ u : Fin 26, gf i.val (gb i.val u) = u := by decide +kernel
theorem rel_ok : ∀ i : Fin 3, ∀ u v : Fin 26, rel (gf i.val u) (gf i.val v) = rel u v := by
  decide +kernel
theorem nxt_lt : ∀ a b : Fin 26, nxt a b < 3 := by decide +kernel
theorem reach_ok : ∀ a b : Fin 26, rel a b = false → reach 11 a b = true := by decide +kernel

def perm (i : Fin 3) : Equiv.Perm (Fin 26) := ⟨gf i.val, gb i.val, left_ok i, right_ok i⟩

lemma orbit (n : ℕ) (a b : Fin 26) (h : reach n a b = true) :
    ∃ π : Equiv.Perm (Fin 26), (∀ u v, rel (π u) (π v) = rel u v) ∧
      π a = 0 ∧ (π b = 0 ∨ π b = 1 ∨ π b = 14) := by
  have atBase (u v : Fin 26) (hb : base u v = true) :
      ∃ π : Equiv.Perm (Fin 26), (∀ s t, rel (π s) (π t) = rel s t) ∧
        π u = 0 ∧ (π v = 0 ∨ π v = 1 ∨ π v = 14) := by
    have huv : (u = 0) ∧ ((v = 0 ∨ v = 1) ∨ v = 14) := by
      simpa only [base, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hb
    exact ⟨Equiv.refl _, fun _ _ => rfl, huv.1, or_assoc.mp huv.2⟩
  induction n generalizing a b with
  | zero => exact atBase a b h
  | succ n ih =>
    simp only [reach, Bool.or_eq_true] at h
    rcases h with hb | hr
    · exact atBase a b hb
    · obtain ⟨π, hπ, ha, hb⟩ := ih _ _ hr
      let i : Fin 3 := ⟨nxt a b, nxt_lt a b⟩
      refine ⟨(perm i).trans π, ?_, ha, hb⟩
      intro u v
      change rel (π (gf i.val u)) (π (gf i.val v)) = rel u v
      rw [hπ, rel_ok]

def differences : Finset (Fin 13) := {0, 1, 3, 9}

def pairInput (a b u : Fin 26) : Bool := decide (u = a ∨ u = b)

def hasEdge (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, p - l ∈ differences ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def endpoint (u : Fin 26) : Fin 13 := Fin.ofNat 13 u.val

lemma rel_points : ∀ p l : Fin 13,
    rel (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true ↔ p - l ∈ differences := by
  decide +kernel

lemma rel_endpoints : ∀ u v : Fin 26, rel u v = true →
    (u = Fin.castAdd 13 (endpoint u) ∧ v = Fin.natAdd 13 (endpoint v)) ∨
    (v = Fin.castAdd 13 (endpoint v) ∧ u = Fin.natAdd 13 (endpoint u)) := by
  decide +kernel

lemma rel_symm (u v : Fin 26) : rel u v = rel v u := by
  simp only [rel, Bool.or_comm]

lemma hasEdge_iff (x : Fin 26 → Bool) :
    hasEdge x ↔ ∃ u v : Fin 26, rel u v = true ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨p, l, h, hp, hl⟩
    exact ⟨_, _, (rel_points p l).2 h, hp, hl⟩
  · rintro ⟨u, v, h, hu, hv⟩
    rcases rel_endpoints u v h with ⟨hup, hvl⟩ | ⟨hvp, hul⟩
    · refine ⟨endpoint u, endpoint v, (rel_points _ _).1 ?_, hup ▸ hu, hvl ▸ hv⟩
      conv at h => lhs; rw [hup, hvl]
      exact h
    · refine ⟨endpoint v, endpoint u, (rel_points _ _).1 ?_, hvp ▸ hv, hul ▸ hu⟩
      rw [rel_symm u v] at h
      conv at h => lhs; rw [hvp, hul]
      exact h

lemma hasEdge_perm (π : Equiv.Perm (Fin 26)) (hπ : ∀ u v, rel (π u) (π v) = rel u v)
    (x : Fin 26 → Bool) : hasEdge (x ∘ ⇑π) ↔ hasEdge x := by
  rw [hasEdge_iff, hasEdge_iff]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    exact ⟨π u, π v, (hπ u v).trans h, hu, hv⟩
  · rintro ⟨u, v, h, hu, hv⟩
    have hr := hπ (π.symm u) (π.symm v)
    simp only [Equiv.apply_symm_apply] at hr
    exact ⟨π.symm u, π.symm v, hr.symm.trans h,
      by simpa using hu, by simpa using hv⟩

lemma pairInput_perm (π : Equiv.Perm (Fin 26)) (a b : Fin 26) :
    pairInput (π a) (π b) ∘ ⇑π = pairInput a b := by
  funext u
  apply decide_eq_decide.mpr
  simp

-- The wire relabeling follows L_meta_6848.

def permWire (n : ℕ) (π : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then ↑(π ⟨w, h⟩) else w

def permGate (n : ℕ) (π : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (permWire n π) }

def permCircuit (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permGate n π), output := permWire n π C.output }

lemma permWire_lt (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    permWire n π w < n := by
  simp only [permWire, h, ↓reduceDIte]
  exact (π ⟨w, h⟩).isLt

lemma permWire_ge (n : ℕ) (π : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) :
    permWire n π w = w := by
  have hlt : ¬ w < n := Nat.not_lt.mpr h
  simp only [permWire, hlt, ↓reduceDIte]

lemma getD_append_singleton_lt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i dflt = l.getD i dflt := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_singleton_eq {α : Type*} (l : List α) (v dflt : α) :
    (l ++ [v]).getD l.length dflt = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

lemma getD_append_singleton_gt {α : Type*} (l : List α) (v dflt : α) {i : ℕ} (h : l.length < i) :
    (l ++ [v]).getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD]
  have hge : (l ++ [v]).length ≤ i := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [List.getElem?_eq_none hge]
  rfl

lemma getD_ge_length {α : Type*} (l : List α) (dflt : α) {i : ℕ} (h : l.length ≤ i) :
    l.getD i dflt = dflt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma map_permGate_getD {α : Type*} (n : ℕ) (π : Equiv.Perm (Fin n)) (dflt : α)
    (g : Gate) (acc5 acc1 : List α)
    (hacc : ∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) :
    ((permGate n π g).inputs.map fun i => acc5.getD i dflt) =
      g.inputs.map fun i => acc1.getD i dflt := by
  simp only [permGate, List.map_map, Function.comp_def, hacc]

lemma foldl_perm_eq {α : Type*} (n : ℕ) (π : Equiv.Perm (Fin n)) (dflt : α)
    (val : Gate → List α → α)
    (hval : ∀ g (acc5 acc1 : List α),
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      val (permGate n π g) acc5 = val g acc1)
    (gs : List Gate) :
    ∀ (acc5 acc1 : List α),
      acc5.length = acc1.length →
      n ≤ acc1.length →
      (∀ w, acc5.getD (permWire n π w) dflt = acc1.getD w dflt) →
      ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).length =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).length ∧
      ∀ w, ((gs.map (permGate n π)).foldl (fun acc g => acc ++ [val g acc]) acc5).getD
        (permWire n π w) dflt =
        (gs.foldl (fun acc g => acc ++ [val g acc]) acc1).getD w dflt := by
  induction gs with
  | nil =>
    intro acc5 acc1 hlen _ hacc
    exact ⟨hlen, hacc⟩
  | cons g t ih =>
    intro acc5 acc1 hlen hn hacc
    simp only [List.map_cons, List.foldl_cons]
    have hv : val (permGate n π g) acc5 = val g acc1 := hval g acc5 acc1 hacc
    rw [hv]
    apply ih
    · simp only [List.length_append, List.length_singleton, hlen]
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro w
      rcases Nat.lt_trichotomy w acc1.length with hwlt | rfl | hwgt
      · have hpwlt : permWire n π w < acc5.length := by
          by_cases hwn : w < n
          · have h1 := permWire_lt n π hwn
            omega
          · rw [permWire_ge n π (Nat.le_of_not_lt hwn)]
            omega
        rw [getD_append_singleton_lt acc5 _ dflt hpwlt,
            getD_append_singleton_lt acc1 _ dflt hwlt, hacc w]
      · have hpweq : permWire n π acc1.length = acc1.length := permWire_ge n π hn
        rw [hpweq, ← hlen, getD_append_singleton_eq, hlen, getD_append_singleton_eq]
      · have hpwgt : acc5.length < permWire n π w := by
          have hnw : n ≤ w := by omega
          rw [permWire_ge n π hnw]
          omega
        rw [getD_append_singleton_gt acc5 _ dflt hpwgt,
            getD_append_singleton_gt acc1 _ dflt hwgt]

lemma wires_permCircuit (C : Circuit) (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    ∀ w, ((permCircuit n π C).wires (List.ofFn x)).getD (permWire n π w) false = (C.wires (List.ofFn (x ∘ ⇑π))).getD w false := by
  unfold Circuit.wires
  intro w
  change ((C.gates.map (permGate n π)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD (permWire n π w) false =
    (C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (x ∘ ⇑π))).getD w false
  have h := foldl_perm_eq n π false
    (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false))
    (fun g acc5 acc1 hacc => by
      rw [map_permGate_getD n π false g acc5 acc1 hacc]
      rfl)
    C.gates
    (List.ofFn x)
    (List.ofFn (x ∘ ⇑π))
    (by simp)
    (by simp)
    (by
      intro w
      by_cases hw : w < n
      · have hpw : permWire n π w = (π ⟨w, hw⟩).val := by simp [permWire, hw]
        have hpwlt : (π ⟨w, hw⟩).val < n := (π ⟨w, hw⟩).isLt
        rw [hpw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        simp [hpwlt, hw]
      · have hnw : n ≤ w := Nat.le_of_not_lt hw
        rw [permWire_ge n π hnw, getD_ge_length _ false (by simp; exact hnw),
            getD_ge_length _ false (by simp; exact hnw)])
  exact h.2 w

lemma permCircuit_mono (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit)
    (h : Monotone2 C) : Monotone2 (permCircuit n π C) := by
  intro g hg
  change g ∈ C.gates.map (permGate n π) at hg
  obtain ⟨oldGate, holdGate, rfl⟩ := List.mem_map.mp hg
  simpa [permGate] using h oldGate holdGate

lemma permCircuit_readsBack (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit)
    (h : ReadsBack n C) : ReadsBack n (permCircuit n π C) := by
  intro j hj i hi
  have hjC : j < C.gates.length := by simpa [permCircuit] using hj
  have hg : gateAt (permCircuit n π C) j = permGate n π (gateAt C j) := by
    unfold gateAt
    change (C.gates.map (permGate n π)).getD j _ = permGate n π (C.gates.getD j _)
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjC]
  rw [hg] at hi
  change i ∈ (gateAt C j).inputs.map (permWire n π) at hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
  by_cases hlt : w < n
  · have := permWire_lt n π hlt
    omega
  · rw [permWire_ge n π (Nat.le_of_not_lt hlt)]
    exact h j hjC w hw

lemma append_mono (a b : List Bool) (ha : a.length = b.length) (v z : Bool)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hvz : v = true → z = true) :
    ∀ i, (a ++ [v]).getD i false = true → (b ++ [z]).getD i false = true := by
  intro i
  rcases Nat.lt_trichotomy i a.length with hi | rfl | hi
  · have hib : i < b.length := ha ▸ hi
    rw [getD_append_singleton_lt _ _ _ hi, getD_append_singleton_lt _ _ _ hib]
    exact hab i
  · rw [getD_append_singleton_eq]
    conv => rhs; lhs; rw [ha, getD_append_singleton_eq]
    exact hvz
  · have hib : b.length < i := ha ▸ hi
    rw [getD_append_singleton_gt _ _ _ hi, getD_append_singleton_gt _ _ _ hib]
    exact id

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (a b : List Bool) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  have hop : g.op = .and ∨ g.op = .or := by simpa using hg
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
    intro ha i hi
    exact h i (ha i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_def, id_eq]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, h i ha⟩

lemma fold_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl wireStep a).getD i false = true → (gs.foldl wireStep b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hm g (List.mem_cons_of_mem _ hg)) _ _
      (by simp [wireStep, hlen])
      (append_mono a b hlen _ _ hab (gate_mono g (hm g (by simp)) a b hab))

lemma wires_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin 26 → Bool)
    (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  apply fold_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp) _ w
  intro i
  by_cases hi : i < 26
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] using hxy ⟨i, hi⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_none]
    exact id

def andFires (C : Circuit) (a b : Fin 26) : Prop :=
  ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and ∧
    (C.wires (List.ofFn (pairInput a b))).getD (26 + j.val) false = true

lemma andFires_perm (π : Equiv.Perm (Fin 26)) (C : Circuit) (a b : Fin 26)
    (h : andFires C a b) : andFires (permCircuit 26 π C) (π a) (π b) := by
  obtain ⟨j, hj, hw⟩ := h
  refine ⟨⟨j.val, by simp [permCircuit]⟩, ?_, ?_⟩
  · simpa [permCircuit, permGate] using hj
  · have he := wires_permCircuit C 26 π (pairInput (π a) (π b)) (26 + j.val)
    rw [permWire_ge 26 π (by omega), pairInput_perm] at he
    exact he.trans hw

lemma andFires_diagonal (C : Circuit) (h : Monotone2 C) (hf : andFires C 0 0) :
    andFires C 0 1 := by
  obtain ⟨j, hj, hw⟩ := hf
  refine ⟨j, hj, wires_mono C h _ _ ?_ _ hw⟩
  intro u
  simp only [pairInput, decide_eq_true_eq, or_self]
  exact Or.inl

lemma main (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (hc : ∀ x, C.eval (List.ofFn x) = true ↔ hasEdge x)
    (a b : Fin 26) (hn : ¬ hasEdge (pairInput a b)) (hf : andFires C a b) :
    ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧
      ∀ x, D.eval (List.ofFn x) = true ↔ hasEdge x) ∧
      D.size ≤ C.size ∧ (andFires D 0 1 ∨ andFires D 0 14) := by
  have hab : rel a b = false := by
    cases he : rel a b
    · rfl
    · exact False.elim (hn ((hasEdge_iff _).2
        ⟨a, b, he, by simp [pairInput], by simp [pairInput]⟩))
  obtain ⟨π, hπ, ha, hb⟩ := orbit 11 a b (reach_ok a b hab)
  let D := permCircuit 26 π C
  have hmD : Monotone2 D := permCircuit_mono 26 π C hm
  refine ⟨D, ⟨hmD, permCircuit_readsBack 26 π C hr, ?_⟩, ?_, ?_⟩
  · intro x
    have he := wires_permCircuit C 26 π x C.output
    change (D.eval (List.ofFn x)) = C.eval (List.ofFn (x ∘ ⇑π)) at he
    rw [he, hc, hasEdge_perm π hπ]
  · simp [D, permCircuit, Circuit.size]
  · have hfD : andFires D (π a) (π b) := andFires_perm π C a b hf
    rcases hb with hb | hb | hb
    · rw [ha, hb] at hfD
      exact Or.inl (andFires_diagonal D hmD hfD)
    · rw [ha, hb] at hfD
      exact Or.inl hfD
    · rw [ha, hb] at hfD
      exact Or.inr hfD

end PEqualNP.Outside.L_meta_8143

theorem PEqualNP.Outside.L_meta_8143 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) => ∃ (x8 : Fin x5.gates.length), (x5.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn (x4 x6 x7))).getD ((26 : ℕ) + ↑x8) Bool.false = Bool.true; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → ∀ (x8 x9 : Fin (26 : ℕ)), ¬x2 (x4 x8 x9) → x5 x6 x8 x9 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x3 x12 ∧ x12.size ≤ x6.size ∧ (x5 x12 (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ)) ∨ x5 x12 (0 : Fin (26 : ℕ)) (14 : Fin (26 : ℕ))) := by
  intro _ _ _ _ _ C h a b hn hf
  exact PEqualNP.Outside.L_meta_8143.main C h.1 h.2.1 h.2.2 a b hn hf
