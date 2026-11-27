import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2652_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

def adj (u v : Fin 14) : Bool :=
  edges.any fun p => (p.1 == u.1 && p.2 == v.1) || (p.1 == v.1 && p.2 == u.1)

def finOfList (l : List ℕ) (x : Fin 14) : Fin 14 :=
  ⟨(l.getD x.1 0) % 14, Nat.mod_lt _ (by decide)⟩

def vtList (a : Fin 14) : List ℕ :=
  match a.1 with
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  | 1 => [1, 0, 2, 3, 6, 5, 4, 7, 13, 10, 9, 11, 12, 8]
  | 2 => [1, 2, 0, 4, 6, 5, 3, 13, 7, 12, 9, 11, 10, 8]
  | 3 => [1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12]
  | 4 => [1, 2, 6, 4, 0, 3, 5, 13, 9, 12, 7, 10, 11, 8]
  | 5 => [1, 2, 5, 4, 3, 0, 6, 13, 9, 8, 7, 11, 10, 12]
  | 6 => [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12]
  | 7 => [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]
  | 8 => [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6]
  | 9 => [9, 7, 11, 13, 12, 10, 8, 1, 6, 0, 5, 2, 4, 3]
  | 10 => [7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6]
  | 11 => [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3]
  | 12 => [9, 11, 7, 8, 12, 10, 13, 6, 1, 4, 5, 2, 0, 3]
  | _ => [9, 7, 8, 13, 10, 12, 11, 1, 6, 3, 5, 4, 2, 0]

def stabList (w : Fin 14) : List ℕ :=
  match w.1 with
  | 2 => [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]
  | 3 => [0, 3, 2, 1, 5, 4, 6, 7, 8, 11, 10, 9, 13, 12]
  | 4 => [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13]
  | 5 => [0, 2, 5, 6, 3, 1, 4, 8, 10, 13, 7, 11, 9, 12]
  | 6 => [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12]
  | 8 => [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]
  | 10 => [0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13]
  | 11 => [0, 2, 3, 6, 5, 4, 1, 8, 7, 13, 10, 9, 11, 12]
  | 12 => [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]
  | 13 => [0, 1, 5, 3, 6, 2, 4, 7, 10, 13, 8, 11, 12, 9]
  | _ => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

def vt (a x : Fin 14) : Fin 14 := finOfList (vtList a) x
def stab (w x : Fin 14) : Fin 14 := finOfList (stabList w) x
def aut (a b x : Fin 14) : Fin 14 := stab (vt a b) (vt a x)

lemma vt_surj : ∀ a y : Fin 14, ∃ x : Fin 14, vt a x = y := by decide
lemma stab_surj : ∀ w y : Fin 14, ∃ x : Fin 14, stab w x = y := by decide
lemma vt_adj : ∀ a u v : Fin 14, adj (vt a u) (vt a v) = adj u v := by decide
lemma stab_adj : ∀ w u v : Fin 14, adj (stab w u) (stab w v) = adj u v := by decide
lemma vt_self : ∀ a : Fin 14, vt a a = 0 := by decide
lemma stab_zero : ∀ w : Fin 14, stab w 0 = 0 := by decide
lemma stab_edge : ∀ w : Fin 14, adj 0 w = true → stab w w = 7 := by decide

lemma aut_surj (a b y : Fin 14) : ∃ x : Fin 14, aut a b x = y := by
  obtain ⟨z, hz⟩ := stab_surj (vt a b) y
  obtain ⟨x, hx⟩ := vt_surj a z
  exact ⟨x, by simp [aut, hx, hz]⟩

lemma aut_adj (a b u v : Fin 14) : adj (aut a b u) (aut a b v) = adj u v := by
  simp only [aut, stab_adj, vt_adj]

lemma aut_first (a b : Fin 14) : aut a b a = 0 := by
  simp only [aut, vt_self, stab_zero]

lemma aut_second_edge (a b : Fin 14) (hadj : adj a b = true) : aut a b b = 7 := by
  have h0 : adj 0 (vt a b) = true := by
    rw [← vt_self a, vt_adj, hadj]
  exact stab_edge (vt a b) h0

lemma adj_iff_mem (u v : Fin 14) :
    adj u v = true ↔ (u.1, v.1) ∈ edges ∨ (v.1, u.1) ∈ edges := by
  simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨p1, p2⟩, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (h | h)
    · exact ⟨(u.1, v.1), h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(v.1, u.1), h, Or.inr ⟨rfl, rfl⟩⟩

lemma edge_lt_14 (a b : ℕ) (h : (a, b) ∈ edges ∨ (b, a) ∈ edges) : a < 14 ∧ b < 14 := by
  rcases h with h | h <;>
  · simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                  ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                  ⟨rfl, rfl⟩ <;> omega

def heawoodProp (z : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.1, v.1) ∈ edges ∧ z u = true ∧ z v = true

lemma heawood_comp_aut (a b : Fin 14) (z : Fin 14 → Bool) :
    heawoodProp (fun i => z (aut a b i)) ↔ heawoodProp z := by
  constructor
  · rintro ⟨u, v, huv, hzu, hzv⟩
    have hadj : adj (aut a b u) (aut a b v) = true := by
      rw [aut_adj, adj_iff_mem]
      exact Or.inl huv
    rw [adj_iff_mem] at hadj
    rcases hadj with h | h
    · exact ⟨aut a b u, aut a b v, h, hzu, hzv⟩
    · exact ⟨aut a b v, aut a b u, h, hzv, hzu⟩
  · rintro ⟨u', v', huv', hzu', hzv'⟩
    obtain ⟨u, rfl⟩ := aut_surj a b u'
    obtain ⟨v, rfl⟩ := aut_surj a b v'
    have hadj : adj u v = true := by
      rw [← aut_adj a b, adj_iff_mem]
      exact Or.inl huv'
    rw [adj_iff_mem] at hadj
    rcases hadj with h | h
    · exact ⟨u, v, h, hzu', hzv'⟩
    · exact ⟨v, u, h, hzv', hzu'⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left {w : List Bool} {b : Bool} {k : ℕ} (hk : k < w.length) :
    (w ++ [b]).getD k false = w.getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

lemma getD_append_of_eq {w : List Bool} {b : Bool} {k : ℕ} (hk : w.length = k) :
    (w ++ [b]).getD k false = b := by
  subst hk; exact getD_append_self w b

lemma getD_of_le {w : List Bool} {k : ℕ} (hk : w.length ≤ k) :
    w.getD k false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk, Option.getD_none]

lemma stepW_getD_left {w : List Bool} {g : Gate} {k : ℕ} (hk : k < w.length) :
    (stepW w g).getD k false = w.getD k false :=
  getD_append_left hk

lemma stepW_getD_self (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_append_self w _

lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepW_prefix (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ), k < w.length →
      (gs.foldl stepW w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    rw [List.foldl_cons, ih (stepW w g) k (by simp only [stepW, List.length_append, List.length_singleton]; omega)]
    exact stepW_getD_left hk

lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (List.ofFn z).getD k false = z ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hk, dite_true, Option.getD_some]

lemma circuit_eval_eq_foldl (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stepW x).getD C.output false := rfl

-- Input permutation of an entire circuit (preserves size, Monotone2, maps gate 0 to [0, 7])
def permWire (σ : Fin 14 → Fin 14) (i : ℕ) : ℕ :=
  if h : i < 14 then (σ ⟨i, h⟩).1 else i

lemma permWire_lt (σ : Fin 14 → Fin 14) {i : ℕ} (hi : i < 14) :
    permWire σ i = (σ ⟨i, hi⟩).1 := by
  simp only [permWire, hi, dite_true]

lemma permWire_ge (σ : Fin 14 → Fin 14) {i : ℕ} (hi : ¬ i < 14) :
    permWire σ i = i := by
  simp only [permWire, hi, dite_false]

def permGate (σ : Fin 14 → Fin 14) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire σ)⟩

lemma foldl_perm_eq (σ : Fin 14 → Fin 14) (gs : List Gate) :
    ∀ (wD wC : List Bool),
      14 ≤ wD.length →
      wC.length = wD.length →
      (∀ k, k < wC.length → wD.getD (permWire σ k) false = wC.getD k false) →
      ∀ k, ((gs.map (permGate σ)).foldl stepW wD).getD (permWire σ k) false =
           (gs.foldl stepW wC).getD k false := by
  induction gs with
  | nil =>
    intro wD wC h14 hlen heq k
    simp only [List.map_nil, List.foldl_nil]
    by_cases hk : k < wC.length
    · exact heq k hk
    · rw [permWire_ge σ (by omega), getD_of_le (by omega), getD_of_le (by omega)]
  | cons g gs ih =>
    intro wD wC h14 hlen heq
    simp only [List.map_cons, List.foldl_cons]
    have hval : (permGate σ g).op.eval ((permGate σ g).inputs.map fun i => wD.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      simp only [permGate, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      change wD.getD (permWire σ i) false = wC.getD i false
      by_cases hi : i < wC.length
      · exact heq i hi
      · rw [permWire_ge σ (by omega), getD_of_le (by omega), getD_of_le (by omega)]
    refine ih (stepW wD (permGate σ g)) (stepW wC g) ?_ ?_ ?_
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      by_cases hkl : k < wC.length
      · have hpw_lt : permWire σ k < wD.length := by
          unfold permWire
          split_ifs with hlt
          · have := (σ ⟨k, hlt⟩).2; omega
          · omega
        rw [stepW_getD_left hpw_lt, stepW_getD_left hkl]
        exact heq k hkl
      · have hkeq : k = wC.length := by omega
        subst hkeq
        rw [permWire_ge σ (by omega), hlen, stepW_getD_self, ← hlen, stepW_getD_self]
        exact hval

-- Monotonicity of gate evaluation and circuits
lemma eval_mono_op (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), l1[i] = true → l2[i] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1' : l1[i]'(by omega) = true := h1 _ (List.getElem_mem (by omega))
    exact hle i (by omega) hi h1'
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    refine ⟨l2[i]'(by omega), List.getElem_mem (by omega), ?_⟩
    exact hle i hi (by omega) hbi

lemma foldl_stepW_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ k, w1.getD k false = true → w2.getD k false = true) →
      ∀ k, (gs.foldl stepW w1).getD k false = true → (gs.foldl stepW w2).getD k false = true := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle k hk
    exact hle k hk
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hmono g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')
    simp only [List.foldl_cons]
    refine ih hgs (stepW w1 g) (stepW w2 g) ?_ ?_
    · simp only [stepW, List.length_append, List.length_singleton, hlen]
    · intro k hk
      by_cases hklt : k < w1.length
      · rw [stepW_getD_left hklt] at hk
        rw [stepW_getD_left (by omega)]
        exact hle k hk
      · by_cases hkeq : k = w1.length
        · subst hkeq
          rw [stepW_getD_self] at hk
          rw [hlen, stepW_getD_self]
          refine eval_mono_op g.op hg.1 _ _ (by simp) ?_ hk
          intro idx h1 h2 hval
          simp only [List.getElem_map] at hval ⊢
          exact hle _ hval
        · have hkgt : (stepW w1 g).length ≤ k := by
            simp only [stepW, List.length_append, List.length_singleton]; omega
          rw [getD_of_le hkgt] at hk
          cases hk

-- Deleting wire p and replacing it by rep (where rep < p or rep >= final length)
def delWire (p rep i : ℕ) : ℕ :=
  if i < p then i else if i = p then rep else i - 1

lemma delWire_gt {p rep i : ℕ} (h1 : ¬ i < p) (h2 : i ≠ p) : delWire p rep i = i - 1 := by
  simp only [delWire, h1, h2, ite_false]

def delGate (p rep : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (delWire p rep)⟩

lemma foldl_delWire_eq (suf : List Gate) (p rep : ℕ) :
    ∀ (wD wC : List Bool),
      p ≤ wD.length →
      wC.length = wD.length + 1 →
      (rep < p ∨ wD.length + suf.length ≤ rep) →
      (∀ k, k < wC.length → wD.getD (delWire p rep k) false = wC.getD k false) →
      (∀ k, wC.length ≤ k → wD.getD (delWire p rep k) false = false) →
      ∀ k, ((suf.map (delGate p rep)).foldl stepW wD).getD (delWire p rep k) false =
           (suf.foldl stepW wC).getD k false := by
  induction suf with
  | nil =>
    intro wD wC _ _ _ heq hout k
    simp only [List.map_nil, List.foldl_nil]
    by_cases hk : k < wC.length
    · exact heq k hk
    · rw [hout k (by omega), getD_of_le (by omega : wC.length ≤ k)]
  | cons g gs ih =>
    intro wD wC hp hlen hrep heq hout
    simp only [List.map_cons, List.foldl_cons]
    have hval : (delGate p rep g).op.eval ((delGate p rep g).inputs.map fun i => wD.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      simp only [delGate, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      change wD.getD (delWire p rep i) false = wC.getD i false
      by_cases hi : i < wC.length
      · exact heq i hi
      · rw [hout i (by omega), getD_of_le (by omega : wC.length ≤ i)]
    refine ih (stepW wD (delGate p rep g)) (stepW wC g) ?_ ?_ ?_ ?_ ?_
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_cons, List.length_nil] at hrep ⊢
      omega
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      by_cases hkl : k < wC.length
      · rcases lt_or_ge (delWire p rep k) wD.length with hlt | hge
        · rw [stepW_getD_left hlt, stepW_getD_left hkl]
          exact heq k hkl
        · by_cases hpk : k = p
          · rw [hpk] at hge hkl ⊢
            have hrmp : delWire p rep p = rep := by simp [delWire]
            rw [hrmp] at hge ⊢
            have hrep_big : wD.length + 1 ≤ rep := by
              simp only [List.length_cons] at hrep; omega
            have hge1 : (stepW wD (delGate p rep g)).length ≤ rep := by
              simp only [stepW, List.length_append, List.length_singleton]; omega
            rw [getD_of_le hge1, stepW_getD_left hkl, ← heq p hkl, hrmp,
              getD_of_le (by omega : wD.length ≤ rep)]
          · simp only [delWire, hpk, ite_false] at hge
            split_ifs at hge <;> omega
      · have hkeq : k = wC.length := by omega
        subst hkeq
        have hrm : delWire p rep wC.length = wD.length := by
          rw [delWire_gt (by omega) (by omega), hlen]; omega
        rw [hrm, stepW_getD_self, stepW_getD_self]
        exact hval
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      rw [delWire_gt (by omega) (by omega)]
      have hge : (stepW wD (delGate p rep g)).length ≤ k - 1 := by
        simp only [stepW, List.length_append, List.length_singleton]; omega
      exact getD_of_le hge

lemma foldl_delWire_le (suf : List Gate) (p rep : ℕ)
    (hmono : ∀ g ∈ suf, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (wD wC : List Bool),
      p ≤ wD.length →
      wC.length = wD.length + 1 →
      (rep < p ∨ wD.length + suf.length ≤ rep) →
      (∀ k, wD.getD (delWire p rep k) false = true → wC.getD k false = true) →
      ∀ k, ((suf.map (delGate p rep)).foldl stepW wD).getD (delWire p rep k) false = true →
           (suf.foldl stepW wC).getD k false = true := by
  induction suf with
  | nil =>
    intro wD wC _ _ _ hle k hk
    exact hle k hk
  | cons g gs ih =>
    intro wD wC hp hlen hrep hle
    have hg := hmono g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')
    simp only [List.map_cons, List.foldl_cons]
    have hval : (delGate p rep g).op.eval ((delGate p rep g).inputs.map fun i => wD.getD i false) = true →
        g.op.eval (g.inputs.map fun i => wC.getD i false) = true := by
      simp only [delGate, List.map_map]
      intro h1
      refine eval_mono_op g.op hg.1 _ _ (by simp) ?_ h1
      intro idx hi1 hi2 hidx
      simp only [List.getElem_map] at hidx ⊢
      exact hle _ hidx
    refine ih hgs (stepW wD (delGate p rep g)) (stepW wC g) ?_ ?_ ?_ ?_
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_cons, List.length_nil] at hrep ⊢
      omega
    · intro k hk
      by_cases hkl : k < wC.length
      · rcases lt_or_ge (delWire p rep k) wD.length with hlt | hge
        · rw [stepW_getD_left hlt] at hk
          rw [stepW_getD_left hkl]
          exact hle k hk
        · by_cases hpk : k = p
          · rw [hpk] at hge hk
            have hrmp : delWire p rep p = rep := by simp [delWire]
            rw [hrmp] at hge hk
            have hrep_big : wD.length + 1 ≤ rep := by
              simp only [List.length_cons] at hrep; omega
            have hge1 : (stepW wD (delGate p rep g)).length ≤ rep := by
              simp only [stepW, List.length_append, List.length_singleton]; omega
            rw [getD_of_le hge1] at hk
            cases hk
          · simp only [delWire, hpk, ite_false] at hge
            split_ifs at hge <;> omega
      · by_cases hkeq : k = wC.length
        · subst hkeq
          have hrm : delWire p rep wC.length = wD.length := by
            rw [delWire_gt (by omega) (by omega), hlen]; omega
          rw [hrm, stepW_getD_self] at hk
          rw [stepW_getD_self]
          exact hval hk
        · rw [delWire_gt (by omega) (by omega)] at hk
          have hge : (stepW wD (delGate p rep g)).length ≤ k - 1 := by
            simp only [stepW, List.length_append, List.length_singleton]; omega
          rw [getD_of_le hge] at hk
          cases hk

lemma foldl_delWire_unused (suf : List Gate) (p rep : ℕ)
    (hunused : ∀ g ∈ suf, p ∉ g.inputs) :
    ∀ (wD wC : List Bool),
      p ≤ wD.length →
      wC.length = wD.length + 1 →
      (∀ k, k < wC.length → k ≠ p → wD.getD (delWire p rep k) false = wC.getD k false) →
      (∀ k, wC.length ≤ k → wD.getD (delWire p rep k) false = false) →
      ∀ k, k ≠ p →
        ((suf.map (delGate p rep)).foldl stepW wD).getD (delWire p rep k) false =
        (suf.foldl stepW wC).getD k false := by
  induction suf with
  | nil =>
    intro wD wC _ _ heq hout k hkp
    simp only [List.map_nil, List.foldl_nil]
    by_cases hk : k < wC.length
    · exact heq k hk hkp
    · rw [hout k (by omega), getD_of_le (by omega : wC.length ≤ k)]
  | cons g gs ih =>
    intro wD wC hp hlen heq hout
    have hg_un : p ∉ g.inputs := hunused g List.mem_cons_self
    have hgs_un : ∀ g' ∈ gs, p ∉ g'.inputs := fun g' hg' => hunused g' (List.mem_cons_of_mem g hg')
    simp only [List.map_cons, List.foldl_cons]
    have hval : (delGate p rep g).op.eval ((delGate p rep g).inputs.map fun i => wD.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      simp only [delGate, List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      change wD.getD (delWire p rep i) false = wC.getD i false
      have hip : i ≠ p := fun h => hg_un (h ▸ hi)
      by_cases hilt : i < wC.length
      · exact heq i hilt hip
      · rw [hout i (by omega), getD_of_le (by omega : wC.length ≤ i)]
    refine ih hgs_un (stepW wD (delGate p rep g)) (stepW wC g) ?_ ?_ ?_ ?_
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · simp only [stepW, List.length_append, List.length_singleton]; omega
    · intro k hk hkp
      simp only [stepW, List.length_append, List.length_singleton] at hk
      by_cases hkl : k < wC.length
      · have hrm_lt : delWire p rep k < wD.length := by
          unfold delWire
          simp only [hkp, ite_false]
          split_ifs <;> omega
        rw [stepW_getD_left hrm_lt, stepW_getD_left hkl]
        exact heq k hkl hkp
      · have hkeq : k = wC.length := by omega
        subst hkeq
        have hrm : delWire p rep wC.length = wD.length := by
          rw [delWire_gt (by omega) (by omega), hlen]; omega
        rw [hrm, stepW_getD_self, stepW_getD_self]
        exact hval
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      rw [delWire_gt (by omega) (by omega)]
      have hge : (stepW wD (delGate p rep g)).length ≤ k - 1 := by
        simp only [stepW, List.length_append, List.length_singleton]; omega
      exact getD_of_le hge

lemma stepW_and_07 (z : Fin 14 → Bool) :
    stepW (List.ofFn z) { op := GateOp.and, inputs := [0, 7] } =
      List.ofFn z ++ [z 0 && z 7] := by
  simp only [stepW, GateOp.eval, List.map_cons, List.map_nil,
    getD_ofFn z 0 (by decide), getD_ofFn z 7 (by decide),
    List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rfl

-- Eliminate a gate whose inputs contain an out-of-range (always-false) wire rep0
lemma eliminate_false_input_gate (pre suf : List Gate) (g : Gate) (out rep0 : ℕ)
    (hmono : Monotone2 ⟨pre ++ g :: suf, out⟩)
    (hrep0_hi : 14 + pre.length + 1 + suf.length ≤ rep0)
    (hmem : rep0 ∈ g.inputs) :
    ∃ D2 : Circuit, Monotone2 D2 ∧ D2.size = pre.length + suf.length ∧
      ∀ z : Fin 14 → Bool, D2.eval (List.ofFn z) = (Circuit.mk (pre ++ g :: suf) out).eval (List.ofFn z) := by
  let p : ℕ := 14 + pre.length
  have hg_mono : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    hmono g (by simp)
  have hrep : ∃ rep : ℕ, (rep < p ∨ p + suf.length ≤ rep) ∧
      ∀ w0 : List Bool, w0.length = p →
        w0.getD rep false = g.op.eval (g.inputs.map fun i => w0.getD i false) := by
    have hrep0_ge : ∀ w0 : List Bool, w0.length = p → w0.getD rep0 false = false := by
      intro w0 hw0
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w0.length ≤ rep0)]
    rcases hg_mono with ⟨hop, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop_and | hop_or
    · refine ⟨p + suf.length, Or.inr le_rfl, fun w0 hw0 => ?_⟩
      have hL : w0.getD (p + suf.length) false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w0.length ≤ p + suf.length)]
      have hR : g.op.eval (g.inputs.map fun i => w0.getD i false) = false := by
        rw [hop_and]
        simp only [GateOp.eval, List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨rep0, hmem, hrep0_ge w0 hw0⟩, by decide⟩
      rw [hL, hR]
    · rcases hgi : g.inputs with _ | ⟨i1, t1⟩
      · rw [hgi] at hmem; simp at hmem
      · rcases t1 with _ | ⟨i2, t2⟩
        · rw [hgi] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          subst hmem
          refine ⟨p + suf.length, Or.inr le_rfl, fun w0 hw0 => ?_⟩
          have hL : w0.getD (p + suf.length) false = false := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w0.length ≤ p + suf.length)]
          rw [hL, hop_or]
          simp only [GateOp.eval, List.map_cons, List.map_nil, hrep0_ge w0 hw0,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · rcases t2 with _ | ⟨i3, t3⟩
          · rw [hgi] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl
            · by_cases hi2 : i2 < p
              · refine ⟨i2, Or.inl hi2, fun w0 hw0 => ?_⟩
                rw [hop_or]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hrep0_ge w0 hw0,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
              · refine ⟨p + suf.length, Or.inr le_rfl, fun w0 hw0 => ?_⟩
                have hL : w0.getD (p + suf.length) false = false :=
                  getD_of_le (by omega : w0.length ≤ p + suf.length)
                have hi2f : w0.getD i2 false = false :=
                  getD_of_le (by omega : w0.length ≤ i2)
                rw [hL, hop_or]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hrep0_ge w0 hw0, hi2f,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or]
            · by_cases hi1 : i1 < p
              · refine ⟨i1, Or.inl hi1, fun w0 hw0 => ?_⟩
                rw [hop_or]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hrep0_ge w0 hw0,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
              · refine ⟨p + suf.length, Or.inr le_rfl, fun w0 hw0 => ?_⟩
                have hL : w0.getD (p + suf.length) false = false :=
                  getD_of_le (by omega : w0.length ≤ p + suf.length)
                have hi1f : w0.getD i1 false = false :=
                  getD_of_le (by omega : w0.length ≤ i1)
                rw [hL, hop_or]
                simp only [GateOp.eval, List.map_cons, List.map_nil, hrep0_ge w0 hw0, hi1f,
                  List.any_cons, List.any_nil, id_eq, Bool.false_or]
          · rw [hgi] at hlen; simp at hlen
  rcases hrep with ⟨rep, hrep_bound, hrep_eq⟩
  let D2 : Circuit := ⟨pre ++ suf.map (delGate p rep), delWire p rep out⟩
  refine ⟨D2, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [D2, List.mem_append, List.mem_map] at hg'
    rcases hg' with hpre | ⟨g0, hg0, rfl⟩
    · exact hmono g' (by simp [hpre])
    · obtain ⟨hop, hlen⟩ := hmono g0 (by simp [hg0])
      exact ⟨hop, by simp [delGate, hlen]⟩
  · simp [D2, Circuit.size]
  · intro z
    rw [circuit_eval_eq_foldl, circuit_eval_eq_foldl]
    change ((pre ++ suf.map (delGate p rep)).foldl stepW (List.ofFn z)).getD (delWire p rep out) false =
      ((pre ++ g :: suf).foldl stepW (List.ofFn z)).getD out false
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    let w0 := pre.foldl stepW (List.ofFn z)
    have hw0_len : w0.length = p := by
      simp [w0, foldl_stepW_len, p]
    refine foldl_delWire_eq suf p rep w0 (stepW w0 g) (by omega) ?_ ?_ ?_ ?_ out
    · simp [stepW]
    · rcases hrep_bound with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by omega)
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      by_cases hkp : k < p
      · have hdw : delWire p rep k = k := by simp [delWire, hkp]
        rw [hdw, stepW_getD_left (by omega)]
      · have hkeq : k = p := by omega
        subst hkeq
        have hdw : delWire p rep p = rep := by simp [delWire]
        rw [hdw, hrep_eq w0 hw0_len, ← hw0_len, stepW_getD_self]
    · intro k hk
      simp only [stepW, List.length_append, List.length_singleton] at hk
      rw [delWire_gt (by omega) (by omega)]
      exact getD_of_le (by omega : w0.length ≤ k - 1)

end PEqualNP.Outside.L_meta_2652_aux

open PEqualNP.Outside.L_meta_2652_aux in
theorem PEqualNP.Outside.L_meta_2652 :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 : Fin (14 : ℕ) → Bool), x4 (0 : Fin (14 : ℕ)) = Bool.false ∨ x4 (7 : Fin (14 : ℕ)) = Bool.false → (x3.eval (List.ofFn x4) = Bool.true ↔ x2 x4)) ∧ x3.eval (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (x4 = (0 : Fin (14 : ℕ)) ∨ x4 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x4.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } :: x5 → (x6, x7) ∈ x1 ∨ (x7, x6) ∈ x1 → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ x2 x11) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ (x12.size + (2 : ℕ) ≤ x4.size ∧ x3 x12 ∨ x12.size + (1 : ℕ) ≤ x4.size ∧ ∀ (x13 : Fin (14 : ℕ) → Bool), x12.eval (List.ofFn x13) = Bool.true ↔ x2 x13) := by
  intro x1 x2 x3 C rest a b hgates hedge hmono hcomp
  obtain ⟨ha, hb⟩ := edge_lt_14 a b hedge
  let af : Fin 14 := ⟨a, ha⟩
  let bf : Fin 14 := ⟨b, hb⟩
  have hadj_ab : adj af bf = true := (adj_iff_mem af bf).mpr hedge
  let σ : Fin 14 → Fin 14 := aut af bf
  have hσa : σ af = 0 := aut_first af bf
  have hσb : σ bf = 7 := aut_second_edge af bf hadj_ab
  let rest' : List PEqualNP.CircuitLowerBounds.Gate := rest.map (permGate σ)
  let out' : ℕ := permWire σ C.output
  let C' : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] } :: rest', out'⟩
  have hC'_gates : C'.gates = C.gates.map (permGate σ) := by
    rw [hgates]
    simp [C', rest', permGate, permWire, ha, hb, σ, af, bf, hσa, hσb]
  have hC'_size : C'.size = C.size := by
    simp [C', rest', PEqualNP.CircuitLowerBounds.Circuit.size, hgates]
  have hC'_mono : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    rw [hC'_gates, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    obtain ⟨hop, hlen⟩ := hmono g0 hg0
    exact ⟨hop, by simp [permGate, hlen]⟩
  have hmono_rest' : ∀ g ∈ rest',
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    exact hC'_mono g (List.mem_cons_of_mem _ hg)
  have hC'_comp : ∀ z : Fin 14 → Bool, C'.eval (List.ofFn z) = true ↔ x2 z := by
    intro z
    have heval : C'.eval (List.ofFn z) = C.eval (List.ofFn fun i => z (σ i)) := by
      rw [circuit_eval_eq_foldl, circuit_eval_eq_foldl, hC'_gates]
      refine foldl_perm_eq σ C.gates (List.ofFn z) (List.ofFn fun i => z (σ i))
        (by simp only [List.length_ofFn]; omega)
        (by simp only [List.length_ofFn]) ?_ C.output
      intro k hk
      simp only [List.length_ofFn] at hk
      rw [permWire_lt σ hk, getD_ofFn z (σ ⟨k, hk⟩).1 (σ ⟨k, hk⟩).2, getD_ofFn (fun i => z (σ i)) k hk]
    rw [heval]
    exact (hcomp fun i => z (σ i)).trans (heawood_comp_aut af bf z)
  -- Build D1 by deleting wire 14 and replacing by rep0 := 14 + rest'.length
  let rep0 : ℕ := 14 + rest'.length
  let D1 : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest'.map (delGate 14 rep0), delWire 14 rep0 out'⟩
  have hD1_size : D1.size = rest'.length := by simp [D1, PEqualNP.CircuitLowerBounds.Circuit.size]
  have hD1_mono : PEqualNP.MetaComplexity.Monotone2 D1 := by
    intro g hg
    simp only [D1, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    obtain ⟨hop, hlen⟩ := hmono_rest' g0 hg0
    exact ⟨hop, by simp [delGate, hlen]⟩
  have hD1_le : ∀ z : Fin 14 → Bool, D1.eval (List.ofFn z) = true → C'.eval (List.ofFn z) = true := by
    intro z hDz
    rw [circuit_eval_eq_foldl] at hDz
    rw [circuit_eval_eq_foldl]
    change (rest'.foldl stepW (stepW (List.ofFn z) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] })).getD out' false = true
    rw [stepW_and_07]
    refine foldl_delWire_le rest' 14 rep0 hmono_rest' (List.ofFn z) (List.ofFn z ++ [z 0 && z 7])
      (by simp only [List.length_ofFn]; omega)
      (by simp only [List.length_append, List.length_ofFn, List.length_singleton])
      (Or.inr (by simp only [List.length_ofFn, rep0]; omega)) ?_ out' hDz
    intro k hk
    by_cases hk14 : k < 14
    · simp only [delWire, hk14, ite_true] at hk
      rw [getD_append_left (by simp only [List.length_ofFn]; exact hk14)]
      exact hk
    · by_cases hkeq : k = 14
      · subst hkeq
        have hdw : delWire 14 rep0 14 = rep0 := by simp [delWire]
        rw [hdw, getD_of_le (by simp only [List.length_ofFn, rep0]; omega)] at hk
        cases hk
      · rw [delWire_gt hk14 hkeq, getD_of_le (by simp only [List.length_ofFn]; omega)] at hk
        cases hk
  have hD1_eq_off : ∀ z : Fin 14 → Bool, z 0 = false ∨ z 7 = false →
      D1.eval (List.ofFn z) = C'.eval (List.ofFn z) := by
    intro z hoff
    have hand_f : (z 0 && z 7) = false := by
      rcases hoff with h | h <;> simp [h]
    rw [circuit_eval_eq_foldl, circuit_eval_eq_foldl]
    change ((rest'.map (delGate 14 rep0)).foldl stepW (List.ofFn z)).getD (delWire 14 rep0 out') false =
      (rest'.foldl stepW (stepW (List.ofFn z) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] })).getD out' false
    rw [stepW_and_07, hand_f]
    refine foldl_delWire_eq rest' 14 rep0 (List.ofFn z) (List.ofFn z ++ [false])
      (by simp only [List.length_ofFn]; omega)
      (by simp only [List.length_append, List.length_ofFn, List.length_singleton])
      (Or.inr (by simp only [List.length_ofFn, rep0]; omega)) ?_ ?_ out'
    · intro k hk
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
      by_cases hk14 : k < 14
      · have hdw : delWire 14 rep0 k = k := by simp [delWire, hk14]
        rw [hdw, getD_append_left (by simp only [List.length_ofFn]; exact hk14)]
      · have hkeq : k = 14 := by omega
        subst hkeq
        have hdw : delWire 14 rep0 14 = rep0 := by simp [delWire]
        rw [hdw, getD_of_le (by simp only [List.length_ofFn, rep0]; omega),
          getD_append_of_eq List.length_ofFn]
    · intro k hk
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
      rw [delWire_gt (by omega) (by omega)]
      exact getD_of_le (by simp only [List.length_ofFn]; omega)
  let z07 : Fin 14 → Bool := fun t => Decidable.decide (t = (0 : Fin 14) ∨ t = (7 : Fin 14))
  cases hD1_07 : D1.eval (List.ofFn z07)
  · -- Case B: D1.eval z07 = false, so wire 14 is read by some gate in rest' -> eliminate a second gate!
    have hC'_07 : C'.eval (List.ofFn z07) = true := by
      rw [hC'_comp]
      exact ⟨0, 7, by simp [x1], by simp [z07], by simp [z07]⟩
    have hout_ne : out' ≠ 14 := by
      intro hout14
      let z08 : Fin 14 → Bool := fun t => Decidable.decide (t = (0 : Fin 14) ∨ t = (8 : Fin 14))
      have hC'_08 : C'.eval (List.ofFn z08) = true := by
        rw [hC'_comp]
        exact ⟨0, 8, by simp [x1], by simp [z08], by simp [z08]⟩
      rw [circuit_eval_eq_foldl] at hC'_08
      change (rest'.foldl stepW (stepW (List.ofFn z08) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] })).getD out' false = true at hC'_08
      rw [hout14, stepW_and_07] at hC'_08
      have hpref := foldl_stepW_prefix rest' (List.ofFn z08 ++ [z08 0 && z08 7]) 14
        (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)
      rw [hpref, getD_append_of_eq List.length_ofFn] at hC'_08
      have hz08_7 : z08 7 = false := by decide
      rw [hz08_7, Bool.and_false] at hC'_08
      cases hC'_08
    have hex_use : ∃ g ∈ rest', 14 ∈ g.inputs := by
      by_contra hno
      push Not at hno
      have heq07 : D1.eval (List.ofFn z07) = C'.eval (List.ofFn z07) := by
        rw [circuit_eval_eq_foldl, circuit_eval_eq_foldl]
        change ((rest'.map (delGate 14 rep0)).foldl stepW (List.ofFn z07)).getD (delWire 14 rep0 out') false =
          (rest'.foldl stepW (stepW (List.ofFn z07) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] })).getD out' false
        rw [stepW_and_07]
        refine foldl_delWire_unused rest' 14 rep0 hno (List.ofFn z07) (List.ofFn z07 ++ [z07 0 && z07 7])
          (by simp only [List.length_ofFn]; omega)
          (by simp only [List.length_append, List.length_ofFn, List.length_singleton]) ?_ ?_ out' hout_ne
        · intro k hk hk14ne
          simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
          have hk14 : k < 14 := by omega
          have hdw : delWire 14 rep0 k = k := by simp [delWire, hk14]
          rw [hdw, getD_append_left (by simp only [List.length_ofFn]; exact hk14)]
        · intro k hk
          simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk
          rw [delWire_gt (by omega) (by omega)]
          exact getD_of_le (by simp only [List.length_ofFn]; omega)
      rw [hD1_07, hC'_07] at heq07
      cases heq07
    rcases hex_use with ⟨g0, hg0_mem, h14_mem⟩
    obtain ⟨pre0, suf0, hsplit0⟩ := List.append_of_mem hg0_mem
    let pre1 := pre0.map (delGate 14 rep0)
    let g1 := delGate 14 rep0 g0
    let suf1 := suf0.map (delGate 14 rep0)
    have hD1_eq_split : D1 = ⟨pre1 ++ g1 :: suf1, delWire 14 rep0 out'⟩ := by
      simp [D1, pre1, g1, suf1, hsplit0]
    have hrep0_mem : rep0 ∈ g1.inputs := by
      simp only [g1, delGate, List.mem_map]
      exact ⟨14, h14_mem, by simp [delWire]⟩
    have hrep0_hi : 14 + pre1.length + 1 + suf1.length ≤ rep0 := by
      simp [pre1, suf1, rep0, hsplit0]; omega
    obtain ⟨D2, hD2_mono, hD2_size, hD2_eval⟩ :=
      eliminate_false_input_gate pre1 suf1 g1 (delWire 14 rep0 out') rep0
        (hD1_eq_split ▸ hD1_mono) hrep0_hi hrep0_mem
    refine ⟨D2, hD2_mono, Or.inl ⟨?_, ?_, ?_⟩⟩
    · have hlen_rest' : rest'.length = pre1.length + 1 + suf1.length := by
        simp [pre1, suf1, hsplit0]; omega
      have hC_sz : C.size = rest'.length + 1 := by
        rw [← hC'_size]; simp [C', PEqualNP.CircuitLowerBounds.Circuit.size]
      omega
    · intro z hoff
      rw [hD2_eval z, ← hD1_eq_split, hD1_eq_off z hoff, hC'_comp z]
    · rw [hD2_eval z07, ← hD1_eq_split, hD1_07]
  · -- Case A: D1.eval z07 = true, so D1 computes x2 everywhere with size + 1 <= C.size!
    refine ⟨D1, hD1_mono, Or.inr ⟨?_, ?_⟩⟩
    · have hC_sz : C.size = rest'.length + 1 := by
        rw [← hC'_size]; simp [C', PEqualNP.CircuitLowerBounds.Circuit.size]
      omega
    · intro z
      constructor
      · intro hDz
        exact (hC'_comp z).mp (hD1_le z hDz)
      · intro hx2
        by_cases h0 : z 0 = false
        · rw [hD1_eq_off z (Or.inl h0)]
          exact (hC'_comp z).mpr hx2
        · by_cases h7 : z 7 = false
          · rw [hD1_eq_off z (Or.inr h7)]
            exact (hC'_comp z).mpr hx2
          · have hz0 : z 0 = true := by cases h : z 0 <;> simp_all
            have hz7 : z 7 = true := by cases h : z 7 <;> simp_all
            rw [circuit_eval_eq_foldl] at hD1_07 ⊢
            refine foldl_stepW_mono D1.gates hD1_mono (List.ofFn z07) (List.ofFn z)
              (by simp only [List.length_ofFn]) ?_ D1.output hD1_07
            intro k hk
            by_cases hk14 : k < 14
            · rw [getD_ofFn z07 k hk14] at hk
              rw [getD_ofFn z k hk14]
              simp only [z07, decide_eq_true_eq] at hk
              rcases hk with h | h <;> rw [h]
              · exact hz0
              · exact hz7
            · rw [getD_of_le (by simp only [List.length_ofFn]; omega)] at hk
              cases hk
