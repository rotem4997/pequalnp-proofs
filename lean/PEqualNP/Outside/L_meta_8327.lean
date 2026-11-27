import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8327

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem len_fold (gs : List Gate) : ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [stp, List.length_append, List.length_cons, List.length_nil]
    omega

theorem pre_fold (gs : List Gate) : ∀ w : List Bool, ∃ V, gs.foldl stp w = w ++ V := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨V, hV⟩ := ih (stp w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ V, by
      rw [List.foldl_cons, hV]; simp [stp]⟩

theorem lay_fold (w : List Bool) (gs : List Gate) (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < w.length) :
    ∀ acc : List Bool, gs.foldl stp (w ++ acc) =
      w ++ acc ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    have hg : ∀ i ∈ g.inputs, i < w.length := h g (by simp)
    have hgs : ∀ g' ∈ gs, ∀ i ∈ g'.inputs, i < w.length := fun g' hg' => h g' (by simp [hg'])
    have hm : g.inputs.map (fun i => (w ++ acc).getD i false) = g.inputs.map (fun i => w.getD i false) :=
      List.map_congr_left (fun i hi => List.getD_append _ _ _ _ (hg i hi))
    have e1 : stp (w ++ acc) g = w ++ (acc ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := by
      simp only [stp, hm, List.append_assoc]
    rw [List.foldl_cons, e1, ih hgs]
    simp

def RB (b : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < b + j

theorem RB_cons (b : ℕ) (g : Gate) (gs : List Gate) :
    RB b (g :: gs) ↔ (∀ i ∈ g.inputs, i < b) ∧ RB (b + 1) gs := by
  constructor
  · intro h
    refine ⟨fun i hi => by simpa using h 0 (by simp) i hi, fun j hj i hi => ?_⟩
    have := h (j + 1) (by simp; omega) i (by simpa using hi)
    omega
  · rintro ⟨h0, h1⟩ j hj i hi
    cases j with
    | zero => simpa using h0 i (by simpa using hi)
    | succ j =>
      have := h1 j (by simp at hj; omega) i (by simpa using hi)
      omega

theorem RB_append (l1 : List Gate) : ∀ (b : ℕ) (l2 : List Gate),
    RB b (l1 ++ l2) ↔ RB b l1 ∧ RB (b + l1.length) l2 := by
  induction l1 with
  | nil => intro b l2; simp [RB]
  | cons g l1 ih =>
    intro b l2
    rw [List.cons_append, RB_cons, RB_cons, ih]
    simp only [List.length_cons]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, by rwa [show b + (l1.length + 1) = b + 1 + l1.length by omega]⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, by rwa [show b + (l1.length + 1) = b + 1 + l1.length by omega] at h2⟩

theorem RB_map {α : Type} (b : ℕ) (l : List α) (h : α → Gate)
    (H : ∀ j (hj : j < l.length), ∀ i ∈ (h l[j]).inputs, i < b + j) : RB b (l.map h) := by
  intro j hj i hi
  simp only [List.getElem_map] at hi
  exact H j (by simpa using hj) i hi

theorem RB_of_RB (n : ℕ) (C : Circuit) (h : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    RB n C.gates := by
  intro j hj i hi
  apply h j hj i
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact hi

theorem RB_to (n : ℕ) (C : Circuit) (h : RB n C.gates) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C := by
  intro j hj i hi
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  rw [List.getD_eq_getElem _ _ hj] at hi
  exact h j hj i hi

def cp (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map σ⟩

theorem sim (σ : ℕ → ℕ) (n b : ℕ) (hσ : ∀ a, n ≤ a → σ a = b + (a - n)) (gs : List Gate) :
    ∀ A B : List Bool, n ≤ A.length → B.length + n = b + A.length →
    (∀ a < A.length, σ a < B.length ∧ B.getD (σ a) false = A.getD a false) → RB A.length gs →
    ∀ a < (gs.foldl stp A).length, σ a < ((gs.map (cp σ)).foldl stp B).length ∧
      ((gs.map (cp σ)).foldl stp B).getD (σ a) false = (gs.foldl stp A).getD a false := by
  induction gs with
  | nil => intro A B _ _ hR _; simpa using hR
  | cons g gs ih =>
    intro A B hn hl hR hRB
    rw [RB_cons] at hRB
    obtain ⟨h0, h1⟩ := hRB
    have hv : g.op.eval ((g.inputs.map σ).map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (hR i (h0 i hi)).2
    simp only [List.map_cons, List.foldl_cons]
    apply ih (stp A g) (stp B (cp σ g))
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · intro a ha
      simp only [stp, List.length_append, List.length_singleton] at ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | ha
      · obtain ⟨h1', h2'⟩ := hR a ha
        refine ⟨by simp only [stp, List.length_append, List.length_singleton]; omega, ?_⟩
        simp only [stp]
        rw [List.getD_append _ _ _ _ h1', List.getD_append _ _ _ _ ha, h2']
      · subst ha
        have hsa : σ A.length = B.length := by rw [hσ _ hn]; omega
        refine ⟨by simp only [stp, List.length_append, List.length_singleton]; omega, ?_⟩
        simp only [stp]
        rw [hsa, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl,
          Nat.sub_self, Nat.sub_self]
        exact hv
    · simpa [stp] using h1

theorem copy_step (C : Circuit) (n : ℕ) (hRB : RB n C.gates) (σ : ℕ → ℕ) (b : ℕ) (B : List Bool)
    (y : Fin n → Bool) (hB : B.length = b)
    (hlt : ∀ a < n, σ a < b ∧ B.getD (σ a) false = (List.ofFn y).getD a false)
    (hge : ∀ a, n ≤ a → σ a = b + (a - n)) :
    ((C.gates.map (cp σ)).foldl stp B).length = b + C.gates.length ∧
    (∃ V, (C.gates.map (cp σ)).foldl stp B = B ++ V) ∧
    (C.output < n + C.gates.length → σ C.output < ((C.gates.map (cp σ)).foldl stp B).length ∧
      ((C.gates.map (cp σ)).foldl stp B).getD (σ C.output) false =
        PEqualNP.MetaComplexity.circuitFun n C y) := by
  refine ⟨by rw [len_fold]; simp [hB], pre_fold _ _, fun ho => ?_⟩
  have hs := sim σ n b hge C.gates (List.ofFn y) B (by simp) (by simp [hB])
    (fun a ha => by rw [hB]; exact hlt a (by simpa using ha)) (by simpa using hRB) C.output
    (by rw [len_fold]; simpa using ho)
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  rfl

theorem getD_ofFn {m : ℕ} (z : Fin m → Bool) (i : Fin m) : (List.ofFn z).getD (i : ℕ) false = z i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_ofFn' {n : ℕ} (y : Fin n → Bool) (a : ℕ) (ha : a < n) :
    (List.ofFn y).getD a false = y ⟨a, ha⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]
  simp

noncomputable def EE {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) : List (Fin 3 × Fin n) :=
  (Finset.univ.filter (fun p : Fin 3 × Fin n => f p.1 p.2 ≠ g p.1 p.2)).toList

noncomputable def rho {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) (k : Fin 3) (a : ℕ) : ℕ :=
  if h : a < n then
    (if f k ⟨a, h⟩ = g k ⟨a, h⟩ then ((f k ⟨a, h⟩ : Fin m) : ℕ) else m + (EE f g).idxOf (k, ⟨a, h⟩))
  else 0

noncomputable def sig {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) (s : ℕ) (k : Fin 3) (a : ℕ) : ℕ :=
  if a < n then rho f g k a else (m + (EE f g).length + (k : ℕ) * s) + (a - n)

noncomputable def lay {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) : List Gate :=
  (EE f g).map (fun p => ⟨GateOp.or, [((f p.1 p.2 : Fin m) : ℕ), ((g p.1 p.2 : Fin m) : ℕ)]⟩)

noncomputable def outw {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) (C : Circuit) (k : Fin 3) : ℕ :=
  if C.output < n + C.gates.length then sig f g C.gates.length k C.output else 0

noncomputable def DD {n m : ℕ} (f g : Fin 3 → Fin n → Fin m) (C : Circuit) : Circuit :=
  { gates := lay f g ++ C.gates.map (cp (sig f g C.gates.length 0)) ++
      C.gates.map (cp (sig f g C.gates.length 1)) ++ C.gates.map (cp (sig f g C.gates.length 2)) ++
      [⟨GateOp.or, [outw f g C 0, outw f g C 1]⟩,
       ⟨GateOp.or, [m + (EE f g).length + 3 * C.gates.length, outw f g C 2]⟩],
    output := if C.output < n + C.gates.length then m + (EE f g).length + 3 * C.gates.length + 1
      else m + (EE f g).length + 3 * C.gates.length + 2 }

theorem key (W : List Bool) (o0 o1 o2 t : ℕ) (hW : W.length = t) (h0 : o0 < t) (h1 : o1 < t)
    (h2 : o2 < t) :
    (stp (stp W ⟨GateOp.or, [o0, o1]⟩) ⟨GateOp.or, [t, o2]⟩).getD (t + 1) false =
      (W.getD o0 false || W.getD o1 false || W.getD o2 false) := by
  subst hW
  simp [stp, GateOp.eval, List.getD_append, List.getD_append_right, List.getElem?_append_left h2, List.getElem?_eq_getElem h2, h0, h1, h2]

theorem hex (P : Fin 3 → Bool) : decide (∃ k, P k = true) = (P 0 || P 1 || P 2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

theorem main (n m : ℕ) (f g : Fin 3 → Fin n → Fin m) (C : Circuit) (hm : 0 < m)
    (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 m (DD f g C) ∧
    (DD f g C).size = 3 * C.size + Fintype.card {p : Fin 3 × Fin n // f p.1 p.2 ≠ g p.1 p.2} + 2 ∧
    ∀ z : Fin m → Bool, PEqualNP.MetaComplexity.circuitFun m (DD f g C) z =
      decide (∃ k : Fin 3, (PEqualNP.MetaComplexity.circuitFun n C fun a => z (f k a) || z (g k a)) = true) := by
  obtain ⟨hAO, hRBC, h2⟩ := hC
  have hRB := RB_of_RB n C hRBC
  have hmemE : ∀ p, p ∈ EE f g ↔ f p.1 p.2 ≠ g p.1 p.2 := by intro p; simp [EE]
  have hrho : ∀ k (a : ℕ), a < n → rho f g k a < m + (EE f g).length := by
    intro k a ha
    unfold rho
    rw [dif_pos ha]
    split_ifs with he
    · have := (f k ⟨a, ha⟩).isLt; omega
    · have := List.idxOf_lt_length_of_mem ((hmemE (k, ⟨a, ha⟩)).2 he); omega
  have hsig_lt : ∀ k a, a < n → sig f g C.gates.length k a = rho f g k a := by
    intro k a ha; unfold sig; rw [if_pos ha]
  have hsig_ge : ∀ k a, n ≤ a → sig f g C.gates.length k a =
      (m + (EE f g).length + (k : ℕ) * C.gates.length) + (a - n) := by
    intro k a ha; unfold sig; rw [if_neg (by omega)]
  have hk3 : ∀ k : Fin 3, (k : ℕ) * C.gates.length + C.gates.length ≤ 3 * C.gates.length := by
    intro k
    have := Nat.mul_le_mul_right C.gates.length (show (k : ℕ) + 1 ≤ 3 by omega)
    rw [add_mul, one_mul] at this
    exact this
  have hout : ∀ k, outw f g C k < m + (EE f g).length + 3 * C.gates.length := by
    intro k
    unfold outw
    split_ifs with ho
    · by_cases han : C.output < n
      · rw [hsig_lt k _ han]; have := hrho k _ han; omega
      · rw [hsig_ge k _ (by omega)]; have := hk3 k; omega
    · omega
  have hRBc : ∀ k : Fin 3, ∀ b', b' = m + (EE f g).length + (k : ℕ) * C.gates.length →
      RB b' (C.gates.map (cp (sig f g C.gates.length k))) := by
    intro k b' hb'
    apply RB_map
    intro j hj i hi
    simp only [cp, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have hal := hRB j hj a ha
    by_cases han : a < n
    · rw [hsig_lt k a han]; have := hrho k a han; omega
    · rw [hsig_ge k a (by omega)]; omega
  have hv0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have hv1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have hv2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  have hcard : Fintype.card {p : Fin 3 × Fin n // f p.1 p.2 ≠ g p.1 p.2} = (EE f g).length := by
    simp only [EE, Finset.length_toList]
    exact Fintype.card_subtype _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro gt hg
    simp only [DD, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (((h | h) | h) | h) | h | h
    · simp only [lay, List.mem_map] at h
      obtain ⟨p, -, rfl⟩ := h
      right; rfl
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      exact hAO g0 hg0
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      exact hAO g0 hg0
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      exact hAO g0 hg0
    · subst h; right; rfl
    · subst h; right; rfl
  · apply RB_to
    show RB m (lay f g ++ C.gates.map (cp (sig f g C.gates.length 0)) ++
      C.gates.map (cp (sig f g C.gates.length 1)) ++ C.gates.map (cp (sig f g C.gates.length 2)) ++
      [⟨GateOp.or, [outw f g C 0, outw f g C 1]⟩,
       ⟨GateOp.or, [m + (EE f g).length + 3 * C.gates.length, outw f g C 2]⟩])
    refine (RB_append _ _ _).2 ⟨(RB_append _ _ _).2 ⟨(RB_append _ _ _).2
      ⟨(RB_append _ _ _).2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · unfold lay
      apply RB_map
      intro j hj i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Nat.lt_of_lt_of_le (Fin.isLt _) (Nat.le_add_right _ _)
      · exact Nat.lt_of_lt_of_le (Fin.isLt _) (Nat.le_add_right _ _)
    · apply hRBc 0
      simp only [lay, List.length_map, hv0]; omega
    · apply hRBc 1
      simp only [lay, List.length_map, List.length_append, hv1]; omega
    · apply hRBc 2
      simp only [lay, List.length_map, List.length_append, hv2]; omega
    · rw [RB_cons, RB_cons]
      simp only [lay, List.length_map, List.length_append]
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have := hout 0; omega
        · have := hout 1; omega
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · omega
        · have := hout 2; omega
      · intro j hj; simp at hj
  · intro gt hg
    simp only [DD, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (((h | h) | h) | h) | h | h
    · simp only [lay, List.mem_map] at h
      obtain ⟨p, -, rfl⟩ := h
      rfl
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      simp only [cp, List.length_map]; exact h2 g0 hg0
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      simp only [cp, List.length_map]; exact h2 g0 hg0
    · simp only [List.mem_map] at h
      obtain ⟨g0, hg0, rfl⟩ := h
      simp only [cp, List.length_map]; exact h2 g0 hg0
    · subst h; rfl
    · subst h; rfl
  · simp only [Circuit.size, DD, List.length_append, List.length_map, lay, List.length_cons,
      List.length_nil]
    rw [hcard]
    omega
  · intro z
    show ((DD f g C).gates.foldl stp (List.ofFn z)).getD (DD f g C).output false = _
    simp only [DD, List.foldl_append]
    set W1 := (lay f g).foldl stp (List.ofFn z) with hW1def
    have hlayin : ∀ gt ∈ lay f g, ∀ i ∈ gt.inputs, i < (List.ofFn z).length := by
      intro gt hg i hi
      simp only [lay, List.mem_map] at hg
      obtain ⟨p, -, rfl⟩ := hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [List.length_ofFn]
      rcases hi with rfl | rfl <;> exact Fin.isLt _
    have hW1 : W1 = List.ofFn z ++ (lay f g).map
        (fun gt => gt.op.eval (gt.inputs.map fun i => (List.ofFn z).getD i false)) := by
      have := lay_fold (List.ofFn z) (lay f g) hlayin []
      simp only [List.append_nil] at this
      rw [hW1def]
      exact this
    have hW1len : W1.length = m + (EE f g).length := by
      rw [hW1def, len_fold]; simp [lay]
    have hW1val : ∀ k (a : Fin n), W1.getD (rho f g k a) false = (z (f k a) || z (g k a)) := by
      intro k a
      have hrho_def : rho f g k a =
          if f k a = g k a then ((f k a : Fin m) : ℕ) else m + (EE f g).idxOf (k, a) := by
        simp [rho]
      rw [hrho_def, hW1]
      split_ifs with he
      · rw [List.getD_append _ _ _ _ (by simp), getD_ofFn, he, Bool.or_self]
      · have hmem : (k, a) ∈ EE f g := (hmemE _).2 he
        have hidx := List.idxOf_lt_length_of_mem hmem
        rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left]
        rw [List.getD_eq_getElem _ _ (by simp [lay]; exact hidx)]
        simp only [lay, List.getElem_map, List.getElem_idxOf hidx]
        simp only [GateOp.eval, List.map_cons, List.map_nil, getD_ofFn]
        simp
    have step : ∀ (k : Fin 3) (B : List Bool),
        B.length = m + (EE f g).length + (k : ℕ) * C.gates.length → (∃ V, B = W1 ++ V) →
        ((C.gates.map (cp (sig f g C.gates.length k))).foldl stp B).length =
          m + (EE f g).length + (k : ℕ) * C.gates.length + C.gates.length ∧
        (∃ V, (C.gates.map (cp (sig f g C.gates.length k))).foldl stp B = B ++ V) ∧
        (C.output < n + C.gates.length →
          sig f g C.gates.length k C.output <
            ((C.gates.map (cp (sig f g C.gates.length k))).foldl stp B).length ∧
          ((C.gates.map (cp (sig f g C.gates.length k))).foldl stp B).getD
            (sig f g C.gates.length k C.output) false =
            PEqualNP.MetaComplexity.circuitFun n C (fun a => z (f k a) || z (g k a))) := by
      intro k B hB hP
      obtain ⟨V, hV⟩ := hP
      apply copy_step C n hRB _ _ B _ hB
      · intro a ha
        have hr := hrho k a ha
        refine ⟨by rw [hsig_lt k a ha]; omega, ?_⟩
        rw [hsig_lt k a ha, hV, List.getD_append _ _ _ _ (by rw [hW1len]; exact hr)]
        exact (hW1val k ⟨a, ha⟩).trans (getD_ofFn' (fun a => z (f k a) || z (g k a)) a ha).symm
      · intro a ha; exact hsig_ge k a ha
    obtain ⟨L0, P0, O0⟩ := step 0 W1 (by rw [hW1len, hv0]; omega) ⟨[], by simp⟩
    set B1 := (C.gates.map (cp (sig f g C.gates.length 0))).foldl stp W1 with hB1def
    obtain ⟨L1, P1, O1⟩ := step 1 B1 (by rw [L0, hv0, hv1]; omega)
      (by obtain ⟨V, hV⟩ := P0; exact ⟨V, hV⟩)
    set B2 := (C.gates.map (cp (sig f g C.gates.length 1))).foldl stp B1 with hB2def
    obtain ⟨L2, P2, O2⟩ := step 2 B2 (by rw [L1, hv1, hv2]; omega)
      (by
        obtain ⟨V, hV⟩ := P1
        obtain ⟨V0, hV0⟩ := P0
        exact ⟨V0 ++ V, by rw [hV, hV0, List.append_assoc]⟩)
    set B3 := (C.gates.map (cp (sig f g C.gates.length 2))).foldl stp B2 with hB3def
    have hL3 : B3.length = m + (EE f g).length + 3 * C.gates.length := by
      rw [L2, hv2]; omega
    rw [List.foldl_cons, List.foldl_cons, List.foldl_nil]
    by_cases ho : C.output < n + C.gates.length
    · rw [if_pos ho, key B3 _ _ _ _ hL3 (hout 0) (hout 1) (hout 2)]
      obtain ⟨V2, hV2⟩ := P2
      obtain ⟨V1, hV1⟩ := P1
      have e0 : B3.getD (outw f g C 0) false =
          PEqualNP.MetaComplexity.circuitFun n C (fun a => z (f 0 a) || z (g 0 a)) := by
        obtain ⟨o1, o2⟩ := O0 ho
        unfold outw
        rw [if_pos ho, hV2, hV1, List.append_assoc, List.getD_append _ _ _ _ o1, o2]
      have e1 : B3.getD (outw f g C 1) false =
          PEqualNP.MetaComplexity.circuitFun n C (fun a => z (f 1 a) || z (g 1 a)) := by
        obtain ⟨o1, o2⟩ := O1 ho
        unfold outw
        rw [if_pos ho, hV2, List.getD_append _ _ _ _ o1, o2]
      have e2 : B3.getD (outw f g C 2) false =
          PEqualNP.MetaComplexity.circuitFun n C (fun a => z (f 2 a) || z (g 2 a)) := by
        obtain ⟨o1, o2⟩ := O2 ho
        unfold outw
        rw [if_pos ho, o2]
      rw [e0, e1, e2]
      exact (hex (fun k => PEqualNP.MetaComplexity.circuitFun n C (fun a => z (f k a) || z (g k a)))).symm
    · rw [if_neg ho]
      rw [List.getD_eq_default _ _ (by simp only [stp, List.length_append, List.length_singleton, hL3]; omega)]
      have hcf0 : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C y = false := by
        intro y
        show (C.wires (List.ofFn y)).getD C.output false = false
        rw [List.getD_eq_default]
        rw [wires_eq, len_fold]
        simp only [List.length_ofFn]
        omega
      simp [hcf0]

end PEqualNP.Outside.L_meta_8327

theorem PEqualNP.Outside.L_meta_8327 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin (3 : ℕ) → Fin x1 → Fin x2) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x2 → PEqualNP.TopForm.IsAO2 x1 x5 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x8 ∧ x8.size = (3 : ℕ) * x5.size + Fintype.card { x9 : Fin (3 : ℕ) × Fin x1 // x3 x9.1 x9.2 ≠ x4 x9.1 x9.2 } + (2 : ℕ) ∧ ∀ (x9 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x8 x9 = Decidable.decide (∃ (x10 : Fin (3 : ℕ)), (PEqualNP.MetaComplexity.circuitFun x1 x5 fun (x11 : Fin x1) => x9 (x3 x10 x11) || x9 (x4 x10 x11)) = Bool.true) := by
  intro x1 x2 x3 x4 x5 h1 h2
  exact ⟨PEqualNP.Outside.L_meta_8327.DD x3 x4 x5, PEqualNP.Outside.L_meta_8327.main x1 x2 x3 x4 x5 h1 h2⟩
