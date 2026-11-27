import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19223_aux

open PEqualNP.CircuitLowerBounds

def step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

theorem foldl_len : ∀ (gs : List Gate) (W : List Bool),
    (gs.foldl step W).length = W.length + gs.length
  | [], W => by simp
  | g :: gs, W => by
    rw [List.foldl_cons, foldl_len gs]; simp [step]; omega

theorem getD_pre (W R : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ R).getD i false = W.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_app (W R : List Bool) (i : ℕ) :
    (W ++ R).getD (W.length + i) false = R.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [List.getD_eq_getElem?_getD]

theorem getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) (k : ℕ) (h : k < n) :
    (List.ofFn f).getD k false = f ⟨k, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem foldl_pre : ∀ (gs : List Gate) (W : List Bool), ∃ R, gs.foldl step W = W ++ R
  | [], W => ⟨[], by simp⟩
  | g :: gs, W => by
    obtain ⟨R, hR⟩ := foldl_pre gs (step W g)
    exact ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: R, by
      rw [List.foldl_cons, hR]; simp [step]⟩

theorem pre_getD (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (gs.foldl step W).getD i false = W.getD i false := by
  obtain ⟨R, hR⟩ := foldl_pre gs W
  rw [hR, getD_pre _ _ _ h]

def rl (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem copy (f : ℕ → ℕ) (n0 B : ℕ) (h1 : ∀ k < n0, f k < B)
    (h2 : ∀ k, n0 ≤ k → f k = B + (k - n0)) :
    ∀ (gs : List Gate) (S W : List Bool), n0 ≤ S.length → W.length + n0 = S.length + B →
    (∀ k, W.getD (f k) false = S.getD k false) →
    ∀ k, ((gs.map (rl f)).foldl step W).getD (f k) false = (gs.foldl step S).getD k false
  | [], S, W, _, _, hI => by simpa using hI
  | g :: gs, S, W, hS, hL, hI => by
    have hv : g.op.eval ((g.inputs.map f).map fun i => W.getD i false) =
        g.op.eval (g.inputs.map fun i => S.getD i false) := by
      rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hI i)
    have e1 : step W (rl f g) = W ++ [g.op.eval (g.inputs.map fun i => S.getD i false)] := by
      show W ++ [g.op.eval ((g.inputs.map f).map fun i => W.getD i false)] = _
      rw [hv]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e1]
    apply copy f n0 B h1 h2 gs
    · simp [step]; omega
    · simp [step]; omega
    · intro k
      simp only [step]
      rcases lt_trichotomy k S.length with hk | hk | hk
      · have hf : f k < W.length := by
          by_cases hk0 : k < n0
          · have := h1 k hk0; omega
          · rw [h2 k (by omega)]; omega
        rw [getD_pre _ _ _ hf, getD_pre _ _ _ hk, hI]
      · subst hk
        rw [h2 _ hS]
        have : B + (S.length - n0) = W.length + 0 := by omega
        rw [this, getD_app]
        have h0 : S.length = S.length + 0 := rfl
        rw [h0, getD_app]
      · rw [h2 k (by omega), getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]

theorem indep : ∀ (gs : List Gate) (W : List Bool), (∀ g ∈ gs, ∀ a ∈ g.inputs, a < W.length) →
    gs.foldl step W = W ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => W.getD i false))
  | [], W, _ => by simp
  | g :: gs, W, h => by
    rw [List.foldl_cons, indep gs (step W g) (fun g' hg' a ha => by
      have := h g' (List.mem_cons_of_mem _ hg') a ha
      simp [step]; omega)]
    simp only [step, List.map_cons, List.append_assoc, List.singleton_append]
    congr 2
    apply List.map_congr_left
    intro g' hg'
    congr 1
    apply List.map_congr_left
    intro a ha
    exact getD_pre _ _ _ (h g' (List.mem_cons_of_mem _ hg') a ha)

theorem any_split (g : ℕ → Bool) (m : ℕ) : ∀ q, (List.range (q * m)).any g =
    (List.range q).any (fun t => (List.range m).any (fun i => g (t * m + i)))
  | 0 => by simp
  | q + 1 => by
    rw [Nat.succ_mul, List.range_add, List.any_append, any_split g m q, List.range_succ,
      List.any_append]
    simp [List.any_map, Function.comp_def]

theorem any_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ i ∈ l, f i = g i) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

def bs (N L K : ℕ) : ℕ → ℕ
  | 0 => N
  | t + 1 => N + L + t * (L + K)

theorem bs_ge (N L K t : ℕ) : N ≤ bs N L K t := by
  cases t <;> simp [bs] <;> omega

theorem bs_ss (N L K t : ℕ) : bs N L K (t + 2) = bs N L K (t + 1) + L + K := by
  simp only [bs]; ring

def piX (w m q t k : ℕ) : ℕ :=
  if k < w * m then k / m * (q * m) + (t * m + k % m)
  else w * (q * m) + (w * (t * m) + (k - w * m))

def fm (w m q L t k : ℕ) : ℕ :=
  if k < 2 * w * m then piX w m q t k else bs (2 * w * (q * m)) L (w * w) t + (k - 2 * w * m)

def acc (w m q L : ℕ) (o : Fin w → Fin w → ℕ) : ℕ → Fin w → Fin w → ℕ
  | 0, j, l => fm w m q L 0 (o j l)
  | t + 1, j, l => bs (2 * w * (q * m)) L (w * w) (t + 1) + L + (finProdFinEquiv (j, l)).val

def ors (w m q L : ℕ) (o : Fin w → Fin w → ℕ) (t : ℕ) : List Gate :=
  List.ofFn (fun p : Fin (w * w) => (⟨GateOp.or,
    [acc w m q L o t (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2,
     fm w m q L (t + 1) (o (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)]⟩ : Gate))

def GG (w m q : ℕ) (C : Circuit) (o : Fin w → Fin w → ℕ) : ℕ → List Gate
  | 0 => C.gates.map (rl (fm w m q C.gates.length 0))
  | t + 1 => GG w m q C o t ++ (C.gates.map (rl (fm w m q C.gates.length (t + 1))) ++
      ors w m q C.gates.length o t)

theorem GG_len (w m q : ℕ) (C : Circuit) (o : Fin w → Fin w → ℕ) :
    ∀ t, (GG w m q C o t).length = C.gates.length + t * (C.gates.length + w * w)
  | 0 => by simp [GG]
  | t + 1 => by
    simp only [GG, List.length_append, List.length_map, ors, List.length_ofFn, GG_len w m q C o t]
    ring

theorem GG_fan (w m q : ℕ) (C : Circuit) (o : Fin w → Fin w → ℕ)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) :
    ∀ t, PEqualNP.MetaComplexity.FanInTwo ⟨GG w m q C o t, 0⟩
  | 0 => by
    intro g hg
    simp only [GG, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hF g0 hg0
    exact ⟨h1, by simpa [rl] using h2⟩
  | t + 1 => by
    intro g hg
    simp only [GG, List.mem_append, List.mem_map, ors, List.mem_ofFn] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩ | ⟨p, rfl⟩
    · exact GG_fan w m q C o hF t g hg
    · obtain ⟨h1, h2⟩ := hF g0 hg0
      exact ⟨h1, by simpa [rl] using h2⟩
    · exact ⟨by simp, by simp⟩

theorem piX_lt {w m q t k : ℕ} (hm : 1 ≤ m) (ht : t < q) (hk : k < 2 * w * m) :
    piX w m q t k < 2 * w * (q * m) := by
  unfold piX
  split_ifs with h
  · have ha : k / m < w := (Nat.div_lt_iff_lt_mul (by omega)).2 h
    have hr : k % m < m := Nat.mod_lt _ (by omega)
    have h1 : (k / m + 1) * (q * m) ≤ w * (q * m) := Nat.mul_le_mul_right _ ha
    have h2 : (t + 1) * m ≤ q * m := Nat.mul_le_mul_right _ ht
    nlinarith
  · have h2 : w * ((t + 1) * m) ≤ w * (q * m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ht)
    have e : 2 * w * m = w * m + w * m := by ring
    have hd : k - w * m < w * m := by omega
    nlinarith

theorem fm_lt {w m q L t k : ℕ} (hm : 1 ≤ m) (ht : t < q) (hk : k < 2 * w * m + L) :
    fm w m q L t k < bs (2 * w * (q * m)) L (w * w) t + L := by
  unfold fm
  split_ifs with h
  · have := piX_lt hm ht h; have := bs_ge (2 * w * (q * m)) L (w * w) t; omega
  · omega

theorem acc_lt {w m q L : ℕ} (o : Fin w → Fin w → ℕ) (hm : 1 ≤ m)
    (hO : ∀ j l, o j l < 2 * w * m + L) (j l : Fin w) :
    ∀ t, t < q → acc w m q L o t j l < bs (2 * w * (q * m)) L (w * w) (t + 1)
  | 0, ht => by
    have := fm_lt (L := L) (t := 0) hm ht (hO j l)
    simpa [acc, bs] using this
  | t + 1, ht => by
    rw [bs_ss]; simp only [acc]
    have := (finProdFinEquiv (j, l)).isLt
    omega

theorem copy_t {w m q : ℕ} (hm : 1 ≤ m) (C : Circuit) (x : Fin (2 * w * (q * m)) → Bool)
    (t : ℕ) (ht : t < q) (W : List Bool)
    (hW : W.length = bs (2 * w * (q * m)) C.gates.length (w * w) t)
    (hX : ∀ i < 2 * w * (q * m), W.getD i false = (List.ofFn x).getD i false) (k : ℕ) :
    ((C.gates.map (rl (fm w m q C.gates.length t))).foldl step W).getD
      (fm w m q C.gates.length t k) false =
    (C.wires (List.ofFn (fun k : Fin (2 * w * m) =>
      (List.ofFn x).getD (piX w m q t k) false))).getD k false := by
  refine copy (fm w m q C.gates.length t) (2 * w * m)
    (bs (2 * w * (q * m)) C.gates.length (w * w) t) ?_ ?_ C.gates _ W (by simp)
    (by rw [List.length_ofFn, hW, Nat.add_comm]) ?_ k
  · intro k hk
    have := piX_lt hm ht hk
    have := bs_ge (2 * w * (q * m)) C.gates.length (w * w) t
    simp only [fm, if_pos hk]; omega
  · intro k hk; simp only [fm, if_neg (by omega : ¬ k < 2 * w * m)]
  · intro k
    by_cases hk : k < 2 * w * m
    · simp only [fm, if_pos hk]; rw [hX _ (piX_lt hm ht hk), getD_ofFn_lt _ _ hk]
    · simp only [fm, if_neg hk]
      rw [getD_ge _ _ (by omega), getD_ge _ _ (by simp; omega)]

theorem main_ind {w m q : ℕ} (hm : 1 ≤ m) (C : Circuit) (o : Fin w → Fin w → ℕ)
    (hO : ∀ j l, o j l < 2 * w * m + C.gates.length) (x : Fin (2 * w * (q * m)) → Bool) :
    ∀ t, t < q →
    ((GG w m q C o t).foldl step (List.ofFn x)).length =
      bs (2 * w * (q * m)) C.gates.length (w * w) (t + 1) ∧
    ∀ j l, ((GG w m q C o t).foldl step (List.ofFn x)).getD
      (acc w m q C.gates.length o t j l) false =
      (List.range (t + 1)).any (fun t' => (C.wires (List.ofFn (fun k : Fin (2 * w * m) =>
        (List.ofFn x).getD (piX w m q t' k) false))).getD (o j l) false)
  | 0, ht => by
    refine ⟨?_, fun j l => ?_⟩
    · simp [GG, foldl_len, bs]
    · simp only [GG, acc]
      rw [copy_t hm C x 0 ht _ (by simp [bs]) (fun _ _ => rfl)]
      simp
  | t + 1, ht => by
    obtain ⟨hL, hV⟩ := main_ind hm C o hO x t (by omega)
    obtain ⟨W, hW⟩ : ∃ W, (GG w m q C o t).foldl step (List.ofFn x) = W := ⟨_, rfl⟩
    rw [hW] at hL hV
    have hXW : ∀ i < 2 * w * (q * m), W.getD i false = (List.ofFn x).getD i false := by
      intro i hi; rw [← hW]; exact pre_getD _ _ _ (by simpa using hi)
    obtain ⟨U, hU⟩ : ∃ U, (C.gates.map (rl (fm w m q C.gates.length (t + 1)))).foldl step W = U :=
      ⟨_, rfl⟩
    have hUL : U.length = bs (2 * w * (q * m)) C.gates.length (w * w) (t + 1) + C.gates.length := by
      rw [← hU, foldl_len, hL, List.length_map]
    have hE : (GG w m q C o (t + 1)).foldl step (List.ofFn x) =
        U ++ (ors w m q C.gates.length o t).map
          (fun g => g.op.eval (g.inputs.map fun i => U.getD i false)) := by
      rw [← indep]
      · simp only [GG, List.foldl_append, hW, hU]
      · intro g hg a ha
        simp only [ors, List.mem_ofFn] at hg
        obtain ⟨p, rfl⟩ := hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have := acc_lt (q := q) o hm hO (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 t
            (by omega)
          omega
        · have := fm_lt (L := C.gates.length) (t := t + 1) hm ht
            (hO (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
          omega
    refine ⟨?_, fun j l => ?_⟩
    · rw [hE, List.length_append, hUL, List.length_map, ors, List.length_ofFn, bs_ss]
    · have hA : U.getD (acc w m q C.gates.length o t j l) false =
          (List.range (t + 1)).any (fun t' => (C.wires (List.ofFn (fun k : Fin (2 * w * m) =>
            (List.ofFn x).getD (piX w m q t' k) false))).getD (o j l) false) := by
        rw [← hU, pre_getD _ _ _ (by rw [hL]; exact acc_lt o hm hO j l t (by omega)), hV]
      have hB := copy_t hm C x (t + 1) ht W hL hXW (o j l)
      rw [hU] at hB
      have hidx : acc w m q C.gates.length o (t + 1) j l = U.length + (finProdFinEquiv (j, l)).val := by
        simp only [acc, hUL]
      have hlt := (finProdFinEquiv (j, l)).isLt
      rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false, ← hA, ← hB,
        hE, hidx, getD_app, List.getD_eq_getElem?_getD, List.getElem?_map, ors, List.getElem?_ofFn,
        dif_pos hlt, Fin.eta, Equiv.symm_apply_apply]
      simp only [Option.map_some, Option.getD_some, GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id,
        Bool.or_false]

end PEqualNP.Outside.L_meta_19223_aux

open PEqualNP.Outside.L_meta_19223_aux in
theorem PEqualNP.Outside.L_meta_19223 : ∀ (w m q s : ℕ), 1 ≤ w → 1 ≤ m → 1 ≤ q → (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin w → Fin w → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∀ x : Fin (2 * w * m) → Bool, ∀ j l : Fin w, (C.wires (List.ofFn x)).getD (o j l) false = (List.range m).any (fun i => (List.ofFn x).getD (j.val * m + i) false && (List.ofFn x).getD (w * m + w * i + l.val) false)) → (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin w → Fin w → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ q * s + w * w * (q - 1) ∧ ∀ x : Fin (2 * w * (q * m)) → Bool, ∀ j l : Fin w, (C.wires (List.ofFn x)).getD (o j l) false = (List.range (q * m)).any (fun i => (List.ofFn x).getD (j.val * (q * m) + i) false && (List.ofFn x).getD (w * (q * m) + w * i + l.val) false)) := by
  intro w m q s hw hm hq ⟨C, o, hF, hs, hC⟩
  have hwl : ∀ X : List Bool, (C.wires X).length = X.length + C.gates.length :=
    fun X => foldl_len C.gates X
  have hjb : ∀ (j : Fin w) (i : ℕ), i < m → j.val * m + i < w * m := by
    intro j i hi
    have := Nat.mul_le_mul_right m (show j.val + 1 ≤ w from j.isLt)
    nlinarith
  have hlb : ∀ (l : Fin w) (i : ℕ), i < m → w * m + w * i + l.val < 2 * w * m := by
    intro l i hi
    have := Nat.mul_le_mul_left w (show i + 1 ≤ m from hi)
    have := l.isLt
    nlinarith
  have hO : ∀ j l, o j l < 2 * w * m + C.gates.length := by
    intro j l
    by_contra h
    have h1 := hC (fun _ => true) j l
    rw [getD_ge _ _ (by rw [hwl, List.length_ofFn]; omega)] at h1
    have hj := hjb j 0 hm
    have hl := hlb l 0 hm
    have h2 : (List.range m).any (fun i =>
        (List.ofFn (fun _ : Fin (2 * w * m) => true)).getD (j.val * m + i) false &&
        (List.ofFn (fun _ : Fin (2 * w * m) => true)).getD (w * m + w * i + l.val) false) =
        true := by
      rw [List.any_eq_true]
      exact ⟨0, List.mem_range.2 hm, by
        rw [getD_ofFn_lt _ _ (by omega), getD_ofFn_lt _ _ hl]; rfl⟩
    rw [h2] at h1; exact absurd h1 (by simp)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  refine ⟨⟨GG w m (r + 1) C o r, 0⟩, fun j l => acc w m (r + 1) C.gates.length o r j l,
    GG_fan w m (r + 1) C o hF r, ?_, ?_⟩
  · show (GG w m (r + 1) C o r).length ≤ _
    rw [GG_len]
    have h1 : C.gates.length ≤ s := hs
    have := Nat.mul_le_mul_left r h1
    simp only [Nat.add_sub_cancel]
    nlinarith
  · intro x j l
    have hM := (main_ind hm C o hO x r (by omega)).2 j l
    show ((GG w m (r + 1) C o r).foldl step (List.ofFn x)).getD _ false = _
    rw [hM, any_split]
    apply any_congr'
    intro t ht
    rw [List.mem_range] at ht
    rw [hC]
    apply any_congr'
    intro i hi
    rw [List.mem_range] at hi
    have hjm := hjb j i hi
    have hl := hlb l i hi
    rw [getD_ofFn_lt _ _ (by omega), getD_ofFn_lt _ _ hl]
    have e1 : piX w m (r + 1) t (j.val * m + i) = j.val * ((r + 1) * m) + (t * m + i) := by
      unfold piX; rw [if_pos hjm]
      have hd : (j.val * m + i) / m = j.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi]; simp
      have hmod : (j.val * m + i) % m = i := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
      rw [hd, hmod]
    have e2 : piX w m (r + 1) t (w * m + w * i + l.val) =
        w * ((r + 1) * m) + w * (t * m + i) + l.val := by
      unfold piX; rw [if_neg (by omega)]
      rw [show w * m + w * i + l.val - w * m = w * i + l.val by omega]; ring
    rw [e1, e2]
