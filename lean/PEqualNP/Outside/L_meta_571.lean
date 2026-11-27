import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_571_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

private lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

private lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

private lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (run gs W) (run (gs.map (relGate n m π)) W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [getD_ofFn x _ (π ⟨w, hw⟩).isLt, getD_ofFn (x ∘ π) w hw]
    rfl
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

private lemma hasCircuitSize_congr {m : ℕ} {f1 f2 : (Fin m → Bool) → Bool} {s1 s2 : ℕ}
    (hf : ∀ x, f1 x = f2 x) (hs : s1 = s2) (hc : HasCircuitSize m f1 s1) :
    HasCircuitSize m f2 s2 := by
  subst hs
  obtain ⟨C, hfan, hsize, hev⟩ := hc
  exact ⟨C, hfan, hsize, fun x => (hev x).trans (hf x)⟩

private lemma appendWedge {m : ℕ} (f : (Fin m → Bool) → Bool) (a b c : Fin m) (s : ℕ)
    (hc : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || (x c && (x a || x b))) (s + 3) := by
  obtain ⟨C, hfan, hsize, hev⟩ := hc
  let k := m + C.gates.length
  let outW := if C.output < k then C.output else k + 3
  let g1 : Gate := ⟨GateOp.or, [a.val, b.val]⟩
  let g2 : Gate := ⟨GateOp.and, [c.val, k]⟩
  let g3 : Gate := ⟨GateOp.or, [outW, k + 1]⟩
  let C' : Circuit := ⟨C.gates ++ [g1, g2, g3], k + 2⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro gate hgate
    simp only [C', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with h | rfl | rfl | rfl
    · exact hfan gate h
    · exact ⟨by simp [g1], by simp [g1]⟩
    · exact ⟨by simp [g2], by simp [g2]⟩
    · exact ⟨by simp [g3], by simp [g3]⟩
  · change C'.gates.length ≤ s + 3
    change C.gates.length ≤ s at hsize
    simp only [C', List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x
    set W0 := run C.gates (List.ofFn x)
    have hW0_len : W0.length = k := by simp [W0, run_length, k]
    have hW0_in (i : Fin m) : W0.getD i.val false = x i := by
      rw [show W0 = run C.gates (List.ofFn x) from rfl,
        run_getD_of_lt _ _ i.val (by simp), getD_ofFn x i.val i.isLt]
    have hW0_out : W0.getD outW false = f x := by
      rw [← hev x]
      change W0.getD outW false = W0.getD C.output false
      by_cases ho : C.output < k
      · simp [outW, ho]
      · simp only [outW, ho, ↓reduceIte]
        rw [List.getD_eq_default W0 _ (by rw [hW0_len]; omega),
          List.getD_eq_default W0 _ (by rw [hW0_len]; omega)]
    set W1 := step W0 g1
    set W2 := step W1 g2
    set W3 := step W2 g3
    have hW1_len : W1.length = k + 1 := by simp [W1, step, hW0_len]
    have hW1_val : W1.getD k false = (x a || x b) := by
      rw [← hW0_len]
      simp only [W1, step, getD_snoc_eq, g1, GateOp.eval, List.map_cons, List.map_nil]
      rw [hW0_in a, hW0_in b]
      simp
    have hW2_len : W2.length = k + 2 := by simp [W2, step, hW1_len]
    have hW2_val : W2.getD (k + 1) false = (x c && (x a || x b)) := by
      rw [← hW1_len]
      simp only [W2, step, getD_snoc_eq, g2, GateOp.eval, List.map_cons, List.map_nil]
      rw [show W1.getD c.val false = W0.getD c.val false from
          getD_snoc_lt _ _ _ (by rw [hW0_len]; have := c.isLt; omega),
        hW0_in c, hW1_val]
      simp
    have hW2_out : W2.getD outW false = f x := by
      by_cases ho : C.output < k
      · have hout_lt : outW < W0.length := by simp [outW, ho, hW0_len]
        rw [show W2.getD outW false = W1.getD outW false from
            getD_snoc_lt _ _ _ (by rw [hW1_len]; rw [hW0_len] at hout_lt; omega),
          show W1.getD outW false = W0.getD outW false from
            getD_snoc_lt _ _ _ hout_lt,
          hW0_out]
      · have hout : outW = k + 3 := by simp [outW, ho]
        rw [← hW0_out, hout,
          List.getD_eq_default W2 _ (by rw [hW2_len]; omega),
          List.getD_eq_default W0 _ (by rw [hW0_len]; omega)]
    have hW3_eq : C'.wires (List.ofFn x) = W3 := by
      change run (C.gates ++ [g1, g2, g3]) (List.ofFn x) = W3
      rw [run_append]
      rfl
    change (C'.wires (List.ofFn x)).getD (k + 2) false = _
    rw [hW3_eq, ← hW2_len]
    simp only [W3, step, getD_snoc_eq, g3, GateOp.eval, List.map_cons, List.map_nil]
    rw [hW2_out, hW2_val]
    simp

private lemma appendWedges {m : ℕ} (f : (Fin m → Bool) → Bool)
    (ts : List (Fin m × Fin m × Fin m)) (s : ℕ) (hc : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || ts.any (fun t => x t.2.2 && (x t.1 || x t.2.1)))
      (s + 3 * ts.length) := by
  induction ts with
  | nil =>
    exact hasCircuitSize_congr (fun x => by simp) (by simp) hc
  | cons t ts ih =>
    have hstep := appendWedge _ t.1 t.2.1 t.2.2 _ ih
    refine hasCircuitSize_congr (fun x => ?_) (by simp; omega) hstep
    simp only [List.any_cons]
    cases f x <;> cases x t.2.2 <;> cases x t.1 <;> cases x t.2.1 <;> cases ts.any _ <;> rfl

private def evenPathPred (N h : ℕ) (u v : Fin N) (x : Fin (N + 2 * h) → Bool) : Bool :=
  decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
    ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
     (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
     ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))

private lemma evenPath_from_u (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (hh : 1 ≤ h) (s : ℕ)
    (h1 : HasCircuitSize (N + 1)
      (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s) :
    HasCircuitSize (N + 2 * h)
      (fun x : Fin (N + 2 * h) → Bool =>
        g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || evenPathPred N h u v x)
      (3 * h + s) := by
  let π : Fin (N + 1) → Fin (N + 2 * h) := fun i =>
    if hi : i.val < N then Fin.castAdd (2 * h) ⟨i.val, hi⟩ else Fin.natAdd N ⟨0, by omega⟩
  have hπ_cast : ∀ i : Fin N, π i.castSucc = Fin.castAdd (2 * h) i := by
    intro i
    apply Fin.ext
    simp [π, i.isLt]
  have hπ_last : π (Fin.last N) = Fin.natAdd N ⟨0, by omega⟩ := by
    simp [π]
  have hrel := relabel_size π _ s h1
  let ts : List (Fin (N + 2 * h) × Fin (N + 2 * h) × Fin (N + 2 * h)) :=
    List.ofFn (fun k : Fin h =>
      (Fin.natAdd N ⟨2 * k.val, by omega⟩,
       if hk : 2 * k.val + 2 < 2 * h then Fin.natAdd N ⟨2 * k.val + 2, hk⟩
       else Fin.castAdd (2 * h) v,
       Fin.natAdd N ⟨2 * k.val + 1, by omega⟩))
  have hts_len : ts.length = h := by simp [ts]
  have hw := appendWedges _ ts s hrel
  refine hasCircuitSize_congr (fun x => ?_) (by rw [hts_len]; omega) hw
  have hbase : (fun i : Fin N => (x ∘ π) i.castSucc) = (fun i : Fin N => x (Fin.castAdd (2 * h) i)) := by
    funext i
    simp [Function.comp, hπ_cast]
  have hp : (((x ∘ π) u.castSucc && (x ∘ π) (Fin.last N)) ||
      ts.any (fun t => x t.2.2 && (x t.1 || x t.2.1))) = evenPathPred N h u v x := by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp, hπ_cast, hπ_last, evenPathPred, Bool.or_eq_true, Bool.and_eq_true,
      List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨hu, hz0⟩ | ⟨t, ht, hc, hab⟩)
      · exact ⟨⟨0, by omega⟩, hz0, Or.inl ⟨rfl, hu⟩⟩
      · simp only [ts, List.mem_ofFn] at ht
        obtain ⟨k, rfl⟩ := ht
        rcases hab with ha | hb
        · exact ⟨⟨2 * k.val, by omega⟩, ha, Or.inr (Or.inr ⟨⟨2 * k.val + 1, by omega⟩, rfl, hc⟩)⟩
        · by_cases hk : 2 * k.val + 2 < 2 * h
          · simp only [hk, ↓reduceDIte] at hb
            exact ⟨⟨2 * k.val + 1, by omega⟩, hc, Or.inr (Or.inr ⟨⟨2 * k.val + 2, hk⟩, rfl, hb⟩)⟩
          · simp only [hk, ↓reduceDIte] at hb
            exact ⟨⟨2 * k.val + 1, by omega⟩, hc, Or.inr (Or.inl ⟨by dsimp; omega, hb⟩)⟩
    · rintro ⟨i, hi, (⟨hi0, hu⟩ | ⟨hilast, hv⟩ | ⟨j, hji, hj⟩)⟩
      · left
        have hi' : i = ⟨0, by omega⟩ := Fin.ext hi0
        rw [hi'] at hi
        exact ⟨hu, hi⟩
      · right
        let k : Fin h := ⟨h - 1, by omega⟩
        refine ⟨(Fin.natAdd N ⟨2 * k.val, by omega⟩,
          if hk : 2 * k.val + 2 < 2 * h then Fin.natAdd N ⟨2 * k.val + 2, hk⟩
          else Fin.castAdd (2 * h) v,
          Fin.natAdd N ⟨2 * k.val + 1, by omega⟩), ?_, ?_, ?_⟩
        · simp only [ts, List.mem_ofFn]
          exact ⟨k, rfl⟩
        · have hi' : i = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
          rw [← hi']
          exact hi
        · right
          have hnot : ¬ (2 * k.val + 2 < 2 * h) := by dsimp [k]; omega
          simp only [hnot, ↓reduceDIte]
          exact hv
      · right
        by_cases hpar : i.val % 2 = 0
        · let k : Fin h := ⟨i.val / 2, by omega⟩
          refine ⟨(Fin.natAdd N ⟨2 * k.val, by omega⟩,
            if hk : 2 * k.val + 2 < 2 * h then Fin.natAdd N ⟨2 * k.val + 2, hk⟩
            else Fin.castAdd (2 * h) v,
            Fin.natAdd N ⟨2 * k.val + 1, by omega⟩), ?_, ?_, ?_⟩
          · simp only [ts, List.mem_ofFn]
            exact ⟨k, rfl⟩
          · have hj' : j = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
            rw [← hj']
            exact hj
          · left
            have hi' : i = ⟨2 * k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
            rw [← hi']
            exact hi
        · let k : Fin h := ⟨i.val / 2, by omega⟩
          refine ⟨(Fin.natAdd N ⟨2 * k.val, by omega⟩,
            if hk : 2 * k.val + 2 < 2 * h then Fin.natAdd N ⟨2 * k.val + 2, hk⟩
            else Fin.castAdd (2 * h) v,
            Fin.natAdd N ⟨2 * k.val + 1, by omega⟩), ?_, ?_, ?_⟩
          · simp only [ts, List.mem_ofFn]
            exact ⟨k, rfl⟩
          · have hi' : i = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
            rw [← hi']
            exact hi
          · right
            have hk : 2 * k.val + 2 < 2 * h := by dsimp [k]; omega
            simp only [hk, ↓reduceDIte]
            have hj' : j = ⟨2 * k.val + 2, hk⟩ := Fin.ext (by dsimp [k]; omega)
            rw [← hj']
            exact hj
  rw [hbase, Bool.or_assoc, hp]

private lemma evenPath_from_v (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (hh : 1 ≤ h) (s : ℕ)
    (h2 : HasCircuitSize (N + 1)
      (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s) :
    HasCircuitSize (N + 2 * h)
      (fun x : Fin (N + 2 * h) → Bool =>
        g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || evenPathPred N h u v x)
      (3 * h + s) := by
  have hrev_base := evenPath_from_u N h v u g hh s h2
  let rev : Fin (N + 2 * h) → Fin (N + 2 * h) := fun idx =>
    if hi : idx.val < N then Fin.castAdd (2 * h) ⟨idx.val, hi⟩
    else Fin.natAdd N ⟨2 * h - 1 - (idx.val - N), by omega⟩
  have hrev_cast : ∀ i : Fin N, rev (Fin.castAdd (2 * h) i) = Fin.castAdd (2 * h) i := by
    intro i
    simp [rev, i.isLt]
  have hrev_nat : ∀ i : Fin (2 * h),
      rev (Fin.natAdd N i) = Fin.natAdd N ⟨2 * h - 1 - i.val, by omega⟩ := by
    intro i
    have hnot : ¬ (N + i.val < N) := by omega
    simp only [rev, Fin.val_natAdd, hnot, ↓reduceDIte]
    congr 1
    apply Fin.ext
    dsimp
    omega
  have hrel := relabel_size rev _ (3 * h + s) hrev_base
  refine hasCircuitSize_congr (fun x => ?_) rfl hrel
  have hbase : (fun i : Fin N => (x ∘ rev) (Fin.castAdd (2 * h) i)) =
      (fun i : Fin N => x (Fin.castAdd (2 * h) i)) := by
    funext i
    simp [Function.comp, hrev_cast]
  have hp : evenPathPred N h v u (x ∘ rev) = evenPathPred N h u v x := by
    apply Bool.eq_iff_iff.mpr
    simp only [evenPathPred, Function.comp, hrev_cast, hrev_nat, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, (⟨hi0, hv⟩ | ⟨hilast, hu⟩ | ⟨j, hji, hj⟩)⟩
      · refine ⟨⟨2 * h - 1 - i.val, by omega⟩, hi, Or.inr (Or.inl ⟨by dsimp; omega, hv⟩)⟩
      · refine ⟨⟨2 * h - 1 - i.val, by omega⟩, hi, Or.inl ⟨by dsimp; omega, hu⟩⟩
      · refine ⟨⟨2 * h - 1 - j.val, by omega⟩, hj,
          Or.inr (Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by dsimp; omega, hi⟩)⟩
    · rintro ⟨i, hi, (⟨hi0, hu⟩ | ⟨hilast, hv⟩ | ⟨j, hji, hj⟩)⟩
      · refine ⟨⟨2 * h - 1 - i.val, by omega⟩, ?_, Or.inr (Or.inl ⟨by dsimp; omega, hu⟩)⟩
        have hidx : (⟨2 * h - 1 - (2 * h - 1 - i.val), by omega⟩ : Fin (2 * h)) = i :=
          Fin.ext (by dsimp; omega)
        simpa [hidx] using hi
      · refine ⟨⟨2 * h - 1 - i.val, by omega⟩, ?_, Or.inl ⟨by dsimp; omega, hv⟩⟩
        have hidx : (⟨2 * h - 1 - (2 * h - 1 - i.val), by omega⟩ : Fin (2 * h)) = i :=
          Fin.ext (by dsimp; omega)
        simpa [hidx] using hi
      · refine ⟨⟨2 * h - 1 - j.val, by omega⟩, ?_,
          Or.inr (Or.inr ⟨⟨2 * h - 1 - i.val, by omega⟩, by dsimp; omega, ?_⟩)⟩
        · have hidx : (⟨2 * h - 1 - (2 * h - 1 - j.val), by omega⟩ : Fin (2 * h)) = j :=
            Fin.ext (by dsimp; omega)
          simpa [hidx] using hj
        · have hidx : (⟨2 * h - 1 - (2 * h - 1 - i.val), by omega⟩ : Fin (2 * h)) = i :=
            Fin.ext (by dsimp; omega)
          simpa [hidx] using hi
  rw [hbase, hp]

end PEqualNP.Outside.L_meta_571_aux

open PEqualNP.Outside.L_meta_571_aux in
theorem PEqualNP.Outside.L_meta_571 :
    ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), u ≠ v → 3 ≤ h → g (fun _ : Fin N => false) = false → (∃ x : Fin N → Bool, x u = true ∧ g x = false) → (∃ x : Fin N → Bool, x v = true ∧ g x = false) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g _ hh _ _ _ s
  exact ⟨evenPath_from_u N h u v g (by omega) s, evenPath_from_v N h u v g (by omega) s⟩
