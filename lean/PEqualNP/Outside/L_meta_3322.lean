import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]


lemma rawWire (σ : Equiv.Perm (Fin 14)) {i : ℕ} (hi : i < 14) :
    wmap 14 14 σ i = (σ ⟨i, hi⟩).val := by simp [wmap, hi]

lemma highWire (σ : Equiv.Perm (Fin 14)) {i : ℕ} (hi : 14 ≤ i) :
    wmap 14 14 σ i = i := by
  simp [wmap, Nat.not_lt.mpr hi]
  omega

lemma wireBound (σ : Equiv.Perm (Fin 14)) {i k : ℕ} (hk : 14 ≤ k) (hi : i < k) :
    wmap 14 14 σ i < k := by
  by_cases h : i < 14
  · rw [rawWire σ h]
    exact lt_of_lt_of_le (σ ⟨i, h⟩).isLt hk
  · rw [highWire σ (by omega)]
    exact hi

lemma wireInjective (σ : Equiv.Perm (Fin 14)) : Function.Injective (wmap 14 14 σ) := by
  intro a b e
  by_cases ha : a < 14 <;> by_cases hb : b < 14
  · rw [rawWire σ ha, rawWire σ hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))
  · rw [rawWire σ ha, highWire σ (by omega)] at e
    have hh := (σ ⟨a, ha⟩).isLt
    omega
  · rw [highWire σ (by omega), rawWire σ hb] at e
    have hh := (σ ⟨b, hb⟩).isLt
    omega
  · rw [highWire σ (by omega), highWire σ (by omega)] at e
    exact e

lemma wireTrans (σ τ : Equiv.Perm (Fin 14)) (i : ℕ) :
    wmap 14 14 (σ.trans τ) i = wmap 14 14 τ (wmap 14 14 σ i) := by
  by_cases hi : i < 14
  · rw [rawWire (σ.trans τ) hi, rawWire σ hi, rawWire τ (σ ⟨i, hi⟩).isLt]
    rfl
  · rw [highWire (σ.trans τ) (by omega), highWire σ (by omega), highWire τ (by omega)]

lemma wireFin14 (σ : Equiv.Perm (Fin 14)) (i : Fin 14) :
    wmap 14 14 σ i.val = (σ i).val := rawWire σ i.isLt

lemma wireFin15 (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    wmap 14 14 σ i.val =
      if i < (14 : Fin 15) then (σ (Fin.ofNat 14 i.val)).val else 14 := by
  by_cases hi : i.val < 14
  · have hf : i < (14 : Fin 15) := hi
    have he : Fin.ofNat 14 i.val = ⟨i.val, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    rw [ite_eq_left hf, rawWire σ hi, he]
  · have hf : ¬ i < (14 : Fin 15) := hi
    rw [ite_eq_right hf, highWire σ (by omega)]
    have := i.isLt
    omega

def chunk (a b : ℕ) : ℕ := 15 * min a b + max a b

def prefixRank (a b c d : ℕ) : ℕ := chunk a b * 225 + chunk c d

lemma sortChunk (u : ℕ → ℕ) (a b : ℕ) :
    chunk (u (min a b)) (u (max a b)) = chunk (u a) (u b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h, chunk, min_comm, max_comm]

lemma sortRank (u : ℕ → ℕ) (a b c d : ℕ) :
    prefixRank (u (min a b)) (u (max a b)) (u (min c d)) (u (max c d)) =
      prefixRank (u a) (u b) (u c) (u d) := by
  unfold prefixRank
  rw [sortChunk u a b, sortChunk u c d]

lemma sortEval (o : GateOp) (h : o = GateOp.and ∨ o = GateOp.or) (F : ℕ → Bool) (a b : ℕ) :
    o.eval [F (min a b), F (max a b)] = o.eval [F a, F b] := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hba, max_eq_left hba]
    rcases h with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma inputGet (x : Fin 14 → Bool) (i : Fin 14) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]


end PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3322 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_3322 :
    ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro f C model nodup two small computes
  dsimp only
  obtain ⟨g₁, g₂, tail, hcirc⟩ : ∃ g₁ g₂ tail, C.gates = g₁ :: g₂ :: tail := by
    change 2 ≤ C.gates.length at two
    cases h : C.gates with
    | nil => simp [h] at two
    | cons g xs =>
      cases xs with
      | nil => simp [h] at two
      | cons g' tail => exact ⟨g, g', tail, rfl⟩
  have hg₁ : g₁ ∈ C.gates := by simp [hcirc]
  have hg₂ : g₂ ∈ C.gates := by simp [hcirc]
  have op₁ := model.1 g₁ hg₁
  have op₂ := model.1 g₂ hg₂
  obtain ⟨a, b, h₁⟩ := List.length_eq_two.mp (model.2.2 g₁ hg₁)
  obtain ⟨c, d, h₂⟩ := List.length_eq_two.mp (model.2.2 g₂ hg₂)
  have reads₁ (i : ℕ) (hi : i ∈ g₁.inputs) : i < 14 := by
    have eq : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = g₁ := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hcirc]
    simpa using model.2.1 0 (by simp [hcirc]) i (eq.symm ▸ hi)
  have reads₂ (i : ℕ) (hi : i ∈ g₂.inputs) : i < 15 := by
    have eq : PEqualNP.MetaComplexity.NestedCover.gateAt C 1 = g₂ := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hcirc]
    simpa using model.2.1 1 (by simp [hcirc]) i (eq.symm ▸ hi)
  have ha := reads₁ a (by simp [h₁])
  have hb := reads₁ b (by simp [h₁])
  have hcc := reads₂ c (by simp [h₂])
  have hd := reads₂ d (by simp [h₂])
  have hab : a ≠ b := by simpa [h₁] using nodup g₁ hg₁
  have hcd : c ≠ d := by simpa [h₂] using nodup g₂ hg₂
  let preserves (σ : Equiv.Perm (Fin 14)) : Prop :=
    ∀ x : Fin 14 → Bool, f (x ∘ σ) = f x
  let score (σ : Equiv.Perm (Fin 14)) : ℕ :=
    prefixRank (wmap 14 14 σ a) (wmap 14 14 σ b) (wmap 14 14 σ c) (wmap 14 14 σ d)
  let achieved (r : ℕ) : Prop := ∃ σ, preserves σ ∧ score σ = r
  have hex : ∃ r, achieved r := ⟨score (Equiv.refl _), Equiv.refl _, fun _ => rfl, rfl⟩
  obtain ⟨σ, hσ, hscore⟩ := Nat.find_spec hex
  have least (τ : Equiv.Perm (Fin 14)) (hτ : preserves τ) : score σ ≤ score (σ.trans τ) := by
    have hcomp : preserves (σ.trans τ) := by
      intro x
      change f ((x ∘ τ) ∘ σ) = f x
      exact (hσ (x ∘ τ)).trans (hτ x)
    rw [hscore]
    exact Nat.find_min' hex ⟨σ.trans τ, hcomp, rfl⟩
  let W := wmap 14 14 σ
  let A : Fin 14 := ⟨min (W a) (W b), lt_of_le_of_lt (min_le_left _ _) (wireBound σ le_rfl ha)⟩
  let B : Fin 14 := ⟨max (W a) (W b), max_lt (wireBound σ le_rfl ha) (wireBound σ le_rfl hb)⟩
  let U : Fin 15 := ⟨min (W c) (W d), lt_of_le_of_lt (min_le_left _ _) (wireBound σ (by decide) hcc)⟩
  let V : Fin 15 := ⟨max (W c) (W d), max_lt (wireBound σ (by decide) hcc) (wireBound σ (by decide) hd)⟩
  have abLt : A < B := min_lt_max.mpr (fun e => hab (wireInjective σ e))
  have cdLt : U < V := min_lt_max.mpr (fun e => hcd (wireInjective σ e))
  let D : Circuit := ⟨tail.map (relGate 14 14 σ), W C.output⟩
  refine ⟨A, B, U, V, g₁.op, g₂.op, D, abLt, cdLt, op₁, op₂, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    change prefixRank A.val B.val U.val V.val ≤
      prefixRank (τ A).val (τ B).val
        (if U < (14 : Fin 15) then (τ (Fin.ofNat 14 U.val)).val else 14)
        (if V < (14 : Fin 15) then (τ (Fin.ofNat 14 V.val)).val else 14)
    have lhs : prefixRank A.val B.val U.val V.val = score σ :=
      sortRank id (W a) (W b) (W c) (W d)
    rw [lhs, ← wireFin14 τ A, ← wireFin14 τ B, ← wireFin15 τ U, ← wireFin15 τ V]
    have rhs : prefixRank (wmap 14 14 τ A.val) (wmap 14 14 τ B.val)
        (wmap 14 14 τ U.val) (wmap 14 14 τ V.val) = score (σ.trans τ) := by
      unfold score
      simp only [wireTrans]
      exact sortRank (wmap 14 14 τ) (W a) (W b) (W c) (W d)
    rw [rhs]
    exact least τ hτ
  · intro g hg
    change g ∈ tail.map (relGate 14 14 σ) at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have old : g' ∈ C.gates := by simp [hcirc, hg']
    constructor
    · simpa [relGate] using model.1 g' old
    · simp [relGate, model.2.2 g' old]
  · simp only [D, Circuit.size, List.length_map]
    change C.gates.length ≤ 26 at small
    rw [hcirc] at small
    simp only [List.length_cons] at small
    omega
  · intro x
    let xs := List.ofFn x
    let w := xs ++ [g₁.op.eval [x A, x B]]
    have first : step xs (relGate 14 14 σ g₁) = w := by
      change xs ++ [g₁.op.eval ((g₁.inputs.map W).map fun i => xs.getD i false)] = w
      simp only [h₁, List.map_cons, List.map_nil]
      have eq := sortEval g₁.op op₁ (fun i => xs.getD i false) (W a) (W b)
      change g₁.op.eval [xs.getD A.val false, xs.getD B.val false] =
        g₁.op.eval [xs.getD (W a) false, xs.getD (W b) false] at eq
      rw [← eq, show xs.getD A.val false = x A from inputGet x A,
        show xs.getD B.val false = x B from inputGet x B]
    have second : step w (relGate 14 14 σ g₂) =
        w ++ [g₂.op.eval [w.getD U.val false, w.getD V.val false]] := by
      change w ++ [g₂.op.eval ((g₂.inputs.map W).map fun i => w.getD i false)] = _
      simp only [h₂, List.map_cons, List.map_nil]
      have eq := sortEval g₂.op op₂ (fun i => w.getD i false) (W c) (W d)
      change g₂.op.eval [w.getD U.val false, w.getD V.val false] =
        g₂.op.eval [w.getD (W c) false, w.getD (W d) false] at eq
      rw [eq]
    have relate := (rel_fold 14 14 σ C.gates _ _ (rel_init 14 14 σ x)).2.2 C.output
    have value : (List.foldl step xs (C.gates.map (relGate 14 14 σ))).getD (W C.output) false =
        C.eval (List.ofFn (x ∘ σ)) := relate
    rw [hcirc] at value
    simp only [List.map_cons, List.foldl_cons, first, second] at value
    change D.eval (w ++ [g₂.op.eval [w.getD U.val false, w.getD V.val false]]) = f x
    exact value.trans ((computes (x ∘ σ)).trans (hσ x))
