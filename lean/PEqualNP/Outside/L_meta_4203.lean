import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4203_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

/-- Input wire `i < n` goes to `σ i`; gate wires stay. -/
def tau (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then ((σ ⟨i, h⟩ : Fin n) : ℕ) else i

def rg (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (tau n σ) }

def relabel (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  { gates := C.gates.map (rg n σ), output := tau n σ C.output }

theorem tau_ge (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) (h : n ≤ w) : tau n σ w = w := by
  unfold tau
  rw [dif_neg (by omega)]

theorem tau_fin (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : tau n σ (i : ℕ) = ((σ i : Fin n) : ℕ) := by
  unfold tau
  rw [dif_pos i.isLt]

theorem tau_lt_of_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) (w L : ℕ) (hL : n ≤ L) (hw : w < L) :
    tau n σ w < L := by
  unfold tau
  split_ifs with h
  · exact lt_of_lt_of_le (σ ⟨w, h⟩).isLt hL
  · exact hw

theorem tau_inj (n : ℕ) (σ : Equiv.Perm (Fin n)) : Function.Injective (tau n σ) := by
  intro a b hab
  unfold tau at hab
  by_cases ha : a < n <;> by_cases hb : b < n
  · rw [dif_pos ha, dif_pos hb] at hab
    have := σ.injective (Fin.ext hab)
    exact congrArg Fin.val this
  · rw [dif_pos ha, dif_neg hb] at hab
    have := (σ ⟨a, ha⟩).isLt
    omega
  · rw [dif_neg ha, dif_pos hb] at hab
    have := (σ ⟨b, hb⟩).isLt
    omega
  · rw [dif_neg ha, dif_neg hb] at hab
    exact hab

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dif_neg h]
    exact List.getD_eq_default _ _ (by simp; omega)

theorem base (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) (w : ℕ) :
    (List.ofFn x).getD (tau n σ w) false = (List.ofFn (x ∘ ⇑σ)).getD w false := by
  by_cases h : w < n
  · have ht : tau n σ w = ((σ ⟨w, h⟩ : Fin n) : ℕ) := tau_fin n σ ⟨w, h⟩
    rw [ht, getD_ofFn, getD_ofFn, dif_pos (σ ⟨w, h⟩).isLt, dif_pos h]
    rfl
  · rw [tau_ge n σ w (by omega), getD_ofFn, getD_ofFn, dif_neg h, dif_neg h]

theorem rel_run (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (A B : List Bool), n ≤ B.length → A.length = B.length →
      (∀ w, A.getD (tau n σ w) false = B.getD w false) →
      ∀ w, (drun (gs.map (rg n σ)) A).getD (tau n σ w) false = (drun gs B).getD w false := by
  induction gs with
  | nil => intro A B _ _ h w; exact h w
  | cons g gs ih =>
    intro A B hn hl h
    rw [List.map_cons, drun_cons, drun_cons]
    apply ih
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton, hl]
    · intro w
      rcases lt_trichotomy w B.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ (by rw [hl]; exact tau_lt_of_lt n σ w B.length hn h1),
          List.getD_append _ _ _ _ h1]
        exact h w
      · subst h1
        rw [tau_ge n σ _ hn, List.getD_append_right _ _ _ _ (le_of_eq hl),
          List.getD_append_right _ _ _ _ (le_refl _), hl, Nat.sub_self, List.getD_cons_zero,
          List.getD_cons_zero]
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      · rw [tau_ge n σ w (by omega), List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]

theorem relabel_size (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : (relabel n σ C).size = C.size := by
  simp [relabel, Circuit.size]

theorem relabel_fan (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (relabel n σ C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := h g0 hg0
  exact ⟨h1, by simpa [rg] using h2⟩

theorem relabel_fun (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (relabel n σ C) x = circuitFun n C (x ∘ ⇑σ) := by
  have key := rel_run n σ C.gates (List.ofFn x) (List.ofFn (x ∘ ⇑σ)) (by simp) (by simp) (base n σ x)
  show (drun (C.gates.map (rg n σ)) (List.ofFn x)).getD (tau n σ C.output) false =
    (drun C.gates (List.ofFn (x ∘ ⇑σ))).getD C.output false
  exact key C.output

theorem relabel_min (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (h : IsMinimalCircuit n C) :
    IsMinimalCircuit n (relabel n σ C) := by
  refine ⟨relabel_fan n σ C h.1, fun D hD hfun => ?_⟩
  have hD' := relabel_fan n σ⁻¹ D hD
  have hf : circuitFun n (relabel n σ⁻¹ D) = circuitFun n C := by
    funext x
    rw [relabel_fun, hfun, relabel_fun]
    congr 1
    funext i
    simp
  have := h.2 _ hD' hf
  rw [relabel_size] at this ⊢
  exact this

theorem relabel_get (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (k : Fin C.size) :
    (relabel n σ C).gates.get (finCongr (relabel_size n σ C).symm k) = rg n σ (C.gates.get k) := by
  show (C.gates.map (rg n σ))[(k : ℕ)]'(by simpa [Circuit.size] using k.isLt) =
    rg n σ (C.gates[(k : ℕ)]'k.isLt)
  rw [List.getElem_map]
  rfl

theorem main (n : ℕ) (C : Circuit) (σ : Equiv.Perm (Fin n)) :
    ∃ (D : Circuit) (e : Fin C.size ≃ Fin D.size), D.size = C.size ∧
      (IsMinimalCircuit n C → IsMinimalCircuit n D) ∧
      (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (x ∘ ⇑σ)) ∧
      ∀ k : Fin C.size,
        (D.gates.get (e k)).op = (C.gates.get k).op ∧
        (D.gates.get (e k)).inputs.length = (C.gates.get k).inputs.length ∧
        ((C.gates.get k).inputs.Nodup → (D.gates.get (e k)).inputs.Nodup) ∧
        ((∀ x9 ∈ (C.gates.get k).inputs, x9 < n + ↑k) → ∀ x10 ∈ (D.gates.get (e k)).inputs, x10 < n + ↑(e k)) ∧
        ∀ x9 : Fin n, ((σ x9 : Fin n) : ℕ) ∈ (D.gates.get (e k)).inputs ↔ (x9 : ℕ) ∈ (C.gates.get k).inputs := by
  refine ⟨relabel n σ C, finCongr (relabel_size n σ C).symm, relabel_size n σ C, relabel_min n σ C,
    relabel_fun n σ C, fun k => ?_⟩
  rw [relabel_get]
  refine ⟨rfl, by simp [rg], fun hnd => hnd.map (tau_inj n σ), fun hb x10 hx10 => ?_, fun x9 => ?_⟩
  · simp only [rg, List.mem_map] at hx10
    obtain ⟨x9, hx9, rfl⟩ := hx10
    have := hb x9 hx9
    simp only [finCongr_apply, Fin.val_cast]
    exact tau_lt_of_lt n σ x9 (n + k) (by omega) this
  · simp only [rg]
    rw [← tau_fin n σ x9]
    exact List.mem_map_of_injective (tau_inj n σ)

end PEqualNP.Outside.L_meta_4203_aux

theorem PEqualNP.Outside.L_meta_4203 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2.size ≃ Fin x4.size),     x4.size = x2.size ∧       (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4) ∧         (∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x6 ∘ ⇑x3)) ∧           ∀ (x6 : Fin x2.size),             have x7 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x6;             have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.gates.get (x5 x6);             x8.op = x7.op ∧ x8.inputs.length = x7.inputs.length ∧ (x7.inputs.Nodup → x8.inputs.Nodup) ∧ ((∀ x9 ∈ x7.inputs, x9 < x1 + ↑x6) → ∀ x10 ∈ x8.inputs, x10 < x1 + ↑(x5 x6)) ∧ ∀ (x9 : Fin x1), ↑(x3 x9) ∈ x8.inputs ↔ ↑x9 ∈ x7.inputs := by
  dsimp only
  intro n C σ
  exact PEqualNP.Outside.L_meta_4203_aux.main n C σ
