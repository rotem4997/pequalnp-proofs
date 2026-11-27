import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5268

open PEqualNP.CircuitLowerBounds

def wm (σ τ : Equiv.Perm (Fin 7)) (w : ℕ) : ℕ :=
  if h : w < 7 then ((σ ⟨w, h⟩ : Fin 7) : ℕ)
  else if h2 : w < 14 then 7 + ((τ ⟨w - 7, by omega⟩ : Fin 7) : ℕ) else w

lemma wm_ge (σ τ : Equiv.Perm (Fin 7)) (w : ℕ) (h : 14 ≤ w) : wm σ τ w = w := by
  unfold wm
  rw [dif_neg (by omega), dif_neg (by omega)]

lemma wm_lt (σ τ : Equiv.Perm (Fin 7)) (w : ℕ) (h : w < 14) : wm σ τ w < 14 := by
  unfold wm
  by_cases h1 : w < 7
  · rw [dif_pos h1]
    have := (σ ⟨w, h1⟩).isLt
    omega
  · rw [dif_neg h1, dif_pos h]
    have := (τ ⟨w - 7, by omega⟩).isLt
    omega

lemma wm_le_of (σ τ : Equiv.Perm (Fin 7)) (w k : ℕ) (h : w < 14 + k) : wm σ τ w < 14 + k := by
  by_cases hw : w < 14
  · have := wm_lt σ τ w hw
    omega
  · rw [wm_ge σ τ w (by omega)]
    exact h

lemma wm_inj (σ τ : Equiv.Perm (Fin 7)) : Function.Injective (wm σ τ) := by
  intro a b hab
  rcases lt_or_ge a 14 with ha | ha <;> rcases lt_or_ge b 14 with hb | hb
  · rcases lt_or_ge a 7 with ha7 | ha7 <;> rcases lt_or_ge b 7 with hb7 | hb7
    · unfold wm at hab
      rw [dif_pos ha7, dif_pos hb7] at hab
      have := σ.injective (Fin.ext hab)
      simpa using this
    · unfold wm at hab
      rw [dif_pos ha7, dif_neg (show ¬ b < 7 by omega), dif_pos hb] at hab
      have := (σ ⟨a, ha7⟩).isLt
      omega
    · unfold wm at hab
      rw [dif_pos hb7, dif_neg (show ¬ a < 7 by omega), dif_pos ha] at hab
      have := (σ ⟨b, hb7⟩).isLt
      omega
    · unfold wm at hab
      rw [dif_neg (show ¬ a < 7 by omega), dif_pos ha, dif_neg (show ¬ b < 7 by omega),
        dif_pos hb] at hab
      have h' : τ ⟨a - 7, by omega⟩ = τ ⟨b - 7, by omega⟩ := Fin.ext (by omega)
      have := τ.injective h'
      simp only [Fin.mk.injEq] at this
      omega
  · rw [wm_ge σ τ b hb] at hab
    have := wm_lt σ τ a ha
    omega
  · rw [wm_ge σ τ a ha] at hab
    have := wm_lt σ τ b hb
    omega
  · rw [wm_ge σ τ a ha, wm_ge σ τ b hb] at hab
    exact hab

lemma wm_left (σ τ : Equiv.Perm (Fin 7)) (p : Fin 7) : wm σ τ (p : ℕ) = ((σ p : Fin 7) : ℕ) := by
  unfold wm
  rw [dif_pos p.isLt]

lemma wm_right (σ τ : Equiv.Perm (Fin 7)) (l : Fin 7) :
    wm σ τ (7 + (l : ℕ)) = 7 + ((τ l : Fin 7) : ℕ) := by
  unfold wm
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp

def rg (σ τ : Equiv.Perm (Fin 7)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wm σ τ)⟩

def rc (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rg σ τ), wm σ τ C.output⟩

def Rel {α : Type} (σ τ : Equiv.Perm (Fin 7)) (d : α) (W W' : List α) : Prop :=
  14 ≤ W.length ∧ W'.length = W.length ∧ ∀ w : ℕ, W'.getD (wm σ τ w) d = W.getD w d

lemma rel_step {α : Type} (σ τ : Equiv.Perm (Fin 7)) (d : α) (F : Gate → List α → α)
    (hF : ∀ (g : Gate) (W W' : List α), (∀ w : ℕ, W'.getD (wm σ τ w) d = W.getD w d) →
      F (rg σ τ g) W' = F g W)
    (W W' : List α) (g : Gate) (h : Rel σ τ d W W') :
    Rel σ τ d (W ++ [F g W]) (W' ++ [F (rg σ τ g) W']) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv := hF g W W' h3
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro w
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wm σ τ w < W'.length := by
      rcases lt_or_ge w 14 with h14 | h14
      · have := wm_lt σ τ w h14
        omega
      · rw [wm_ge σ τ w h14]
        omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wm σ τ w = W'.length := by
      rw [wm_ge σ τ w (by omega)]
      omega
    rw [he, hw, hv]
    simp
  · have hge : W'.length + 1 ≤ wm σ τ w := by
      rw [wm_ge σ τ w (by omega)]
      omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold {α : Type} (σ τ : Equiv.Perm (Fin 7)) (d : α) (F : Gate → List α → α)
    (hF : ∀ (g : Gate) (W W' : List α), (∀ w : ℕ, W'.getD (wm σ τ w) d = W.getD w d) →
      F (rg σ τ g) W' = F g W)
    (gs : List Gate) : ∀ W W' : List α, Rel σ τ d W W' →
      Rel σ τ d (gs.foldl (fun w g => w ++ [F g w]) W)
        ((gs.map (rg σ τ)).foldl (fun w g => w ++ [F g w]) W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step σ τ d F hF W W' g h)

lemma hF_bool (σ τ : Equiv.Perm (Fin 7)) : ∀ (g : Gate) (W W' : List Bool),
    (∀ w : ℕ, W'.getD (wm σ τ w) false = W.getD w false) →
    (fun (g : Gate) (w : List Bool) => g.op.eval (g.inputs.map fun i => w.getD i false))
      (rg σ τ g) W' =
    (fun (g : Gate) (w : List Bool) => g.op.eval (g.inputs.map fun i => w.getD i false)) g W := by
  intro g W W' h
  show (rg σ τ g).op.eval ((rg σ τ g).inputs.map fun i => W'.getD i false)
    = g.op.eval (g.inputs.map fun i => W.getD i false)
  have hm : ((rg σ τ g).inputs.map fun i => W'.getD i false)
      = g.inputs.map fun i => W.getD i false := by
    show (g.inputs.map (wm σ τ)).map (fun i => W'.getD i false) = _
    rw [List.map_map]
    exact List.map_congr_left (fun a _ => h a)
  rw [hm] <;> rfl

lemma hF_deg (σ τ : Equiv.Perm (Fin 7)) : ∀ (g : Gate) (W W' : List ℕ),
    (∀ w : ℕ, W'.getD (wm σ τ w) 0 = W.getD w 0) →
    (fun (g : Gate) (w : List ℕ) => g.lineDegree w) (rg σ τ g) W' =
    (fun (g : Gate) (w : List ℕ) => g.lineDegree w) g W := by
  intro g W W' h
  show (rg σ τ g).lineDegree W' = g.lineDegree W
  have hm : ((rg σ τ g).inputs.map fun i => W'.getD i 0)
      = g.inputs.map fun i => W.getD i 0 := by
    show (g.inputs.map (wm σ τ)).map (fun i => W'.getD i 0) = _
    rw [List.map_map]
    exact List.map_congr_left (fun a _ => h a)
  unfold Gate.lineDegree
  rw [hm] <;> rfl

lemma init_bool (σ τ : Equiv.Perm (Fin 7)) (a : Fin 14 → Bool) :
    Rel σ τ false (List.ofFn (fun i : Fin 14 => a ⟨wm σ τ i, wm_lt σ τ i i.isLt⟩))
      (List.ofFn a) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w
  rcases lt_or_ge w 14 with hw | hw
  · rw [List.getD_eq_getElem _ _ (by simpa using wm_lt σ τ w hw),
      List.getD_eq_getElem _ _ (by simpa using hw)]
    simp only [List.getElem_ofFn, Fin.val_mk]
  · rw [wm_ge σ τ w hw, List.getD_eq_default _ _ (by simpa using hw),
      List.getD_eq_default _ _ (by simpa using hw)]

lemma init_deg (σ τ : Equiv.Perm (Fin 7)) (m : ℕ) :
    Rel σ τ 0 ((List.range 14).map fun i => if i ∈ ({m} : Finset ℕ) then 1 else 0)
      ((List.range 14).map fun i => if i ∈ ({wm σ τ m} : Finset ℕ) then 1 else 0) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w
  rcases lt_or_ge w 14 with hw | hw
  · rw [List.getD_eq_getElem _ _ (by simpa using wm_lt σ τ w hw),
      List.getD_eq_getElem _ _ (by simpa using hw)]
    simp [(wm_inj σ τ).eq_iff]
  · rw [wm_ge σ τ w hw, List.getD_eq_default _ _ (by simpa using hw),
      List.getD_eq_default _ _ (by simpa using hw)]

lemma eval_rc (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) (a : Fin 14 → Bool) :
    (rc σ τ C).eval (List.ofFn a)
      = C.eval (List.ofFn (fun i : Fin 14 => a ⟨wm σ τ i, wm_lt σ τ i i.isLt⟩)) := by
  have h := (rel_fold σ τ false
    (fun (g : Gate) (w : List Bool) => g.op.eval (g.inputs.map fun i => w.getD i false))
    (hF_bool σ τ) C.gates _ _ (init_bool σ τ a)).2.2 C.output
  exact h

lemma deg_rc (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) (m : ℕ) :
    (rc σ τ C).lineDeg 14 {wm σ τ m} = C.lineDeg 14 {m} := by
  have h := (rel_fold σ τ 0 (fun (g : Gate) (w : List ℕ) => g.lineDegree w)
    (hF_deg σ τ) C.gates _ _ (init_deg σ τ m)).2.2 C.output
  exact h

lemma flatMap_rg (σ τ : Equiv.Perm (Fin 7)) (gs : List Gate) :
    (gs.map (rg σ τ)).flatMap Gate.inputs = (gs.flatMap Gate.inputs).map (wm σ τ) := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [rg, ih]

lemma filter_wm (σ τ : Equiv.Perm (Fin 7)) (L : List ℕ) :
    (L.map (wm σ τ)).filter (fun x => decide (14 ≤ x)) = L.filter (fun x => decide (14 ≤ x)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases ha : 14 ≤ a
    · simp [List.filter_cons, ha, wm_ge σ τ a ha, ih]
    · have h1 : ¬ 14 ≤ wm σ τ a := by
        have := wm_lt σ τ a (by omega)
        omega
      simp [List.filter_cons, ha, h1, ih]

def inc (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

def good (C : Circuit) : Prop :=
  C.size ≤ 27 ∧ (∀ (x3 : ℕ) (x4 : Gate), C.gates[x3]? = Option.some x4 →
    (x4.op = GateOp.and ∨ x4.op = GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧
      x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧
    ∀ (x3 : Fin (14 : ℕ) → Bool), C.eval (List.ofFn x3) = Bool.true ↔
      ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), inc x4 x5 ∧
        x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true

def nd (C : Circuit) : Prop :=
  (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4))
    (C.output :: List.flatMap Gate.inputs C.gates)).Nodup

theorem main (σ τ : Equiv.Perm (Fin 7)) (hA : ∀ (p l : Fin 7), inc (σ p) (τ l) ↔ inc p l)
    (C : Circuit) (hC : good C) :
    ∃ D : Circuit, good D ∧ (nd D ↔ nd C) ∧
      (∀ (x10 : Fin 7), D.lineDeg 14 {((σ x10 : Fin 7) : ℕ)} = C.lineDeg 14 {(x10 : ℕ)}) ∧
      ∀ (x10 : Fin 7), D.lineDeg 14 {7 + ((τ x10 : Fin 7) : ℕ)} = C.lineDeg 14 {7 + (x10 : ℕ)} := by
  obtain ⟨hsz, hgates, hfun⟩ := hC
  refine ⟨rc σ τ C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Circuit.size, rc] using hsz
  · intro i g hg
    simp only [rc, List.getElem?_map] at hg
    rcases hc : C.gates[i]? with _ | g0
    · rw [hc] at hg
      simp at hg
    · rw [hc] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      obtain ⟨hop, a, b, hin, hab, ha, hb⟩ := hgates i g0 hc
      refine ⟨hop, wm σ τ a, wm σ τ b, ?_, fun h => hab (wm_inj σ τ h),
        wm_le_of σ τ a i ha, wm_le_of σ τ b i hb⟩
      show g0.inputs.map (wm σ τ) = _
      rw [hin]
      rfl
  · intro a
    rw [eval_rc, hfun]
    have hb1 : ∀ p : Fin 7, (⟨wm σ τ ((Fin.castAdd 7 p : Fin 14) : ℕ),
        wm_lt σ τ _ (Fin.castAdd 7 p : Fin 14).isLt⟩ : Fin 14) = Fin.castAdd 7 (σ p) := by
      intro p
      apply Fin.ext
      first
      | exact wm_left σ τ p
      | simp [wm_left]
    have hb2 : ∀ l : Fin 7, (⟨wm σ τ ((Fin.natAdd 7 l : Fin 14) : ℕ),
        wm_lt σ τ _ (Fin.natAdd 7 l : Fin 14).isLt⟩ : Fin 14) = Fin.natAdd 7 (τ l) := by
      intro l
      apply Fin.ext
      first
      | exact wm_right σ τ l
      | simp [wm_right]
    constructor
    · rintro ⟨p, l, hpl, h1, h2⟩
      refine ⟨σ p, τ l, (hA p l).2 hpl, ?_, ?_⟩
      · exact (congrArg a (hb1 p)).symm.trans h1
      · exact (congrArg a (hb2 l)).symm.trans h2
    · rintro ⟨p, l, hpl, h1, h2⟩
      refine ⟨σ.symm p, τ.symm l, (hA _ _).1 (by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hpl), ?_, ?_⟩
      · have e := congrArg a (hb1 (σ.symm p))
        rw [Equiv.apply_symm_apply] at e
        exact e.trans h1
      · have e := congrArg a (hb2 (τ.symm l))
        rw [Equiv.apply_symm_apply] at e
        exact e.trans h2
  · have hl : (rc σ τ C).output :: List.flatMap Gate.inputs (rc σ τ C).gates
        = (C.output :: List.flatMap Gate.inputs C.gates).map (wm σ τ) := by
      show wm σ τ C.output :: List.flatMap Gate.inputs (C.gates.map (rg σ τ)) = _
      rw [flatMap_rg, List.map_cons]
    unfold nd
    rw [hl, filter_wm]
  · intro x10
    rw [← wm_left σ τ x10]
    exact deg_rc σ τ C x10
  · intro x10
    rw [← wm_right σ τ x10]
    exact deg_rc σ τ C (7 + x10)

end PEqualNP.Outside.L_meta_5268

theorem PEqualNP.Outside.L_meta_5268 : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 x5 : Equiv.Perm (Fin (7 : ℕ))), (∀ (x6 x7 : Fin (7 : ℕ)), x1 (x4 x6) (x5 x7) ↔ x1 x6 x7) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x2 x7 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ (x3 x9 ↔ x3 x7) ∧ (∀ (x10 : Fin (7 : ℕ)), x9.lineDeg (14 : ℕ) {↑(x4 x10)} = x7.lineDeg (14 : ℕ) {↑x10}) ∧ ∀ (x10 : Fin (7 : ℕ)), x9.lineDeg (14 : ℕ) {(7 : ℕ) + ↑(x5 x10)} = x7.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x10} := by
  intro x1 x2 x3 x4 x5 hA x7 hx7
  exact PEqualNP.Outside.L_meta_5268.main x4 x5 hA x7 hx7
