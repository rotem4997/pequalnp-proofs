import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8164

open PEqualNP.MetaComplexity

def meval {n : ℕ} : DMFormula n → (Fin n → Bool) → Bool
  | DMFormula.lit i _, x => x i
  | DMFormula.and a b, x => meval a x && meval b x
  | DMFormula.or a b, x => meval a x || meval b x

theorem rec_eq {n : ℕ} (F : DMFormula n) (x : Fin n → Bool) :
    DMFormula.rec (motive := fun _ => Bool) (fun (i : Fin n) (_ : Bool) => x i)
      (fun (_ _ : DMFormula n) (p q : Bool) => p && q)
      (fun (_ _ : DMFormula n) (p q : Bool) => p || q) F = meval F x := by
  induction F with
  | lit i b => rfl
  | and a b ihA ihB =>
      change (DMFormula.rec (motive := fun _ => Bool) (fun (i : Fin n) (_ : Bool) => x i)
        (fun (_ _ : DMFormula n) (p q : Bool) => p && q)
        (fun (_ _ : DMFormula n) (p q : Bool) => p || q) a &&
        DMFormula.rec (motive := fun _ => Bool) (fun (i : Fin n) (_ : Bool) => x i)
        (fun (_ _ : DMFormula n) (p q : Bool) => p && q)
        (fun (_ _ : DMFormula n) (p q : Bool) => p || q) b) = (meval a x && meval b x)
      rw [ihA, ihB]
  | or a b ihA ihB =>
      change (DMFormula.rec (motive := fun _ => Bool) (fun (i : Fin n) (_ : Bool) => x i)
        (fun (_ _ : DMFormula n) (p q : Bool) => p && q)
        (fun (_ _ : DMFormula n) (p q : Bool) => p || q) a ||
        DMFormula.rec (motive := fun _ => Bool) (fun (i : Fin n) (_ : Bool) => x i)
        (fun (_ _ : DMFormula n) (p q : Bool) => p && q)
        (fun (_ _ : DMFormula n) (p q : Bool) => p || q) b) = (meval a x || meval b x)
      rw [ihA, ihB]

theorem splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

theorem rects {n : ℕ} (φ : DMFormula n) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, meval φ x = true → meval φ y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → meval φ x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → meval φ y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [meval] using hx, by simpa [meval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [meval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [meval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ meval b x = true) (fun i x => XB i x ∧ meval a x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ meval a y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : meval a x = true ∧ meval b x = true := by
          simpa only [meval, Bool.and_eq_true_iff] using hx
        apply splitUnique
        cases ha : meval a y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : meval b y = false := by
              simpa [meval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ meval b x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [meval, ha, h.2], by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ meval a x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [meval, hb, h.2], by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [meval, ha], by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ meval a y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [meval, hb], by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ meval a x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ meval b y = false) (fun i y => YB i y ∧ meval a y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : meval a y = false ∧ meval b y = false := by
          simpa only [meval, Bool.or_eq_false_iff] using hy
        apply splitUnique
        cases ha : meval a x with
        | false =>
            right
            have hb : meval b x = true := by
              simpa [meval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [meval, ha], by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ meval a x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [meval, hb], by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ meval b y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [meval, ha, h.2], by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ meval a y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [meval, hb, h.2], by simpa [label, Fin.addCases_right] using hv⟩

end PEqualNP.Outside.L_meta_8164

theorem PEqualNP.Outside.L_meta_8164 : ∀ (x1 : ℕ) (x2 : PEqualNP.MetaComplexity.DMFormula x1),   have x3 : (Fin x1 → Bool) → Bool := fun (x3 : Fin x1 → Bool) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x4 : Fin x1) (x5 : Bool) => x3 x4) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 && x7) (fun (x4 x5 : PEqualNP.MetaComplexity.DMFormula x1) (x6 x7 : Bool) => x6 || x7) x2;   ∃ (x4 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x5 : Fin x2.leaves → (Fin x1 → Bool) → Prop) (x6 : Fin x2.leaves → Fin x1), ∀ (x7 x8 : Fin x1 → Bool), x3 x7 = Bool.true → x3 x8 = Bool.false → (∃! x11 : Fin x2.leaves, x4 x11 x7 ∧ x5 x11 x8) ∧ ∀ (x11 : Fin x2.leaves), x4 x11 x7 → x5 x11 x8 → x7 (x6 x11) = Bool.true ∧ x8 (x6 x11) = Bool.false := by
  intro x1 x2 x3
  obtain ⟨X, Y, L, h1, h2, h3⟩ := PEqualNP.Outside.L_meta_8164.rects x2
  refine ⟨X, Y, L, fun x7 x8 hx hy => ?_⟩
  have hx' : PEqualNP.Outside.L_meta_8164.meval x2 x7 = true :=
    (PEqualNP.Outside.L_meta_8164.rec_eq x2 x7).symm.trans hx
  have hy' : PEqualNP.Outside.L_meta_8164.meval x2 x8 = false :=
    (PEqualNP.Outside.L_meta_8164.rec_eq x2 x8).symm.trans hy
  exact ⟨h1 x7 x8 hx' hy', fun i hi hj => ⟨(h2 i x7 hi).2, (h3 i x8 hj).2⟩⟩
