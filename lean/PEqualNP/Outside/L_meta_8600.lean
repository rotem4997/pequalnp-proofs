import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8600

def gv (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun w g => w ++ [gv w g]) w

def step (wz : List Bool) (g : Gate) : Gate :=
  if gv wz g = true then ⟨GateOp.or, []⟩ else ⟨g.op, g.inputs.filter fun i => !(wz.getD i false)⟩

def build : List Gate → List Bool → List Gate
  | [], _ => []
  | g :: gs, wz => step wz g :: build gs (wz ++ [gv wz g])

def Inv (wz w w' : List Bool) : Prop :=
  wz.length = w.length ∧ w'.length = w.length ∧
  (∀ i, wz.getD i false = true → w.getD i false = true) ∧
  (∀ i, w'.getD i false = (w.getD i false && !(wz.getD i false)))

theorem getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false = if i < l.length then l.getD i false else if i = l.length then b else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | h | h
  · simp [List.getElem?_append_left h, h]
  · subst h; simp
  · have h1 : ¬ i < l.length := by omega
    have h2 : i ≠ l.length := by omega
    have h3 : (l ++ [b])[i]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    simp [h3, h1, h2]

theorem ev_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f f' : ℕ → Bool)
    (H : ∀ i, f i = true → f' i = true) : op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with h | h <;> subst h
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro K b ⟨i, hi, rfl⟩
    exact H i (K (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, k⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, H i k⟩

theorem ev_filter_and (l : List ℕ) (fz f f' : ℕ → Bool)
    (M : ∀ i, fz i = true → f i = true) (R : ∀ i, f' i = (f i && !(fz i))) :
    GateOp.and.eval ((l.filter fun i => !(fz i)).map f') = GateOp.and.eval (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [GateOp.eval] at ih ⊢
    have hM := M a
    have hR := R a
    cases hfz : fz a <;> cases hf : f a <;> simp_all [List.filter_cons]

theorem ev_filter_or (l : List ℕ) (fz f f' : ℕ → Bool)
    (R : ∀ i, f' i = (f i && !(fz i))) (hz : GateOp.or.eval (l.map fz) = false) :
    GateOp.or.eval ((l.filter fun i => !(fz i)).map f') = GateOp.or.eval (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [GateOp.eval] at ih hz ⊢
    have hR := R a
    cases hfz : fz a <;> cases hf : f a <;> simp_all [List.filter_cons]

theorem inv_step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (wz w w' : List Bool)
    (h : Inv wz w w') : Inv (wz ++ [gv wz g]) (w ++ [gv w g]) (w' ++ [gv w' (step wz g)]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have mono : gv wz g = true → gv w g = true := ev_mono g.op hg g.inputs _ _ h3
  have rel : gv w' (step wz g) = (gv w g && !(gv wz g)) := by
    unfold step
    by_cases hz : gv wz g = true
    · rw [if_pos hz, hz]
      simp [gv, GateOp.eval]
    · rw [if_neg hz]
      have hz' : gv wz g = false := by simpa using hz
      rw [hz']
      simp only [Bool.not_false, Bool.and_true]
      rcases hg with hg | hg
      · unfold gv
        simp only [hg]
        exact ev_filter_and g.inputs _ _ _ h3 h4
      · unfold gv at hz' ⊢
        simp only [hg] at hz' ⊢
        exact ev_filter_or g.inputs _ _ _ h4 hz'
  refine ⟨by simp [h1], by simp [h2], fun i => ?_, fun i => ?_⟩
  · rw [getD_snoc, getD_snoc, h1]
    split_ifs
    · exact h3 i
    · exact mono
    · simp
  · rw [getD_snoc, getD_snoc, getD_snoc, h1, h2]
    split_ifs
    · exact h4 i
    · exact rel
    · simp

theorem inv_run (gs : List Gate) : ∀ (wz w w' : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Inv wz w w' →
    Inv (run gs wz) (run gs w) (run (build gs wz) w') := by
  induction gs with
  | nil => intro wz w w' _ h; exact h
  | cons g gs ih =>
    intro wz w w' hg h
    exact ih _ _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (inv_step g (hg g (by simp)) wz w w' h)

theorem build_len (gs : List Gate) : ∀ wz, (build gs wz).length = gs.length := by
  induction gs with
  | nil => intro wz; rfl
  | cons g gs ih => intro wz; simp [build, ih]

theorem build_mono (gs : List Gate) : ∀ wz,
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ g ∈ build gs wz, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro wz _ g hg; simp [build] at hg
  | cons g gs ih =>
    intro wz H g' hg'
    simp only [build, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · unfold step
      split
      · exact ⟨Or.inr rfl, by simp⟩
      · exact ⟨(H g (by simp)).1, le_trans (List.length_filter_le _ _) (H g (by simp)).2⟩
    · exact ih _ (fun g'' h'' => H g'' (List.mem_cons_of_mem _ h'')) g' hg'

theorem zf (n i : ℕ) : (List.ofFn fun (_ : Fin n) => Bool.false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (List.ofFn fun (_ : Fin n) => Bool.false)[i]? with
  | none => rfl
  | some b =>
    have hb := List.mem_of_getElem? h
    simp only [List.mem_ofFn] at hb
    cases b <;> simp_all

theorem base (n : ℕ) (x : Fin n → Bool) :
    Inv (List.ofFn fun (_ : Fin n) => Bool.false) (List.ofFn x) (List.ofFn x) :=
  ⟨by simp, rfl, fun i h => by rw [zf] at h; exact absurd h (by simp), fun i => by rw [zf]; simp⟩

end PEqualNP.Outside.L_meta_8600

theorem PEqualNP.Outside.L_meta_8600 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin x1 → Bool), x4.eval (List.ofFn x6) = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8 ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ (∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) ∧ x7.size ≤ x4.size ∧ ∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x7.wires (List.ofFn fun (x12 : Fin x1) => Bool.false)).getD (x1 + x8) Bool.false = Bool.false := by
  intro x1 x2 x3 x4 hm hf
  have hmo : ∀ g ∈ x4.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hm g hg
  have hz0 : (PEqualNP.Outside.L_meta_8600.run x4.gates (List.ofFn fun (_ : Fin x1) => Bool.false)).getD x4.output false = false :=
    (hf (fun _ => Bool.false)).trans (by simp)
  have key := fun (x : Fin x1 → Bool) => PEqualNP.Outside.L_meta_8600.inv_run x4.gates _ _ _
    (fun g hg => (hmo g hg).1) (PEqualNP.Outside.L_meta_8600.base x1 x)
  refine ⟨⟨PEqualNP.Outside.L_meta_8600.build x4.gates (List.ofFn fun (_ : Fin x1) => Bool.false), x4.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact PEqualNP.Outside.L_meta_8600.build_mono x4.gates _ hmo g hg
  · intro x
    rw [← hf x]
    show (PEqualNP.Outside.L_meta_8600.run (PEqualNP.Outside.L_meta_8600.build x4.gates (List.ofFn fun (_ : Fin x1) => Bool.false)) (List.ofFn x)).getD x4.output false = (PEqualNP.Outside.L_meta_8600.run x4.gates (List.ofFn x)).getD x4.output false
    rw [(key x).2.2.2 x4.output, hz0]
    simp
  · exact le_of_eq (PEqualNP.Outside.L_meta_8600.build_len _ _)
  · intro x8 x9 _ _
    have k := (key (fun _ => Bool.false)).2.2.2 (x1 + x8)
    show (PEqualNP.Outside.L_meta_8600.run (PEqualNP.Outside.L_meta_8600.build x4.gates (List.ofFn fun (_ : Fin x1) => Bool.false)) (List.ofFn fun (_ : Fin x1) => Bool.false)).getD (x1 + x8) false = false
    rw [k]
    simp
