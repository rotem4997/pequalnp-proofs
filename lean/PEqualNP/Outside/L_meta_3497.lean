import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds

def comb (n : ℕ) (L : List (Finset (Finset (Fin n)))) (g : Gate) : Finset (Finset (Fin n)) :=
  if g.op.eval [false, true] = true then
    (L.getD (g.inputs.getD 0 0) {∅}).biUnion
      (fun c => (L.getD (g.inputs.getD 1 0) {∅}).image (fun d => c ∪ d))
  else L.getD (g.inputs.getD 0 0) {∅} ∪ L.getD (g.inputs.getD 1 0) {∅}

def fams (n : ℕ) (gs : List Gate) : List (Finset (Finset (Fin n))) :=
  gs.foldl (fun L g => L ++ [comb n L g])
    (List.ofFn fun i : Fin n => ({{i}} : Finset (Finset (Fin n))))

def wr (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Sat (n : ℕ) (x : List Bool) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ c ∈ F, ∃ i ∈ c, x.getD (↑i) false = true

theorem fams_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    fams n (gs ++ [g]) = fams n gs ++ [comb n (fams n gs) g] := by
  unfold fams; rw [List.foldl_append]; rfl

theorem wr_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wr (gs ++ [g]) x = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  unfold wr; rw [List.foldl_append]; rfl

theorem fams_len (n : ℕ) (gs : List Gate) : (fams n gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [fams]
  | append_singleton gs g ih => rw [fams_snoc]; simp [ih]; omega

theorem wr_len (gs : List Gate) (x : List Bool) : (wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr]
  | append_singleton gs g ih => rw [wr_snoc]; simp [ih]; omega

theorem fams_prefix (n : ℕ) (l1 : List Gate) (w : ℕ) (hw : w < n + l1.length) :
    ∀ l2 : List Gate, (fams n (l1 ++ l2)).getD w {∅} = (fams n l1).getD w {∅} := by
  intro l2
  induction l2 using List.reverseRecOn with
  | nil => simp
  | append_singleton l2 g ih =>
    rw [← List.append_assoc, fams_snoc,
      List.getD_append _ _ _ _ (by rw [fams_len]; simp; omega)]
    exact ih

theorem fams_input (n : ℕ) (gs : List Gate) (i : Fin n) :
    (fams n gs).getD i {∅} = {{i}} := by
  induction gs using List.reverseRecOn with
  | nil =>
    simp only [fams, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | append_singleton gs g ih =>
    rw [fams_snoc, List.getD_append _ _ _ _ (by rw [fams_len]; omega)]
    exact ih

theorem sat_union (n : ℕ) (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat n x (A ∪ B) ↔ Sat n x A ∧ Sat n x B := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (Finset.mem_union_left _ hc), fun c hc => h c (Finset.mem_union_right _ hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases Finset.mem_union.1 hc with hc | hc
    exacts [h1 c hc, h2 c hc]

theorem sat_prod (n : ℕ) (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat n x (A.biUnion fun c => B.image fun d => c ∪ d) ↔ Sat n x A ∨ Sat n x B := by
  constructor
  · intro h
    by_contra hn
    rw [not_or] at hn
    obtain ⟨h1, h2⟩ := hn
    simp only [Sat, not_forall] at h1 h2
    obtain ⟨c, hc, hc1⟩ := h1
    obtain ⟨d, hd, hd1⟩ := h2
    obtain ⟨i, hi, hx⟩ := h (c ∪ d) (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_image.2 ⟨d, hd, rfl⟩⟩)
    rcases Finset.mem_union.1 hi with hi | hi
    exacts [hc1 ⟨i, hi, hx⟩, hd1 ⟨i, hi, hx⟩]
  · rintro (h | h) e he
    · obtain ⟨c, hc, he1⟩ := Finset.mem_biUnion.1 he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he1
      obtain ⟨i, hi, hx⟩ := h c hc
      exact ⟨i, Finset.mem_union_left _ hi, hx⟩
    · obtain ⟨c, hc, he1⟩ := Finset.mem_biUnion.1 he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he1
      obtain ⟨i, hi, hx⟩ := h d hd
      exact ⟨i, Finset.mem_union_right _ hi, hx⟩

theorem sat_empty (n : ℕ) (x : List Bool) : ¬ Sat n x ({∅} : Finset (Finset (Fin n))) := by
  intro h
  obtain ⟨i, hi, -⟩ := h ∅ (Finset.mem_singleton_self _)
  simp at hi

theorem key (n : ℕ) (x : List Bool) (hx : x.length = n) : ∀ gs : List Gate,
    (∀ (j : ℕ) (g : Gate), gs[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
    ∀ w : ℕ, ((wr gs x).getD w false = true ↔ Sat n x ((fams n gs).getD w {∅})) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w
    by_cases hw : w < n
    · have h1 := fams_input n [] ⟨w, hw⟩
      simp only at h1
      rw [h1]
      simp [Sat, wr]
    · simp only [wr, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by rw [fams_len]; simp; omega)]
      simp only [Bool.false_eq_true, false_iff]
      exact sat_empty n x
  | append_singleton gs g ih =>
    intro hgs w
    have hpre : ∀ (j : ℕ) (g1 : Gate), gs[j]? = some g1 → (g1.op = GateOp.and ∨ g1.op = GateOp.or) ∧
        ∃ a b : ℕ, g1.inputs = [a, b] ∧ a < b ∧ b < n + j := by
      intro j g1 h
      obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 h
      apply hgs j g1
      rw [List.getElem?_append_left hj]
      exact h
    have ihw := ih hpre
    obtain ⟨hop, a, b, hin, hab, hb⟩ := hgs gs.length g (by simp)
    have hl1 : (wr gs x).length = n + gs.length := by rw [wr_len, hx]
    have hl2 : (fams n gs).length = n + gs.length := fams_len n gs
    rw [wr_snoc, fams_snoc]
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ihw w
    · subst hw
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        hl1, hl2, Nat.sub_self]
      simp only [List.getD_cons_zero]
      unfold comb
      rw [hin]
      simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      rcases hop with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
          Bool.false_eq_true, ite_false]
        rw [sat_union, ← ihw a, ← ihw b, Bool.and_eq_true]
      · rw [hop]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.false_or,
          ite_true]
        rw [sat_prod, ← ihw a, ← ihw b, Bool.or_eq_true]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp only [Bool.false_eq_true, false_iff]
      exact sat_empty n x

end PEqualNP.Outside.L_meta_3497

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C hmono hin
  refine ⟨fun w => (PEqualNP.Outside.L_meta_3497.fams n C.gates).getD w {∅}, ?_, ?_, ?_⟩
  · intro i
    exact PEqualNP.Outside.L_meta_3497.fams_input n C.gates i
  · intro j hj
    have hj1 : j < C.gates.length := hj
    obtain ⟨a, b, hg, hab, hb⟩ := hin j C.gates[j] (List.getElem?_eq_getElem hj1)
    refine ⟨a, b, hg, hab, hb, ?_⟩
    have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
      rw [← List.take_succ_eq_append_getElem hj1, List.take_append_drop]
    have htl : (C.gates.take j).length = j := List.length_take_of_le (by omega)
    have hpa : ∀ w, w < n + j → (PEqualNP.Outside.L_meta_3497.fams n C.gates).getD w {∅} =
        (PEqualNP.Outside.L_meta_3497.fams n (C.gates.take j)).getD w {∅} := by
      intro w hw
      have := PEqualNP.Outside.L_meta_3497.fams_prefix n (C.gates.take j) w (by rw [htl]; exact hw)
        (C.gates.drop j)
      rw [List.take_append_drop] at this
      exact this
    have hval : (PEqualNP.Outside.L_meta_3497.fams n C.gates).getD (n + j) {∅} =
        PEqualNP.Outside.L_meta_3497.comb n
          (PEqualNP.Outside.L_meta_3497.fams n (C.gates.take j)) C.gates[j] := by
      have h1 := PEqualNP.Outside.L_meta_3497.fams_prefix n (C.gates.take j ++ [C.gates[j]]) (n + j)
        (by simp only [List.length_append, htl, List.length_singleton]; omega) (C.gates.drop (j + 1))
      rw [← hsplit] at h1
      rw [h1, PEqualNP.Outside.L_meta_3497.fams_snoc,
        List.getD_append_right _ _ _ _ (by rw [PEqualNP.Outside.L_meta_3497.fams_len, htl]),
        PEqualNP.Outside.L_meta_3497.fams_len, htl, Nat.sub_self]
      rfl
    simp only
    rw [hval, hpa a (by omega), hpa b hb]
    unfold PEqualNP.Outside.L_meta_3497.comb
    rw [hg]
    rfl
  · intro x hx w
    have h := PEqualNP.Outside.L_meta_3497.key n x hx C.gates (by
      intro j g hgj
      refine ⟨?_, hin j g hgj⟩
      have hm := (hmono g (List.mem_of_getElem? hgj)).1
      simpa using hm) w
    exact h
