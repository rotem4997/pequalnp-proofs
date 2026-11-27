import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.FoldCircuit
import PEqualNP.MetaComplexity.Helpers.LiveSize
import PEqualNP.MetaComplexity.Helpers.LeafBound

/-!
# The structure of a normal-form circuit with one dirty AND

`OneDirty G C g` bundles the hypotheses of the one-dirty-AND case rows: `C` is an `IsAO2` circuit for the
edge function `F`, lift-fixed, no AND reads a wire below `F`, every gate lies in the output's cone, and `g`
is its one AND not below `F`. A wire is LOW when it is not below `F`.

* `val_low`: a low wire is an OR of variables, or that OR `g`. `opnd_val`: an operand of `g` is an OR of
  variables. `reach_le`: `g` is below every wire that reaches it.
* `low_opnd`: operands of low gates are low. `low_and`: the only low AND is `g`. `below_or`: the operands of an
  OR below `F` are below `F`.
* `and_pair`: variables of the two operands of an AND other than `g` are adjacent. `not_both`: at most one of
  its operands reaches `g`.
* `top_down`: where `C` is true some AND below `F` is true. `top_up`: truth passes from a gate below `F` to the
  output through the ORs below `F`, for any gate values closed under those ORs.
-/

namespace PEqualNP.MetaComplexity.LowerPart

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput InCone)

variable {n : ℕ}

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem opnd_lt (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) :
    opnd C k b < n + k := LeafBound.opnd_lt hC hk b

theorem mem_opnd (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (w : ℕ)
    (hw : w ∈ (gateAt C k).inputs) : ∃ b : Fin 2, opnd C k b = w := by
  rw [LeafBound.ao_inputs hC hk] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩

theorem opv_or (p q : Bool) : opv false p q = true ↔ p = true ∨ q = true := by
  cases p <;> cases q <;> simp [opv]

theorem opv_and (p q : Bool) : opv true p q = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> simp [opv]

theorem val_or (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k 0) x = true ∨ wireVal n C (opnd C k 1) x = true := by
  rw [gate_eq C hC k hk x, ho]
  exact opv_or _ _

theorem val_and (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C k x = true ↔ wireVal n C (opnd C k 0) x = true ∧ wireVal n C (opnd C k 1) x = true := by
  rw [gate_eq C hC k hk x, ho]
  exact opv_and _ _

/-- Induction on wires. -/
theorem wire_induction (C : Circuit) (hC : IsAO2 n C) (p : ℕ → Prop) (hin : ∀ w < n, p w)
    (hgate : ∀ k < C.gates.length, (∀ b, p (opnd C k b)) → p (n + k)) :
    ∀ w < n + C.gates.length, p w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h : w < n
    · exact hin w h
    · have hk : w - n < C.gates.length := by omega
      have h2 := hgate (w - n) hk fun b => by
        have := opnd_lt C hC (w - n) hk b
        exact ih _ (by omega) (by omega)
      rwa [show n + (w - n) = w by omega] at h2

theorem ones_val (C : Circuit) (hC : IsAO2 n C) :
    ∀ w < n + C.gates.length, wireVal n C w (fun _ => true) = true := by
  refine wire_induction C hC _ (fun w hw => wireVal_lt C w hw _) ?_
  intro k hk h
  show gateVal n C k _ = true
  rcases LeafBound.ao_op hC hk with ho | ho
  · exact (val_and C hC k hk ho _).2 ⟨h 0, h 1⟩
  · exact (val_or C hC k hk ho _).2 (Or.inl (h 0))

theorem mono (C : Circuit) (hC : IsAO2 n C) (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
    ∀ w < n + C.gates.length, wireVal n C w x = true → wireVal n C w y = true := by
  refine wire_induction C hC _ ?_ ?_
  · intro w hw h
    rw [wireVal_lt C w hw] at h ⊢
    exact hxy _ h
  · intro k hk h hx
    have hx' : gateVal n C k x = true := hx
    show gateVal n C k y = true
    rcases LeafBound.ao_op hC hk with ho | ho
    · obtain ⟨h0, h1⟩ := (val_and C hC k hk ho _).1 hx'
      exact (val_and C hC k hk ho _).2 ⟨h 0 h0, h 1 h1⟩
    · rcases (val_or C hC k hk ho _).1 hx' with h0 | h0
      · exact (val_or C hC k hk ho _).2 (Or.inl (h 0 h0))
      · exact (val_or C hC k hk ho _).2 (Or.inr (h 1 h0))

/-- The gate step of `orSets`. -/
def orF (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  cs.length :: (if g.op = GateOp.or then
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => cs.getD (w - n) []) else [])

theorem orSets_eq (C : Circuit) : orSets n C = C.gates.foldl (fun R g => R ++ [orF n R g]) [] := rfl

theorem reach_input (C : Circuit) (w g : ℕ) (hw : w < n) : ¬ OrReaches n C w g := fun h => by
  have := h.1
  omega

theorem reach_gate (C : Circuit) (hC : IsAO2 n C) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧ ∃ b, OrReaches n C (opnd C k b) g) := by
  obtain ⟨h1, h2, h3⟩ := LeafBound.foldl_snoc_split (orF n) C.gates [] k hk []
  simp only [List.length_nil, zero_add] at h1 h3
  rw [← orSets_eq] at h1 h2
  generalize (C.gates.take k).foldl (fun R g => R ++ [orF n R g]) [] = P at h1 h2 h3
  have hgk : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
  rw [hgk] at h1
  have hget : ∀ w, n ≤ w → w < n + k → P.getD (w - n) [] = (orSets n C).getD (w - n) [] := by
    intro w hw hwk
    obtain ⟨t, ht⟩ := h2
    rw [← ht, List.getD_append _ _ _ _ (by omega)]
  unfold OrReaches
  rw [show n + k - n = k by omega, h1]
  unfold orF
  rw [h3]
  simp only [List.mem_cons]
  constructor
  · rintro ⟨_, h | h⟩
    · exact Or.inl h
    · by_cases ho : (gateAt C k).op = GateOp.or
      · rw [ite_eq_left ho] at h
        obtain ⟨w, hw, hg⟩ := List.mem_flatMap.1 h
        rw [List.mem_filter] at hw
        obtain ⟨hw1, hw2⟩ := hw
        rw [decide_eq_true_eq] at hw2
        obtain ⟨b, hb⟩ := mem_opnd C hC k hk w hw1
        refine Or.inr ⟨ho, b, ?_⟩
        rw [hb]
        refine ⟨hw2.1, ?_⟩
        rw [← hget w hw2.1 hw2.2]
        exact hg
      · rw [ite_eq_right ho] at h
        exact absurd h (by simp)
  · rintro (h | ⟨ho, b, hb1, hb2⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ?_⟩
      rw [ite_eq_left ho]
      have hlt := opnd_lt C hC k hk b
      refine List.mem_flatMap.2 ⟨opnd C k b, List.mem_filter.2 ⟨LeafBound.opnd_mem hC hk b, ?_⟩, ?_⟩
      · rw [decide_eq_true_eq]
        exact ⟨hb1, hlt⟩
      · rw [hget _ hb1 hlt]
        exact hb2

/-- A wire reaching `g` through ORs is at least `n + g`, and above `g`. -/
theorem reach_le (C : Circuit) (hC : IsAO2 n C) (g : ℕ) : ∀ w < n + C.gates.length, OrReaches n C w g →
    n + g ≤ w ∧ ∀ x, gateVal n C g x = true → wireVal n C w x = true := by
  refine wire_induction C hC _ (fun w hw h => absurd h (reach_input C w g hw)) ?_
  intro k hk ih h
  rcases (reach_gate C hC k g hk).1 h with rfl | ⟨ho, b, hb⟩
  · exact ⟨le_refl _, fun x hx => hx⟩
  · obtain ⟨h1, h2⟩ := ih b hb
    have hlt := opnd_lt C hC k hk b
    refine ⟨by omega, fun x hx => ?_⟩
    show gateVal n C k x = true
    rw [val_or C hC k hk ho]
    have := h2 x hx
    fin_cases b
    · exact Or.inl this
    · exact Or.inr this

theorem not_reach_opnd (C : Circuit) (hC : IsAO2 n C) (g : ℕ) (hg : g < C.gates.length) (b : Fin 2) :
    ¬ OrReaches n C (opnd C g b) g := by
  intro h
  have hlt := opnd_lt C hC g hg b
  have := (reach_le C hC g _ (by omega) h).1
  omega

/-- The wire is not below `F`. -/
def Low (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ¬ ∀ x : Fin n → Bool, wireVal n C w x = true → graphFun G ∅ x = true

/-- The hypotheses of the one-dirty-AND case rows. -/
structure OneDirty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) : Prop where
  ao : IsAO2 n C
  comp : circuitFun n C = graphFun G ∅
  lift : PEqualNP.Core.IsLiftFixedPoint G C
  andLow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
    ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true)
  cone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k
  hg : g < C.gates.length
  gand : (gateAt C g).op = GateOp.and
  dirty : ¬ BelowF G C g
  others : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

theorem unit_false (y : Fin n) : graphFun G ∅ (unitInput y) = false := by
  by_contra h
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 (by simpa using h)
  simp only [unitInput, decide_eq_true_eq] at hu hw
  rw [hu, hw] at huw
  exact G.loopless.irrefl _ huw

theorem input_low (w : ℕ) (hw : w < n) : Low G C w := by
  intro h
  have h1 := h (unitInput ⟨w, hw⟩) (by rw [wireVal_lt C w hw]; simp [unitInput])
  rw [unit_false] at h1
  exact Bool.false_ne_true h1

theorem low_and (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hl : Low G C (n + k)) : k = g := by
  by_contra h
  exact hl (H.others k hk ho h)

/-- Operands of a low gate are low; operands of any AND are low. -/
theorem low_opnd (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (b : Fin 2)
    (hl : Low G C (n + k) ∨ (gateAt C k).op = GateOp.and) : Low G C (opnd C k b) := by
  rcases LeafBound.ao_op H.ao hk with ho | ho
  · exact H.andLow k hk ho _ (LeafBound.opnd_mem H.ao hk b)
  · have hl' : Low G C (n + k) := by
      rcases hl with h | h
      · exact h
      · rw [ho] at h; exact absurd h (by decide)
    intro hbel
    refine H.lift ⟨k, hk, b, H.cone k hk, ho, hl', hbel, fun _ => true, ?_⟩
    have hlt := opnd_lt C H.ao k hk b
    exact ones_val C H.ao _ (by omega)

/-- Operands of an OR below `F` are below `F`. -/
theorem below_or (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or)
    (hb : BelowF G C k) (b : Fin 2) (x : Fin n → Bool) (hx : wireVal n C (opnd C k b) x = true) :
    graphFun G ∅ x = true := by
  refine hb x ((val_or C hC k hk ho x).2 ?_)
  fin_cases b
  · exact Or.inl hx
  · exact Or.inr hx

/-- A low wire is an OR of its variables, or that OR `g`. -/
theorem val_low (H : OneDirty G C g) : ∀ w < n + C.gates.length, Low G C w → ∀ x,
    (wireVal n C w x = true ↔ (∃ y, x y = true ∧ wireVal n C w (unitInput y) = true) ∨
      (OrReaches n C w g ∧ gateVal n C g x = true)) := by
  refine wire_induction C H.ao _ ?_ ?_
  · intro w hw _ x
    rw [wireVal_lt C w hw]
    constructor
    · intro h
      exact Or.inl ⟨⟨w, hw⟩, h, by rw [wireVal_lt C w hw]; simp [unitInput]⟩
    · rintro (⟨y, hy, h⟩ | ⟨h, _⟩)
      · rw [wireVal_lt C w hw] at h
        simp only [unitInput, decide_eq_true_eq] at h
        rw [h]; exact hy
      · exact absurd h (reach_input C w g hw)
  · intro k hk ih hl x
    rcases LeafBound.ao_op H.ao hk with ho | ho
    · have hkg := low_and H k hk ho hl
      subst hkg
      constructor
      · intro h
        exact Or.inr ⟨(reach_gate C H.ao k k hk).2 (Or.inl rfl), h⟩
      · rintro (⟨y, hy, h⟩ | ⟨_, h⟩)
        · refine mono C H.ao (unitInput y) x ?_ (n + k) (by omega) h
          intro a ha
          simp only [unitInput, decide_eq_true_eq] at ha
          rw [ha]; exact hy
        · exact h
    · have h0 := ih 0 (low_opnd H k hk 0 (Or.inl hl)) x
      have h1 := ih 1 (low_opnd H k hk 1 (Or.inl hl)) x
      have hv : ∀ z, wireVal n C (n + k) z = true ↔
          wireVal n C (opnd C k 0) z = true ∨ wireVal n C (opnd C k 1) z = true := val_or C H.ao k hk ho
      have hkg : g ≠ k := by
        rintro rfl
        rw [H.gand] at ho
        exact absurd ho (by decide)
      rw [hv x, h0, h1, reach_gate C H.ao k g hk]
      constructor
      · rintro ((⟨y, hy, h⟩ | ⟨h, hgx⟩) | (⟨y, hy, h⟩ | ⟨h, hgx⟩))
        · exact Or.inl ⟨y, hy, (hv _).2 (Or.inl h)⟩
        · exact Or.inr ⟨Or.inr ⟨ho, 0, h⟩, hgx⟩
        · exact Or.inl ⟨y, hy, (hv _).2 (Or.inr h)⟩
        · exact Or.inr ⟨Or.inr ⟨ho, 1, h⟩, hgx⟩
      · rintro (⟨y, hy, h⟩ | ⟨h | ⟨_, b, h⟩, hgx⟩)
        · rcases (hv _).1 h with h' | h'
          · exact Or.inl (Or.inl ⟨y, hy, h'⟩)
          · exact Or.inr (Or.inl ⟨y, hy, h'⟩)
        · exact absurd h hkg
        · fin_cases b
          · exact Or.inl (Or.inr ⟨h, hgx⟩)
          · exact Or.inr (Or.inr ⟨h, hgx⟩)

/-- An operand of an AND that does not reach `g` is an OR of its variables. -/
theorem pure_val (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (b : Fin 2) (hr : ¬ OrReaches n C (opnd C k b) g) (x : Fin n → Bool) :
    wireVal n C (opnd C k b) x = true ↔ ∃ y, x y = true ∧ wireVal n C (opnd C k b) (unitInput y) = true := by
  have hlt := opnd_lt C H.ao k hk b
  rw [val_low H _ (by omega) (low_opnd H k hk b (Or.inr ho)) x]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · exact absurd h hr
  · exact Or.inl

/-- An operand of `g` is an OR of its variables. -/
theorem opnd_val (H : OneDirty G C g) (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C g b) x = true ↔ ∃ y, x y = true ∧ wireVal n C (opnd C g b) (unitInput y) = true :=
  pure_val H g H.hg H.gand b (not_reach_opnd C H.ao g H.hg b) x

/-- Variables of the two operands of an AND other than `g` are adjacent. -/
theorem and_pair (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (hkg : k ≠ g) (y z : Fin n) (hy : wireVal n C (opnd C k 0) (unitInput y) = true)
    (hz : wireVal n C (opnd C k 1) (unitInput z) = true) : G.Adj y z := by
  have h0 := opnd_lt C H.ao k hk 0
  have h1 := opnd_lt C H.ao k hk 1
  have hx : graphFun G ∅ (pairInput y z) = true := by
    refine H.others k hk ho hkg _ ((val_and C H.ao k hk ho _).2 ⟨?_, ?_⟩)
    · refine mono C H.ao _ _ ?_ _ (by omega) hy
      intro a ha
      simp only [unitInput, pairInput, decide_eq_true_eq] at ha ⊢
      exact Or.inl ha
    · refine mono C H.ao _ _ ?_ _ (by omega) hz
      intro a ha
      simp only [unitInput, pairInput, decide_eq_true_eq] at ha ⊢
      exact Or.inr ha
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).1 hx
  simp only [pairInput, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw
  · exact huw.symm
  · exact absurd huw (G.loopless.irrefl _)

/-- At most one operand of an AND reaches `g`. -/
theorem not_both (H : OneDirty G C g) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) :
    ¬ (OrReaches n C (opnd C k 0) g ∧ OrReaches n C (opnd C k 1) g) := by
  rintro ⟨h0, h1⟩
  by_cases hkg : k = g
  · subst hkg
    exact not_reach_opnd C H.ao k hk 0 h0
  · have hl0 := opnd_lt C H.ao k hk 0
    have hl1 := opnd_lt C H.ao k hk 1
    refine H.dirty fun x hx => H.others k hk ho hkg x ((val_and C H.ao k hk ho x).2 ⟨?_, ?_⟩)
    · exact (reach_le C H.ao g _ (by omega) h0).2 x hx
    · exact (reach_le C H.ao g _ (by omega) h1).2 x hx

/-- The output is a gate below `F`. -/
theorem out_gate (H : OneDirty G C g) : ∃ o < C.gates.length, C.output = n + o ∧ BelowF G C o := by
  have hb : ∀ o, C.output = n + o → BelowF G C o := by
    intro o ho x hx
    rw [← H.comp]
    show wireVal n C C.output x = true
    rw [ho]; exact hx
  obtain ⟨_, h | ⟨hn, hin⟩⟩ := H.cone g H.hg
  · exact ⟨g, H.hg, h, hb g h⟩
  · refine ⟨C.output - n, ?_, by omega, hb _ (by omega)⟩
    rw [LiveSize.cone_iff] at hin
    obtain ⟨c, hc⟩ := LiveSize.tg_last hin
    exact hc.1

/-- A gate below `F` other than the output is read by an OR below `F`. -/
theorem reader_or (H : OneDirty G C g) (p : ℕ) (hp : p < C.gates.length) (hb : BelowF G C p)
    (hne : C.output ≠ n + p) : ∃ j < C.gates.length, p < j ∧ (gateAt C j).op = GateOp.or ∧ BelowF G C j ∧
      ∃ b, opnd C j b = n + p := by
  obtain ⟨_, h | ⟨_, hin⟩⟩ := H.cone p hp
  · exact absurd h hne
  · rw [LiveSize.cone_iff] at hin
    obtain ⟨j, hj, _⟩ := Relation.TransGen.head'_iff.1 hin
    obtain ⟨hjl, hpj, hmem⟩ := hj
    obtain ⟨b, hbj⟩ := mem_opnd C H.ao j hjl _ hmem
    have hnl : ¬ Low G C (opnd C j b) := by
      rw [hbj]
      exact fun h => h hb
    rcases LeafBound.ao_op H.ao hjl with ho | ho
    · exact absurd (low_opnd H j hjl b (Or.inr ho)) hnl
    · refine ⟨j, hjl, hpj, ho, ?_, b, hbj⟩
      by_contra hl
      exact hnl (low_opnd H j hjl b (Or.inl hl))

/-- Truth passes from a gate below `F` up to the output through the ORs below `F`. -/
theorem top_up (H : OneDirty G C g) (t : ℕ → Bool)
    (ht : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → BelowF G C j → ∀ b i, opnd C j b = n + i →
      BelowF G C i → t i = true → t j = true) :
    ∀ p < C.gates.length, BelowF G C p → t p = true → ∃ o, C.output = n + o ∧ t o = true := by
  have key : ∀ m, ∀ p < C.gates.length, C.gates.length - p = m → BelowF G C p → t p = true →
      ∃ o, C.output = n + o ∧ t o = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro p hp hm hb htp
      by_cases ho : C.output = n + p
      · exact ⟨p, ho, htp⟩
      · obtain ⟨j, hj, hpj, hop, hbj, b, hbo⟩ := reader_or H p hp hb ho
        exact ih (C.gates.length - j) (by omega) j hj rfl hbj (ht j hj hop hbj b p hbo hb htp)
  exact fun p hp => key _ p hp rfl

/-- Where a gate below `F` is true some AND below `F` is true. -/
theorem top_down (H : OneDirty G C g) (x : Fin n → Bool) (hx : graphFun G ∅ x = true) :
    ∃ p < C.gates.length, (gateAt C p).op = GateOp.and ∧ BelowF G C p ∧ gateVal n C p x = true := by
  have key : ∀ m, ∀ k < C.gates.length, k = m → BelowF G C k → gateVal n C k x = true →
      ∃ p < C.gates.length, (gateAt C p).op = GateOp.and ∧ BelowF G C p ∧ gateVal n C p x = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk hm hb hkx
      rcases LeafBound.ao_op H.ao hk with ho | ho
      · exact ⟨k, hk, ho, hb, hkx⟩
      · obtain ⟨b, hbx⟩ : ∃ b, wireVal n C (opnd C k b) x = true := by
          rcases (val_or C H.ao k hk ho x).1 hkx with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        have hlt := opnd_lt C H.ao k hk b
        have hbel : ∀ z, wireVal n C (opnd C k b) z = true → graphFun G ∅ z = true :=
          fun z hz => below_or H.ao k hk ho hb b z hz
        by_cases hin : opnd C k b < n
        · exact absurd hbel (input_low _ hin)
        · have e : n + (opnd C k b - n) = opnd C k b := by omega
          refine ih (opnd C k b - n) (by omega) _ (by omega) rfl ?_ ?_
          · intro z hz
            refine hbel z ?_
            rw [← e]; exact hz
          · show wireVal n C (n + (opnd C k b - n)) x = true
            rw [e]; exact hbx
  obtain ⟨o, hol, ho, hob⟩ := out_gate H
  refine key o o hol rfl hob ?_
  have h : circuitFun n C x = true := by rw [H.comp]; exact hx
  have h' : wireVal n C C.output x = true := h
  rw [ho] at h'
  exact h'

end

end PEqualNP.MetaComplexity.LowerPart
