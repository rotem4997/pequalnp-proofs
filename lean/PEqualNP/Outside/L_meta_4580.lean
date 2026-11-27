import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4580

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev inc (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def evalPL (C : Circuit) (P L : Finset (Fin 13)) : Bool :=
  circuitFun 26 C (fun i =>
    Fin.addCases (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L)) i)

def isGeneric (P L : Finset (Fin 13)) : Prop :=
  (∀ l : Fin 13, l ∈ L ↔ ∀ p ∈ P, ¬ inc p l) ∧
  (∀ p ∉ P, ∃ l ∈ L, inc p l) ∧
  (¬ ∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧
  (¬ ∃ p : Fin 13, ∀ l ∈ L, inc p l)

def isGood (C : Circuit) : Prop :=
  (∀ p l : Fin 13, inc p l → evalPL C {p} {l} = true) ∧
  (∀ P L : Finset (Fin 13), isGeneric P L → evalPL C P L = false)

def degOK (C : Circuit) : Prop :=
  let d1 := C.lineDeg 26 (Finset.range 13)
  let d2 := C.lineDeg 26 (Finset.Ico 13 26)
  2 ≤ min d1 d2 ∧ 3 ≤ max d1 d2

def hitsTarget (C : Circuit) : Prop :=
  ∃ m ∈ ([8191, 15860, 31200, 107904] : List ℕ),
    circuitFun 26 C (fun i : Fin 26 => m.testBit i.val) = true

/-! ## Circuit evaluation helpers and monotonicity -/

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepB x := rfl

theorem stepB_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (h : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    (stepB w1 g).length = (stepB w2 g).length ∧
    ∀ i, (stepB w1 g).getD i false = true → (stepB w2 g).getD i false = true := by
  have hlen' : (stepB w1 g).length = (stepB w2 g).length := by simp [stepB, hlen]
  refine ⟨hlen', fun i hi => ?_⟩
  by_cases hlt : i < w1.length
  · have hlt2 : i < w2.length := hlen ▸ hlt
    simp only [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
      List.getElem?_append_left hlt2] at hi ⊢
    exact h i hi
  · by_cases heq : i = w1.length
    · subst heq
      have h1 : (stepB w1 g).getD w1.length false =
          g.op.eval (g.inputs.map fun j => w1.getD j false) := by
        simp [stepB, List.getD_eq_getElem?_getD]
      have h2 : (stepB w2 g).getD w1.length false =
          g.op.eval (g.inputs.map fun j => w2.getD j false) := by
        rw [hlen]
        simp [stepB, List.getD_eq_getElem?_getD]
      rw [h1] at hi
      rw [h2]
      rcases hg with ha | ho
      · rw [ha] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        intro j hj
        exact h j (hi j hj)
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨j, hj, hjv⟩ := hi
        exact ⟨j, hj, h j hjv⟩
    · have hge1 : (stepB w1 g).length ≤ i := by simp [stepB]; omega
      rw [List.getD_eq_default _ _ hge1] at hi
      exact Bool.noConfusion hi

theorem foldl_stepB_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl stepB w1).getD i false = true → (gs.foldl stepB w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w1 w2 hlen h i hi
    have hg := hgs g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    obtain ⟨hlen', h'⟩ := stepB_mono g hg w1 w2 hlen h
    exact ih hrest (stepB w1 g) (stepB w2 g) hlen' h' i hi

theorem circuitFun_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin 26 → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    circuitFun 26 C x = true → circuitFun 26 C y = true := by
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hm g hg).1
  apply foldl_stepB_mono C.gates hgs (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hlt : i < 26
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
      Option.getD_some] at hi ⊢
    exact hxy ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

/-! ## Input wire relabelling `permCircuit` -/

def permWire (σ : Fin 26 → Fin 26) (i : ℕ) : ℕ :=
  if h : i < 26 then (σ ⟨i, h⟩).val else i

def permGate (σ : Fin 26 → Fin 26) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire σ)⟩

def permCircuit (σ : Fin 26 → Fin 26) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permGate σ), output := permWire σ C.output }

theorem permCircuit_size (σ : Fin 26 → Fin 26) (C : Circuit) :
    (permCircuit σ C).size = C.size := by
  simp [permCircuit, Circuit.size]

theorem permCircuit_mono (σ : Fin 26 → Fin 26) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (permCircuit σ C) := by
  intro g hg
  simp only [permCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [permGate] using hm g0 hg0

theorem stepB_perm (σ : Fin 26 → Fin 26) (g : Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (h26 : 26 ≤ w1.length)
    (hinv : ∀ i, w2.getD (permWire σ i) false = w1.getD i false) :
    (stepB w1 g).length = (stepB w2 (permGate σ g)).length ∧
    26 ≤ (stepB w1 g).length ∧
    ∀ i, (stepB w2 (permGate σ g)).getD (permWire σ i) false = (stepB w1 g).getD i false := by
  have hval : (permGate σ g).op.eval ((permGate σ g).inputs.map fun j => w2.getD j false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
    simp only [permGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hinv i
  refine ⟨by simp [stepB, hlen], by simp [stepB]; omega, fun i => ?_⟩
  by_cases hi26 : i < 26
  · have hpi : permWire σ i < 26 := by
      simp only [permWire, hi26, ↓reduceDIte]
      exact (σ ⟨i, hi26⟩).isLt
    have hlt1 : i < w1.length := by omega
    have hlt2 : permWire σ i < w2.length := by omega
    simp only [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
      List.getElem?_append_left hlt2]
    exact hinv i
  · have hpi : permWire σ i = i := by simp [permWire, hi26]
    rw [hpi]
    by_cases hlt : i < w1.length
    · have hlt2 : i < w2.length := hlen ▸ hlt
      simp only [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_append_left hlt2]
      have h0 := hinv i
      rw [hpi] at h0
      exact h0
    · by_cases heq : i = w1.length
      · subst heq
        have h1 : (stepB w1 g).getD w1.length false =
            g.op.eval (g.inputs.map fun j => w1.getD j false) := by
          simp [stepB, List.getD_eq_getElem?_getD]
        have h2 : (stepB w2 (permGate σ g)).getD w1.length false =
            (permGate σ g).op.eval ((permGate σ g).inputs.map fun j => w2.getD j false) := by
          rw [hlen]
          simp [stepB, List.getD_eq_getElem?_getD]
        rw [h1, h2, hval]
      · have hge1 : (stepB w1 g).length ≤ i := by simp [stepB]; omega
        have hge2 : (stepB w2 (permGate σ g)).length ≤ i := by simp [stepB]; omega
        rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]

theorem foldl_stepB_perm (σ : Fin 26 → Fin 26) (gs : List Gate) :
    ∀ w1 w2 : List Bool, w1.length = w2.length → 26 ≤ w1.length →
      (∀ i, w2.getD (permWire σ i) false = w1.getD i false) →
      ∀ i, ((gs.map (permGate σ)).foldl stepB w2).getD (permWire σ i) false =
        (gs.foldl stepB w1).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ hinv i; exact hinv i
  | cons g gs ih =>
    intro w1 w2 hlen h26 hinv i
    obtain ⟨hlen', h26', hinv'⟩ := stepB_perm σ g w1 w2 hlen h26 hinv
    exact ih (stepB w1 g) (stepB w2 (permGate σ g)) hlen' h26' hinv' i

theorem permCircuit_eval (σ : Fin 26 → Fin 26) (C : Circuit) (y : Fin 26 → Bool) :
    circuitFun 26 (permCircuit σ C) y = circuitFun 26 C (fun i => y (σ i)) := by
  apply foldl_stepB_perm σ C.gates (List.ofFn (fun i => y (σ i))) (List.ofFn y)
    (by simp) (by simp)
  intro i
  by_cases hi : i < 26
  · have hlt : (σ ⟨i, hi⟩).val < 26 := (σ ⟨i, hi⟩).isLt
    simp only [permWire, hi, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt,
      Option.getD_some, Fin.eta]
  · simp only [permWire, hi, ↓reduceDIte]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def stepD (d : List ℕ) (g : Gate) : List ℕ :=
  d ++ [g.lineDegree d]

theorem stepD_perm (σ : Fin 26 → Fin 26) (g : Gate) (d1 d2 : List ℕ)
    (hlen : d1.length = d2.length) (h26 : 26 ≤ d1.length)
    (hinv : ∀ i, d2.getD (permWire σ i) 0 = d1.getD i 0) :
    (stepD d1 g).length = (stepD d2 (permGate σ g)).length ∧
    26 ≤ (stepD d1 g).length ∧
    ∀ i, (stepD d2 (permGate σ g)).getD (permWire σ i) 0 = (stepD d1 g).getD i 0 := by
  have hval : (permGate σ g).lineDegree d2 = g.lineDegree d1 := by
    let _ := lineDegreeGateOpDecEq
    unfold Gate.lineDegree
    have hmap : ((permGate σ g).inputs.map fun j => d2.getD j 0) =
        g.inputs.map (fun i => d1.getD i 0) := by
      simp only [permGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact hinv i
    change (if g.op = GateOp.and then _ else _) = (if g.op = GateOp.and then _ else _)
    rw [hmap]
  refine ⟨by simp [stepD, hlen], by simp [stepD]; omega, fun i => ?_⟩
  by_cases hi26 : i < 26
  · have hpi : permWire σ i < 26 := by
      simp only [permWire, hi26, ↓reduceDIte]
      exact (σ ⟨i, hi26⟩).isLt
    have hlt1 : i < d1.length := by omega
    have hlt2 : permWire σ i < d2.length := by omega
    simp only [stepD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
      List.getElem?_append_left hlt2]
    exact hinv i
  · have hpi : permWire σ i = i := by simp [permWire, hi26]
    rw [hpi]
    by_cases hlt : i < d1.length
    · have hlt2 : i < d2.length := hlen ▸ hlt
      simp only [stepD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_append_left hlt2]
      have h0 := hinv i
      rw [hpi] at h0
      exact h0
    · by_cases heq : i = d1.length
      · subst heq
        have h1 : (stepD d1 g).getD d1.length 0 = g.lineDegree d1 := by
          simp [stepD, List.getD_eq_getElem?_getD]
        have h2 : (stepD d2 (permGate σ g)).getD d1.length 0 = (permGate σ g).lineDegree d2 := by
          rw [hlen]
          simp [stepD, List.getD_eq_getElem?_getD]
        rw [h1, h2, hval]
      · have hge1 : (stepD d1 g).length ≤ i := by simp [stepD]; omega
        have hge2 : (stepD d2 (permGate σ g)).length ≤ i := by simp [stepD]; omega
        rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]

theorem foldl_stepD_perm (σ : Fin 26 → Fin 26) (gs : List Gate) :
    ∀ d1 d2 : List ℕ, d1.length = d2.length → 26 ≤ d1.length →
      (∀ i, d2.getD (permWire σ i) 0 = d1.getD i 0) →
      ∀ i, ((gs.map (permGate σ)).foldl stepD d2).getD (permWire σ i) 0 =
        (gs.foldl stepD d1).getD i 0 := by
  induction gs with
  | nil => intro d1 d2 _ _ hinv i; exact hinv i
  | cons g gs ih =>
    intro d1 d2 hlen h26 hinv i
    obtain ⟨hlen', h26', hinv'⟩ := stepD_perm σ g d1 d2 hlen h26 hinv
    exact ih (stepD d1 g) (stepD d2 (permGate σ g)) hlen' h26' hinv' i

theorem permCircuit_lineDeg (σ : Fin 26 → Fin 26) (C : Circuit) (M M' : Finset ℕ)
    (hM : ∀ i : Fin 26, (σ i).val ∈ M ↔ i.val ∈ M') :
    (permCircuit σ C).lineDeg 26 M = C.lineDeg 26 M' := by
  show ((C.gates.map (permGate σ)).foldl stepD
      ((List.range 26).map fun j => if j ∈ M then 1 else 0)).getD (permWire σ C.output) 0 =
    (C.gates.foldl stepD ((List.range 26).map fun i => if i ∈ M' then 1 else 0)).getD C.output 0
  apply foldl_stepD_perm σ C.gates _ _ (by simp) (by simp)
  intro i
  by_cases hi : i < 26
  · have hlt : (σ ⟨i, hi⟩).val < 26 := (σ ⟨i, hi⟩).isLt
    simp only [permWire, hi, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hlt, List.getElem?_range hi, Option.map_some, Option.getD_some]
    by_cases hm : i ∈ M'
    · have hm2 : (σ ⟨i, hi⟩).val ∈ M := (hM ⟨i, hi⟩).2 hm
      simp only [hm, hm2, ↓reduceIte]
    · have hm2 : (σ ⟨i, hi⟩).val ∉ M := fun h => hm ((hM ⟨i, hi⟩).1 h)
      simp only [hm, hm2, ↓reduceIte]
  · simp only [permWire, hi, ↓reduceDIte]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-! ## Collineations and duality of PG(2,3) -/

def colSigma (φ ψ : Fin 13 → Fin 13) (i : Fin 26) : Fin 26 :=
  Fin.addCases (m := 13) (n := 13)
    (fun p : Fin 13 => (Fin.castAdd 13 (φ p) : Fin 26))
    (fun l : Fin 13 => (Fin.natAdd 13 (ψ l) : Fin 26))
    (i : Fin (13 + 13))

theorem colSigma_evalPL (φ ψ φ' ψ' : Fin 13 → Fin 13)
    (hφL : ∀ x, φ' (φ x) = x) (hφR : ∀ y, φ (φ' y) = y)
    (hψL : ∀ x, ψ' (ψ x) = x) (hψR : ∀ y, ψ (ψ' y) = y)
    (C : Circuit) (P L : Finset (Fin 13)) :
    evalPL (permCircuit (colSigma φ ψ) C) P L = evalPL C (P.image φ') (L.image ψ') := by
  unfold evalPL
  rw [permCircuit_eval]
  congr 1
  funext i
  refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
  · simp only [colSigma, Fin.addCases_left]
    have hiff : φ p ∈ P ↔ p ∈ P.image φ' := by
      constructor
      · intro hp; exact Finset.mem_image.2 ⟨φ p, hp, hφL p⟩
      · intro hp; obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hp; rw [← hqe, hφR q]; exact hq
    exact decide_eq_decide.2 hiff
  · simp only [colSigma, Fin.addCases_right]
    have hiff : ψ l ∈ L ↔ l ∈ L.image ψ' := by
      constructor
      · intro hl; exact Finset.mem_image.2 ⟨ψ l, hl, hψL l⟩
      · intro hl; obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hl; rw [← hqe, hψR q]; exact hq
    exact decide_eq_decide.2 hiff

theorem colSigma_preserves (φ ψ φ' ψ' : Fin 13 → Fin 13)
    (hφL : ∀ x, φ' (φ x) = x) (hφR : ∀ y, φ (φ' y) = y)
    (hψL : ∀ x, ψ' (ψ x) = x) (hψR : ∀ y, ψ (ψ' y) = y)
    (hinc : ∀ p l, inc (φ p) (ψ l) ↔ inc p l)
    (C : Circuit) (hgood : isGood C) (hdeg : degOK C) :
    isGood (permCircuit (colSigma φ ψ) C) ∧ degOK (permCircuit (colSigma φ ψ) C) := by
  have hinc' : ∀ p l, inc (φ' p) (ψ' l) ↔ inc p l := by
    intro p l
    rw [← hinc (φ' p) (ψ' l), hφR p, hψR l]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p l hpl
    rw [colSigma_evalPL φ ψ φ' ψ' hφL hφR hψL hψR C {p} {l}]
    simp only [Finset.image_singleton]
    exact hgood.1 (φ' p) (ψ' l) ((hinc' p l).2 hpl)
  · intro P L hgen
    rw [colSigma_evalPL φ ψ φ' ψ' hφL hφR hψL hψR C P L]
    apply hgood.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l
      constructor
      · intro hl p hp
        obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.1 hl
        obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.1 hp
        exact fun hi => (hgen.1 l0).1 hl0 p0 hp0 ((hinc' p0 l0).1 hi)
      · intro hall
        have hmem : ψ l ∈ L := (hgen.1 (ψ l)).2 (fun p0 hp0 hi =>
          hall (φ' p0) (Finset.mem_image.2 ⟨p0, hp0, rfl⟩)
            ((hinc (φ' p0) l).1 (by rw [hφR p0]; exact hi)))
        exact Finset.mem_image.2 ⟨ψ l, hmem, hψL l⟩
    · intro p hp
      have hnp : φ p ∉ P := fun hm => hp (Finset.mem_image.2 ⟨φ p, hm, hφL p⟩)
      obtain ⟨l0, hl0, hi⟩ := hgen.2.1 (φ p) hnp
      exact ⟨ψ' l0, Finset.mem_image.2 ⟨l0, hl0, rfl⟩,
        (hinc p (ψ' l0)).1 (by rw [hψR l0]; exact hi)⟩
    · rintro ⟨l, hl⟩
      apply hgen.2.2.1
      refine ⟨ψ l, fun p0 hp0 => ?_⟩
      have := hl (φ' p0) (Finset.mem_image.2 ⟨p0, hp0, rfl⟩)
      rwa [← hinc (φ' p0) l, hφR p0] at this
    · rintro ⟨p, hp⟩
      apply hgen.2.2.2
      refine ⟨φ p, fun l0 hl0 => ?_⟩
      have := hp (ψ' l0) (Finset.mem_image.2 ⟨l0, hl0, rfl⟩)
      rwa [← hinc p (ψ' l0), hψR l0] at this
  · have hM1 : ∀ i : Fin 26, (colSigma φ ψ i).val ∈ Finset.range 13 ↔ i.val ∈ Finset.range 13 := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
      · simp [colSigma, (φ p).isLt, p.isLt]
      · simp only [colSigma, Fin.addCases_right, Finset.mem_range, Fin.val_natAdd]
        omega
    have hM2 : ∀ i : Fin 26, (colSigma φ ψ i).val ∈ Finset.Ico 13 26 ↔ i.val ∈ Finset.Ico 13 26 := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
      · simp only [colSigma, Fin.addCases_left, Finset.mem_Ico, Fin.val_castAdd]
        have := (φ p).isLt; have := p.isLt; omega
      · simp only [colSigma, Fin.addCases_right, Finset.mem_Ico, Fin.val_natAdd]
        have := (ψ l).isLt; have := l.isLt; omega
    unfold degOK at hdeg ⊢
    rw [permCircuit_lineDeg (colSigma φ ψ) C _ _ hM1,
        permCircuit_lineDeg (colSigma φ ψ) C _ _ hM2]
    exact hdeg

def dualSigma (i : Fin 26) : Fin 26 :=
  Fin.addCases (m := 13) (n := 13)
    (fun p : Fin 13 => (Fin.natAdd 13 (-p) : Fin 26))
    (fun l : Fin 13 => (Fin.castAdd 13 (-l) : Fin 26))
    (i : Fin (13 + 13))

theorem inc_neg_iff (p l : Fin 13) : inc (-l) (-p) ↔ inc p l := by
  revert p l; decide

theorem dualSigma_evalPL (C : Circuit) (P L : Finset (Fin 13)) :
    evalPL (permCircuit dualSigma C) P L = evalPL C (L.image (-·)) (P.image (-·)) := by
  unfold evalPL
  rw [permCircuit_eval]
  congr 1
  funext i
  refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
  · simp only [dualSigma, Fin.addCases_left, Fin.addCases_right]
    have hiff : (-p) ∈ L ↔ p ∈ L.image (-·) := by
      constructor
      · intro h; exact Finset.mem_image.2 ⟨-p, h, neg_neg p⟩
      · intro h; obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 h; rw [← hqe, neg_neg q]; exact hq
    exact decide_eq_decide.2 hiff
  · simp only [dualSigma, Fin.addCases_right, Fin.addCases_left]
    have hiff : (-l) ∈ P ↔ l ∈ P.image (-·) := by
      constructor
      · intro h; exact Finset.mem_image.2 ⟨-l, h, neg_neg l⟩
      · intro h; obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 h; rw [← hqe, neg_neg q]; exact hq
    exact decide_eq_decide.2 hiff

theorem dualSigma_preserves (C : Circuit) (hgood : isGood C) (hdeg : degOK C) :
    isGood (permCircuit dualSigma C) ∧ degOK (permCircuit dualSigma C) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p l hpl
    rw [dualSigma_evalPL]
    simp only [Finset.image_singleton]
    exact hgood.1 (-l) (-p) ((inc_neg_iff p l).2 hpl)
  · intro P L hgen
    rw [dualSigma_evalPL]
    apply hgood.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l
      constructor
      · intro hl p hp
        obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.1 hl
        obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.1 hp
        exact fun hi => (hgen.1 p0).1 hp0 l0 hl0 ((inc_neg_iff l0 p0).1 hi)
      · intro hall
        by_contra hnot
        have hnp : (-l) ∉ P := fun h => hnot (Finset.mem_image.2 ⟨-l, h, neg_neg l⟩)
        obtain ⟨q, hq, hi⟩ := hgen.2.1 (-l) hnp
        exact hall (-q) (Finset.mem_image.2 ⟨q, hq, rfl⟩)
          ((inc_neg_iff (-l) q).2 hi |> fun h => by rwa [neg_neg] at h)
    · intro p hp
      have hnp : (-p) ∉ L := fun h => hp (Finset.mem_image.2 ⟨-p, h, neg_neg p⟩)
      have hne : ¬ ∀ q ∈ P, ¬ inc q (-p) := fun hall => hnp ((hgen.1 (-p)).2 hall)
      push Not at hne
      obtain ⟨q, hq, hi⟩ := hne
      exact ⟨-q, Finset.mem_image.2 ⟨q, hq, rfl⟩,
        (inc_neg_iff q (-p)).2 hi |> fun h => by rwa [neg_neg] at h⟩
    · rintro ⟨l, hl⟩
      apply hgen.2.2.2
      refine ⟨-l, fun q hq => ?_⟩
      have h1 := hl (-q) (Finset.mem_image.2 ⟨q, hq, rfl⟩)
      exact (inc_neg_iff (-l) q).1 (by rwa [neg_neg])
    · rintro ⟨p, hp⟩
      apply hgen.2.2.1
      refine ⟨-p, fun q hq => ?_⟩
      have h1 := hp (-q) (Finset.mem_image.2 ⟨q, hq, rfl⟩)
      exact (inc_neg_iff q (-p)).1 (by rwa [neg_neg])
  · have hM1 : ∀ i : Fin 26, (dualSigma i).val ∈ Finset.range 13 ↔ i.val ∈ Finset.Ico 13 26 := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
      · simp only [dualSigma, Fin.addCases_left, Finset.mem_range, Finset.mem_Ico,
          Fin.val_natAdd, Fin.val_castAdd]
        have := p.isLt; omega
      · simp only [dualSigma, Fin.addCases_right, Finset.mem_range, Finset.mem_Ico,
          Fin.val_castAdd, Fin.val_natAdd]
        have := (-l).isLt; have := l.isLt; omega
    have hM2 : ∀ i : Fin 26, (dualSigma i).val ∈ Finset.Ico 13 26 ↔ i.val ∈ Finset.range 13 := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) (i : Fin (13 + 13))
      · simp only [dualSigma, Fin.addCases_left, Finset.mem_Ico, Finset.mem_range,
          Fin.val_natAdd, Fin.val_castAdd]
        have := (-p).isLt; have := p.isLt; omega
      · simp only [dualSigma, Fin.addCases_right, Finset.mem_Ico, Finset.mem_range,
          Fin.val_castAdd, Fin.val_natAdd]
        have := (-l).isLt; omega
    unfold degOK at hdeg ⊢
    dsimp only at hdeg ⊢
    rw [permCircuit_lineDeg dualSigma C _ _ hM1,
        permCircuit_lineDeg dualSigma C _ _ hM2,
        min_comm, max_comm]
    exact hdeg

/-! ## Polarity sets, pencils, and explicit PG(2,3) collineations -/

def perpP (P : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ P, ¬ inc p l)

def perpL (L : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => ∀ l ∈ L, ¬ inc p l)

def pencil (p0 : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => inc p0 l)

theorem pencil_card (p0 : Fin 13) : (pencil p0).card = 4 := by
  revert p0; decide

theorem perpL_pencil (p0 : Fin 13) : perpL (pencil p0) = ∅ := by
  revert p0; decide

theorem perpL_image (φ ψ φ' ψ' : Fin 13 → Fin 13)
    (hφL : ∀ x, φ' (φ x) = x) (hφR : ∀ y, φ (φ' y) = y)
    (_hψL : ∀ x, ψ' (ψ x) = x) (hψR : ∀ y, ψ (ψ' y) = y)
    (hinc : ∀ p l, inc (φ p) (ψ l) ↔ inc p l)
    (L : Finset (Fin 13)) :
    (perpL L).image φ' = perpL (L.image ψ') := by
  ext p
  simp only [Finset.mem_image, perpL, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p0, hp0, rfl⟩ l ⟨l0, hl0, rfl⟩ hi
    exact hp0 l0 hl0 ((hinc (φ' p0) (ψ' l0)).2 hi |> fun h => by rwa [hφR p0, hψR l0] at h)
  · intro hall
    refine ⟨φ p, fun l0 hl0 hi => ?_, hφL p⟩
    exact hall (ψ' l0) ⟨l0, hl0, rfl⟩ ((hinc p (ψ' l0)).1 (by rw [hψR l0]; exact hi))

def arrToFn (xs : List ℕ) (i : Fin 13) : Fin 13 :=
  Fin.ofNat 13 (xs.getD i.val 0)

def invFn (f : Fin 13 → Fin 13) (y : Fin 13) : Fin 13 :=
  ((List.finRange 13).find? (fun x => decide (f x = y))).getD 0

def phi2 (idx : Fin 6) : Fin 13 → Fin 13 :=
  match idx.val with
  | 0 => arrToFn [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | 1 => arrToFn [0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 11, 7]
  | 2 => arrToFn [0, 1, 5, 3, 6, 11, 12, 10, 7, 9, 8, 2, 4]
  | 3 => arrToFn [5, 1, 0, 8, 3, 2, 10, 11, 4, 6, 9, 12, 7]
  | 4 => arrToFn [5, 1, 0, 6, 3, 11, 12, 2, 7, 8, 9, 10, 4]
  | _ => arrToFn [5, 1, 7, 6, 11, 2, 10, 3, 4, 8, 12, 9, 0]

def psi2 (idx : Fin 6) : Fin 13 → Fin 13 :=
  match idx.val with
  | 0 => arrToFn [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | 1 => arrToFn [0, 5, 2, 7, 12, 1, 9, 3, 8, 6, 10, 11, 4]
  | 2 => arrToFn [0, 5, 2, 3, 10, 11, 9, 7, 6, 8, 12, 1, 4]
  | 3 => arrToFn [5, 0, 12, 7, 2, 1, 10, 8, 3, 6, 9, 11, 4]
  | 4 => arrToFn [5, 0, 10, 3, 2, 11, 12, 6, 7, 8, 9, 1, 4]
  | _ => arrToFn [5, 11, 6, 10, 2, 1, 7, 3, 8, 12, 9, 0, 4]

def phi3 (idx : Fin 4) : Fin 13 → Fin 13 :=
  match idx.val with
  | 0 => arrToFn [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | 1 => arrToFn [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8]
  | 2 => arrToFn [0, 1, 7, 3, 12, 8, 6, 2, 5, 9, 11, 10, 4]
  | _ => arrToFn [7, 8, 0, 3, 12, 1, 6, 11, 5, 10, 2, 9, 4]

def psi3 (idx : Fin 4) : Fin 13 → Fin 13 :=
  match idx.val with
  | 0 => arrToFn [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | 1 => arrToFn [0, 1, 2, 7, 10, 11, 6, 3, 9, 8, 4, 5, 12]
  | 2 => arrToFn [0, 11, 7, 3, 12, 5, 6, 2, 9, 8, 10, 1, 4]
  | _ => arrToFn [7, 12, 0, 3, 11, 5, 10, 2, 9, 1, 6, 8, 4]

theorem col2_valid (idx : Fin 6) :
    (∀ x, invFn (phi2 idx) (phi2 idx x) = x) ∧
    (∀ y, phi2 idx (invFn (phi2 idx) y) = y) ∧
    (∀ x, invFn (psi2 idx) (psi2 idx x) = x) ∧
    (∀ y, psi2 idx (invFn (psi2 idx) y) = y) ∧
    (∀ p l, inc (phi2 idx p) (psi2 idx l) ↔ inc p l) := by
  revert idx; decide

theorem col2_hits : ∀ a b : Fin 13, a ≠ b → inc 1 a → inc 1 b →
    ∃ idx : Fin 6, (psi2 idx a = 0 ∧ psi2 idx b = 1) ∨ (psi2 idx a = 1 ∧ psi2 idx b = 0) := by
  decide

theorem col3_valid (idx : Fin 4) :
    (∀ x, invFn (phi3 idx) (phi3 idx x) = x) ∧
    (∀ y, phi3 idx (invFn (phi3 idx) y) = y) ∧
    (∀ x, invFn (psi3 idx) (psi3 idx x) = x) ∧
    (∀ y, psi3 idx (invFn (psi3 idx) y) = y) ∧
    (∀ p l, inc (phi3 idx p) (psi3 idx l) ↔ inc p l) := by
  revert idx; decide

theorem col3_hits : ∀ lm : Fin 13, inc 3 lm →
    ∃ idx : Fin 4, phi3 idx 3 = 3 ∧ psi3 idx lm = 7 := by
  decide

theorem bits_8191 : ∀ i : Fin 26, (8191 : ℕ).testBit i.val =
    Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL ∅))
      (fun l : Fin 13 => decide (l ∈ (∅ : Finset (Fin 13)))) i := by decide

theorem bits_15860 : ∀ i : Fin 26, (15860 : ℕ).testBit i.val =
    Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0}))
      (fun l : Fin 13 => decide (l ∈ ({0} : Finset (Fin 13)))) i := by decide

theorem bits_31200 : ∀ i : Fin 26, (31200 : ℕ).testBit i.val =
    Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0, 1}))
      (fun l : Fin 13 => decide (l ∈ ({0, 1} : Finset (Fin 13)))) i := by decide

theorem bits_107904 : ∀ i : Fin 26, (107904 : ℕ).testBit i.val =
    Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0, 2, 3}))
      (fun l : Fin 13 => decide (l ∈ ({0, 2, 3} : Finset (Fin 13)))) i := by decide

theorem pencil3_erase7 : (pencil 3).erase 7 = ({0, 2, 3} : Finset (Fin 13)) := by decide

theorem trans_inc (c p l : Fin 13) : inc (p + c) (l + c) ↔ inc p l := by
  revert c p l; decide

theorem from_pencil (C : Circuit) (hm : Monotone2 C) (hgood : isGood C) (hdeg : degOK C)
    (L : Finset (Fin 13)) (p0 : Fin 13)
    (hLpen : ∀ l ∈ L, inc p0 l) (hLP : L = perpP (perpL L))
    (htrue : evalPL C (perpL L) L = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ isGood C' ∧ degOK C' ∧ hitsTarget C' := by
  have hsub : L ⊆ pencil p0 := fun l hl => Finset.mem_filter.2 ⟨Finset.mem_univ l, hLpen l hl⟩
  have hcard_le : L.card ≤ 4 := (Finset.card_le_card hsub).trans_eq (pencil_card p0)
  have hne4 : L.card ≠ 4 := by
    intro h4
    have heq : L = pencil p0 := Finset.eq_of_subset_of_card_le hsub (by rw [pencil_card p0, h4])
    rw [heq, perpL_pencil] at hLP
    have huniv : perpP (∅ : Finset (Fin 13)) = Finset.univ := by ext x; simp [perpP]
    rw [huniv] at hLP
    have hc : L.card = 13 := by rw [heq, hLP]; simp
    omega
  have hcases : L.card = 0 ∨ L.card = 1 ∨ L.card = 2 ∨ L.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hLe : L = ∅ := Finset.card_eq_zero.1 h0
    subst hLe
    refine ⟨C, hm, le_rfl, hgood, hdeg, 8191, by simp, ?_⟩
    have heq : (fun i : Fin 26 => (8191 : ℕ).testBit i.val) =
        (fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL ∅))
          (fun l : Fin 13 => decide (l ∈ (∅ : Finset (Fin 13)))) i) := funext bits_8191
    rw [heq]
    exact htrue
  · obtain ⟨l1, rfl⟩ := Finset.card_eq_one.1 h1
    let φ : Fin 13 → Fin 13 := fun p => p + (-l1)
    let φ' : Fin 13 → Fin 13 := fun p => p + l1
    have hL : ∀ x, φ' (φ x) = x := fun x => neg_add_cancel_right x l1
    have hR : ∀ y, φ (φ' y) = y := fun y => add_neg_cancel_right y l1
    have hinc : ∀ p l, inc (φ p) (φ l) ↔ inc p l := fun p l => trans_inc (-l1) p l
    let C' := permCircuit (colSigma φ φ) C
    obtain ⟨hgood', hdeg'⟩ := colSigma_preserves φ φ φ' φ' hL hR hL hR hinc C hgood hdeg
    refine ⟨C', permCircuit_mono _ C hm, by rw [permCircuit_size], hgood', hdeg', 15860, by simp, ?_⟩
    have heq : (fun i : Fin 26 => (15860 : ℕ).testBit i.val) =
        (fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0}))
          (fun l : Fin 13 => decide (l ∈ ({0} : Finset (Fin 13)))) i) := funext bits_15860
    rw [heq]
    change evalPL C' (perpL {0}) {0} = true
    rw [colSigma_evalPL φ φ φ' φ' hL hR hL hR C (perpL {0}) {0},
        perpL_image φ φ φ' φ' hL hR hL hR hinc {0}]
    have himg : ({0} : Finset (Fin 13)).image φ' = {l1} := by simp [φ']
    rw [himg]
    exact htrue
  · obtain ⟨l1, l2, hne, rfl⟩ := Finset.card_eq_two.1 h2
    let c : Fin 13 := 1 - p0
    have hpc : p0 + c = 1 := by dsimp [c]; exact add_sub_cancel p0 1
    have hinc1 : inc 1 (l1 + c) := by
      rw [← hpc]
      exact (trans_inc c p0 l1).2 (hLpen l1 (by simp))
    have hinc2 : inc 1 (l2 + c) := by
      rw [← hpc]
      exact (trans_inc c p0 l2).2 (hLpen l2 (by simp))
    have hne' : l1 + c ≠ l2 + c := fun h => hne (add_right_cancel h)
    obtain ⟨idx, hhit⟩ := col2_hits (l1 + c) (l2 + c) hne' hinc1 hinc2
    obtain ⟨hφ2L, hφ2R, hψ2L, hψ2R, hinc2'⟩ := col2_valid idx
    let φ : Fin 13 → Fin 13 := fun p => phi2 idx (p + c)
    let ψ : Fin 13 → Fin 13 := fun l => psi2 idx (l + c)
    let φ' : Fin 13 → Fin 13 := fun p => invFn (phi2 idx) p + (-c)
    let ψ' : Fin 13 → Fin 13 := fun l => invFn (psi2 idx) l + (-c)
    have hφL : ∀ x, φ' (φ x) = x := fun x => by dsimp [φ, φ']; rw [hφ2L]; exact add_neg_cancel_right x c
    have hφR : ∀ y, φ (φ' y) = y := fun y => by
      dsimp [φ, φ']; rw [neg_add_cancel_right, hφ2R]
    have hψL : ∀ x, ψ' (ψ x) = x := fun x => by dsimp [ψ, ψ']; rw [hψ2L]; exact add_neg_cancel_right x c
    have hψR : ∀ y, ψ (ψ' y) = y := fun y => by
      dsimp [ψ, ψ']; rw [neg_add_cancel_right, hψ2R]
    have hinc : ∀ p l, inc (φ p) (ψ l) ↔ inc p l := fun p l =>
      (hinc2' (p + c) (l + c)).trans (trans_inc c p l)
    let C' := permCircuit (colSigma φ ψ) C
    obtain ⟨hgood', hdeg'⟩ := colSigma_preserves φ ψ φ' ψ' hφL hφR hψL hψR hinc C hgood hdeg
    refine ⟨C', permCircuit_mono _ C hm, by rw [permCircuit_size], hgood', hdeg', 31200, by simp, ?_⟩
    have heq : (fun i : Fin 26 => (31200 : ℕ).testBit i.val) =
        (fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0, 1}))
          (fun l : Fin 13 => decide (l ∈ ({0, 1} : Finset (Fin 13)))) i) := funext bits_31200
    rw [heq]
    change evalPL C' (perpL {0, 1}) {0, 1} = true
    rw [colSigma_evalPL φ ψ φ' ψ' hφL hφR hψL hψR C (perpL {0, 1}) {0, 1},
        perpL_image φ ψ φ' ψ' hφL hφR hψL hψR hinc {0, 1}]
    have himg : ({0, 1} : Finset (Fin 13)).image ψ' = {l1, l2} := by
      rcases hhit with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have e0 : ψ' 0 = l1 := by rw [← ha]; exact hψL l1
        have e1 : ψ' 1 = l2 := by rw [← hb]; exact hψL l2
        simp [e0, e1]
      · have e0 : ψ' 0 = l2 := by rw [← hb]; exact hψL l2
        have e1 : ψ' 1 = l1 := by rw [← ha]; exact hψL l1
        ext x; simp [e0, e1, or_comm]
    rw [himg]
    exact htrue
  · have hsdiff : (pencil p0 \ L).card = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hsub
      rw [pencil_card p0, h3] at this
      omega
    obtain ⟨lm, hlm⟩ := Finset.card_eq_one.1 hsdiff
    have hlm_mem : lm ∈ pencil p0 \ L := by rw [hlm]; simp
    have hlm_pen : inc p0 lm := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hlm_mem).1).2
    have hLeq : L = (pencil p0).erase lm := by
      ext l
      simp only [Finset.mem_erase]
      constructor
      · intro hl
        refine ⟨fun h => (Finset.mem_sdiff.1 hlm_mem).2 (h ▸ hl), hsub hl⟩
      · rintro ⟨hne, hpen⟩
        by_contra hnl
        have : l ∈ pencil p0 \ L := Finset.mem_sdiff.2 ⟨hpen, hnl⟩
        rw [hlm, Finset.mem_singleton] at this
        exact hne this
    let c : Fin 13 := 3 - p0
    have hpc : p0 + c = 3 := by dsimp [c]; exact add_sub_cancel p0 3
    have hincm : inc 3 (lm + c) := by
      rw [← hpc]
      exact (trans_inc c p0 lm).2 hlm_pen
    obtain ⟨idx, hfix3, hmap7⟩ := col3_hits (lm + c) hincm
    obtain ⟨hφ3L, hφ3R, hψ3L, hψ3R, hinc3'⟩ := col3_valid idx
    let φ : Fin 13 → Fin 13 := fun p => phi3 idx (p + c)
    let ψ : Fin 13 → Fin 13 := fun l => psi3 idx (l + c)
    let φ' : Fin 13 → Fin 13 := fun p => invFn (phi3 idx) p + (-c)
    let ψ' : Fin 13 → Fin 13 := fun l => invFn (psi3 idx) l + (-c)
    have hφL : ∀ x, φ' (φ x) = x := fun x => by dsimp [φ, φ']; rw [hφ3L]; exact add_neg_cancel_right x c
    have hφR : ∀ y, φ (φ' y) = y := fun y => by
      dsimp [φ, φ']; rw [neg_add_cancel_right, hφ3R]
    have hψL : ∀ x, ψ' (ψ x) = x := fun x => by dsimp [ψ, ψ']; rw [hψ3L]; exact add_neg_cancel_right x c
    have hψR : ∀ y, ψ (ψ' y) = y := fun y => by
      dsimp [ψ, ψ']; rw [neg_add_cancel_right, hψ3R]
    have hinc : ∀ p l, inc (φ p) (ψ l) ↔ inc p l := fun p l =>
      (hinc3' (p + c) (l + c)).trans (trans_inc c p l)
    have hφp0 : φ p0 = 3 := by
      dsimp [φ]
      rw [hpc, hfix3]
    have hψlm : ψ lm = 7 := hmap7
    let C' := permCircuit (colSigma φ ψ) C
    obtain ⟨hgood', hdeg'⟩ := colSigma_preserves φ ψ φ' ψ' hφL hφR hψL hψR hinc C hgood hdeg
    refine ⟨C', permCircuit_mono _ C hm, by rw [permCircuit_size], hgood', hdeg', 107904, by simp, ?_⟩
    have heq : (fun i : Fin 26 => (107904 : ℕ).testBit i.val) =
        (fun i => Fin.addCases (fun p : Fin 13 => decide (p ∈ perpL {0, 2, 3}))
          (fun l : Fin 13 => decide (l ∈ ({0, 2, 3} : Finset (Fin 13)))) i) := funext bits_107904
    rw [heq]
    change evalPL C' (perpL {0, 2, 3}) {0, 2, 3} = true
    rw [colSigma_evalPL φ ψ φ' ψ' hφL hφR hψL hψR C (perpL {0, 2, 3}) {0, 2, 3},
        perpL_image φ ψ φ' ψ' hφL hφR hψL hψR hinc {0, 2, 3}]
    have himg : ({0, 2, 3} : Finset (Fin 13)).image ψ' = L := by
      rw [← pencil3_erase7, hLeq]
      ext l
      simp only [Finset.mem_image, Finset.mem_erase, pencil, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨l0, ⟨hne7, hi3⟩, rfl⟩
        refine ⟨fun h => hne7 (by rw [← hψlm, ← h, hψR l0]), ?_⟩
        rw [← hinc p0 (ψ' l0), hφp0, hψR l0]
        exact hi3
      · rintro ⟨hnelm, hip0⟩
        refine ⟨ψ l, ⟨fun h => hnelm (by rw [← hψL l, h, ← hψlm, hψL lm]), ?_⟩, hψL l⟩
        rw [← hφp0]
        exact (hinc p0 l).2 hip0
    rw [himg]
    exact htrue

theorem main (C : Circuit) (hm : Monotone2 C) (hgood : isGood C) (hdeg : degOK C)
    (P L : Finset (Fin 13)) (hfree : ∀ p ∈ P, ∀ l ∈ L, ¬ inc p l)
    (htrue : evalPL C P L = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ isGood C' ∧ degOK C' ∧ hitsTarget C' := by
  let L' := perpP P
  let P' := perpL L'
  have hLsub : L ⊆ L' := fun l hl => Finset.mem_filter.2 ⟨Finset.mem_univ l, fun p hp => hfree p hp l hl⟩
  have hPsub : P ⊆ P' := fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ p, fun l hl =>
    (Finset.mem_filter.1 hl).2 p hp⟩
  have hL'eq : L' = perpP P' := by
    ext l
    simp only [perpP, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hl p hp
      exact (Finset.mem_filter.1 hp).2 l hl
    · intro hall
      exact Finset.mem_filter.2 ⟨Finset.mem_univ l, fun p hp => hall p (hPsub hp)⟩
  have htrue' : evalPL C P' L' = true := by
    apply circuitFun_mono C hm _ _ _ htrue
    intro i
    refine Fin.addCases (m := 13) (n := 13) (fun p hi => ?_) (fun l hi => ?_) (i : Fin (13 + 13))
    · simp only [Fin.addCases_left, decide_eq_true_eq] at hi ⊢
      exact hPsub hi
    · simp only [Fin.addCases_right, decide_eq_true_eq] at hi ⊢
      exact hLsub hi
  have hnotgen : ¬ isGeneric P' L' := by
    intro hgen
    have hfalse := hgood.2 P' L' hgen
    rw [htrue'] at hfalse
    exact Bool.noConfusion hfalse
  have h1 : ∀ l : Fin 13, l ∈ L' ↔ ∀ p ∈ P', ¬ inc p l := by
    intro l
    rw [hL'eq]
    simp [perpP]
  have h2 : ∀ p ∉ P', ∃ l ∈ L', inc p l := by
    intro p hp
    have hne : ¬ ∀ l ∈ L', ¬ inc p l := fun hall => hp (Finset.mem_filter.2 ⟨Finset.mem_univ p, hall⟩)
    push Not at hne
    exact hne
  have hor : (∃ l0 : Fin 13, ∀ p ∈ P', inc p l0) ∨ (∃ p0 : Fin 13, ∀ l ∈ L', inc p0 l) := by
    by_contra hc
    exact hnotgen ⟨h1, h2, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
  rcases hor with ⟨l0, hl0⟩ | ⟨p0, hp0⟩
  · -- Case A: dualize via dualSigma
    let Cd := permCircuit dualSigma C
    obtain ⟨hgood_d, hdeg_d⟩ := dualSigma_preserves C hgood hdeg
    let Ld := P'.image (-·)
    let Pd := L'.image (-·)
    have hPd_eq : Pd = perpL Ld := by
      ext x
      simp only [Pd, Ld, Finset.mem_image, perpL, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, rfl⟩ y ⟨p, hp, rfl⟩ hi
        exact (h1 l).1 hl p hp ((inc_neg_iff p l).1 hi)
      · intro hall
        refine ⟨-x, (h1 (-x)).2 (fun p hp hi => ?_), neg_neg x⟩
        exact hall (-p) ⟨p, hp, rfl⟩ ((inc_neg_iff p (-x)).2 hi |> fun h => by rwa [neg_neg] at h)
    have hLd_eq : Ld = perpP (perpL Ld) := by
      rw [← hPd_eq]
      ext x
      simp only [Ld, Pd, Finset.mem_image, perpP, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, hp, rfl⟩ y ⟨l, hl, rfl⟩ hi
        exact (h1 l).1 hl p hp ((inc_neg_iff p l).1 hi)
      · intro hall
        refine ⟨-x, ?_, neg_neg x⟩
        by_contra hnp
        obtain ⟨l, hl, hi⟩ := h2 (-x) hnp
        exact hall (-l) ⟨l, hl, rfl⟩ ((inc_neg_iff (-x) l).2 hi |> fun h => by rwa [neg_neg] at h)
    have hLd_pen : ∀ l ∈ Ld, inc (-l0) l := by
      intro l hl
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hl
      exact (inc_neg_iff p l0).2 (hl0 p hp)
    have htrue_d : evalPL Cd (perpL Ld) Ld = true := by
      rw [← hPd_eq, dualSigma_evalPL]
      have e1 : Ld.image (-·) = P' := by
        ext x; simp only [Ld, Finset.mem_image]
        constructor
        · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩; simpa using hp
        · intro hx; exact ⟨-x, ⟨x, hx, rfl⟩, neg_neg x⟩
      have e2 : Pd.image (-·) = L' := by
        ext x; simp only [Pd, Finset.mem_image]
        constructor
        · rintro ⟨y, ⟨l, hl, rfl⟩, rfl⟩; simpa using hl
        · intro hx; exact ⟨-x, ⟨x, hx, rfl⟩, neg_neg x⟩
      rw [e1, e2]
      exact htrue'
    obtain ⟨C', hm', hsz', hgood', hdeg', hhit'⟩ :=
      from_pencil Cd (permCircuit_mono _ C hm) hgood_d hdeg_d Ld (-l0) hLd_pen hLd_eq htrue_d
    exact ⟨C', hm', hsz'.trans (by rw [permCircuit_size]), hgood', hdeg', hhit'⟩
  · exact from_pencil C hm hgood hdeg L' p0 hp0 hL'eq htrue'

end PEqualNP.Outside.L_meta_4580

theorem PEqualNP.Outside.L_meta_4580 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → x6 x9 → x7 x9 → (∃ (x13 : x2) (x14 : x2), (∀ x15 ∈ x13, ∀ x17 ∈ x14, ¬x3 x15 x17) ∧ x4 x9 x13 x14 = Bool.true) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size ≤ x9.size ∧ x6 x14 ∧ x7 x14 ∧ x8 x14 := by
  dsimp only
  intro C hm hgood hdeg ⟨P, L, hfree, htrue⟩
  exact PEqualNP.Outside.L_meta_4580.main C hm hgood hdeg P L hfree htrue
