import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9020
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def pw (n i : ℕ) : ℕ := if i < n then i else 2 * n + 2 * (i - n)

def nw (n i : ℕ) : ℕ := if i < n then n + i else 2 * n + 2 * (i - n) + 1

def posG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.and, g.inputs.map (pw n)⟩ else ⟨GateOp.or, []⟩
  | GateOp.or => ⟨GateOp.or, (g.inputs.filter (fun i => decide (i < L))).map (pw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.and, []⟩
    | a :: _ => if a < L then ⟨GateOp.and, [nw n a]⟩ else ⟨GateOp.and, []⟩

def negG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.or, g.inputs.map (nw n)⟩ else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, (g.inputs.filter (fun i => decide (i < L))).map (nw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.or, []⟩
    | a :: _ => if a < L then ⟨GateOp.or, [pw n a]⟩ else ⟨GateOp.or, []⟩

def Rel (n : ℕ) (U U' : List Bool) : Prop :=
  ∀ i, i < U.length → U'.getD (pw n i) false = U.getD i false ∧ U'.getD (nw n i) false = !U.getD i false

theorem dm1 : ∀ l : List Bool, (l.map fun b => !b).any id = !(l.all id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_and]

theorem dm2 : ∀ l : List Bool, (l.map fun b => !b).all id = !(l.any id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_or]

theorem any_filter (p : ℕ → Bool) (f : ℕ → Bool) : ∀ ins : List ℕ, (∀ i ∈ ins, p i = false → f i = false) →
    ((ins.filter p).map f).any id = (ins.map f).any id := by
  intro ins
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have iht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.any_cons, iht]
    · have hp' : p a = false := by simpa using hp
      have hf := h a (List.mem_cons_self ..) hp'
      simp only [List.filter_cons, hp', Bool.false_eq_true, if_false, List.map_cons, List.any_cons, iht, hf, id,
        Bool.false_or]

theorem gate_dual (n L : ℕ) (U U' : List Bool) (hL : U.length = L) (hR : Rel n U U') (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (posG n L g).op.eval ((posG n L g).inputs.map fun i => U'.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) ∧
    (negG n L g).op.eval ((negG n L g).inputs.map fun i => U'.getD i false)
      = !(g.op.eval (g.inputs.map fun i => U.getD i false)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  have hinv : ∀ i, ¬ i < L → U.getD i false = false := fun i hi =>
    List.getD_eq_default _ _ (by omega)
  have hmp : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (pw n)).map (fun i => U'.getD i false) = l.map fun i => U.getD i false := by
    intro l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).1
  have hmn : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (nw n)).map (fun i => U'.getD i false)
      = (l.map fun i => U.getD i false).map fun b => !b := by
    intro l hl
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).2
  rcases hop with rfl | rfl | rfl
  · by_cases hall : ins.all (fun i => decide (i < L)) = true
    · have hl : ∀ i ∈ ins, i < L := fun i hi => by simpa using List.all_eq_true.1 hall i hi
      simp only [posG, negG, hall, if_true]
      constructor
      · show ((ins.map (pw n)).map fun i => U'.getD i false).all id = (ins.map fun i => U.getD i false).all id
        rw [hmp ins hl]
      · show ((ins.map (nw n)).map fun i => U'.getD i false).any id = !((ins.map fun i => U.getD i false).all id)
        rw [hmn ins hl, dm1]
    · simp only [posG, negG, hall, if_false]
      have hf : (ins.map fun i => U.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hc
        apply hall
        rw [List.all_eq_true] at hc ⊢
        intro i hi
        by_contra hlt
        have h1 := hc (U.getD i false) (List.mem_map.2 ⟨i, hi, rfl⟩)
        rw [hinv i (by simpa using hlt)] at h1
        exact absurd h1 (by simp)
      constructor
      · show ([] : List Bool).any id = (ins.map fun i => U.getD i false).all id
        rw [hf]; rfl
      · show ([] : List Bool).all id = !((ins.map fun i => U.getD i false).all id)
        rw [hf]; rfl
  · have hl : ∀ i ∈ ins.filter (fun i => decide (i < L)), i < L := fun i hi => by
      simpa using (List.mem_filter.1 hi).2
    have hfa := any_filter (fun i => decide (i < L)) (fun i => U.getD i false) ins
      (fun i _ hp => hinv i (by simpa using hp))
    simp only [posG, negG]
    constructor
    · show (((ins.filter fun i => decide (i < L)).map (pw n)).map fun i => U'.getD i false).any id
        = (ins.map fun i => U.getD i false).any id
      rw [hmp _ hl, hfa]
    · show (((ins.filter fun i => decide (i < L)).map (nw n)).map fun i => U'.getD i false).all id
        = !((ins.map fun i => U.getD i false).any id)
      rw [hmn _ hl, dm2, hfa]
  · cases ins with
    | nil =>
      simp only [posG, negG]
      exact ⟨rfl, rfl⟩
    | cons a t =>
      by_cases ha : a < L
      · simp only [posG, negG, ha, if_true]
        have h1 := hR a (by rw [hL]; exact ha)
        constructor
        · show (U'.getD (nw n a) false && true) = !(U.getD a false)
          rw [h1.2, Bool.and_true]
        · show (U'.getD (pw n a) false || false) = !!(U.getD a false)
          rw [h1.1, Bool.or_false, Bool.not_not]
      · simp only [posG, negG, ha, if_false]
        have h0 := hinv a ha
        constructor
        · show true = !(U.getD a false)
          rw [h0]; rfl
        · show false = !!(U.getD a false)
          rw [h0]; rfl

def dual (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => posG n L g :: negG n L g :: dual n (L + 1) t

theorem dual_len (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (dual n L gs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp only [dual, List.length_cons, ih]; omega

theorem pn_ok (n L : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ((posG n L g).op = GateOp.and ∨ (posG n L g).op = GateOp.or) ∧ (posG n L g).inputs.length ≤ 2 ∧
    ((negG n L g).op = GateOp.and ∨ (negG n L g).op = GateOp.or) ∧ (negG n L g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  simp only at hlen
  have hfl := List.length_filter_le (fun i => decide (i < L)) ins
  cases op with
  | and => simp only [posG, negG]; split_ifs <;> simp <;> omega
  | or => simp only [posG, negG]; simp; omega
  | not =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | mod m =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | maj =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp

theorem dual_ok (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ dual n L gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro L _ g hg; simp [dual] at hg
  | cons g0 t ih =>
    intro L h g hg
    simp only [dual, List.mem_cons] at hg
    have hp := pn_ok n L g0 (h g0 (List.mem_cons_self ..))
    rcases hg with rfl | rfl | hg
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ih (L + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) g hg

theorem dual_sim (n : ℕ) : ∀ (gs : List Gate) (L : ℕ) (U U' : List Bool), U.length = L → n ≤ L →
    U'.length = 2 * n + 2 * (L - n) → Rel n U U' →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    Rel n (wf gs U) (wf (dual n L gs) U') := by
  intro gs
  induction gs with
  | nil => intro L U U' _ _ _ hR _; exact hR
  | cons g t ih =>
    intro L U U' hL hn hL' hR hop
    have hpl : ∀ i, i < L → pw n i < U'.length ∧ nw n i < U'.length := by
      intro i hi
      unfold pw nw
      constructor <;> split_ifs <;> omega
    have hg := gate_dual n L U U' hL hR g (hop g (List.mem_cons_self ..))
    generalize hv : g.op.eval (g.inputs.map fun i => U.getD i false) = v at hg
    have hR1 : Rel n U (U' ++ [v]) := by
      intro i hi
      have := hpl i (by omega)
      rw [getD_snoc_lt U' _ _ this.1, getD_snoc_lt U' _ _ this.2]
      exact hR i hi
    have hg2 := gate_dual n L U _ hL hR1 g (hop g (List.mem_cons_self ..))
    rw [hv] at hg2
    show Rel n (wf (g :: t) U) (wf (posG n L g :: negG n L g :: dual n (L + 1) t) U')
    rw [wf_cons, wf_cons, wf_cons, hv, hg.1, hg2.2]
    refine ih (L + 1) _ _ (by simp [hL]) (by omega) (by simp [hL']; omega) ?_
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    have hi' : i < L + 1 := by simpa [hL] using hi
    by_cases hil : i < L
    · have h12 := hpl i hil
      constructor
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.1,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).1
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.2,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).2
    · have hie : i = L := by omega
      subst hie
      have e1 : pw n i = U'.length := by unfold pw; rw [if_neg (by omega)]; omega
      have e2 : nw n i = (U' ++ [v]).length := by
        unfold nw; rw [if_neg (by omega), List.length_append]; simp; omega
      constructor
      · rw [e1, getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; simp), getD_snoc_eq, ← hL, getD_snoc_eq]
      · rw [e2, getD_snoc_eq, ← hL, getD_snoc_eq]

end PEqualNP.Outside.L_meta_9020

open PEqualNP.Outside.L_meta_9020 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9020 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  intro n s f ⟨C, hF, hs, hf⟩
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := fun g hg => by
    simpa using (hF g hg).1
  refine ⟨⟨dual n n C.gates, if C.output < n + C.gates.length then pw n C.output else 2 * n + 2 * C.gates.length⟩,
    fun g hg => ?_, ?_, fun x => ?_⟩
  · have := dual_ok n C.gates n (fun g' hg' => (hF g' hg').2) g hg
    exact ⟨by rcases this.1 with h | h <;> simp [h], this.2⟩
  · show (dual n n C.gates).length ≤ 2 * s
    rw [dual_len]
    have : C.gates.length ≤ s := hs
    omega
  · have hR0 : Rel n (List.ofFn x) (List.ofFn x ++ List.ofFn fun i => !x i) := by
      intro i hi
      have hi' : i < n := by simpa using hi
      unfold pw nw
      rw [if_pos hi', if_pos hi', List.getD_append _ _ _ _ (by simpa using hi'),
        List.getD_append_right _ _ _ _ (by simp)]
      have e1 := getD_ofFn x ⟨i, hi'⟩
      have e2 := getD_ofFn (fun i => !x i) ⟨i, hi'⟩
      simp only at e1 e2
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [e1, e2]
      simp
    have hR := dual_sim n C.gates n (List.ofFn x) _ (by simp) le_rfl (by simp; omega) hR0 hop
    rw [← hf x]
    show (wf (dual n n C.gates) (List.ofFn x ++ List.ofFn fun i => !x i)).getD _ false
      = (wf C.gates (List.ofFn x)).getD C.output false
    by_cases ho : C.output < n + C.gates.length
    · rw [if_pos ho]
      exact (hR C.output (by rw [wf_len]; simpa using ho)).1
    · rw [if_neg ho, List.getD_eq_default _ _ (by rw [wf_len, dual_len]; simp; omega),
        List.getD_eq_default _ _ (by rw [wf_len]; simp; omega)]
