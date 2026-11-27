import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2539

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih]
    simp [step]
    omega

theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

theorem getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def normG (g : Gate) : Gate :=
  { op := g.op, inputs := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs }

theorem normG_eval (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) (f : ℕ → Bool) :
    (normG g).op.eval ((normG g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
  rcases hop with rfl | rfl | rfl
  · simp [normG, GateOp.eval]
  · simp [normG, GateOp.eval]
  · cases ins <;> simp [normG, GateOp.eval]

theorem normG_ok (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) :
    ((normG g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (normG g).inputs.length ≤ 2) ∧
    ((normG g).op = GateOp.not → (normG g).inputs.length ≤ 1) := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, by simpa [normG, GateOp.eval] using h.2⟩, by simp [normG]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), by simpa [normG, GateOp.eval] using h.2⟩, by simp [normG]⟩
  · refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normG, GateOp.eval]
    · simp [normG, GateOp.eval]

theorem wiresFrom_normG (gs : List Gate)
    (hok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ w : List Bool, wiresFrom (gs.map normG) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have hg := hok g List.mem_cons_self
    have s1 : wiresFrom ((g :: gs).map normG) w = wiresFrom (gs.map normG) (step w (normG g)) := rfl
    have s2 : wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl
    have hs : step w (normG g) = step w g := by
      dsimp [step]
      rw [normG_eval g hg]
    rw [s1, s2, hs, ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]

def shiftWire (x7 : Bool) (w : ℕ) : ℕ :=
  if w = 9 then (if x7 then 0 else 9)
  else if 10 ≤ w then w - 1
  else w

def transGate (x7 : Bool) (g : Gate) : Gate :=
  if 0 ∈ g.inputs ∧ 9 ∈ g.inputs then
    match g.op with
    | GateOp.and => ⟨GateOp.or, []⟩
    | _ => ⟨GateOp.and, []⟩
  else
    ⟨g.op, g.inputs.map (shiftWire x7)⟩

theorem transGate_ok (x7 : Bool) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (transGate x7 g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    (transGate x7 g).inputs.length ≤ 2 := by
  unfold transGate
  split_ifs
  · cases g.op <;> simp
  · exact ⟨h.1, by simpa using h.2⟩

theorem transGate_mem0 (x7 : Bool) (g : Gate) :
    (transGate x7 g).inputs.contains 0 = true →
    ([0, 9].any fun w => g.inputs.contains w) = true := by
  unfold transGate
  split_ifs with h09
  · cases g.op <;> simp
  · intro hm
    rw [List.contains_iff_mem, List.mem_map] at hm
    obtain ⟨w, hw, hsw⟩ := hm
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, List.contains_iff_mem]
    unfold shiftWire at hsw
    by_cases hw9 : w = 9
    · subst hw9; exact Or.inr hw
    · rw [if_neg hw9] at hsw
      by_cases hw10 : 10 ≤ w
      · rw [if_pos hw10] at hsw; omega
      · rw [if_neg hw10] at hsw; subst hsw; exact Or.inl hw

theorem filter_map_length_le {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ a, q (f a) = true → p a = true) (l : List α) :
    ((l.map f).filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases hq : q (f a) = true
    · have hp := h a hq
      simp only [hq, hp, ↓reduceIte, List.length_cons]
      omega
    · have hqf : q (f a) = false := Bool.eq_false_iff.mpr hq
      simp only [hqf, Bool.false_eq_true, ↓reduceIte]
      by_cases hp : p a = true
      · simp only [hp, ↓reduceIte, List.length_cons]; omega
      · have hpf : p a = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem two_mem_eq (l : List ℕ) (hlen : l.length ≤ 2) (h0 : 0 ∈ l) (h9 : 9 ∈ l) :
    l = [0, 9] ∨ l = [9, 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · cases h0
  · simp only [List.mem_singleton] at h0 h9; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9
    rcases h0 with ha0 | hb0 <;> rcases h9 with ha9 | hb9
    · omega
    · subst ha0; subst hb9; exact Or.inl rfl
    · subst hb0; subst ha9; exact Or.inr rfl
    · omega
  · simp at hlen

def Rel (x7 b0 : Bool) (k : ℕ) (w1 w2 : List Bool) : Prop :=
  w1.length = 10 + k ∧ w2.length = 9 + k ∧
  w1.getD 0 false = b0 ∧ w1.getD 9 false = !b0 ∧
  (∀ i, 1 ≤ i → i < 9 → w2.getD i false = w1.getD i false) ∧
  (∀ j < k, w2.getD (9 + j) false = w1.getD (10 + j) false) ∧
  (x7 = false → w2.getD 0 false = b0) ∧
  (x7 = true → w2.getD 0 false = !b0)

theorem rel_init (x7 : Bool) (x8 : Fin 9 → Bool) :
    Rel x7 (x8 0) 0 (List.ofFn x8 ++ [!x8 0])
      (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i) := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by simp)]
    simp
  · have hsn := getD_snoc_eq (List.ofFn x8) (!x8 0)
    rwa [List.length_ofFn] at hsn
  · intro i hi1 hi9
    rw [List.getD_append _ _ _ _ (by simp [hi9])]
    have hne : (⟨i, hi9⟩ : Fin 9) ≠ 0 := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have h1 : (List.ofFn fun j : Fin 9 => if j = 0 then x7 != x8 0 else x8 j).getD i false =
        (if (⟨i, hi9⟩ : Fin 9) = 0 then x7 != x8 0 else x8 ⟨i, hi9⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
    have h2 : (List.ofFn x8).getD i false = x8 ⟨i, hi9⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
    rw [h1, h2]
    simp [hne]
  · intro j hj; cases hj
  · intro hx7; subst hx7; simp
  · intro hx7; subst hx7; simp

theorem rel_step (x7 b0 : Bool) (k : ℕ) (w1 w2 : List Bool) (g : Gate)
    (hrel : Rel x7 b0 k w1 w2)
    (hg_ok : (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hcond : (x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) :
    Rel x7 b0 (k + 1) (step w1 g) (step w2 (transGate x7 g)) := by
  obtain ⟨hl1, hl2, hw0, hw9, hmid, hprev, hf0, ht0⟩ := hrel
  have heval_eq : (transGate x7 g).op.eval
      ((transGate x7 g).inputs.map fun i => w2.getD i false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
    unfold transGate
    split_ifs with h09
    · have hnot_not : g.op ≠ GateOp.not := by
        intro hn
        have hl := hg_ok.2 hn
        rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _⟩⟩
        · rw [hinp] at h09; exact List.not_mem_nil h09.1
        · rw [hinp] at h09; simp only [List.mem_singleton] at h09; omega
        · rw [hinp] at hl; simp at hl
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg_ok.1.1
      have hl_eq := two_mem_eq g.inputs hg_ok.1.2 h09.1 h09.2
      rcases hop with hop | hop | hop
      · rw [hop]
        rcases hl_eq with hin | hin <;> rw [hin] <;>
          simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
      · rw [hop]
        rcases hl_eq with hin | hin <;> rw [hin] <;>
          simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
      · exact (hnot_not hop).elim
    · simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro w hw
      simp only [Function.comp_apply, shiftWire]
      by_cases hw_eq9 : w = 9
      · subst hw_eq9
        rw [if_pos rfl]
        cases hx7 : x7
        · exfalso
          exact h09 ⟨hcond.2 hx7 hw, hw⟩
        · simp only [↓reduceIte, ht0 hx7, hw9]
      · rw [if_neg hw_eq9]
        by_cases hw10 : 10 ≤ w
        · rw [if_pos hw10]
          by_cases hwk : w < 10 + k
          · have hjk : w - 10 < k := by omega
            have h1 : w - 1 = 9 + (w - 10) := by omega
            have h2 : w = 10 + (w - 10) := by omega
            rw [h1, hprev (w - 10) hjk, ← h2]
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · rw [if_neg hw10]
          by_cases hw_eq0 : w = 0
          · subst hw_eq0
            cases hx7 : x7
            · rw [hf0 hx7, hw0]
            · exact (hcond.1 hx7 hw).elim
          · exact hmid w (by omega) (by omega)
  let v := g.op.eval (g.inputs.map fun i => w1.getD i false)
  have hs1 : step w1 g = w1 ++ [v] := rfl
  have hs2 : step w2 (transGate x7 g) = w2 ++ [v] := by dsimp [step]; rw [heval_eq]
  rw [hs1, hs2]
  refine ⟨by simp [hl1]; omega, by simp [hl2]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw0
  · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw9
  · intro i hi1 hi9
    rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
    exact hmid i hi1 hi9
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
      exact hprev j hlt
    · have e2 : 9 + j = w2.length := by omega
      have e1 : 10 + j = w1.length := by omega
      rw [e2, getD_snoc_eq, e1, getD_snoc_eq]
  · intro hx7
    rw [getD_snoc_ne _ _ _ (by omega)]; exact hf0 hx7
  · intro hx7
    rw [getD_snoc_ne _ _ _ (by omega)]; exact ht0 hx7

theorem rel_wiresFrom (x7 b0 : Bool) (gs : List Gate) :
    ∀ (k : ℕ) (w1 w2 : List Bool),
      Rel x7 b0 k w1 w2 →
      (∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      (∀ g ∈ gs, (x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) →
      Rel x7 b0 (k + gs.length) (wiresFrom gs w1) (wiresFrom (gs.map (transGate x7)) w2) := by
  induction gs with
  | nil =>
    intro k w1 w2 hrel _ _
    simpa [wiresFrom] using hrel
  | cons g gs ih =>
    intro k w1 w2 hrel hok hcond
    have h1 := rel_step x7 b0 k w1 w2 g hrel (hok g List.mem_cons_self) (hcond g List.mem_cons_self)
    have h2 := ih (k + 1) (step w1 g) (step w2 (transGate x7 g)) h1
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hcond g' (List.mem_cons_of_mem _ hg'))
    simpa [wiresFrom, Nat.add_assoc, add_comm 1] using h2

theorem single_filter_disj {α : Type} (p : α → Bool) (l : List α)
    (hlen : (l.filter p).length ≤ 1) (a b : α) (ha : a ∈ l) (hb : b ∈ l)
    (hpa : p a = true) (hpb : p b = true) (q : α → Prop) (hqa : q a) (hqb : ¬ q b) : False := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.filter_cons] at hlen
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte, List.length_cons] at hlen
      have h0 : xs.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hnone : ∀ y ∈ xs, p y ≠ true := by
        intro y hy hpy
        have hm : y ∈ xs.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
        rw [h0] at hm; cases hm
      rcases List.mem_cons.mp ha with rfl | haxs
      · rcases List.mem_cons.mp hb with rfl | hbxs
        · exact hqb hqa
        · exact hnone b hbxs hpb
      · exact hnone a haxs hpa
    · have hpxf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [hpxf, Bool.false_eq_true, ↓reduceIte] at hlen
      rcases List.mem_cons.mp ha with rfl | haxs
      · rw [hpa] at hpxf; cases hpxf
      · rcases List.mem_cons.mp hb with rfl | hbxs
        · rw [hpb] at hpxf; cases hpxf
        · exact ih hlen haxs hbxs

end PEqualNP.Outside.L_meta_2539

open PEqualNP.Outside.L_meta_2539 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2539 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9 := by
  intro x1 x2_in hfan hw9 hflt
  dsimp only [x2_in] at hflt
  obtain ⟨gs, out⟩ := x1
  cases gs with
  | nil =>
    exfalso
    have h0 := hw9 (fun _ => false)
    have hl : (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = false :=
      List.getD_eq_default _ _ (by simp)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at h0
    rw [hl] at h0
    cases h0
  | cons g0 tail =>
    have hsz_pos : 0 < ({ gates := g0 :: tail, output := out } : Circuit).size := by
      change 0 < (g0 :: tail).length; simp
    have hw_g0 : ∀ x : Fin 9 → Bool,
        step (List.ofFn x) g0 = List.ofFn x ++ [!x 0] := by
      intro x
      have h9 := hw9 x
      change (wiresFrom tail (step (List.ofFn x) g0)).getD 9 false = !x 0 at h9
      rw [getD_wiresFrom_lt tail _ 9 (by simp [step])] at h9
      have hl : (List.ofFn x).length = 9 := List.length_ofFn
      have hsn : (step (List.ofFn x) g0).getD 9 false =
          g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
        have h0 := getD_snoc_eq (List.ofFn x)
          (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false))
        rwa [List.length_ofFn] at h0
      rw [hsn] at h9
      dsimp [step]
      rw [h9]
    let x2 := tail.map normG
    have htail_fan : ∀ g ∈ tail,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan g (List.mem_cons_of_mem _ hg)
    have hx2_ok : ∀ g ∈ x2,
        (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (g.op = GateOp.not → g.inputs.length ≤ 1) := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact normG_ok g' (htail_fan g' hg')
    have hw_eq : ∀ x : Fin 9 → Bool,
        ({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x) =
          wiresFrom x2 (List.ofFn x ++ [!x 0]) := by
      intro x
      change wiresFrom tail (step (List.ofFn x) g0) = _
      rw [hw_g0 x, wiresFrom_normG tail htail_fan]
    by_cases hout9 : out < 9
    · refine ⟨⟨[], out⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
      intro x8
      change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
        (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD out false
      rw [hw_eq x8, getD_wiresFrom_lt x2 _ out (by simp; omega),
        List.getD_append _ _ _ _ (by simp [hout9])]
      congr 1
      ext i
      by_cases hi0 : i = 0
      · subst hi0; simp
      · simp [hi0]
    · by_cases hout_eq9 : out = 9
      · subst hout_eq9
        refine ⟨⟨[], 0⟩, true, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
        intro x8
        rw [show circuitFun 9 { gates := g0 :: tail, output := 9 } x8 = !x8 0 from hw9 x8]
        change (!x8 0) = (List.ofFn fun x9 : Fin 9 => if x9 = 0 then true != x8 0 else x8 x9).getD 0 false
        simp
      · by_cases hout_ge : 10 + x2.length ≤ out
        · refine ⟨⟨[], 9⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
          intro x8
          change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
            (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD 9 false
          rw [hw_eq x8, List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
            List.getD_eq_default _ _ (by simp)]
        · let x7 : Bool := decide (∃ g ∈ x2, 9 ∈ g.inputs ∧ 0 ∉ g.inputs)
          have hflt' : (x2.filter (fun g => [0, 9].any fun w => g.inputs.contains w)).length ≤ 1 := hflt
          have hcond : ∀ g ∈ x2, (x7 = true → 0 ∉ g.inputs) ∧
              (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs) := by
            intro g hg
            refine ⟨?_, ?_⟩
            · intro hx7 h0g
              obtain ⟨g9, hg9, h9in, h0not⟩ := of_decide_eq_true hx7
              have p_g : ([0, 9].any fun w => g.inputs.contains w) = true := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                  List.contains_iff_mem]
                exact Or.inl h0g
              have p_g9 : ([0, 9].any fun w => g9.inputs.contains w) = true := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                  List.contains_iff_mem]
                exact Or.inr h9in
              exact single_filter_disj _ x2 hflt' g g9 hg hg9 p_g p_g9
                (fun z => 0 ∈ z.inputs) h0g h0not
            · intro hx7 h9g
              by_contra h0not
              have ht : x7 = true := decide_eq_true ⟨g, hg, h9g, h0not⟩
              rw [hx7] at ht; cases ht
          let x6 : Circuit := ⟨x2.map (transGate x7), out - 1⟩
          have hx6_fan : FanInTwo x6 := by
            intro g hg
            obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
            exact transGate_ok x7 g' (hx2_ok g' hg').1
          have hx6_sz : x6.size < ({ gates := g0 :: tail, output := out } : Circuit).size := by
            change (x2.map (transGate x7)).length < (g0 :: tail).length
            simp [x2]
          have hx6_flt : (x6.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 :=
            (filter_map_length_le (transGate x7)
              (fun g => [0, 9].any fun w => g.inputs.contains w)
              (fun g => g.inputs.contains 0)
              (transGate_mem0 x7) x2).trans hflt'
          refine ⟨x6, x7, hx6_fan, hx6_sz, hx6_flt, ?_⟩
          intro x8
          have hrel := rel_wiresFrom x7 (x8 0) x2 0
            (List.ofFn x8 ++ [!x8 0])
            (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)
            (rel_init x7 x8) hx2_ok hcond
          have hj_lt : out - 10 < 0 + x2.length := by omega
          have hprev := hrel.2.2.2.2.2.1 (out - 10) hj_lt
          have e1 : 10 + (out - 10) = out := by omega
          have e2 : 9 + (out - 10) = out - 1 := by omega
          rw [e1, e2] at hprev
          change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
            (wiresFrom (x2.map (transGate x7))
              (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)).getD (out - 1) false
          rw [hw_eq x8, hprev]
