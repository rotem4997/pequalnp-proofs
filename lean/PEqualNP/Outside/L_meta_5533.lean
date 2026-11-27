import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5533

-- A circuit witnessing the upper bound.

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩

theorem upper :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 4 => (366 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

-- The four-corner obstruction for read-once monotone formulas.

open PEqualNP.MetaComplexity

def formulaVars {n : ℕ} : DMFormula n → Set (Fin n)
  | .lit i _ => {i}
  | .and f g => formulaVars f ∪ formulaVars g
  | .or f g => formulaVars f ∪ formulaVars g

def positiveReadOnce {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False
  | .or f g => positiveReadOnce f ∧ positiveReadOnce g ∧
      ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False

def singletonInput {n : ℕ} (a : Fin n) : Fin n → Bool :=
  fun i => decide (i = a)

def pairInput {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i => decide (i = a ∨ i = b)

def cornerIndices {n : ℕ} (a b c d : Fin n) : Set (Fin n) := {a, b, c, d}

theorem formula_agree {n : ℕ} (f : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ i ∈ formulaVars f, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | lit i b =>
      have hi := h i (by simp [formulaVars])
      simp [DMFormula.eval, hi]
  | and f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]
  | or f g ihf ihg =>
      simp only [DMFormula.eval]
      rw [ihf (fun i hi => h i (Or.inl hi)), ihg (fun i hi => h i (Or.inr hi))]

theorem formula_zero {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f) :
    f.eval (fun _ => false) = false := by
  induction f with
  | lit i b =>
      change b = true at h
      simp [DMFormula.eval, h]
  | and f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]
  | or f g ihf ihg => simp [DMFormula.eval, ihf h.1, ihg h.2.1]

theorem formula_mono {n : ℕ} (f : DMFormula n) (h : positiveReadOnce f)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    f.eval x = true → f.eval y = true := by
  induction f with
  | lit i b =>
      change b = true at h
      simpa [DMFormula.eval, h] using hxy i
  | and f g ihf ihg =>
      simp only [DMFormula.eval, Bool.and_eq_true]
      rintro ⟨hxF, hxG⟩
      exact ⟨ihf h.1 hxF, ihg h.2.1 hxG⟩
  | or f g ihf ihg =>
      simp only [DMFormula.eval, Bool.or_eq_true]
      rintro (hxF | hxG)
      · exact Or.inl (ihf h.1 hxF)
      · exact Or.inr (ihg h.2.1 hxG)

theorem input_pair_comm {n : ℕ} (a b : Fin n) : pairInput a b = pairInput b a := by
  funext i
  simp [pairInput, or_comm]

theorem formula_pair_swap {n : ℕ} (f : DMFormula n) (a : Fin n) {b c : Fin n}
    (hb : b ∉ formulaVars f) (hc : c ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (pairInput a c) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  have hindC : i ≠ c := fun he => hc (he ▸ hi)
  simp [pairInput, hindB, hindC]

theorem formula_pair_singleton {n : ℕ} (f : DMFormula n) (a : Fin n) {b : Fin n}
    (hb : b ∉ formulaVars f) :
    f.eval (pairInput a b) = f.eval (singletonInput a) := by
  apply formula_agree
  intro i hi
  have hindB : i ≠ b := fun he => hb (he ▸ hi)
  simp [pairInput, singletonInput, hindB]

theorem some_vars_of_pair {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f) {a b : Fin n}
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∨ b ∈ formulaVars f := by
  classical
  by_contra hab
  have hzero : f.eval (pairInput a b) = f.eval (fun _ => false) := by
    apply formula_agree
    intro i hi
    have hiA : i ≠ a := fun he => hab (Or.inl (he ▸ hi))
    have hiB : i ≠ b := fun he => hab (Or.inr (he ▸ hi))
    simp [pairInput, hiA, hiB]
  rw [h, formula_zero f hf] at hzero
  contradiction

theorem both_vars_of_pair {n : ℕ} (f : DMFormula n) {a b : Fin n}
    (hsa : f.eval (singletonInput a) = false)
    (hsb : f.eval (singletonInput b) = false)
    (h : f.eval (pairInput a b) = true) : a ∈ formulaVars f ∧ b ∈ formulaVars f := by
  classical
  constructor
  · by_contra hA
    have he := formula_pair_singleton f b hA
    rw [← input_pair_comm a b, h, hsb] at he
    contradiction
  · by_contra hB
    have he := formula_pair_singleton f a hB
    rw [h, hsa] at he
    contradiction

theorem opposite_vars_of_and_pair {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b : Fin n}
    (hF : f.eval (pairInput a b) = true) (hG : g.eval (pairInput a b) = true) :
    a ∈ formulaVars f ↔ b ∉ formulaVars f := by
  rcases some_vars_of_pair f hf hF with hFa | hFb
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact False.elim (hfg a hFa hGa)
    · exact ⟨fun _ hFb => hfg b hFb hGb, fun _ => hFa⟩
  · rcases some_vars_of_pair g hg hG with hGa | hGb
    · exact ⟨fun hFa => False.elim (hfg a hFa hGa), fun hnFb => False.elim (hnFb hFb)⟩
    · exact False.elim (hfg b hFb hGb)

theorem formula_and_corner_side {n : ℕ} (f g : DMFormula n)
    (hf : positiveReadOnce f) (hg : positiveReadOnce g)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hacF : f.eval (pairInput a c) = true) (hacG : g.eval (pairInput a c) = true)
    (hadF : f.eval (pairInput a d) = true) (hadG : g.eval (pairInput a d) = true)
    (hbcF : f.eval (pairInput b c) = true) (hbcG : g.eval (pairInput b c) = true) :
    f.eval (pairInput b d) = true := by
  classical
  have hac := opposite_vars_of_and_pair f g hf hg hfg hacF hacG
  have had := opposite_vars_of_and_pair f g hf hg hfg hadF hadG
  have hbc := opposite_vars_of_and_pair f g hf hg hfg hbcF hbcG
  by_cases hA : a ∈ formulaVars f
  · exact (formula_pair_swap f b (had.mp hA) (hac.mp hA)).trans hbcF
  · have hC : c ∈ formulaVars f :=
      Classical.byContradiction (fun hnC => hA (hac.mpr hnC))
    have hB : b ∉ formulaVars f := fun hb => hbc.mp hb hC
    have he : f.eval (pairInput b d) = f.eval (pairInput a d) := by
      rw [input_pair_comm b d, input_pair_comm a d]
      exact formula_pair_swap f d hB hA
    exact he.trans hadF

theorem force_or_corner {n : ℕ} (f g : DMFormula n)
    (hfg : ∀ i, i ∈ formulaVars f → i ∈ formulaVars g → False) {a b c d : Fin n}
    (hsF : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hsG : ∀ i ∈ cornerIndices a b c d, g.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true ∨ g.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true ∨ g.eval (pairInput b c) = true) :
    f.eval (pairInput a d) = true ∧ f.eval (pairInput b c) = true := by
  have ha := both_vars_of_pair f (hsF a (by simp [cornerIndices]))
    (hsF c (by simp [cornerIndices])) hac
  constructor
  · rcases had with had | had
    · exact had
    · exact False.elim (hfg a ha.1
        (both_vars_of_pair g (hsG a (by simp [cornerIndices]))
          (hsG d (by simp [cornerIndices])) had).1)
  · rcases hbc with hbc | hbc
    · exact hbc
    · exact False.elim (hfg c ha.2
        (both_vars_of_pair g (hsG b (by simp [cornerIndices]))
          (hsG c (by simp [cornerIndices])) hbc).2)

theorem positive_read_once_corners {n : ℕ} (f : DMFormula n) (hf : positiveReadOnce f)
    (a b c d : Fin n)
    (hs : ∀ i ∈ cornerIndices a b c d, f.eval (singletonInput i) = false)
    (hac : f.eval (pairInput a c) = true)
    (had : f.eval (pairInput a d) = true)
    (hbc : f.eval (pairInput b c) = true) : f.eval (pairInput b d) = true := by
  induction f with
  | lit i polarity =>
      change polarity = true at hf
      have ha : i = a ∨ i = c := by
        simpa [DMFormula.eval, hf, pairInput] using hac
      have hin : i ∈ cornerIndices a b c d := by
        rcases ha with h | h <;> simp [cornerIndices, h]
      have hi := hs i hin
      simp [DMFormula.eval, hf, singletonInput] at hi
  | and f g ihF ihG =>
      simp only [DMFormula.eval, Bool.and_eq_true] at hac had hbc ⊢
      exact
        ⟨formula_and_corner_side f g hf.1 hf.2.1 hf.2.2
            hac.1 hac.2 had.1 had.2 hbc.1 hbc.2,
          formula_and_corner_side g f hf.2.1 hf.1 (fun i hg hf' => hf.2.2 i hf' hg)
            hac.2 hac.1 had.2 had.1 hbc.2 hbc.1⟩
  | or f g ihF ihG =>
      simp only [DMFormula.eval, Bool.or_eq_true] at hac had hbc ⊢
      have hsF (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          f.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : f.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      have hsG (i : Fin n) (him : i ∈ cornerIndices a b c d) :
          g.eval (singletonInput i) = false := by
        have hi := hs i him
        cases he : g.eval (singletonInput i) <;> simp [DMFormula.eval, he] at hi ⊢
      rcases hac with hacF | hacG
      · have h := force_or_corner f g hf.2.2 hsF hsG hacF had hbc
        exact Or.inl (ihF hf.1 hsF hacF h.1 h.2)
      · have h := force_or_corner g f (fun i hg hf' => hf.2.2 i hf' hg) hsG hsF
          hacG had.symm hbc.symm
        exact Or.inr (ihG hf.2.1 hsG hacG h.1 h.2)

theorem formula_singleton_false_of_pair {n : ℕ} (f : DMFormula n)
    (hf : positiveReadOnce f) (a b : Fin n) (h : f.eval (pairInput a b) = false) :
    f.eval (singletonInput a) = false := by
  cases hsingle : f.eval (singletonInput a) with
  | false => rfl
  | true =>
      have hsubset (i : Fin n) (hi : singletonInput a i = true) : pairInput a b i = true := by
        have he : i = a := of_decide_eq_true hi
        simp [pairInput, he]
      have hpair := formula_mono f hf hsubset hsingle
      exact False.elim (Bool.false_ne_true (h.symm.trans hpair))

def mask366RowWire (u : Fin 4) : Fin 14 := ⟨u.val, by omega⟩

def mask366ColumnWire (v : Fin 4) : Fin 14 := ⟨4 + v.val, by omega⟩

theorem mask366_pair_wires (u v : Fin 4) :
    (fun i : Fin 14 => (PEqualNP.Represents.oneEach u v).getD i.val false) =
      pairInput (mask366RowWire u) (mask366ColumnWire v) := by
  have h : ∀ (u v : Fin 4) (i : Fin 14),
      (PEqualNP.Represents.oneEach u v).getD i.val false =
        pairInput (mask366RowWire u) (mask366ColumnWire v) i := by decide
  exact funext (h u v)

theorem no_formula_mask366 (f : DMFormula 14) (hf : positiveReadOnce f)
    (hrep : ∀ u v : Fin 4, f.eval (pairInput (mask366RowWire u) (mask366ColumnWire v)) =
      (366 : ℕ).testBit (4 * u.val + v.val)) : False := by
  have h05 : f.eval (pairInput 0 5) = true := (hrep 0 1).trans (by decide)
  have h07 : f.eval (pairInput 0 7) = true := (hrep 0 3).trans (by decide)
  have h15 : f.eval (pairInput 1 5) = true := (hrep 1 1).trans (by decide)
  have h17 : f.eval (pairInput 1 7) = false := (hrep 1 3).trans (by decide)
  have h04 : f.eval (pairInput 0 4) = false := (hrep 0 0).trans (by decide)
  have h35 : f.eval (pairInput 3 5) = false := (hrep 3 1).trans (by decide)
  have h37 : f.eval (pairInput 3 7) = false := (hrep 3 3).trans (by decide)
  have hs (i : Fin 14) (hi : i ∈ cornerIndices 0 1 5 7) :
      f.eval (singletonInput i) = false := by
    have hi' : i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 7 := by
      simpa [cornerIndices] using hi
    rcases hi' with rfl | rfl | rfl | rfl
    · exact formula_singleton_false_of_pair f hf 0 4 h04
    · exact formula_singleton_false_of_pair f hf 1 7 h17
    · apply formula_singleton_false_of_pair f hf 5 3
      rwa [input_pair_comm 5 3]
    · apply formula_singleton_false_of_pair f hf 7 3
      rwa [input_pair_comm 7 3]
  have h := positive_read_once_corners f hf 0 1 5 7 hs h05 h07 h15
  exact Bool.false_ne_true (h17.symm.trans h)

-- Expand the live wires backwards. Seven necessary inputs force a tree.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def expand (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) : Finset ℕ :=
  if wire ∈ live then live.erase wire ∪ deps.toFinset else live

theorem expand_le (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2) :
    (expand live wire deps).card ≤ live.card + 1 := by
  by_cases hw : wire ∈ live
  · rw [expand, ite_eq_left hw]
    have hs := Finset.card_erase_add_one hw
    have hu := Finset.card_union_le (live.erase wire) deps.toFinset
    have hdf := List.toFinset_card_le deps
    omega
  · simp [expand, hw]

theorem expand_full (live : Finset ℕ) (wire : ℕ) (deps : List ℕ) (hd : deps.length ≤ 2)
    (he : (expand live wire deps).card = live.card + 1) :
    wire ∈ live ∧ deps.length = 2 ∧ deps.Nodup ∧ Disjoint (live.erase wire) deps.toFinset := by
  have hw : wire ∈ live := by
    by_contra hn
    simp [expand, hn] at he
  rw [expand, ite_eq_left hw] at he
  have hs := Finset.card_erase_add_one hw
  have hu := Finset.card_union_add_card_inter (live.erase wire) deps.toFinset
  have hdf := List.toFinset_card_le deps
  have hi : ((live.erase wire) ∩ deps.toFinset).card = 0 := by omega
  refine ⟨hw, by omega, ?_, ?_⟩
  · exact Multiset.toFinset_card_eq_card_iff_nodup.mp (by
      change deps.toFinset.card = deps.length
      omega)
  · exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)

def frontier : ℕ → List Gate → Finset ℕ → Finset ℕ
  | _, [], live => live
  | n, g :: gs, live => expand (frontier (n + 1) gs live) n (g.inputs.filter (· < n))

theorem frontier_le (n : ℕ) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (frontier n gs live).card ≤ live.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [frontier]
  | cons g gs ih =>
    have ht := ih (n + 1) (fun a ha => hf a (List.mem_cons_of_mem g ha))
    have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
    simpa [frontier, List.length_cons, Nat.add_assoc] using
      (expand_le (frontier (n + 1) gs live) n _ hg).trans (Nat.add_le_add_right ht 1)

theorem frontier_full (n : ℕ) (g : Gate) (gs : List Gate) (live : Finset ℕ)
    (hf : ∀ a ∈ g :: gs, a.inputs.length ≤ 2)
    (h : (frontier n (g :: gs) live).card = live.card + (g :: gs).length) :
    let rest := frontier (n + 1) gs live
    let deps := g.inputs.filter (· < n)
    rest.card = live.card + gs.length ∧ n ∈ rest ∧ deps.length = 2 ∧ deps.Nodup ∧
      Disjoint (rest.erase n) deps.toFinset := by
  dsimp only
  have ht := frontier_le (n + 1) gs live (fun a ha => hf a (List.mem_cons_of_mem g ha))
  have hg := (List.length_filter_le (· < n) g.inputs).trans (hf g (by simp))
  have hb := expand_le (frontier (n + 1) gs live) n _ hg
  rw [frontier, List.length_cons] at h
  refine ⟨by omega, expand_full (frontier (n + 1) gs live) n _ hg ?_⟩
  omega

def Agree (live : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ live, x.getD i false = y.getD i false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst i; simp [step]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp [step]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem agree_step (n : ℕ) (g : Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (expand live n (g.inputs.filter (· < n))) x y) :
    Agree live (step x g) (step y g) := by
  intro i hi
  rw [getD_step, getD_step, hx, hy]
  by_cases hn : i = n
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    congr 1
    apply List.map_congr_left
    intro j hj
    by_cases hjn : j < n
    · apply ha j
      simp [expand, hi, hj, hjn]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · rw [ite_eq_right hn, ite_eq_right hn]
    apply ha i
    by_cases h : n ∈ live
    · simp [expand, h, hi, hn]
    · simpa [expand, h] using hi

theorem agree_frontier (n : ℕ) (gs : List Gate) (live : Finset ℕ) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (ha : Agree (frontier n gs live) x y) : Agree live (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing n x y with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih (n + 1) (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy]) ?_
    exact agree_step n g (frontier (n + 1) gs live) x y hx hy ha

theorem eval_agree_frontier (C : Circuit) (x y : List Bool) (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ i ∈ frontier 8 C.gates {C.output}, x.getD i false = y.getD i false) :
    C.eval x = C.eval y :=
  agree_frontier 8 C.gates {C.output} x y hx hy h C.output (by simp)

def plug {m : ℕ} (t : Fin m) (r : DMFormula m) : DMFormula m → DMFormula m
  | .lit i b => if i = t then r else .lit i b
  | .and f g => .and (plug t r f) (plug t r g)
  | .or f g => .or (plug t r f) (plug t r g)

theorem plug_vars {m : ℕ} (t i : Fin m) (r f : DMFormula m) :
    i ∈ formulaVars (plug t r f) ↔
      (i ∈ formulaVars f ∧ i ≠ t) ∨ (t ∈ formulaVars f ∧ i ∈ formulaVars r) := by
  induction f with
  | lit j b =>
    by_cases h : j = t
    · subst j; simp [plug, formulaVars]
    · simp only [plug, h, ite_false, formulaVars, Set.mem_singleton_iff]
      grind
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug,formulaVars,Set.mem_union,ihf,ihg]
    constructor
    · rintro ((⟨h, hne⟩ | ⟨h, hr⟩) | (⟨h, hne⟩ | ⟨h, hr⟩))
      · exact Or.inl ⟨Or.inl h, hne⟩
      · exact Or.inr ⟨Or.inl h, hr⟩
      · exact Or.inl ⟨Or.inr h, hne⟩
      · exact Or.inr ⟨Or.inr h, hr⟩
    · rintro (⟨h | h, hne⟩ | ⟨h | h, hr⟩)
      · exact Or.inl (Or.inl ⟨h, hne⟩)
      · exact Or.inr (Or.inl ⟨h, hne⟩)
      · exact Or.inl (Or.inr ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, hr⟩)

theorem plug_read {m : ℕ} (t : Fin m) (r f : DMFormula m)
    (hr : positiveReadOnce r) (hf : positiveReadOnce f)
    (hs : ∀ i ∈ formulaVars f, i ≠ t → i ∈ formulaVars r → False) :
    positiveReadOnce (plug t r f) := by
  induction f with
  | lit i b =>
    by_cases h : i = t
    · simpa [plug, h] using hr
    · simpa [plug, h] using hf
  | and f g ihf ihg | or f g ihf ihg =>
    refine ⟨ihf hf.1 (fun i hi => hs i (Or.inl hi)),
      ihg hf.2.1 (fun i hi => hs i (Or.inr hi)), ?_⟩
    intro i hiF hiG
    rw [plug_vars] at hiF hiG
    rcases hiF with ⟨hiF, hiT⟩ | ⟨htF, hiR⟩ <;> rcases hiG with ⟨hiG, hiT'⟩ | ⟨htG, hiR'⟩
    · exact hf.2.2 i hiF hiG
    · exact hs i (Or.inl hiF) hiT hiR'
    · exact hs i (Or.inr hiG) hiT' hiR
    · exact hf.2.2 t htF htG

theorem plug_eval {m : ℕ} (t : Fin m) (r f : DMFormula m) (hf : positiveReadOnce f)
    (x : Fin m → Bool) : (plug t r f).eval x = f.eval (fun i => if i = t then r.eval x else x i) := by
  induction f with
  | lit i b =>
    change b = true at hf
    subst b
    by_cases h : i = t <;> simp [plug, DMFormula.eval, h]
  | and f g ihf ihg | or f g ihf ihg =>
    simp only [plug, DMFormula.eval, ihf hf.1, ihg hf.2.1]

def value {m : ℕ} (w : List Bool) (i : Fin m) : Bool := w.getD i.val false

def supportsFrontier {m : ℕ} (live : Finset ℕ) (f : DMFormula m) : Prop :=
  ∀ i : Fin m, i.val ∈ live ↔ i ∈ formulaVars f

def twoGate {m : ℕ} (o : GateOp) (a b : Fin m) : DMFormula m :=
  match o with
  | .and => .and (.lit a true) (.lit b true)
  | _ => .or (.lit a true) (.lit b true)

theorem twoGate_vars {m : ℕ} (o : GateOp) (a b i : Fin m) :
    i ∈ formulaVars (twoGate o a b) ↔ i = a ∨ i = b := by
  cases o <;> simp only [twoGate, formulaVars, Set.mem_union, Set.mem_singleton_iff]

theorem twoGate_read {m : ℕ} (o : GateOp) (a b : Fin m) (hne : a ≠ b) :
    positiveReadOnce (twoGate o a b) := by
  cases o <;> simp [twoGate, formulaVars, positiveReadOnce, hne]

theorem twoGate_eval {m : ℕ} (g : Gate) (a b : Fin m) (x : List Bool)
    (ho : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hi : g.inputs = [a.val,b.val]) :
    (twoGate g.op a b).eval (value x) = g.op.eval (g.inputs.map fun j => x.getD j false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  rcases ho with h | h <;> simp [twoGate, DMFormula.eval, hi, h, value, GateOp.eval]

theorem frontier_tree {m : ℕ} (n : ℕ) (gs : List Gate) (live : Finset ℕ) (f : DMFormula m)
    (hn : n + gs.length ≤ m) (hr : positiveReadOnce f) (hm : supportsFrontier live f)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier n gs live).card = live.card + gs.length) :
    ∃ F : DMFormula m, positiveReadOnce F ∧ supportsFrontier (frontier n gs live) F ∧
      ∀ w : List Bool, w.length = n → F.eval (value w) = f.eval (value (gs.foldl step w)) := by
  induction gs generalizing n with
  | nil => exact ⟨f, hr, hm, fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ht, hmem, hlen, hnd, hdj⟩ :=
      frontier_full n g gs live (fun a ha => (hf a ha).2) hfull
    obtain ⟨F, hFr, hFm, hFe⟩ := ih (n + 1) (by simp only [List.length_cons] at hn; omega)
      (fun a ha => hf a (List.mem_cons_of_mem g ha)) ht
    have hg := hf g (by simp)
    have he : g.inputs.filter (· < n) = g.inputs :=
      List.filter_sublist.eq_of_length_le (by omega)
    have hb : n < m := by simp only [List.length_cons] at hn; omega
    let t : Fin m := ⟨n, hb⟩
    rw [he] at hlen hnd hdj
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
      cases he' : g.inputs with
      | nil => simp [he'] at hlen
      | cons a rest =>
        cases rest with
        | nil => simp [he'] at hlen
        | cons b tail =>
          have hc : tail = [] := by simpa [he'] using hlen
          exact ⟨a, b, by simp [hc]⟩
    have hn' := List.filter_eq_self.mp he
    have ha : a < n := of_decide_eq_true (hn' a (by simp [hab]))
    have hb' : b < n := of_decide_eq_true (hn' b (by simp [hab]))
    let A : Fin m := ⟨a, ha.trans hb⟩
    let B : Fin m := ⟨b, hb'.trans hb⟩
    have hab' : A ≠ B := by
      intro e
      have ea := congrArg Fin.val e
      simp [hab, show a = b from ea] at hnd
    let r := twoGate g.op A B
    have htv : t ∈ formulaVars F := (hFm t).mp hmem
    have hpd : ∀ i ∈ formulaVars F, i ≠ t → i ∈ formulaVars r → False := by
      intro i hif hit hir
      apply (Finset.disjoint_left.mp hdj) (a := i.val)
      · exact Finset.mem_erase.mpr ⟨fun equ => hit (Fin.ext equ), (hFm i).mpr hif⟩
      · obtain hi | hi := (twoGate_vars g.op A B i).mp hir <;> simp [hi, hab, A, B]
    refine ⟨plug t r F, plug_read t r F (twoGate_read g.op A B hab') hFr hpd, ?_, ?_⟩
    · intro i
      rw [frontier, expand, ite_eq_left hmem, he, Finset.mem_union, Finset.mem_erase,
        List.mem_toFinset, hFm i, plug_vars, twoGate_vars]
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqA : i.val = a ↔ i = A := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      have hEqB : i.val = b ↔ i = B := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false, hEqA, hEqB, htv, true_and]
      constructor
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨h2, fun e => h1 (hEq.mpr e)⟩
        · exact Or.inr h
      · rintro (⟨h1,h2⟩ | h)
        · exact Or.inl ⟨fun e => h2 (hEq.mp e), h1⟩
        · exact Or.inr h
    · intro w hw
      rw [plug_eval t r F hFr]
      simp only [List.foldl_cons]
      rw [← hFe (step w g) (by simp [step, hw])]
      congr 1
      funext i
      have hEq : i.val = n ↔ i = t := ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
      simp only [value, getD_step, hw, hEq]
      rw [show r.eval (value w) = g.op.eval (g.inputs.map fun j => w.getD j false) from
        twoGate_eval g A B w hg.1 hab]

theorem circuit_tree (C : Circuit) (hs : C.size ≤ 6) (ho : C.output < 14)
    (hf : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hfull : (frontier 8 C.gates {C.output}).card = 1 + C.gates.length) :
    ∃ F : DMFormula 14, positiveReadOnce F ∧ supportsFrontier (frontier 8 C.gates {C.output}) F ∧
      ∀ w : List Bool, w.length = 8 → F.eval (value w) = C.eval w := by
  let t : Fin 14 := ⟨C.output, ho⟩
  have hm : supportsFrontier {C.output} (.lit t true) := by
    intro i
    simpa [formulaVars] using (show i.val = C.output ↔ i = t from
      ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩)
  have hn : 8 + C.gates.length ≤ 14 := by simpa [Circuit.size] using Nat.add_le_add_left hs 8
  have h : (frontier 8 C.gates {C.output}).card = ({C.output} : Finset ℕ).card + C.gates.length := by
    simpa using hfull
  obtain ⟨F, fr, fm, fe⟩ := frontier_tree 8 C.gates {C.output} (.lit t true) hn rfl hm hf h
  refine ⟨F, fr, fm, ?_⟩
  intro w hw
  change F.eval (value w) = (C.gates.foldl step w).getD C.output false
  simpa [DMFormula.eval, value, t] using fe w hw

-- Each of the seven nonisolated inputs is necessary by monotonicity.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ExtendsBits (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (x y : List Bool) (h : ExtendsBits x y) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => h.2 i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h.2 i ht⟩

theorem getD_snoc (x : List Bool) (b : Bool) : (x ++ [b]).getD x.length false = b := by
  simp

theorem gate_step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : ExtendsBits x y) : ExtendsBits (step x g) (step y g) := by
  refine ⟨by simp [step, h.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i x.length with hlt | heq | hgt
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 i hi
  · subst i
    rw [step, getD_snoc] at hi
    rw [h.1, step, getD_snoc]
    exact gate_map_mono g.op hop g.inputs x y h hi
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
    contradiction

theorem gates_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ExtendsBits x y) :
    ExtendsBits (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have ht : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (List.mem_cons_of_mem _ hk)
    exact ih ht _ _ (gate_step_mono g (hgs g (by simp)) x y hxy)

theorem circuit_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hxy : ExtendsBits x y) (hx : C.eval x = true) : C.eval y = true := by
  have hop g (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hC g hg).1
  exact (gates_mono C.gates hop x y hxy).2 C.output hx

def target366 (u v : Fin 4) : Bool := (366 : ℕ).testBit (4 * u.val + v.val)

def oneWire (i : ℕ) : List Bool := List.ofFn fun j : Fin 8 => decide (j.val = i)

theorem oneWire_len (i : ℕ) : (oneWire i).length = 8 := by simp [oneWire]

theorem pair_len (u v : Fin 4) : (oneEach u v).length = 8 := by simp [oneEach]

theorem singleton_nonedge : ∀ i : Fin 8, ∃ u v : Fin 4, target366 u v = false ∧
    ∀ j : Fin 8, (oneWire i.val).getD j.val false = true →
      (oneEach u v).getD j.val false = true := by decide +kernel

theorem singleton_false (C : Circuit) (hC : Monotone2 C) (hrep : Represents target366 C)
    (i : Fin 8) : C.eval (oneWire i.val) = false := by
  obtain ⟨u, v, hzero, hle⟩ := singleton_nonedge i
  cases h : C.eval (oneWire i.val) with
  | false => rfl
  | true =>
    have hxy : ExtendsBits (oneWire i.val) (oneEach u v) := by
      refine ⟨by rw [oneWire_len, pair_len], ?_⟩
      intro j hj
      by_cases hj8 : j < 8
      · exact hle ⟨j, hj8⟩ hj
      · rw [List.getD_eq_default _ _ (by rw [oneWire_len]; omega)] at hj
        contradiction
    have hc := circuit_mono C hC _ _ hxy h
    rw [hrep u v, hzero] at hc
    contradiction

theorem essential_edge : ∀ i : Fin 8, i.val ≠ 3 → ∃ (u v : Fin 4) (j : Fin 8),
    target366 u v = true ∧ ∀ k : Fin 8, k.val ≠ i.val →
      (oneWire j.val).getD k.val false = (oneEach u v).getD k.val false := by decide +kernel

theorem essential_support (C : Circuit) (hC : Monotone2 C) (hrep : Represents target366 C)
    (S : Finset ℕ)
    (hs : ∀ x y : List Bool, x.length = 8 → y.length = 8 →
      (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y) :
    ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ) ⊆ S := by
  intro i hi
  have hirange : i < 8 ∧ i ≠ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  by_contra hnot
  obtain ⟨u, v, j, hp, heq⟩ := essential_edge ⟨i, hirange.1⟩ hirange.2
  have hagree : ∀ k ∈ S, (oneWire j.val).getD k false = (oneEach u v).getD k false := by
    intro k hk
    by_cases hk8 : k < 8
    · apply heq ⟨k, hk8⟩
      intro he
      change k = i at he
      exact hnot (he ▸ hk)
    · rw [List.getD_eq_default _ _ (by rw [oneWire_len]; omega),
        List.getD_eq_default _ _ (by rw [pair_len]; omega)]
  have heval := hs (oneWire j.val) (oneEach u v) (oneWire_len _) (pair_len _ _) hagree
  rw [singleton_false C hC hrep j, hrep u v, hp] at heval
  contradiction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, step, Nat.add_comm, Nat.add_left_comm]

theorem lower : ¬ RepSizeAtMost target366 6 := by
  rintro ⟨C, hm, hs, hrep⟩
  have hlen : C.gates.length ≤ 6 := hs
  have req := essential_support C hm hrep _ (eval_agree_frontier C)
  have hmin : 7 ≤ (frontier 8 C.gates {C.output}).card := by
    have hc := Finset.card_le_card req
    have hs' : ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ).card = 7 := by decide
    rwa [hs'] at hc
  have hmax := frontier_le 8 C.gates {C.output} (fun g hg => (hm g hg).2)
  rw [Finset.card_singleton] at hmax
  have hfull : (frontier 8 C.gates {C.output}).card = 1 + C.gates.length := by omega
  have hout : C.output < 14 := by
    by_contra h
    have hv : C.eval (oneEach (0 : Fin 4) (1 : Fin 4)) = true :=
      (hrep 0 1).trans (by decide)
    change (C.gates.foldl step (oneEach (0 : Fin 4) (1 : Fin 4))).getD
      C.output false = true at hv
    rw [List.getD_eq_default _ _ (by rw [run_length, pair_len]; omega)] at hv
    contradiction
  obtain ⟨F, hf, _, he⟩ := circuit_tree C hs hout hm hfull
  apply no_formula_mask366 F hf
  intro u v
  have hpair : value (oneEach u v) = pairInput (mask366RowWire u) (mask366ColumnWire v) :=
    mask366_pair_wires u v
  rw [← hpair, he _ (pair_len u v)]
  exact hrep u v

end PEqualNP.Outside.L_meta_5533

theorem PEqualNP.Outside.L_meta_5533 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (366 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (366 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_5533.upper, PEqualNP.Outside.L_meta_5533.lower⟩
