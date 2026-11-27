import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2280_37
    (noSixAnd :
      let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      let F (x : Fin 14 → Bool) : Prop :=
        ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
      ∀ (C : Circuit) (r : Fin 14), r = 7 ∨ r = 9 → Monotone2 C →
        (∀ x : Fin 14 → Bool,
          C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x) →
        PEqualNP.ReadTwo.nAnd C ≠ 6)
    (orCount :
      let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      let F (x : Fin 14 → Bool) : Prop :=
        ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
      ∀ (C : Circuit) (r : Fin 14), r = 7 ∨ r = 9 → Monotone2 C →
        (∀ x : Fin 14 → Bool,
          C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]]) = true ↔ F x) →
        19 ≤ PEqualNP.ReadTwo.nOr C) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  classical
  intro E F B C r hr hC hc
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let ca (gs : List Gate) : ℕ :=
    (gs.filter (fun g => decide (g.op = .and))).length
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have get_snoc (l : List Bool) (s : Bool) (k : ℕ) :
      (l ++ [s]).getD k false =
        if k < l.length then l.getD k false else if k = l.length then s else false := by
    by_cases h1 : k < l.length
    · simp [h1, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · by_cases h2 : k = l.length
      · subst h2
        simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right h1, ite_eq_right h2, List.getD_eq_default]
        simp only [List.length_append, List.length_singleton]
        omega

  have eval_mono (op : GateOp) (hop : op = .and ∨ op = .or) (ins : List ℕ)
      (a b : List Bool) (h : ∀ k, a.getD k false = true → b.getD k false = true) :
      op.eval (ins.map fun i => a.getD i false) = true →
      op.eval (ins.map fun i => b.getD i false) = true := by
    rcases hop with rfl | rfl
    · intro H
      change (ins.map fun i => a.getD i false).all id = true at H
      change (ins.map fun i => b.getD i false).all id = true
      rw [List.all_eq_true] at H ⊢
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
      exact h i (H _ (List.mem_map.2 ⟨i, hi, rfl⟩))
    · intro H
      change (ins.map fun i => a.getD i false).any id = true at H
      change (ins.map fun i => b.getD i false).any id = true
      rw [List.any_eq_true] at H ⊢
      obtain ⟨v, hv, hvt⟩ := H
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
      exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, h i hvt⟩

  have fold_mono : ∀ (gs : List Gate) (a b : List Bool),
      (∀ g ∈ gs, g.op = .and ∨ g.op = .or) → a.length = b.length →
      (∀ k, a.getD k false = true → b.getD k false = true) →
      ∀ k, (gs.foldl step a).getD k false = true →
        (gs.foldl step b).getD k false = true := by
    intro gs
    induction gs with
    | nil => intro a b _ _ h; exact h
    | cons g gs ih =>
      intro a b hAO hl h
      refine ih (step a g) (step b g) (fun g' h' => hAO g' (List.mem_cons_of_mem _ h'))
        (by simp [step, hl]) ?_
      intro k
      unfold step
      rw [get_snoc, get_snoc, hl]
      by_cases c1 : k < b.length
      · rw [ite_eq_left c1, ite_eq_left c1]
        exact h k
      · rw [ite_eq_right c1, ite_eq_right c1]
        by_cases c2 : k = b.length
        · rw [ite_eq_left c2, ite_eq_left c2]
          exact eval_mono g.op (hAO g List.mem_cons_self) g.inputs a b h
        · rw [ite_eq_right c2, ite_eq_right c2]
          exact id

  have extend {n : ℕ} (F : (Fin n → Bool) → Prop) (G : (Fin n → Bool) → Bool)
      (hm : ∀ x y, x ≤ y → G x = true → G y = true)
      (hc : ∀ x,
        ((F x ∧ ∀ i, x i = true → ¬ F (Function.update x i false)) ∨
        (¬ F x ∧ ∀ i, x i = false → F (Function.update x i true))) →
        (G x = true ↔ F x)) : ∀ x, G x = true ↔ F x := by
    classical
    intro x
    constructor
    · intro hg
      by_contra hf
      obtain ⟨y, hy, hmax⟩ :=
        (Set.toFinite {y : Fin n → Bool | x ≤ y ∧ ¬ F y}).exists_maximal ⟨x, le_rfl, hf⟩
      have boundary : ∀ i, y i = false → F (Function.update y i true) := by
        intro i hi
        by_contra hbad
        have up : y ≤ Function.update y i true := by
          intro j
          by_cases hj : j = i
          · subst j
            simp
          · simp [Function.update_of_ne hj]
        have back : Function.update y i true ≤ y :=
          hmax ⟨hy.1.trans up, hbad⟩ up
        have nope := back i
        exact (by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hi] using nope)
      exact hy.2 ((hc y (Or.inr ⟨hy.2, boundary⟩)).mp (hm x y hy.1 hg))
    · intro hf
      obtain ⟨y, hy, hmin⟩ :=
        (Set.toFinite {y : Fin n → Bool | y ≤ x ∧ F y}).exists_minimal ⟨x, le_rfl, hf⟩
      have boundary : ∀ i, y i = true → ¬ F (Function.update y i false) := by
        intro i hi hbad
        have down : Function.update y i false ≤ y := by
          intro j
          by_cases hj : j = i
          · subst j
            simp
          · simp [Function.update_of_ne hj]
        have back : y ≤ Function.update y i false :=
          hmin ⟨down.trans hy.1, hbad⟩ down
        have nope := back i
        exact (by decide : ¬ ((true : Bool) ≤ false)) (by simpa [hi] using nope)
      exact hm y x hy.1 ((hc y (Or.inl ⟨hy.2, boundary⟩)).mpr hy.2)
  have get_ofFn {n : ℕ} (x : Fin n → Bool) (k : Fin n) :
      (List.ofFn x).getD k.val false = x k := by
    simp [List.getD_eq_getElem?_getD]
  let G (x : Fin 14 → Bool) : Bool :=
    C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x r]])
  have hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or :=
    fun g hg => (hC g hg).1
  have gmono : ∀ x y : Fin 14 → Bool, x ≤ y → G x = true → G y = true := by
    intro x y hxy
    apply fold_mono C.gates
      (List.ofFn x ++ [GateOp.or.eval [x 0,x r]])
      (List.ofFn y ++ [GateOp.or.eval [y 0,y r]]) hops (by simp)
    intro k
    rw [get_snoc, get_snoc, List.length_ofFn, List.length_ofFn]
    by_cases hk : k < 14
    · rw [ite_eq_left hk, ite_eq_left hk]
      have hx : (List.ofFn x).getD k false = x ⟨k,hk⟩ := get_ofFn x ⟨k,hk⟩
      have hy : (List.ofFn y).getD k false = y ⟨k,hk⟩ := get_ofFn y ⟨k,hk⟩
      rw [hx, hy]
      exact Bool.le_iff_imp.mp (hxy ⟨k,hk⟩)
    · rw [ite_eq_right hk, ite_eq_right hk]
      by_cases he : k = 14
      · rw [ite_eq_left he, ite_eq_left he]
        change (x 0 || (x r || false)) = true → (y 0 || (y r || false)) = true
        simp only [Bool.or_false, Bool.or_eq_true]
        intro h
        exact h.elim (fun h0 => Or.inl (Bool.le_iff_imp.mp (hxy 0) h0))
          (fun hr => Or.inr (Bool.le_iff_imp.mp (hxy r) hr))
      · rw [ite_eq_right he, ite_eq_right he]
        exact id
  have full : ∀ x : Fin 14 → Bool, G x = true ↔ F x :=
    extend F G gmono (fun x hx => hc x hx)
  have gate_join (g : Gate) (hm : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      (a b c : List Bool)
      (h : ∀ i, c.getD i false = (a.getD i false || b.getD i false))
      (hsame : g.op = .and → a.getD (g.inputs.headD 0) false = b.getD (g.inputs.headD 0) false) :
      g.op.eval (g.inputs.map fun i => c.getD i false) =
        (g.op.eval (g.inputs.map fun i => a.getD i false) ||
          g.op.eval (g.inputs.map fun i => b.getD i false)) := by
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen⟩ := hm
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
    · rcases hop with rfl | rfl <;> rfl
    · rcases hop with rfl | rfl
      · change (c.getD i false && true) = ((a.getD i false && true) || (b.getD i false && true))
        simpa only [Bool.and_true] using h i
      · change (c.getD i false || false) = ((a.getD i false || false) || (b.getD i false || false))
        simpa only [Bool.or_false] using h i
    · rcases hop with rfl | rfl
      · have eq : a.getD i false = b.getD i false := hsame rfl
        change (c.getD i false && (c.getD j false && true)) =
          ((a.getD i false && (a.getD j false && true)) ||
            (b.getD i false && (b.getD j false && true)))
        simp only [Bool.and_true, h]
        rw [eq]
        cases b.getD i false <;> cases a.getD j false <;> cases b.getD j false <;> rfl
      · change (c.getD i false || (c.getD j false || false)) =
          ((a.getD i false || (a.getD j false || false)) ||
            (b.getD i false || (b.getD j false || false)))
        simp only [Bool.or_false, h]
        cases a.getD i false <;> cases b.getD i false <;>
          cases a.getD j false <;> cases b.getD j false <;> rfl
    · simp only [List.length_cons] at hlen
      omega

  have bound {ι : Type} [DecidableEq ι] : ∀ (gs : List Gate),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
      ∀ (L : ℕ) (A : ι → List Bool) (J : ι → ι → List Bool) (S : Finset ι) (out : ℕ),
      (∀ s ∈ S, (A s).length = L) →
      (∀ s ∈ S, ∀ t ∈ S, (J s t).length = L) →
      (∀ s ∈ S, ∀ t ∈ S, ∀ i,
        (J s t).getD i false = ((A s).getD i false || (A t).getD i false)) →
      (∀ s ∈ S, (gs.foldl step (A s)).getD out false = false) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → (gs.foldl step (J s t)).getD out false = true) →
      S.card ≤ 2 ^ ca gs := by
    intro gs
    induction gs with
    | nil =>
      intro _ L A J S out _ _ hj hz ht
      change S.card ≤ 1
      apply Finset.card_le_one.mpr
      intro s hs t hts
      by_contra ne
      have bad := hj s hs t hts out
      have zs : (A s).getD out false = false := hz s hs
      have zt : (A t).getD out false = false := hz t hts
      have jp : (J s t).getD out false = true := ht s hs t hts ne
      rw [zs, zt, jp] at bad
      cases bad
    | cons g gs ih =>
      intro hm L A J S out ha hj hrel hz ht
      have hg := hm g List.mem_cons_self
      have tail := fun g hg' => hm g (List.mem_cons_of_mem _ hg')
      have limited (T : Finset ι) (hT : T ⊆ S)
          (same : g.op = .and → ∀ s ∈ T, ∀ t ∈ T,
            (A s).getD (g.inputs.headD 0) false = (A t).getD (g.inputs.headD 0) false) :
          T.card ≤ 2 ^ ca gs := by
        apply ih tail (L + 1) (fun s => step (A s) g) (fun s t => step (J s t) g) T out
        · intro s hs
          simp [step, ha s (hT hs)]
        · intro s hs t hts
          simp [step, hj s (hT hs) t (hT hts)]
        · intro s hs t hts k
          dsimp [step]
          rw [get_snoc, get_snoc, get_snoc, ha s (hT hs), ha t (hT hts),
            hj s (hT hs) t (hT hts)]
          by_cases h1 : k < L
          · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
            exact hrel s (hT hs) t (hT hts) k
          · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h1]
            by_cases h2 : k = L
            · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left h2]
              exact gate_join g hg (A s) (A t) (J s t)
                (hrel s (hT hs) t (hT hts)) (fun h => same h s hs t hts)
            · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h2]
              rfl
        · intro s hs
          exact hz s (hT hs)
        · intro s hs t hts ne
          exact ht s (hT hs) t (hT hts) ne
      rcases hg.1 with hop | hop
      · let T0 := S.filter (fun s => (A s).getD (g.inputs.headD 0) false = false)
        let T1 := S.filter (fun s => (A s).getD (g.inputs.headD 0) false = true)
        have c0 := limited T0 (Finset.filter_subset _ _) (fun _ s hs t hts =>
          (Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp hts).2.symm)
        have c1 := limited T1 (Finset.filter_subset _ _) (fun _ s hs t hts =>
          (Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp hts).2.symm)
        have covered : S ⊆ T0 ∪ T1 := by
          intro s hs
          cases hh : (A s).getD (g.inputs.headD 0) false
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,hh⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,hh⟩)
        have card := Finset.card_le_card covered
        have un := Finset.card_union_le T0 T1
        have cnt : ca (g :: gs) = ca gs + 1 := by
          simp [ca, hop]
        rw [cnt, pow_succ]
        omega
      · have card := limited S (fun _ h => h) (fun h => by simp [hop] at h)
        simpa [ca, hop] using card
  let rows (s : Fin 37) (i : Fin 14) : Bool :=
    (([127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ).getD s.val 0).testBit i.val
  let input (x : Fin 14 → Bool) : List Bool :=
    List.ofFn x ++ [GateOp.or.eval [x 0,x r]]
  have zeros : ∀ s : Fin 37, ¬ F (rows s) := by
    dsimp only [F]
    decide +kernel
  have joins : ∀ s t : Fin 37, s ≠ t → F (fun i => rows s i || rows t i) := by
    dsimp only [F]
    decide +kernel
  have input_join : ∀ (x y : Fin 14 → Bool) (k : ℕ),
      (input (fun i => x i || y i)).getD k false =
        ((input x).getD k false || (input y).getD k false) := by
    intro x y k
    dsimp only [input]
    rw [get_snoc, get_snoc, get_snoc, List.length_ofFn, List.length_ofFn, List.length_ofFn]
    by_cases hk : k < 14
    · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk,
        get_ofFn _ ⟨k,hk⟩, get_ofFn _ ⟨k,hk⟩, get_ofFn _ ⟨k,hk⟩]
    · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk]
      by_cases he : k = 14
      · rw [ite_eq_left he, ite_eq_left he, ite_eq_left he]
        change ((x 0 || y 0) || ((x r || y r) || false)) =
          ((x 0 || (x r || false)) || (y 0 || (y r || false)))
        cases x 0 <;> cases y 0 <;> cases x r <;> cases y r <;> rfl
      · rw [ite_eq_right he, ite_eq_right he, ite_eq_right he]
        rfl
  have rejects : ∀ s : Fin 37, (C.gates.foldl step (input (rows s))).getD C.output false = false := by
    intro s
    change C.eval (input (rows s)) = false
    cases hv : C.eval (input (rows s))
    · rfl
    · exact False.elim (zeros s ((full _).mp hv))
  have accepts : ∀ s t : Fin 37, s ≠ t →
      (C.gates.foldl step (input (fun i => rows s i || rows t i))).getD C.output false = true := by
    intro s t ne
    exact (full _).mpr (joins s t ne)
  have card := bound C.gates (fun g hg => hC g hg) 15
    (fun s => input (rows s))
    (fun s t => input (fun i => rows s i || rows t i)) Finset.univ C.output
    (fun _ _ => by simp [input]) (fun _ _ _ _ => by simp [input])
    (fun s _ t _ k => input_join (rows s) (rows t) k)
    (fun s _ => rejects s) (fun s _ t _ ne => accepts s t ne)
  rw [Finset.card_univ, Fintype.card_fin] at card
  change 37 ≤ 2 ^ PEqualNP.ReadTwo.nAnd C at card
  have six : 6 ≤ PEqualNP.ReadTwo.nAnd C := by
    by_contra bad
    have cnt : PEqualNP.ReadTwo.nAnd C ≤ 5 := by omega
    have powbound : 2 ^ PEqualNP.ReadTwo.nAnd C ≤ 2 ^ 5 :=
      pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) cnt
    norm_num at powbound
    omega
  have notSix := noSixAnd C r hr hC full
  have hor := orCount C r hr hC full
  have partition : ∀ gs : List Gate,
      (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
      (gs.filter (fun g => decide (g.op = .and))).length +
        (gs.filter (fun g => decide (g.op = .or))).length = gs.length := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro hm
      have htail := ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))
      rcases hm g List.mem_cons_self with hg | hg
      · simp [hg] at htail ⊢
        omega
      · simp [hg] at htail ⊢
        omega
  have counts : PEqualNP.ReadTwo.nAnd C + PEqualNP.ReadTwo.nOr C = C.size :=
    partition C.gates hops
  omega
