import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4077_2
    (takeKeeps : ∀ (C : Circuit) (m : ℕ) (xs : List Bool) (w : ℕ), m ≤ C.size →
      w < xs.length + m → ((Circuit.mk (C.gates.take m) 0).wires xs).getD w false =
        (C.wires xs).getD w false)
    (supportBound : ∀ (b : Bool) (C : Circuit) (r : ℕ), FanInTwo C →
      let w := fun (x : Fin 10 → Bool) =>
        (C.wires (List.ofFn x ++ [x 0 || if b = true then x 1 else x 2])).getD r false
      ∃ S : Finset (Fin 10), S.card ≤ max 2 (r - 8) ∧
        ∀ x y, (∀ i ∈ S, x i = y i) → w x = w y)
    (core : ∀ (b : Bool) (C : Circuit) (a d : ℕ), FanInTwo C → C.size ≤ 17 →
      18 ≤ a → 14 ≤ d → max a d + 1 = 11 + C.size →
      let w := fun (x : Fin 10 → Bool) (i : ℕ) =>
        (C.wires (List.ofFn x ++ [x 0 || if b = true then x 1 else x 2])).getD i false
      (∃ x, w x a = true ∧ w x d = false) → (∃ x, w x a = false ∧ w x d = true) →
      (∀ i : Fin 10, ∃ u v : Fin 10,
        let x := fun k : Fin 10 => decide (k = u ∨ k = v)
        w x a = false ∧ w (fun k => decide (k=i) || x k) a = true) →
      ¬ (∀ x, (w x a && w x d) = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10)))) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) || if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  classical
  intro x1 x2 x3 x4 hfan hsize x7 x8 H1 H2 H3
  by_contra hneg
  have exactPair (x : Fin 10 → Bool) : (x8 x x3 && x8 x x4) = x7 x := by
    cases hx : x7 x
    · cases hA : x8 x x3 <;> cases hB : x8 x x4 <;> try rfl
      exact (hneg ⟨x,hx,hA,hB⟩).elim
    · obtain ⟨hA,hB⟩ := H3 x hx
      simp [hA,hB]
  let step (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have lengthRun (gs : List Gate) (ws : List Bool) :
      (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).length = _
      rw [ih]
      simp [step]
      omega
  have retain (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step ws g)).getD i false = ws.getD i false
      rw [ih _ (by simpa [step] using Nat.lt_succ_of_lt hi)]
      exact List.getD_append _ _ _ _ hi
  let seed (x : Fin 10 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 || if x1 = true then x 1 else x 2]
  have seed_len (x : Fin 10 → Bool) : (seed x).length = 11 := by simp [seed]
  have bound (i : ℕ) (h : ∀ x, x7 x = true → x8 x i = true) : 11 ≤ i ∧ i < 11 + x2.size := by
    let xa := fun j : Fin 10 => (24 : ℕ).testBit j.val
    let xb := fun j : Fin 10 => (160 : ℕ).testBit j.val
    have hxa : x8 xa i = true := h xa (by decide)
    have hxb : x8 xb i = true := h xb (by decide)
    have hlo : 11 ≤ i := by
      by_contra! hi
      have readA := retain x2.gates (seed xa) i (by rwa [seed_len])
      have readB := retain x2.gates (seed xb) i (by rwa [seed_len])
      change (x2.gates.foldl step (seed xa)).getD i false = true at hxa
      change (x2.gates.foldl step (seed xb)).getD i false = true at hxb
      rw [readA] at hxa
      rw [readB] at hxb
      have incompatible : ∀ (b : Bool) (j : Fin 11),
          ¬ ((List.ofFn xa ++ [xa 0 || if b = true then xa 1 else xa 2]).getD j.val false = true ∧
             (List.ofFn xb ++ [xb 0 || if b = true then xb 1 else xb 2]).getD j.val false = true) := by
        decide
      exact incompatible x1 ⟨i, hi⟩ ⟨hxa, hxb⟩
    refine ⟨hlo, ?_⟩
    by_contra! hi
    change (x2.gates.foldl step (seed xa)).getD i false = true at hxa
    rw [List.getD_eq_default _ _ (by rw [lengthRun, seed_len]; exact hi)] at hxa
    exact Bool.false_ne_true hxa
  have hx3 := bound x3 (fun x hx => (H3 x hx).1)
  have hx4 := bound x4 (fun x hx => (H3 x hx).2)
  have pc10 : ∀ x : Fin 10 → Bool,
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85].any fun e : ℕ =>
        x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) = x7 x := by
    intro x
    have h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool,
        (a0 && a1 || (a1 && a2 || (a2 && a3 || (a3 && a4 || (a4 && a0 || (a0 && a5 || (a1 && a6 || (a2 && a7 || (a3 && a8 || (a4 && a9 || (a5 && a7 || (a7 && a9 || (a9 && a6 || (a6 && a8 || (a8 && a5 || false))))))))))))))) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 || a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a4 && a9 || a5 && a7 || a7 && a9 || a9 && a6 || a6 && a8 || a8 && a5) := by
      decide
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

  let pair (u v k : Fin 10) := decide (k=u ∨ k=v)
  let add (i : Fin 10) (x : Fin 10 → Bool) (k : Fin 10) := decide (k=i) || x k
  have links : ∀ i j : Fin 10, ∃ u v : Fin 10, x7 (pair u v) = false ∧
      x7 (add i (pair u v)) = true ∧ x7 (add j (pair u v)) = true := by decide +kernel
  let detects (a : ℕ) := ∀ i : Fin 10, ∃ u v : Fin 10,
      x8 (pair u v) a = false ∧ x8 (add i (pair u v)) a = true
  have allInputs : detects x3 ∨ detects x4 := by
    by_cases hd : detects x3
    · exact Or.inl hd
    · right
      change ¬ (∀ i : Fin 10, ∃ u v : Fin 10,
        x8 (pair u v) x3 = false ∧ x8 (add i (pair u v)) x3 = true) at hd
      push Not at hd
      obtain ⟨i,hi⟩ := hd
      intro j
      obtain ⟨u,v,hn,hleft,hright⟩ := links i j
      have ha := (H3 _ hleft).1
      have hb := (H3 _ hright).2
      refine ⟨u,v,?_,hb⟩
      cases aa : x8 (pair u v) x3 with
      | false => exact False.elim (by simpa [ha] using hi u v aa)
      | true =>
        have z := (exactPair _).trans hn
        simpa [aa] using z
  have finish (a d : ℕ) (ha : 11 ≤ a ∧ a < 11 + x2.size) (hd : 11 ≤ d ∧ d < 11 + x2.size)
      (sa : ∃ x, x8 x a = true ∧ x8 x d = false) (sd : ∃ x, x8 x a = false ∧ x8 x d = true)
      (fullSupport : detects a) (correct : ∀ x, (x8 x a && x8 x d) = x7 x) : False := by
    obtain ⟨S,hSc,hS⟩ := supportBound x1 x2 a hfan
    have univS : S = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      obtain ⟨u,v,h0,h1⟩ := fullSupport i
      have eq := hS (pair u v) (add i (pair u v)) (by
        intro j hj
        have ne : j ≠ i := fun e => hi (e ▸ hj)
        simp only [add, ne, decide_false, Bool.false_or])
      change x8 (pair u v) a = x8 (add i (pair u v)) a at eq
      rw [h0,h1] at eq
      contradiction
    rw [univS,Finset.card_univ,Fintype.card_fin] at hSc
    have ha18 : 18 ≤ a := by omega
    obtain ⟨T,hTc,hT⟩ := supportBound x1 x2 d hfan
    have hT6 : 6 ≤ T.card := by
      by_contra! hsmall
      let edges : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
      have miss : ∀ s : Finset (Fin 10), s.card < 6 → ∃ e ∈ edges,
          Fin.ofNat 10 (e/10) ∉ s ∧ Fin.ofNat 10 (e%10) ∉ s := by decide +kernel
      obtain ⟨e,he,hu,hv⟩ := miss T hsmall
      obtain ⟨x,_,h0⟩ := sa
      let y : Fin 10 → Bool := fun i => if i ∈ T then x i else true
      have eq := hT x y (fun i hi => by simp only [y,hi,ite_true])
      change x8 x d = x8 y d at eq
      have hp : x7 y = true := by
        rw [← pc10 y, List.any_eq_true]
        exact ⟨e, he, Bool.and_eq_true_iff.mpr ⟨ite_eq_right hu, ite_eq_right hv⟩⟩
      have h1 := (correct y).trans hp
      have hon := (Bool.and_eq_true_iff.mp h1).2
      rw [h0,hon] at eq
      contradiction
    have hd14 : 14 ≤ d := by omega
    let k := max a d + 1 - 11
    have htop : max a d + 1 = 11 + k := by dsimp [k]; omega
    have hkle : k ≤ x2.size := by
      have hu := max_lt ha.2 hd.2
      omega
    let D : Circuit := ⟨x2.gates.take k,0⟩
    have hs : D.size = k := by
      change k ≤ x2.gates.length at hkle
      change (x2.gates.take k).length = k
      rw [List.length_take, Nat.min_eq_left hkle]
    have hf : FanInTwo D := fun g hg => hfan g (List.mem_of_mem_take hg)
    have read (i : ℕ) (hi : i ≤ max a d) (x : Fin 10 → Bool) :
        (D.wires (List.ofFn x ++ [x 0 || if x1 = true then x 1 else x 2])).getD i false = x8 x i :=
      takeKeeps x2 k (seed x) i hkle (by rw [seed_len]; omega)
    have ra := read a (le_max_left _ _)
    have rd := read d (le_max_right _ _)
    refine core x1 D a d hf (by omega) ha18 hd14 (by omega) ?_ ?_ ?_ ?_
    · simpa only [ra,rd] using sa
    · simpa only [ra,rd] using sd
    · change ∀ i : Fin 10, ∃ u v : Fin 10,
        (D.wires (seed (pair u v))).getD a false = false ∧
        (D.wires (seed (add i (pair u v)))).getD a false = true
      intro i
      obtain ⟨u,v,hu,hv⟩ := fullSupport i
      exact ⟨u,v,(ra _).trans hu,(ra _).trans hv⟩
    · intro x
      exact (congrArg₂ Bool.and (ra x) (rd x)).trans ((correct x).trans (pc10 x).symm)
  rcases allInputs with h | h
  · exact finish x3 x4 hx3 hx4 H1 H2 h exactPair
  · apply finish x4 x3 hx4 hx3 _ _ h (fun x => (Bool.and_comm _ _).trans (exactPair x))
    · obtain ⟨x,ha,hb⟩ := H2
      exact ⟨x,hb,ha⟩
    · obtain ⟨x,ha,hb⟩ := H1
      exact ⟨x,hb,ha⟩
