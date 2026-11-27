import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_4966_319
    (hLift : ∀ (n m : ℕ) (e : Fin n → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (φ : ℕ → ℕ),
        PEqualNP.MetaComplexity.Monotone2 D ∧
        D.size = C.size ∧
        (∀ a < n + C.size, φ a < m + D.size) ∧
        (∀ (x : Fin m → Bool) (a : ℕ), a < n + C.size →
          (D.wires (List.ofFn x)).getD (φ a) false =
          (C.wires (List.ofFn (x ∘ e))).getD a false))
    (hCompact :
      let adj : Fin 9 → Fin 12 → Prop := fun p l =>
        (([1, 3, 4, 5, 6, 7, 9, 10, 11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈
          ([0, 1, 3, 9] : List ℕ)
      let indep : (Fin 21 → Bool) → Prop := fun x =>
        ∀ (p : Fin 9) (l : Fin 12), adj p l →
          x (Fin.castAdd 12 p) = false ∨ x (Fin.natAdd 9 l) = false
      let indepQ : (Fin 21 → Bool) → Prop := fun x =>
        indep x ∧ x 9 = false ∧ x 11 = false ∧ x 17 = false
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : Fin 9 → ℕ) (q : ℕ),
        let ev : (Fin 21 → Bool) → ℕ → Bool := fun x a => (C.wires (List.ofFn x)).getD a false
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ 28 ∧
        (∀ p : Fin 9, w p < 21 + C.size) ∧
        q < 21 + C.size ∧
        (∃ (p : Fin 9) (l : Fin 12), adj p l ∧
          ev (fun i => decide (i = Fin.natAdd 9 l)) (w p) = false) ∧
        (∀ (p : Fin 9) (l : Fin 12), adj p l →
          ev (fun i => decide (i = Fin.castAdd 12 p ∨ i = Fin.natAdd 9 l)) (w p) = true) ∧
        (∀ l : Fin 12, l.val ∈ ([0, 2, 8] : List ℕ) →
          ev (fun i => decide (i = Fin.natAdd 9 l)) q = true) ∧
        (∀ x, indep x → (∀ y, indep y → (∀ i, x i = true → y i = true) → y = x) →
          ∀ p : Fin 9, x (Fin.castAdd 12 p) = true → ev x (w p) = false) ∧
        (∀ x, indepQ x → (∀ y, indepQ y → (∀ i, x i = true → y i = true) → y = x) →
          ev x q = false)) :
    have x1 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x1 x2 : Fin (25 : ℕ)) => ↑x1 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x1 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (25 : ℕ) → ℕ) (x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (28 : ℕ) ∧       (∀ (x5 : Fin (25 : ℕ)), x3 x5 < (25 : ℕ) + x2.size) ∧         x4 < (25 : ℕ) + x2.size ∧           (∃ (x5 : Fin (25 : ℕ)) (x6 : Fin (25 : ℕ)), x1 x5 x6 ∧ (x2.wires (List.ofFn fun (x7 : Fin (25 : ℕ)) => Decidable.decide (x7 = x6))).getD (x3 x5) Bool.false = Bool.false) ∧             ∀ (x5 : Fin (25 : ℕ) → Bool),               have x6 : ℕ → Bool := fun (x6 : ℕ) => (x2.wires (List.ofFn x5)).getD x6 Bool.false;               (∀ (x7 x8 : Fin (25 : ℕ)), x1 x7 x8 → x5 x7 = Bool.true → x5 x8 = Bool.true → x6 (x3 x7) = Bool.true) ∧ ((¬∃ (x7 : Fin (25 : ℕ)) (x8 : Fin (25 : ℕ)), x1 x7 x8 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) → (∀ (x8 : Fin (25 : ℕ)), ↑x8 < (12 : ℕ) → ↑x8 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] → x5 x8 = Bool.true → x6 (x3 x8) = Bool.false) ∧ x6 x4 = (x5 (13 : Fin (25 : ℕ)) || x5 (15 : Fin (25 : ℕ)) || x5 (21 : Fin (25 : ℕ)))) := by
  classical
  dsimp only
  have foldl_wires_mono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp)) →
      ∀ (w₁ w₂ : List Bool),
        w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₁).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₂).length ∧
        ∀ a,
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₁).getD a false = true →
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w₂).getD a false = true := by
    intro gs
    induction gs with
    | nil =>
      intro _ w₁ w₂ hlen hle
      exact ⟨hlen, hle⟩
    | cons g gs ih =>
      intro hmono w₁ w₂ hlen hle
      have hg : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        have hm := hmono g List.mem_cons_self
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
      have hbit : g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
        rcases hg with hop | hop
        · rw [hop]
          intro h1
          change (g.inputs.map fun i => w₂.getD i false).all id = true
          change (g.inputs.map fun i => w₁.getD i false).all id = true at h1
          rw [List.all_eq_true] at h1 ⊢
          intro b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          exact hle i (h1 (w₁.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩))
        · rw [hop]
          intro h1
          change (g.inputs.map fun i => w₂.getD i false).any id = true
          change (g.inputs.map fun i => w₁.getD i false).any id = true at h1
          rw [List.any_eq_true] at h1 ⊢
          obtain ⟨b, hb, hbt⟩ := h1
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          exact ⟨w₂.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, hle i hbt⟩
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg'))
      · simp [hlen]
      · intro i hi
        let b₁ := g.op.eval (g.inputs.map fun i => w₁.getD i false)
        let b₂ := g.op.eval (g.inputs.map fun i => w₂.getD i false)
        change (w₁ ++ [b₁]).getD i false = true at hi
        change (w₂ ++ [b₂]).getD i false = true
        by_cases hlt : i < w₁.length
        · have hlt2 : i < w₂.length := hlen ▸ hlt
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
          exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
        · by_cases heq : i = w₁.length
          · subst heq
            have heq2 : w₁.length = w₂.length := hlen
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
            rw [List.getD_eq_getElem?_getD, heq2, List.getElem?_append_right (le_refl _), Nat.sub_self]
            simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
            exact hbit hi
          · rw [List.getD_eq_getElem?_getD] at hi
            have hnone : (w₁ ++ [b₁])[i]? = none := by
              apply List.getElem?_eq_none
              simp
              omega
            rw [hnone] at hi
            simp at hi
  have wires_mono : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) →
      ∀ (a : ℕ),
        (C.wires (List.ofFn x)).getD a false = true →
        (C.wires (List.ofFn y)).getD a false = true := by
    intro n C hm x y hle a
    have hbase : ∀ i : ℕ, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i hi
      by_cases hlt : i < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
        exact hle ⟨i, hlt⟩ hi
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_none] at hi
        contradiction
    exact (foldl_wires_mono C.gates (fun g hg => (hm g hg).1) (List.ofFn x) (List.ofFn y)
      (by simp) hbase).2 a
  have exists_maximal_extension : ∀ (n : ℕ) (P : (Fin n → Bool) → Prop) (x : Fin n → Bool),
      P x →
      ∃ z : Fin n → Bool, P z ∧ (∀ i, x i = true → z i = true) ∧
        (∀ y, P y → (∀ i, z i = true → y i = true) → y = z) := by
    intro n P x hx
    let wt : (Fin n → Bool) → ℕ := fun u => (Finset.univ.filter fun i => u i = true).card
    have hwt_le : ∀ u, wt u ≤ n := fun u => by
      have h1 : wt u ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      simpa using h1
    have step : ∀ k : ℕ, ∀ u : Fin n → Bool, n - wt u = k → P u →
        ∃ z : Fin n → Bool, P z ∧ (∀ i, u i = true → z i = true) ∧
          (∀ y, P y → (∀ i, z i = true → y i = true) → y = z) := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro u hk hu
        by_cases hmax : ∀ y, P y → (∀ i, u i = true → y i = true) → y = u
        · exact ⟨u, hu, fun _ h => h, hmax⟩
        · push Not at hmax
          obtain ⟨y, hyP, hule, hyne⟩ := hmax
          have hsub : (Finset.univ.filter fun i => u i = true) ⊂
              (Finset.univ.filter fun i => y i = true) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun i hi => ?_, fun heq => hyne (funext fun i => ?_)⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact hule i hi
            · have hmem : i ∈ Finset.univ.filter (fun j => u j = true) ↔
                  i ∈ Finset.univ.filter (fun j => y j = true) := by rw [heq]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              cases hyi : y i <;> cases hui : u i
              · rfl
              · exact absurd (hmem.mp hui) (by rw [hyi]; decide)
              · exact absurd (hmem.mpr hyi) (by rw [hui]; decide)
              · rfl
          have hlt : wt u < wt y := Finset.card_lt_card hsub
          have hy_le : wt y ≤ n := hwt_le y
          have hdrop : n - wt y < k := by omega
          obtain ⟨z, hzP, hyle, hzmax⟩ := ih (n - wt y) hdrop y rfl hyP
          exact ⟨z, hzP, fun i hi => hyle i (hule i hi), hzmax⟩
    exact step (n - wt x) x rfl hx
  let e : Fin 21 → Fin 25 := fun i =>
    ([1, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List (Fin 25)).getD i.val 0
  let invP : Fin 25 → Option (Fin 9) := fun a =>
    ([none, some 0, none, some 1, some 2, some 3, some 4, some 5, none, some 6, some 7, some 8] :
      List (Option (Fin 9))).getD a.val none
  let adj : Fin 9 → Fin 12 → Prop := fun p l =>
    (([1, 3, 4, 5, 6, 7, 9, 10, 11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈
      ([0, 1, 3, 9] : List ℕ)
  let edge : Fin 25 → Fin 25 → Prop := fun a b =>
    a.val < 12 ∧ 12 ≤ b.val ∧ (a.val + b.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
      a.val ∉ ([0, 2, 8] : List ℕ)
  have e_inj : Function.Injective e := by decide +kernel
  have invP_e : ∀ p : Fin 9, invP (e (Fin.castAdd 12 p)) = some p := by decide +kernel
  have invP_some : ∀ (a : Fin 25), a.val < 12 → a.val ∉ ([0, 2, 8] : List ℕ) →
      ∃ p : Fin 9, invP a = some p ∧ e (Fin.castAdd 12 p) = a := by decide +kernel
  have edge_iff : ∀ (p : Fin 9) (l : Fin 12),
      edge (e (Fin.castAdd 12 p)) (e (Fin.natAdd 9 l)) ↔ adj p l := by decide +kernel
  have line_cover : ∀ (a b : Fin 25), edge a b →
      ∃ (p : Fin 9) (l : Fin 12), e (Fin.castAdd 12 p) = a ∧ e (Fin.natAdd 9 l) = b ∧ adj p l := by
    decide +kernel
  have e9 : e 9 = 13 := by decide
  have e11 : e 11 = 15 := by decide
  have e17 : e 17 = 21 := by decide
  obtain ⟨C, w, q, hmonoC, hsizeC, hwC, hqC, hcond1, hposW, hposQ, hnegW, hnegQ⟩ := hCompact
  obtain ⟨D, φ, hmonoD, hsizeD, hφlt, hφeval⟩ := hLift 21 25 e C hmonoC
  let w25 : Fin 25 → ℕ := fun a => (invP a).elim 0 (fun p => φ (w p))
  have hw25_lt : ∀ a : Fin 25, w25 a < 25 + D.size := by
    intro a
    dsimp only [w25]
    cases h : invP a with
    | none => simp
    | some p => exact hφlt (w p) (hwC p)
  have hw25_e : ∀ p : Fin 9, w25 (e (Fin.castAdd 12 p)) = φ (w p) := by
    intro p
    simp [w25, invP_e p]
  refine ⟨D, w25, φ q, hmonoD, by omega, hw25_lt, hφlt q hqC, ?_, ?_⟩
  · obtain ⟨p, l, hadj, hfalse⟩ := hcond1
    refine ⟨e (Fin.castAdd 12 p), e (Fin.natAdd 9 l), (edge_iff p l).mpr hadj, ?_⟩
    rw [hw25_e p, hφeval _ (w p) (hwC p)]
    have hcomp : ((fun j : Fin 25 => decide (j = e (Fin.natAdd 9 l))) ∘ e) =
        (fun i : Fin 21 => decide (i = Fin.natAdd 9 l)) := by
      funext i
      simp only [Function.comp_apply]
      by_cases hi : i = Fin.natAdd 9 l
      · simp [hi]
      · have hne : e i ≠ e (Fin.natAdd 9 l) := fun h => hi (e_inj h)
        simp [hi, hne]
    rw [hcomp]
    exact hfalse
  · intro x5
    constructor
    · intro a b hab ha hb
      obtain ⟨p, l, rfl, rfl, hadj⟩ := line_cover a b hab
      rw [hw25_e p, hφeval x5 (w p) (hwC p)]
      apply wires_mono 21 C hmonoC
        (fun i : Fin 21 => decide (i = Fin.castAdd 12 p ∨ i = Fin.natAdd 9 l)) (x5 ∘ e)
      · intro i hi
        have hor : i = Fin.castAdd 12 p ∨ i = Fin.natAdd 9 l := of_decide_eq_true hi
        rcases hor with rfl | rfl
        · exact ha
        · exact hb
      · exact hposW p l hadj
    · intro hnoedge
      have hindep : ∀ (p : Fin 9) (l : Fin 12), adj p l →
          (x5 ∘ e) (Fin.castAdd 12 p) = false ∨ (x5 ∘ e) (Fin.natAdd 9 l) = false := by
        intro p l hadj
        by_contra hboth
        push Not at hboth
        have h1 : x5 (e (Fin.castAdd 12 p)) = true := by
          cases hx : x5 (e (Fin.castAdd 12 p))
          · exact absurd hx hboth.1
          · rfl
        have h2 : x5 (e (Fin.natAdd 9 l)) = true := by
          cases hx : x5 (e (Fin.natAdd 9 l))
          · exact absurd hx hboth.2
          · rfl
        exact hnoedge ⟨e (Fin.castAdd 12 p), e (Fin.natAdd 9 l), (edge_iff p l).mpr hadj, h1, h2⟩
      constructor
      · intro a ha1 ha2 hxa
        obtain ⟨p, hinv, rfl⟩ := invP_some a ha1 ha2
        rw [hw25_e p, hφeval x5 (w p) (hwC p)]
        let indep : (Fin 21 → Bool) → Prop := fun x =>
          ∀ (p' : Fin 9) (l' : Fin 12), adj p' l' →
            x (Fin.castAdd 12 p') = false ∨ x (Fin.natAdd 9 l') = false
        obtain ⟨z, hzind, hxz, hzmax⟩ :=
          exists_maximal_extension 21 indep (x5 ∘ e) hindep
        have hzp : z (Fin.castAdd 12 p) = true := hxz (Fin.castAdd 12 p) hxa
        have hfalse : (C.wires (List.ofFn z)).getD (w p) false = false :=
          hnegW z hzind hzmax p hzp
        cases hc : (C.wires (List.ofFn (x5 ∘ e))).getD (w p) false
        · rfl
        · have htrue : (C.wires (List.ofFn z)).getD (w p) false = true :=
            wires_mono 21 C hmonoC (x5 ∘ e) z hxz (w p) hc
          rw [hfalse] at htrue
          contradiction
      · rw [hφeval x5 q hqC]
        cases h13 : x5 13 <;> cases h15 : x5 15 <;> cases h21 : x5 21
        · simp only [Bool.false_or]
          let indepQ : (Fin 21 → Bool) → Prop := fun x =>
            (∀ (p' : Fin 9) (l' : Fin 12), adj p' l' →
              x (Fin.castAdd 12 p') = false ∨ x (Fin.natAdd 9 l') = false) ∧
            x 9 = false ∧ x 11 = false ∧ x 17 = false
          have hinit : indepQ (x5 ∘ e) := by
            refine ⟨hindep, ?_, ?_, ?_⟩
            · simp [Function.comp_apply, e9, h13]
            · simp [Function.comp_apply, e11, h15]
            · simp [Function.comp_apply, e17, h21]
          obtain ⟨z, hzindQ, hxz, hzmax⟩ :=
            exists_maximal_extension 21 indepQ (x5 ∘ e) hinit
          have hfalse : (C.wires (List.ofFn z)).getD q false = false :=
            hnegQ z hzindQ hzmax
          cases hc : (C.wires (List.ofFn (x5 ∘ e))).getD q false
          · rfl
          · have htrue : (C.wires (List.ofFn z)).getD q false = true :=
              wires_mono 21 C hmonoC (x5 ∘ e) z hxz q hc
            rw [hfalse] at htrue
            contradiction
        · simp only [Bool.false_or, Bool.or_true]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (8 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (8 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e17] using h21
          · exact hposQ 8 (by decide)
        · simp only [Bool.false_or, Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (2 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (2 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e11] using h15
          · exact hposQ 2 (by decide)
        · simp only [Bool.false_or, Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (2 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (2 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e11] using h15
          · exact hposQ 2 (by decide)
        · simp only [Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (0 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (0 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e9] using h13
          · exact hposQ 0 (by decide)
        · simp only [Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (0 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (0 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e9] using h13
          · exact hposQ 0 (by decide)
        · simp only [Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (0 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (0 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e9] using h13
          · exact hposQ 0 (by decide)
        · simp only [Bool.true_or]
          apply wires_mono 21 C hmonoC
            (fun i : Fin 21 => decide (i = Fin.natAdd 9 (0 : Fin 12))) (x5 ∘ e)
          · intro i hi
            have heq : i = Fin.natAdd 9 (0 : Fin 12) := of_decide_eq_true hi
            subst heq
            simpa [Function.comp_apply, e9] using h13
          · exact hposQ 0 (by decide)
