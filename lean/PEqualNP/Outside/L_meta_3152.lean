import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3152

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ h

theorem read {N : ℕ} (x : Fin N → Bool) (i : Fin N) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

abbrev at_ (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

theorem run_gate {N : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step x).getD (N + j) false =
      (at_ gs j).op.eval ((at_ gs j).inputs.map fun i =>
        if i < N + j then (gs.foldl step x).getD i false else false) := by
  have hg : at_ gs j = gs[j] := by
    simp [at_, List.getD_eq_getElem?_getD, hj]
  have split : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  have whole : gs.foldl step x = (gs.drop (j + 1)).foldl step
      (step ((gs.take j).foldl step x) gs[j]) := by
    have h := congrArg (fun l => List.foldl step x l) split
    simp only [List.foldl_append, List.foldl_cons] at h
    exact h
  have len : ((gs.take j).foldl step x).length = N + j := by
    rw [run_length, hx, List.length_take]
    omega
  have low (i : ℕ) (hi : i < N + j) :
      (gs.foldl step x).getD i false = ((gs.take j).foldl step x).getD i false := by
    rw [whole, run_keep _ _ _ (by simp [step, len]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have args : (gs[j].inputs.map fun i => ((gs.take j).foldl step x).getD i false) =
      (gs[j].inputs.map fun i => if i < N + j then (gs.foldl step x).getD i false else false) := by
    apply List.map_congr_left
    intro i _
    by_cases h : i < N + j
    · rw [if_pos h, low i h]
    · rw [if_neg h, getD_big _ _ (by omega)]
  have top : (gs.foldl step x).getD (N + j) false =
      (step ((gs.take j).foldl step x) gs[j]).getD (N + j) false := by
    rw [whole, run_keep _ _ _ (by simp [step, len])]
  rw [top, hg, step, List.getD_append_right _ _ _ _ (by omega), len, args]
  simp

theorem prune {Y : Type} (a b : Y → List Bool) (N M B : ℕ) (gs : List Gate)
    (ha : ∀ y, (a y).length = N) (hb : ∀ y, (b y).length = M) (hB : M + gs.length ≤ B)
    (μ0 : ℕ → ℕ) (h0 : ∀ i < N, μ0 i < M ∨ μ0 i = B)
    (h1 : ∀ y, ∀ i < N, (a y).getD i false = (b y).getD (μ0 i) false)
    (R : Finset ℕ)
    (hR : ∀ j ∈ R, (∀ y, (gs.foldl step (a y)).getD (N + j) false = false) ∨
      ∃ i < N + j, ∀ y, (gs.foldl step (a y)).getD (N + j) false = (gs.foldl step (a y)).getD i false)
    (m : ℕ) (hm : m ≤ gs.length) :
    ∃ (hs : List Gate) (μ : ℕ → ℕ), hs.length + (R.filter (· < m)).card ≤ m ∧
      (∀ g ∈ hs, ∃ j < gs.length, g.op = (at_ gs j).op ∧ g.inputs.length = (at_ gs j).inputs.length) ∧
      (∀ i < N + m, μ i < M + hs.length ∨ μ i = B) ∧
      ∀ y, ∀ i < N + m, (gs.foldl step (a y)).getD i false = (hs.foldl step (b y)).getD (μ i) false := by
  induction m with
  | zero =>
    refine ⟨[], μ0, by simp, by simp, by simpa using h0, ?_⟩
    intro y i hi
    rw [run_keep _ _ _ (by rw [ha]; exact hi)]
    exact h1 y i hi
  | succ m ih =>
    obtain ⟨hs, μ, hc, hg, hμ, hv⟩ := ih (by omega)
    have small : hs.length ≤ m := by omega
    have big (y) : (hs.foldl step (b y)).getD B false = false := by
      apply getD_big
      rw [run_length, hb]
      omega
    by_cases hmR : m ∈ R
    · have cardS : (R.filter (· < m + 1)).card ≤ (R.filter (· < m)).card + 1 := by
        have : R.filter (· < m + 1) ⊆ insert m (R.filter (· < m)) := by
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_insert] at hu ⊢
          rcases eq_or_ne u m with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hu.1, by omega⟩
        exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
      have fin (t : ℕ) (ht : t < M + hs.length ∨ t = B)
          (val : ∀ y, (gs.foldl step (a y)).getD (N + m) false = (hs.foldl step (b y)).getD t false) :
          ∃ (hs : List Gate) (μ : ℕ → ℕ), hs.length + (R.filter (· < m + 1)).card ≤ m + 1 ∧
      (∀ g ∈ hs, ∃ j < gs.length, g.op = (at_ gs j).op ∧ g.inputs.length = (at_ gs j).inputs.length) ∧
      (∀ i < N + (m + 1), μ i < M + hs.length ∨ μ i = B) ∧
      ∀ y, ∀ i < N + (m + 1), (gs.foldl step (a y)).getD i false = (hs.foldl step (b y)).getD (μ i) false := by
        refine ⟨hs, fun i => if i = N + m then t else μ i, by omega, hg, ?_, ?_⟩
        · intro i hi
          by_cases h : i = N + m
          · simpa only [if_pos h] using ht
          · simp only [if_neg h]
            exact hμ i (by omega)
        · intro y i hi
          by_cases h : i = N + m
          · simp only [if_pos h]
            rw [h]
            exact val y
          · simp only [if_neg h]
            exact hv y i (by omega)
      rcases hR m hmR with h | ⟨i, hi, h⟩
      · exact fin B (Or.inr rfl) fun y => by rw [h y, big y]
      · exact fin (μ i) (hμ i hi) fun y => by rw [h y, hv y i hi]
    · have cardS : (R.filter (· < m + 1)).card ≤ (R.filter (· < m)).card := by
        apply Finset.card_le_card
        intro u hu
        simp only [Finset.mem_filter] at hu ⊢
        refine ⟨hu.1, ?_⟩
        have : u ≠ m := fun h => hmR (h ▸ hu.1)
        omega
      let g' : Gate := ⟨(at_ gs m).op, (at_ gs m).inputs.map fun i => if i < N + m then μ i else B⟩
      have len (y) : (hs.foldl step (b y)).length = M + hs.length := by rw [run_length, hb]
      have run (y) : ((hs ++ [g']).foldl step (b y)) = step (hs.foldl step (b y)) g' := by
        rw [List.foldl_append]
        rfl
      refine ⟨hs ++ [g'], fun i => if i = N + m then M + hs.length else μ i, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append]
        simp only [List.length_singleton]
        omega
      · intro g hgm
        rcases List.mem_append.mp hgm with h | h
        · exact hg g h
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨m, by omega, rfl, by simp [g']⟩
      · intro i hi
        rw [List.length_append]
        simp only [List.length_singleton]
        by_cases h : i = N + m
        · simp only [if_pos h]
          left
          omega
        · simp only [if_neg h]
          rcases hμ i (by omega) with h | h
          · left
            omega
          · exact Or.inr h
      · intro y i hi
        rw [run y]
        by_cases h : i = N + m
        · simp only [if_pos h]
          rw [h, run_gate gs (a y) (ha y) m (by omega), step,
            List.getD_append_right _ _ _ _ (by rw [len]), len]
          have args : ((at_ gs m).inputs.map fun i =>
              if i < N + m then (gs.foldl step (a y)).getD i false else false) =
              (g'.inputs.map fun i => (hs.foldl step (b y)).getD i false) := by
            simp only [g', List.map_map]
            apply List.map_congr_left
            intro i _
            by_cases h : i < N + m
            · simp only [Function.comp, if_pos h]
              exact hv y i h
            · simp only [Function.comp, if_neg h]
              exact (big y).symm
          rw [args]
          simp [g']
        · simp only [if_neg h]
          rw [hv y i (by omega)]
          rcases hμ i (by omega) with h' | h'
          · exact (List.getD_append _ _ _ _ (by rw [len]; exact h')).symm
          · rw [h', big y]
            symm
            apply getD_big
            rw [step, List.length_append, len]
            simp only [List.length_singleton]
            omega

theorem swap_other (l r : List Gate) (u v d : Gate) (j : ℕ) (h : j ≠ l.length) :
    (l ++ u :: r).getD j d = (l ++ v :: r).getD j d := by
  by_cases hj : j < l.length
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hj]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, j - l.length = k + 1 := ⟨j - l.length - 1, by omega⟩
    rw [hk, List.getD_cons_succ, List.getD_cons_succ]

theorem swap_here (l r : List Gate) (u d : Gate) : (l ++ u :: r).getD l.length d = u := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem getD_mem (l : List Gate) (d : Gate) (j : ℕ) (h : j < l.length) : l.getD j d ∈ l := by
  rw [List.getD_eq_getElem?_getD]
  simp [h]

theorem swap_mem (l r : List Gate) (u d : Gate) (j : ℕ) (h : j ≠ l.length)
    (hj : j < (l ++ u :: r).length) : (l ++ u :: r).getD j d ∈ l ++ r := by
  by_cases h' : j < l.length
  · rw [List.getD_append _ _ _ _ h']
    exact List.mem_append_left _ (getD_mem l d j h')
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, j - l.length = k + 1 := ⟨j - l.length - 1, by omega⟩
    rw [hk, List.getD_cons_succ]
    rw [List.length_append, List.length_cons] at hj
    exact List.mem_append_right _ (getD_mem r d k (by omega))

/-- Wires outside `D` agree when every gate outside `D` agrees as soon as the earlier ones do. -/
theorem agree {N : ℕ} {gs gs' : List Gate} {x x' : List Bool} (hx : x.length = N) (hx' : x'.length = N)
    (hl : gs.length = gs'.length) (D : ℕ → Prop)
    (base : ∀ i < N, ¬ D i → x.getD i false = x'.getD i false)
    (next : ∀ j < gs.length, ¬ D (N + j) →
      (∀ i < N + j, ¬ D i → (gs.foldl step x).getD i false = (gs'.foldl step x').getD i false) →
      (gs.foldl step x).getD (N + j) false = (gs'.foldl step x').getD (N + j) false) :
    ∀ i, ¬ D i → (gs.foldl step x).getD i false = (gs'.foldl step x').getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hD
    by_cases h : i < N
    · rw [run_keep _ _ _ (by omega), run_keep _ _ _ (by omega)]
      exact base i h hD
    obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
    by_cases hj : j < gs.length
    · exact next j hj hD fun i hi hDi => ih i hi hDi
    · rw [getD_big _ _ (by rw [run_length]; omega), getD_big _ _ (by rw [run_length]; omega)]

theorem same_gate {N : ℕ} {gs gs' : List Gate} {x x' : List Bool} (hx : x.length = N) (hx' : x'.length = N)
    (hl : gs.length = gs'.length) (D : ℕ → Prop) (j : ℕ) (hj : j < gs.length)
    (hg : at_ gs j = at_ gs' j) (hD : ∀ i ∈ (at_ gs j).inputs, i < N + j → ¬ D i)
    (ih : ∀ i < N + j, ¬ D i → (gs.foldl step x).getD i false = (gs'.foldl step x').getD i false) :
    (gs.foldl step x).getD (N + j) false = (gs'.foldl step x').getD (N + j) false := by
  rw [run_gate gs x hx j hj, run_gate gs' x' hx' j (hl ▸ hj), ← hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h : i < N + j
  · rw [if_pos h, if_pos h]
    exact ih i h (hD i hi h)
  · rw [if_neg h, if_neg h]

theorem cut {n : ℕ} (F : (Fin (n + 1) → Bool) → Bool)
    (e1 : ∀ v, ∃ x, F x = true ∧ x v = true ∧ F (Function.update x v false) = false)
    (e2 : ∀ v : Fin (n + 1), ∃ x, F x = true ∧ x v = false)
    (x2 x3 : List Gate) (x4 : Gate) (x5 : ℕ) (x6 : Fin (n + 1))
    (hF : FanInTwo ⟨x2 ++ x4 :: x3, x5⟩)
    (hn : ∀ g ∈ x2 ++ x3, g.op ≠ GateOp.not) (ho : x4.op = GateOp.not)
    (hc : circuitFun (n + 1) ⟨x2 ++ x4 :: x3, x5⟩ = F)
    (hne : circuitFun (n + 1) ⟨x2 ++ ⟨GateOp.or, []⟩ :: x3, x5⟩ ≠ F)
    (hs : ∀ y : Fin n → Bool, circuitFun (n + 1) ⟨x2 ++ ⟨GateOp.or, []⟩ :: x3, x5⟩
        (x6.insertNth (α := fun _ => Bool) false y) = F (x6.insertNth (α := fun _ => Bool) false y)) :
    HasCircuitSize n (F ∘ fun y : Fin n → Bool => x6.insertNth (α := fun _ => Bool) false y)
      ((x2 ++ x4 :: x3).length - 3) := by
  classical
  let C := x2 ++ x4 :: x3
  let E : List Gate := x2 ++ ⟨GateOp.or, []⟩ :: x3
  let j0 := x2.length
  have hl : C.length = E.length := by simp [C, E]
  have hj0 : j0 < C.length := by simp [C, j0]
  have other (j : ℕ) (h : j ≠ j0) : at_ C j = at_ E j := swap_other x2 x3 _ _ _ j h
  have here : at_ C j0 = x4 := swap_here x2 x3 _ _
  have hereE : at_ E j0 = ⟨GateOp.or, []⟩ := swap_here x2 x3 _ _
  have shape (j : ℕ) (hj : j < C.length) (h : j ≠ j0) :
      ((at_ E j).op = GateOp.and ∨ (at_ E j).op = GateOp.or) ∧ (at_ E j).inputs.length ≤ 2 := by
    rw [← other j h]
    have m1 := hF _ (getD_mem C ⟨GateOp.or, []⟩ j hj)
    have m2 := hn _ (swap_mem x2 x3 x4 ⟨GateOp.or, []⟩ j h hj)
    refine ⟨?_, m1.2⟩
    have := m1.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h m2
  let V (x : Fin (n + 1) → Bool) (i : ℕ) : Bool := (C.foldl step (List.ofFn x)).getD i false
  let W (x : Fin (n + 1) → Bool) (i : ℕ) : Bool := (E.foldl step (List.ofFn x)).getD i false
  have evC (x) : V x x5 = F x := by rw [← hc]; rfl
  have lenx (x : Fin (n + 1) → Bool) : (List.ofFn x).length = n + 1 := List.length_ofFn
  have rd (x : Fin (n + 1) → Bool) (i : Fin (n + 1)) : (List.ofFn x).getD i.val false = x i := read x i
  let pt (y : Fin n → Bool) : Fin (n + 1) → Bool := x6.insertNth (α := fun _ => Bool) false y
  have slice (x : Fin (n + 1) → Bool) (h : x x6 = false) : pt (x6.removeNth x) = x := by
    simp only [pt]
    rw [Fin.insertNth_removeNth]
    rw [← h]
    exact Function.update_eq_self x6 x
  have evE (x : Fin (n + 1) → Bool) (h : x x6 = false) : W x x5 = F x := by
    have := hs (x6.removeNth x)
    rw [show x6.insertNth (α := fun _ => Bool) false (x6.removeNth x) = x from slice x h] at this
    exact this
  have hj0W (x) : W x (n + 1 + j0) = false := by
    simp only [W]
    rw [run_gate E _ (lenx x) j0 (hl ▸ hj0), hereE]
    rfl
  have outOk (i : ℕ) (hz : ∀ x : Fin (n + 1) → Bool, x x6 = false → W x i = false) : x5 ≠ i := by
    rintro rfl
    obtain ⟨x, hx, h0⟩ := e2 x6
    have := hz x h0
    rw [evE x h0, hx] at this
    cases this
  have x6W (x : Fin (n + 1) → Bool) (h : x x6 = false) : W x x6.val = false := by
    simp only [W]
    rw [run_keep _ _ _ (by rw [lenx]; exact x6.2), rd, h]
  -- a gate with a false input can be removed
  have kill (j : ℕ) (hj : j < C.length) (h : j ≠ j0) (i : ℕ) (hi : i ∈ (at_ E j).inputs) (hij : i < n + 1 + j)
      (hz : ∀ x : Fin (n + 1) → Bool, x x6 = false → W x i = false) :
      (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false) ∨
        ∃ u < n + 1 + j, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = W x u := by
    obtain ⟨hop, hlen⟩ := shape j hj h
    have val (x) : W x (n + 1 + j) = (at_ E j).op.eval ((at_ E j).inputs.map fun i =>
        if i < n + 1 + j then W x i else false) := run_gate E _ (lenx x) j (hl ▸ hj)
    have get (x : Fin (n + 1) → Bool) (hx : x x6 = false) : (if i < n + 1 + j then W x i else false) = false := by
      rw [if_pos hij, hz x hx]
    rcases hop with hop | hop
    · left
      intro x hx
      rw [val, hop]
      simp only [GateOp.eval]
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.mpr ⟨i, hi, get x hx⟩, by simp⟩
    · have pair (b : ℕ) (hv : ∀ x : Fin (n + 1) → Bool, x x6 = false →
          W x (n + 1 + j) = if b < n + 1 + j then W x b else false) :
          (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false) ∨
            ∃ u < n + 1 + j, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = W x u := by
        by_cases hb : b < n + 1 + j
        · exact Or.inr ⟨b, hb, fun x hx => by rw [hv x hx, if_pos hb]⟩
        · exact Or.inl fun x hx => by rw [hv x hx, if_neg hb]
      generalize hq : (at_ E j).inputs = q at *
      match q, hlen, hi with
      | [u], _, hi =>
        rw [List.mem_singleton] at hi
        subst hi
        left
        intro x hx
        rw [val, hop]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, get x hx]
        rfl
      | [u, v], _, hi =>
        rcases List.mem_cons.mp hi with rfl | hi
        · apply pair v
          intro x hx
          rw [val, hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, get x hx]
          simp
        · rw [List.mem_singleton] at hi
          subst hi
          apply pair u
          intro x hx
          rw [val, hop]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, get x hx]
          simp
  -- false wires are read by some gate
  have escape (T : Finset ℕ) (h0 : j0 ∈ T)
      (hz : ∀ j ∈ T, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false) :
      ∃ k < C.length, k ∉ T ∧ ∃ j ∈ T, n + 1 + j ∈ (at_ E k).inputs ∧ j < k := by
    by_contra hno
    push Not at hno
    apply hne
    funext x
    rw [← evC x]
    change W x x5 = V x x5
    symm
    apply agree (lenx x) (lenx x) hl (fun i => ∃ j ∈ T, i = n + 1 + j)
    · intro i _ _
      rfl
    · intro j hj hD ih
      have hjT : j ∉ T := fun h => hD ⟨j, h, rfl⟩
      have hjj : j ≠ j0 := fun h => hjT (h ▸ h0)
      apply same_gate (lenx x) (lenx x) hl _ j hj (other j hjj) _ ih
      rintro i hi hij ⟨t, ht, rfl⟩
      rw [other j hjj] at hi
      exact absurd (hno j hj hjT t ht hi) (by omega)
    · rintro ⟨j, hj, h⟩
      exact outOk _ (hz j hj) h
  -- the restricted input is read by another gate
  have reader : ∃ g < C.length, g ≠ j0 ∧ x6.val ∈ (at_ E g).inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx, hv, hx0⟩ := e1 x6
    let z := Function.update x x6 false
    have hz0 : z x6 = false := by simp [z]
    have base : ∀ i < n + 1, ¬ i = x6.val → (List.ofFn x).getD i false = (List.ofFn z).getD i false := by
      intro i hi hne
      rw [rd x ⟨i, hi⟩, rd z ⟨i, hi⟩]
      simp only [z]
      rw [Function.update_of_ne]
      intro h
      exact hne (congrArg Fin.val h)
    have out6 : ¬ x5 = x6.val := outOk _ x6W
    by_cases hh : x4.inputs.head? = some x6.val
    · have q1 : V x x5 = W x x5 := by
        apply agree (lenx x) (lenx x) hl (fun _ => False)
        · intro i _ _
          rfl
        · intro j hj _ ih
          by_cases hjj : j = j0
          · subst hjj
            refine Eq.trans ?_ (hj0W x).symm
            rw [run_gate C _ (lenx x) j0 hj0, here, ho]
            obtain ⟨r, hr⟩ : ∃ r, x4.inputs = x6.val :: r := by
              cases hq : x4.inputs with
              | nil => rw [hq] at hh; cases hh
              | cons u r =>
                rw [hq] at hh
                exact ⟨r, by rw [Option.some.inj hh]⟩
            rw [hr]
            simp only [GateOp.eval, List.map_cons, List.headD_cons]
            rw [if_pos (by have := x6.2; omega), run_keep _ _ _ (by rw [lenx]; exact x6.2), rd, hv]
            rfl
          · exact same_gate (lenx x) (lenx x) hl (fun _ => False) j hj (other j hjj) (fun _ _ _ h => h) ih
        · exact fun h => h
      have q2 : W x x5 = W z x5 := by
        apply agree (lenx x) (lenx z) rfl (fun i => i = x6.val) base
        · intro j hj _ ih
          apply same_gate (lenx x) (lenx z) rfl _ j hj rfl _ ih
          rintro i hi _ rfl
          by_cases hjj : j = j0
          · rw [hjj, hereE] at hi
            cases hi
          · exact hno j (hl ▸ hj) hjj hi
        · exact out6
      rw [evC, hx] at q1
      rw [← q1, evE z hz0, hx0] at q2
      cases q2
    · have q : V x x5 = V z x5 := by
        apply agree (lenx x) (lenx z) rfl (fun i => i = x6.val) base
        · intro j hj _ ih
          by_cases hjj : j = j0
          · subst hjj
            rw [run_gate C _ (lenx x) j0 hj0, run_gate C _ (lenx z) j0 hj0, here, ho]
            simp only [GateOp.eval]
            congr 1
            cases hq : x4.inputs with
            | nil => rfl
            | cons u r =>
              simp only [List.map_cons, List.headD_cons]
              by_cases hu : u < n + 1 + j0
              · rw [if_pos hu, if_pos hu]
                apply ih u hu
                rintro rfl
                rw [hq] at hh
                exact hh rfl
              · rw [if_neg hu, if_neg hu]
          · apply same_gate (lenx x) (lenx z) rfl _ j hj rfl _ ih
            rintro i hi _ rfl
            rw [other j hjj] at hi
            exact hno j hj hjj hi
        · exact out6
      rw [evC, evC, hx, hx0] at q
      cases q
  have three : ∃ R : Finset ℕ, 3 ≤ (R.filter (· < E.length)).card ∧ ∀ j ∈ R,
      (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false) ∨
        ∃ u < n + 1 + j, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = W x u := by
    have mk (p q : ℕ) (hp : p < C.length) (hq : q < C.length) (h1 : p ≠ j0) (h2 : q ≠ j0) (h3 : p ≠ q)
        (kp : (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + p) = false) ∨
          ∃ u < n + 1 + p, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + p) = W x u)
        (kq : (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + q) = false) ∨
          ∃ u < n + 1 + q, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + q) = W x u) :
        ∃ R : Finset ℕ, 3 ≤ (R.filter (· < E.length)).card ∧ ∀ j ∈ R,
      (∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false) ∨
        ∃ u < n + 1 + j, ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = W x u := by
      refine ⟨{j0, p, q}, ?_, ?_⟩
      · rw [Finset.filter_true_of_mem]
        · rw [Finset.card_eq_three.mpr ⟨j0, p, q, h1.symm, h2.symm, h3, rfl⟩]
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          omega
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl fun x _ => hj0W x
        · exact kp
        · exact kq
    obtain ⟨g, hg, hgj, hgi⟩ := reader
    obtain ⟨h, hh, hhT, t, ht, hhi, hth⟩ := escape {j0} (Finset.mem_singleton_self _) (by
      intro j hj x _
      rw [Finset.mem_singleton.mp hj]
      exact hj0W x)
    rw [Finset.mem_singleton] at hhT ht
    subst ht
    have kg := kill g hg hgj x6.val hgi (by have := x6.2; omega) x6W
    have kh := kill h hh hhT _ hhi (by omega) (fun x _ => hj0W x)
    by_cases hgh : g = h
    · subst hgh
      -- both inputs of the gate are false
      have dead : ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + g) = false := by
        intro x hx
        obtain ⟨hop, hlen⟩ := shape g hg hgj
        have val : W x (n + 1 + g) = (at_ E g).op.eval ((at_ E g).inputs.map fun i =>
          if i < n + 1 + g then W x i else false) := run_gate E _ (lenx x) g (hl ▸ hg)
        have hne : x6.val ≠ n + 1 + j0 := by have := x6.2; omega
        have allz : ∀ i ∈ (at_ E g).inputs, (if i < n + 1 + g then W x i else false) = false := by
          intro i hi
          have : i = x6.val ∨ i = n + 1 + j0 := by
            generalize (at_ E g).inputs = q at hgi hhi hlen hi
            match q, hlen with
            | [], _ => cases hi
            | [u], _ =>
              rw [List.mem_singleton] at hgi hhi
              omega
            | [u, v], _ =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hgi hhi hi
              omega
          rcases this with rfl | rfl
          · rw [x6W x hx]
            exact ite_self _
          · rw [hj0W x]
            exact ite_self _
        rw [val]
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval]
          rw [List.all_eq_false]
          exact ⟨false, List.mem_map.mpr ⟨_, hgi, allz _ hgi⟩, by simp⟩
        · rw [hop]
          simp only [GateOp.eval]
          rw [List.any_eq_false]
          intro b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          rw [allz i hi]
          simp
      have both : ∀ j ∈ ({j0, g} : Finset ℕ), ∀ x : Fin (n + 1) → Bool, x x6 = false → W x (n + 1 + j) = false := by
        intro j hj x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hj0W x
        · exact dead x hx
      obtain ⟨k, hk, hkT, t, ht, hki, htk⟩ := escape {j0, g} (by simp) both
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkT
      exact mk g k hg hk hgj hkT.1 (Ne.symm hkT.2) kg
        (kill k hk hkT.1 _ hki (by omega) (both t ht))
    · exact mk g h hg hh hgj hhT hgh kg kh
  obtain ⟨R, hR3, hR⟩ := three
  let B := n + E.length
  let μ0 (i : ℕ) : ℕ := if h : ∃ t : Fin n, (x6.succAbove t).val = i then h.choose.val else B
  have pt6 (y) : pt y x6 = false := by simp [pt]
  obtain ⟨gs, μ, hcard, hshape, _, hval⟩ := prune (fun y : Fin n → Bool => List.ofFn (pt y))
    (fun y : Fin n → Bool => List.ofFn y) (n + 1) n B E (fun y => lenx _) (fun y => List.length_ofFn) le_rfl
    μ0 (by
      intro i _
      by_cases h : ∃ t : Fin n, (x6.succAbove t).val = i
      · left
        simp only [μ0, dif_pos h]
        exact h.choose.2
      · right
        simp only [μ0, dif_neg h])
    (by
      intro y i hi
      by_cases h : ∃ t : Fin n, (x6.succAbove t).val = i
      · simp only [μ0, dif_pos h]
        have hi' : i = (x6.succAbove h.choose).val := h.choose_spec.symm
        conv_lhs => rw [hi', rd]
        simp [pt, List.getD_eq_getElem?_getD]
      · simp only [μ0, dif_neg h]
        rw [getD_big (List.ofFn y) B (by rw [List.length_ofFn]; exact Nat.le_add_right _ _)]
        have : (⟨i, hi⟩ : Fin (n + 1)) = x6 := by
          by_contra hne
          obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hne
          exact h ⟨t, congrArg Fin.val ht⟩
        rw [rd (pt y) ⟨i, hi⟩, this, pt6])
    R (by
      intro j hj
      rcases hR j hj with h | ⟨u, hu, h⟩
      · exact Or.inl fun y => h (pt y) (pt6 y)
      · exact Or.inr ⟨u, hu, fun y => h (pt y) (pt6 y)⟩)
    E.length le_rfl
  have final (y : Fin n → Bool) (i : ℕ) (hi : n + 1 + E.length ≤ i) : W (pt y) i = false := by
    apply getD_big
    rw [run_length, lenx]
    exact hi
  refine ⟨⟨gs, if x5 < n + 1 + E.length then μ x5 else B + gs.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, h1, h2⟩ := hshape g hg
    rw [h1, h2]
    by_cases hjj : j = j0
    · rw [hjj, hereE]
      simp
    · obtain ⟨hop, hlen⟩ := shape j (hl ▸ hj) hjj
      refine ⟨?_, hlen⟩
      rcases hop with h | h <;> rw [h] <;> simp
  · change gs.length ≤ C.length - 3
    omega
  · intro y
    change (gs.foldl step (List.ofFn y)).getD _ false = F (pt y)
    rw [← evE (pt y) (pt6 y)]
    by_cases h : x5 < n + 1 + E.length
    · rw [if_pos h]
      exact (hval y x5 h).symm
    · rw [if_neg h, final y x5 (by omega)]
      apply getD_big
      rw [run_length, List.length_ofFn]
      simp only [B]
      omega

theorem main : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : Fin (9 : ℕ)),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x8 : (Fin (9 : ℕ) → Bool) → Bool := PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x9 : (Fin (8 : ℕ) → Bool) → Fin (9 : ℕ) → Bool := fun (x9 : Fin (8 : ℕ) → Bool) => x6.insertNth Bool.false x9;   PEqualNP.MetaComplexity.FanInTwo x7 → (∀ x11 ∈ x2 ++ x3, x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x7 = x1 → x8 ≠ x1 → x8 ∘ x9 = x1 ∘ x9 → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (x1 ∘ x9) (x7.size - (3 : ℕ)) := by
  intro F x2 x3 x4 x5 x6 _ _ _ h1 h2 h3 h4 h5 h6
  refine cut (n := 8) F ?_ ?_ x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 (fun y => congrFun h6 y)
  · have key : ∀ v : Fin 9, ∃ u : Fin 9, F (fun k => k == v || k == u) = true ∧
        F (Function.update (fun k => k == v || k == u) v false) = false := by
      decide
    intro v
    obtain ⟨u, h, h'⟩ := key v
    exact ⟨_, h, by simp, h'⟩
  · have key : ∀ v : Fin 9, ∃ u w : Fin 9, F (fun k => k == u || k == w) = true ∧
        (v == u || v == w) = false := by
      decide
    intro v
    obtain ⟨u, w, h, h'⟩ := key v
    exact ⟨fun k => k == u || k == w, h, h'⟩

end PEqualNP.Outside.L_meta_3152

theorem PEqualNP.Outside.L_meta_3152 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : Fin (9 : ℕ)),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x8 : (Fin (9 : ℕ) → Bool) → Bool := PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x9 : (Fin (8 : ℕ) → Bool) → Fin (9 : ℕ) → Bool := fun (x9 : Fin (8 : ℕ) → Bool) => x6.insertNth Bool.false x9;   PEqualNP.MetaComplexity.FanInTwo x7 → (∀ x11 ∈ x2 ++ x3, x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x7 = x1 → x8 ≠ x1 → x8 ∘ x9 = x1 ∘ x9 → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (x1 ∘ x9) (x7.size - (3 : ℕ)) :=
  PEqualNP.Outside.L_meta_3152.main
