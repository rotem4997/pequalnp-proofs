import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4865_1
    (h1 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (S : Finset ℕ), PEqualNP.MetaComplexity.FanInTwo C → (ρ = id ∨ ∃ v : Fin n, ρ = fun x => Function.update x v false) → (∃ x y : Fin n → Bool, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y))) → (∀ j ∈ S, j < C.gates.length ∧ ((∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (ρ x))).getD (n + j) false = b) ∨ ∃ o, o < n + j ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (ρ x))).getD (n + j) false = (C.wires (List.ofFn (ρ x))).getD o false)) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (ρ x))) (C.size - S.card))
    (h2 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.FanInTwo C → j < C.gates.length → C.output ≠ n + j → (∀ g ∈ C.gates, n + j ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2)) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn x)) (C.size - 1))
    (h3 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ (∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x18]? = some x19 ∧ x19 ∈ x7 x16 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∃ x20, List.filter (fun (x21 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x21.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x21.inputs).contains (x1 + x18)) x5.gates = [x20] ∧ x20.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  classical
  intro n G _ A C
  dsimp only
  intro hdeg hgirth hA hedge hF hcomp hmin hread hnot hcount
  by_contra hno
  obtain ⟨v, hvA, hlen2, g, hgR, hgnot⟩ := hnot
  have hnc : ∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update x v false) ≠ PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update y v false) := by
    have h3v := hdeg v hvA
    obtain ⟨u, hu⟩ : (G.neighborSet v).Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero; omega
    have huv : G.Adj v u := hu
    have huA : u ∉ A := hA u v huv.symm
    have h3u := hdeg u huA
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ G.neighborSet u, w ≠ v := by
      by_contra hcon
      push_neg at hcon
      have hsub : G.neighborSet u ⊆ {v} := fun w hw => hcon w hw
      have := Set.ncard_le_ncard hsub (Set.finite_singleton v)
      rw [Set.ncard_singleton] at this
      omega
    have huw : G.Adj u w := hw
    have hne : u ≠ v := huv.ne'
    have gF : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G A x = (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
    refine ⟨fun _ => false, fun z => decide (z = u ∨ z = w), ?_⟩
    have e1 : PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update (fun _ => false) v false) = false := by
      have : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
        funext z; simp [Function.update_apply]
      rw [this, gF]
      simp
    have e2 : PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update (fun z => decide (z = u ∨ z = w)) v false) = true := by
      rw [gF, Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      refine ⟨u, w, huw, ?_, ?_⟩
      · rw [Function.update_apply, if_neg hne]; simp
      · rw [Function.update_apply, if_neg hwv]; simp
    rw [e1, e2]
    simp
  have hncf : ∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G A x ≠ PEqualNP.MetaComplexity.NestedCover.graphFun G A y := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨_, _, hxy⟩
  obtain ⟨eff, heff⟩ : ∃ eff : PEqualNP.CircuitLowerBounds.Gate → List ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, eff g = g.inputs.take (bif g.op.eval [false] then 1 else 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨val, hval⟩ : ∃ val : (Fin n → Bool) → ℕ → Bool, ∀ x w, val x w = (C.wires (List.ofFn x)).getD w false := ⟨_, fun _ _ => rfl⟩
  have base : ∀ (W : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool), (∀ gs x, W gs x = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gs) → (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ), i < x.length → (W gs x).getD i false = x.getD i false) ∧ (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gs[k]? = some g → (W gs x).getD (x.length + k) false = g.op.eval (g.inputs.map fun i => if i < x.length + k then (W gs x).getD i false else false)) := by
    intro W hW
    have W_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool), W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
      intro gs g x
      rw [hW, hW]
      simp [List.foldl_append]
    have W_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool), (W gs x).length = x.length + gs.length := by
      intro gs x
      induction gs using List.reverseRecOn with
      | nil => rw [hW]; simp
      | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
    have W_inp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ), i < x.length → (W gs x).getD i false = x.getD i false := by
      intro gs x i hi
      induction gs using List.reverseRecOn with
      | nil => rw [hW]; simp
      | append_singleton gs g ih =>
        rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih
    have W_oob : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ), x.length + gs.length ≤ i → (W gs x).getD i false = false := by
      intro gs x i hi
      apply List.getD_eq_default; rw [W_len]; exact hi
    refine ⟨W_inp, ?_⟩
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro k g h; simp at h
    | append_singleton gs a ih =>
      intro k g h
      rw [W_snoc]
      rcases Nat.lt_or_ge k gs.length with hk | hk
      · rw [List.getElem?_append_left hk] at h
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
      · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
        · have hk2 : k = gs.length := by omega
          subst hk2
          have hag : a = g := by simpa using h
          subst hag
          rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
          simp only [Nat.sub_self, List.getD_cons_zero]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < x.length + gs.length
          · simp only [hi, if_true]
            rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
          · simp only [hi, if_false]
            exact W_oob gs x i (by omega)
        · rw [List.getElem?_eq_none (by simp; omega)] at h
          cases h
  obtain ⟨winp, wspec⟩ := base (fun gs x => (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires x) (fun _ _ => rfl)
  have hin : ∀ (x : Fin n → Bool) (u : ℕ) (hu : u < n), val x u = x ⟨u, hu⟩ := by
    intro x u hu
    rw [hval]
    have e := winp C.gates (List.ofFn x) u (by simpa using hu)
    have e2 : (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hu)]
      simp
    exact e.trans e2
  have key : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → ∀ x : Fin n → Bool, val x (n + k) = g.op.eval (g.inputs.map fun i => if i < n + k then val x i else false) := by
    intro k g hg x
    have e := wspec C.gates (List.ofFn x) k g hg
    rw [List.length_ofFn] at e
    simp only [hval]
    exact e
  have hout2 : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G A x = val x C.output := by
    intro x
    rw [hval, ← hcomp]
    rfl
  have evA : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and l = l.all id := fun _ => rfl
  have evO : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id := fun _ => rfl
  have evN : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.not l = !(l.headD false) := fun _ => rfl
  have gl0 : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) → g.inputs.length ≤ 2 → ∀ (q : ℕ) (c : Bool), q ∈ eff g → (∃ b : Bool, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = b) ∨ (∃ w : ℕ, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = ρ w) := by
    intro g hop hlen q c hq
    rw [heff] at hq
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [evA, evO, evN] at hq
      · simp [evA, evO, evN] at hq
        subst hq
        exact Or.inl ⟨c, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
      · simp [evA, evO, evN] at hq
        cases c with
        | false =>
          exact Or.inl ⟨false, fun ρ hρ => by
            rcases hq with rfl | rfl <;> simp [evA, evO, evN, hρ]⟩
        | true =>
          rcases hq with rfl | rfl
          · exact Or.inr ⟨b, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
          · exact Or.inr ⟨a, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
      · simp at hlen
    | or =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [evA, evO, evN] at hq
      · simp [evA, evO, evN] at hq
        subst hq
        exact Or.inl ⟨c, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
      · simp [evA, evO, evN] at hq
        cases c with
        | true =>
          exact Or.inl ⟨true, fun ρ hρ => by
            rcases hq with rfl | rfl <;> simp [evA, evO, evN, hρ]⟩
        | false =>
          rcases hq with rfl | rfl
          · exact Or.inr ⟨b, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
          · exact Or.inr ⟨a, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
      · simp at hlen
    | not =>
      rcases inputs with _ | ⟨a, l⟩
      · simp [evA, evO, evN] at hq
      · simp [evA, evO, evN] at hq
        subst hq
        exact Or.inl ⟨!c, fun ρ hρ => by simp [evA, evO, evN, hρ]⟩
    | mod m => simp at hop
    | maj => simp at hop
  have gnot : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∀ q : ℕ, q ∈ eff g → ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = !ρ q := by
    intro g hop q hq ρ
    rw [heff] at hq
    obtain ⟨op, inputs⟩ := g
    dsimp only at hop
    subst hop
    rcases inputs with _ | ⟨a, l⟩
    · simp [evA, evO, evN] at hq
    · simp [evA, evO, evN] at hq
      subst hq
      simp [evA, evO, evN]
  have gnot1 : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∀ q q' : ℕ, q ∈ eff g → q' ∈ eff g → q = q' := by
    intro g hop q q' hq hq'
    rw [heff] at hq hq'
    obtain ⟨op, inputs⟩ := g
    dsimp only at hop
    subst hop
    rcases inputs with _ | ⟨a, l⟩
    · simp [evA, evO, evN] at hq
    · simp [evA, evO, evN] at hq hq'
      rw [hq, hq']
  have gor : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ q : ℕ, q ∈ eff g → ∀ ρ : ℕ → Bool, ρ q = true → g.op.eval (g.inputs.map ρ) = true := by
    intro g hop q hq ρ hρ
    rw [heff] at hq
    have hm : q ∈ g.inputs := List.mem_of_mem_take hq
    rw [hop]
    show (g.inputs.map ρ).any id = true
    rw [List.any_eq_true]
    exact ⟨ρ q, List.mem_map_of_mem hm, hρ⟩
  have gand : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ q : ℕ, q ∈ eff g → ∀ ρ : ℕ → Bool, ρ q = false → g.op.eval (g.inputs.map ρ) = false := by
    intro g hop q hq ρ hρ
    rw [heff] at hq
    have hm : q ∈ g.inputs := List.mem_of_mem_take hq
    rw [hop]
    show (g.inputs.map ρ).all id = false
    rw [List.all_eq_false]
    exact ⟨ρ q, List.mem_map_of_mem hm, by simp [hρ]⟩
  obtain ⟨Red, hRed⟩ : ∃ Red : ((Fin n → Bool) → Fin n → Bool) → ℕ → Prop, ∀ ρ j, Red ρ j ↔ ((∃ b : Bool, ∀ x, val (ρ x) (n + j) = b) ∨ ∃ o, o < n + j ∧ ∀ x, val (ρ x) (n + j) = val (ρ x) o) := ⟨_, fun _ _ => Iff.rfl⟩
  have hFg : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := fun k g h => hF g (List.mem_of_getElem? h)
  have klt : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k < C.gates.length := by
    intro k g hg
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have gl : ∀ (ρ : (Fin n → Bool) → Fin n → Bool) (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → ∀ q : ℕ, q ∈ eff g → (∃ c : Bool, ∀ x, (if q < n + k then val (ρ x) q else false) = c) → Red ρ k := by
    rintro ρ k g hg q hq ⟨c, hc⟩
    rw [hRed]
    rcases gl0 g (hFg k g hg).1 (hFg k g hg).2 q c hq with ⟨b, hb⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨b, fun x => by
        rw [key k g hg (ρ x)]
        exact hb (fun i => if i < n + k then val (ρ x) i else false) (hc x)⟩
    · by_cases hwk : w < n + k
      · exact Or.inr ⟨w, hwk, fun x => by
          rw [key k g hg (ρ x), hw (fun i => if i < n + k then val (ρ x) i else false) (hc x)]
          exact if_pos hwk⟩
      · exact Or.inl ⟨false, fun x => by
          rw [key k g hg (ρ x), hw (fun i => if i < n + k then val (ρ x) i else false) (hc x)]
          exact if_neg hwk⟩
  have vnot : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∀ q : ℕ, q ∈ eff g → q < n + k → ∀ x, val x (n + k) = !val x q := by
    intro k g hg hop q hq hlt x
    rw [key k g hg x, gnot g hop q hq]
    simp only [if_pos hlt]
  have vor : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ q : ℕ, q ∈ eff g → q < n + k → ∀ x, val x q = true → val x (n + k) = true := by
    intro k g hg hop q hq hlt x hx
    rw [key k g hg x]
    refine gor g hop q hq _ ?_
    show (if q < n + k then val x q else false) = true
    rw [if_pos hlt]
    exact hx
  have vand : ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ q : ℕ, q ∈ eff g → ∀ x, (q < n + k → val x q = false) → val x (n + k) = false := by
    intro k g hg hop q hq x hx
    rw [key k g hg x]
    refine gand g hop q hq _ ?_
    show (if q < n + k then val x q else false) = false
    by_cases hlt : q < n + k
    · rw [if_pos hlt]; exact hx hlt
    · rw [if_neg hlt]
  have hsz : C.size = C.gates.length := rfl
  have NR : ∀ j, j < C.gates.length → ¬ Red id j := by
    intro j hj hR
    rw [hRed] at hR
    simp only [hval] at hR
    have hh := h1 n C id {j} hF (Or.inl rfl) (by
      obtain ⟨x, y, hxy⟩ := hncf
      refine ⟨x, y, ?_⟩
      rw [← hcomp] at hxy
      exact hxy) (by
      intro j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      exact ⟨hj, hR⟩)
    have e : (fun x : Fin n → Bool => C.eval (List.ofFn (id x))) = PEqualNP.MetaComplexity.NestedCover.graphFun G A := hcomp
    rw [e] at hh
    have := hmin _ hh
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨upd, hupd⟩ : ∃ upd : (Fin n → Bool) → Fin n → Bool, ∀ x, upd x = Function.update x v false := ⟨_, fun _ => rfl⟩
  have N3 : ∀ S : Finset ℕ, (∀ j ∈ S, j < C.gates.length ∧ Red upd j) → S.card ≤ 3 := by
    intro S hS
    by_contra hc
    apply hno
    have hh := h1 n C upd S hF (Or.inr ⟨v, funext hupd⟩) (by
      obtain ⟨x, y, hxy⟩ := hnc
      refine ⟨x, y, ?_⟩
      rw [← hcomp, ← hupd, ← hupd] at hxy
      exact hxy) (by
      intro j hj
      have h' := (hS j hj).2
      rw [hRed] at h'
      simp only [hval] at h'
      exact ⟨(hS j hj).1, h'⟩)
    have hle : S.card ≤ C.gates.length := by
      have hsub : S ⊆ Finset.range C.gates.length := fun j hj => Finset.mem_range.mpr (hS j hj).1
      simpa using Finset.card_le_card hsub
    refine ⟨v, hvA, C.size - S.card, by omega, ?_⟩
    have e : (fun x : Fin n → Bool => C.eval (List.ofFn (upd x))) = fun x => PEqualNP.MetaComplexity.NestedCover.graphFun G A (Function.update x v false) := by
      funext x
      rw [hupd]
      exact congrFun hcomp _
    rw [e] at hh
    exact hh
  have vfalse : ∀ x, val (upd x) v.val = false := by
    intro x
    rw [hin (upd x) v.val v.isLt, hupd]
    simp
  have HR : ∀ p, p < C.gates.length → (∃ c : Bool, ∀ x, val (upd x) (n + p) = c) → ∃ (m : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h ∧ n + p ∈ eff h ∧ p < m := by
    rintro p hp ⟨c, hc⟩
    by_cases hB : ∃ (m : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h ∧ n + p ∈ eff h
    · obtain ⟨m, h, hm, hph⟩ := hB
      by_cases hle : m ≤ p
      · exact absurd (gl id m h hm (n + p) hph ⟨false, fun x => if_neg (by omega)⟩) (NR m (klt m h hm))
      · exact ⟨m, h, hm, hph, by omega⟩
    · exfalso
      by_cases hout : C.output = n + p
      · obtain ⟨x, y, hxy⟩ := hnc
        apply hxy
        rw [← hupd, ← hupd, hout2 (upd x), hout2 (upd y), hout, hc x, hc y]
      · have hh := h2 n C p hF hp hout (by
          intro g' hg' hmem
          obtain ⟨m, hm⟩ := List.getElem?_of_mem hg'
          exact hB ⟨m, g', hm, by rw [heff]; exact hmem⟩)
        have e : (fun x : Fin n → Bool => C.eval (List.ofFn x)) = PEqualNP.MetaComplexity.NestedCover.graphFun G A := hcomp
        rw [e] at hh
        have := hmin _ hh
        omega
  have four : ∀ a b c d : ℕ, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → (a < C.gates.length ∧ Red upd a) → (b < C.gates.length ∧ Red upd b) → (c < C.gates.length ∧ Red upd c) → (d < C.gates.length ∧ Red upd d) → False := by
    intro a b c d e1 e2 e3 e4 e5 e6 ha hb hc hd
    have hcard : 4 ≤ ({a, b, c, d} : Finset ℕ).card := by
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega), Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega), Finset.card_pair e6]
    have := N3 {a, b, c, d} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd)
    omega
  have pos2 : ∀ (p : PEqualNP.CircuitLowerBounds.Gate → Bool) (l : List PEqualNP.CircuitLowerBounds.Gate) (i : ℕ), 2 ≤ (l.filter p).length → ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), j ≠ i ∧ l[j]? = some h ∧ p h = true := by
    intro p l
    induction l with
    | nil => intro i h; simp at h
    | cons a t ih =>
      intro i h
      by_cases hpa : p a = true
      · rcases i with _ | i'
        · rw [List.filter_cons_of_pos hpa, List.length_cons] at h
          obtain ⟨b, hb⟩ := List.exists_mem_of_length_pos (by omega : 0 < (t.filter p).length)
          obtain ⟨hbt, hpb⟩ := List.mem_filter.mp hb
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hbt
          exact ⟨j + 1, b, by omega, by simpa using hj, hpb⟩
        · exact ⟨0, a, by omega, by simp, hpa⟩
      · rw [List.filter_cons_of_neg hpa] at h
        obtain ⟨j, h', hj, hjt, hp⟩ := ih (i - 1) h
        refine ⟨j + 1, h', ?_, by simpa using hjt, hp⟩
        rcases i with _ | i'
        · omega
        · simp only [Nat.add_sub_cancel] at hj
          omega
  have uniqf : ∀ (p : PEqualNP.CircuitLowerBounds.Gate → Bool) (l : List PEqualNP.CircuitLowerBounds.Gate) (k : ℕ) (r : PEqualNP.CircuitLowerBounds.Gate), l[k]? = some r → p r = true → (∀ (m : ℕ) (r' : PEqualNP.CircuitLowerBounds.Gate), l[m]? = some r' → p r' = true → m = k) → l.filter p = [r] := by
    intro p l
    induction l with
    | nil => intro k r h; simp at h
    | cons a t ih =>
      intro k r hk hp hu
      rcases k with _ | k'
      · have har : a = r := by simpa using hk
        subst har
        rw [List.filter_cons_of_pos hp]
        have hnil : t.filter p = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb hpb
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
          have := hu (j + 1) b (by simpa using hj) hpb
          omega
        rw [hnil]
      · have hna : ¬ p a = true := by
          intro hpa
          have := hu 0 a (by simp) hpa
          omega
        rw [List.filter_cons_of_neg hna]
        exact ih k' r (by simpa using hk) hp (fun m r' hm hp' => by
          have := hu (m + 1) r' (by simpa using hm) hp'
          omega)
  have effc : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ), (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains w = true ↔ w ∈ eff g := by
    intro g w
    rw [heff]
    exact List.contains_iff_mem
  have opc : ∀ (m : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h' → h'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h'.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro m h' hm
    have := (hFg m h' hm).1
    simpa [Set.mem_insert_iff] using this
  obtain ⟨hgmem, hgc⟩ := List.mem_filter.mp hgR
  obtain ⟨i, hgi⟩ := List.getElem?_of_mem hgmem
  have hgv : v.val ∈ eff g := (effc g v.val).mp hgc
  obtain ⟨jh, h, hjhi, hh, hhc⟩ := pos2 (fun g => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v.val) C.gates i (le_of_eq hlen2.symm)
  have hhv : v.val ∈ eff h := (effc h v.val).mp hhc
  have hvn := v.isLt
  have valg : ∀ x, val x (n + i) = !x v := by
    intro x
    rw [vnot i g hgi hgnot v.val hgv (by omega) x, hin x v.val hvn]
  have cstg : ∀ x, val (upd x) (n + i) = true := by
    intro x
    rw [valg, hupd]
    simp
  have redv : ∀ (m : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h' → v.val ∈ eff h' → m < C.gates.length ∧ Red upd m := by
    intro m h' hm hv'
    exact ⟨klt m h' hm, gl upd m h' hm v.val hv' ⟨false, fun x => by rw [if_pos (by omega)]; exact vfalse x⟩⟩
  have redc : ∀ p : ℕ, (∃ c : Bool, ∀ x, val (upd x) (n + p) = c) → ∀ (m : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h' → n + p ∈ eff h' → m < C.gates.length ∧ Red upd m := by
    rintro p ⟨c, hc⟩ m h' hm hv'
    refine ⟨klt m h' hm, gl upd m h' hm (n + p) hv' ?_⟩
    by_cases hlt : n + p < n + m
    · exact ⟨c, fun x => by rw [if_pos hlt]; exact hc x⟩
    · exact ⟨false, fun x => if_neg hlt⟩
  have NB : ∀ (m : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some h' → v.val ∈ eff h' → n + i ∈ eff h' → False := by
    intro m h' hm hv' hi'
    by_cases hle : m ≤ i
    · exact NR m (klt m h' hm) (gl id m h' hm (n + i) hi' ⟨false, fun x => if_neg (by omega)⟩)
    · rcases opc m h' hm with ho | ho | ho
      · refine NR m (klt m h' hm) ((hRed id m).mpr (Or.inl ⟨false, fun x => ?_⟩))
        show val x (n + m) = false
        cases hx : x v
        · exact vand m h' hm ho v.val hv' x (fun _ => by rw [hin x v.val hvn]; exact hx)
        · exact vand m h' hm ho (n + i) hi' x (fun _ => by rw [valg, hx]; rfl)
      · refine NR m (klt m h' hm) ((hRed id m).mpr (Or.inl ⟨true, fun x => ?_⟩))
        show val x (n + m) = true
        cases hx : x v
        · exact vor m h' hm ho (n + i) hi' (by omega) x (by rw [valg, hx]; rfl)
        · exact vor m h' hm ho v.val hv' (by omega) x (by rw [hin x v.val hvn]; exact hx)
      · have := gnot1 h' ho _ _ hv' hi'
        omega
  have hii : i < C.gates.length := klt i g hgi
  obtain ⟨k, r, hrk, hrg, hik⟩ := HR i hii ⟨true, cstg⟩
  have hkjh : k ≠ jh := by
    intro e
    have hh' : C.gates[k]? = some h := by rw [e]; exact hh
    have hrh : r = h := Option.some.inj (hrk.symm.trans hh')
    exact NB k h hh' hhv (hrh ▸ hrg)
  have Ri := redv i g hgi hgv
  have Rj := redv jh h hh hhv
  have Rk := redc i ⟨true, cstg⟩ k r hrk hrg
  have uniq : ∀ (m : ℕ) (r' : PEqualNP.CircuitLowerBounds.Gate), C.gates[m]? = some r' → n + i ∈ eff r' → m = k := by
    intro m r' hm hr'
    by_contra hne
    have hmi : m ≠ i := by
      intro e
      have hg' : C.gates[m]? = some g := by rw [e]; exact hgi
      have hrg' : r' = g := Option.some.inj (hm.symm.trans hg')
      have := gnot1 g hgnot _ _ hgv (hrg' ▸ hr')
      omega
    have hmjh : m ≠ jh := by
      intro e
      have hh' : C.gates[m]? = some h := by rw [e]; exact hh
      have hrh : r' = h := Option.some.inj (hm.symm.trans hh')
      exact NB m h hh' hhv (hrh ▸ hr')
    exact four i jh k m (Ne.symm hjhi) (by omega) (Ne.symm hmi) (Ne.symm hkjh) (Ne.symm hmjh) (Ne.symm hne) Ri Rj Rk (redc i ⟨true, cstg⟩ m r' hm hr')
  have rand : r.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases opc k r hrk with ho | ho | ho
    · exact ho
    · exfalso
      have cstr : ∀ x, val (upd x) (n + k) = true := fun x => vor k r hrk ho (n + i) hrg (by omega) (upd x) (cstg x)
      obtain ⟨m, hm', hmk, hmr, hkm⟩ := HR k (klt k r hrk) ⟨true, cstr⟩
      by_cases e : m = jh
      · have hh' : C.gates[m]? = some h := by rw [e]; exact hh
        have hrh : hm' = h := Option.some.inj (hmk.symm.trans hh')
        have hhr : n + k ∈ eff h := hrh ▸ hmr
        rcases opc jh h hh with ho' | ho' | ho'
        · have csth : ∀ x, val (upd x) (n + jh) = false := fun x => vand jh h hh ho' v.val hhv (upd x) (fun _ => vfalse x)
          obtain ⟨m2, hq2, hm2, hm2r, hlt2⟩ := HR jh (klt jh h hh) ⟨false, csth⟩
          exact four i jh k m2 (Ne.symm hjhi) (by omega) (by omega) (Ne.symm hkjh) (by omega) (by omega) Ri Rj Rk (redc jh ⟨false, csth⟩ m2 hq2 hm2 hm2r)
        · refine NR jh (klt jh h hh) ((hRed id jh).mpr (Or.inl ⟨true, fun x => ?_⟩))
          show val x (n + jh) = true
          cases hx : x v
          · exact vor jh h hh ho' (n + k) hhr (by omega) x (vor k r hrk ho (n + i) hrg (by omega) x (by rw [valg, hx]; rfl))
          · exact vor jh h hh ho' v.val hhv (by omega) x (by rw [hin x v.val hvn]; exact hx)
        · have := gnot1 h ho' _ _ hhv hhr
          omega
      · exact four i jh k m (Ne.symm hjhi) (by omega) (by omega) (Ne.symm hkjh) (Ne.symm e) (by omega) Ri Rj Rk (redc k ⟨true, cstr⟩ m hm' hmk hmr)
    · exfalso
      refine NR k (klt k r hrk) ((hRed id k).mpr (Or.inr ⟨v.val, by omega, fun x => ?_⟩))
      show val x (n + k) = val x v.val
      rw [vnot k r hrk ho (n + i) hrg (by omega) x, valg x, Bool.not_not, hin x v.val hvn]
  have hor : h.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    rcases opc jh h hh with ho' | ho' | ho'
    · exfalso
      have csth : ∀ x, val (upd x) (n + jh) = false := fun x => vand jh h hh ho' v.val hhv (upd x) (fun _ => vfalse x)
      obtain ⟨m2, hq2, hm2, hm2r, hlt2⟩ := HR jh (klt jh h hh) ⟨false, csth⟩
      have hm2i : m2 ≠ i := by
        intro e
        have hg' : C.gates[m2]? = some g := by rw [e]; exact hgi
        have hrg' : hq2 = g := Option.some.inj (hm2.symm.trans hg')
        have := gnot1 g hgnot _ _ hgv (hrg' ▸ hm2r)
        omega
      have hm2k : m2 ≠ k := by
        intro e
        have hr' : C.gates[m2]? = some r := by rw [e]; exact hrk
        have hrr : hq2 = r := Option.some.inj (hm2.symm.trans hr')
        have hrj : n + jh ∈ eff r := hrr ▸ hm2r
        refine NR k (klt k r hrk) ((hRed id k).mpr (Or.inl ⟨false, fun x => ?_⟩))
        show val x (n + k) = false
        cases hx : x v
        · exact vand k r hrk rand (n + jh) hrj x (fun _ => vand jh h hh ho' v.val hhv x (fun _ => by rw [hin x v.val hvn]; exact hx))
        · exact vand k r hrk rand (n + i) hrg x (fun _ => by rw [valg, hx]; rfl)
      exact four i jh k m2 (Ne.symm hjhi) (by omega) (Ne.symm hm2i) (Ne.symm hkjh) (by omega) (Ne.symm hm2k) Ri Rj Rk (redc jh ⟨false, csth⟩ m2 hq2 hm2 hm2r)
    · exact ho'
    · exfalso
      have valh : ∀ x, val x (n + jh) = !x v := by
        intro x
        rw [vnot jh h hh ho' v.val hhv (by omega) x, hin x v.val hvn]
      rcases Nat.lt_or_gt_of_ne hjhi with hlt | hlt
      · refine NR i hii ((hRed id i).mpr (Or.inr ⟨n + jh, by omega, fun x => ?_⟩))
        show val x (n + i) = val x (n + jh)
        rw [valg, valh]
      · refine NR jh (klt jh h hh) ((hRed id jh).mpr (Or.inr ⟨n + i, by omega, fun x => ?_⟩))
        show val x (n + jh) = val x (n + i)
        rw [valg, valh]
  apply hno
  refine h3 n G A C hdeg hgirth hA hF hcomp hmin hread ?_ hcount
  refine ⟨v, hvA, hlen2, ⟨h, List.mem_filter.mpr ⟨List.mem_of_getElem? hh, hhc⟩, hor⟩, i, g, hgi, hgR, hgnot, r, ?_, rand⟩
  exact uniqf _ C.gates k r hrk ((effc r (n + i)).mpr hrg) (fun m r' hm hp => uniq m r' hm ((effc r' (n + i)).mp hp))
