import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2638_3
    (hOne : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      H = G.deleteEdges (G.incidenceSet z) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn x)) s → C.size ≤ s) →
      (∃ v : Fin n, (∃ u : Fin n, H.Adj v u) ∧
        (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 1 ∧
        (∀ g ∈ C.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val = true →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          ∃ w ∈ g.inputs, n ≤ w)) →
      H.edgeSet.ncard + k ≤ C.size + 1)
    (hTwo : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      H = G.deleteEdges (G.incidenceSet z) →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn x)) s → C.size ≤ s) →
      (∀ v : Fin n, (∃ u : Fin n, H.Adj v u) →
        2 ≤ (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) →
      (∃ v : Fin n, (H.neighborSet v).ncard = 3 ∧
        (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 2) →
      H.edgeSet.ncard + k ≤ C.size + 1) :
    (∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ)) := by
  classical
  intro n k s G A z f hdeg hgirth hnoA hE hzA hf htau hs
  let H : SimpleGraph (Fin n) := G.deleteEdges (G.incidenceSet z)
  have hH_eq : H = G.deleteIncidenceSet z := rfl
  have hdegG : ∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    intro v
    by_cases hv : v ∈ A
    · left
      have hempty : G.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun w hw => hnoA v w hw hv)
      simp [hempty]
    · exact Or.inr (hdeg v hv)
  have hzdeg : (G.neighborSet z).ncard = 3 := hdeg z hzA
  have hHE : ∃ u0 v0 : Fin n, H.Adj u0 v0 := by
    have hznb : (G.neighborSet z).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨u0, hu0⟩ := hznb
    have hzu0 : G.Adj z u0 := hu0
    have hu0z : u0 ≠ z := hzu0.ne.symm
    have hu0A : u0 ∉ A := hnoA u0 z hzu0.symm
    have hu0deg : (G.neighborSet u0).ncard = 3 := hdeg u0 hu0A
    by_contra hno
    have hsub : G.neighborSet u0 ⊆ ({z} : Set (Fin n)) := by
      intro v0 hv0
      by_contra hv0z
      have hv0ne : v0 ≠ z := by simpa only [Set.mem_singleton_iff] using hv0z
      exact hno ⟨u0, v0, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hv0, hu0z, hv0ne⟩⟩
    have hle := Set.ncard_le_ncard hsub
    simp [hu0deg] at hle
  have hnoAH : ∀ u v : Fin n, H.Adj u v → u ∉ A :=
    fun u v huv => hnoA u v (SimpleGraph.deleteIncidenceSet_adj.mp huv).1
  have hdegH : ∀ v : Fin n,
      (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 2 ∨ (H.neighborSet v).ncard = 3 := by
    intro v
    by_cases hvz : v = z
    · subst hvz
      left
      have hempty : H.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun w hw => (SimpleGraph.deleteIncidenceSet_adj.mp hw).2.1 rfl)
      simp [hempty]
    · rcases hdegG v with h0 | h3
      · left
        have hsub : H.neighborSet v ⊆ G.neighborSet v :=
          fun w hw => (SimpleGraph.deleteIncidenceSet_adj.mp hw).1
        have hle := Set.ncard_le_ncard hsub
        omega
      · have heq : H.neighborSet v = G.neighborSet v \ {z} := by
          ext w
          have hadj : H.Adj v w ↔ G.Adj v w ∧ v ≠ z ∧ w ≠ z := by
            simpa [hH_eq] using (SimpleGraph.deleteIncidenceSet_adj (G := G) (x := z) (v₁ := v) (v₂ := w))
          simp [SimpleGraph.mem_neighborSet, hadj, hvz]
        rw [heq]
        by_cases hzv : z ∈ G.neighborSet v
        · right; left
          have hdiff := Set.ncard_sdiff_singleton_add_one hzv (Set.toFinite _)
          omega
        · right; right
          rw [Set.sdiff_singleton_eq_self hzv]
          exact h3
  have hk_le_edges : k ≤ H.edgeSet.ncard := by
    let pick : Sym2 (Fin n) → Fin n := fun e =>
      Classical.choose (show ∃ u : Fin n, u ∈ e by
        induction e using Sym2.ind with
        | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩)
    have hpick : ∀ e : Sym2 (Fin n), pick e ∈ e := fun e =>
      Classical.choose_spec (show ∃ u : Fin n, u ∈ e by
        induction e using Sym2.ind with
        | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩)
    let T : Finset (Fin n) := H.edgeFinset.image pick
    have hcov : ∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T := by
      intro u v huv
      have he : s(u, v) ∈ H.edgeFinset := H.mem_edgeFinset.mpr huv
      have hwT : pick s(u, v) ∈ T := Finset.mem_image_of_mem pick he
      rcases Sym2.mem_iff.mp (hpick s(u, v)) with hpu | hpv
      · exact Or.inl (hpu ▸ hwT)
      · exact Or.inr (hpv ▸ hwT)
    have hkT : k ≤ T.card := htau T hcov
    have hTle : T.card ≤ H.edgeFinset.card := Finset.card_image_le
    have hedgeEq : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    omega
  have getD_snoc_lt : ∀ {α : Type} (w : List α) (v d : α) (i : ℕ), i < w.length →
      (w ++ [v]).getD i d = w.getD i d := by
    clear * -
    intro α w v d i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ {α : Type} (w : List α) (v d : α) (i : ℕ), i = w.length →
      (w ++ [v]).getD i d = v := by
    clear * -
    intro α w v d i hi
    subst hi
    simp
  have ofFn_getD_lt : ∀ {α : Type} (x : Fin n → α) (d : α) (i : ℕ) (hi : i < n),
      (List.ofFn x).getD i d = x ⟨i, hi⟩ := by
    clear * -
    intro α x d i hi
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
  let wiresFrom : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append : ∀ (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    clear * -
    intro gs₁ gs₂ w
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    clear * -
    intro gs
    induction gs with
    | nil => intro w; simp [wiresFrom]
    | cons g gs ih =>
      intro w
      have h1 : wiresFrom (g :: gs) w =
          wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [h1, ih]
      simp
      omega
  have wiresFrom_keep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
    clear * - getD_snoc_lt
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g rest ih =>
      intro w i hi
      have hstep : wiresFrom (g :: rest) w =
          wiresFrom rest (w ++ [g.op.eval (g.inputs.map fun k0 => w.getD k0 false)]) := rfl
      rw [hstep, ih _ i (by simp; omega), getD_snoc_lt _ _ _ _ hi]
  let reads : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun v g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  have wiresFrom_agree_eff : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (v : ℕ) (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      (∀ g ∈ gs, reads v g = false) →
      ∀ i, i ≠ v → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    clear * - getD_snoc_lt getD_snoc_eq
    have gate_eval_agree : ∀ (g : PEqualNP.CircuitLowerBounds.Gate),
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
        g.inputs.length ≤ 2 → ∀ (w₁ w₂ : List Bool) (v : ℕ),
        (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
        reads v g = false →
        g.op.eval (g.inputs.map fun i => w₁.getD i false) =
          g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
      intro g hop hlen w₁ w₂ v hag hnr
      have hnr' : v ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
        intro hm
        have ht : reads v g = true := List.contains_iff_mem.2 hm
        rw [hnr] at ht
        cases ht
      have hop' : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
      rcases hop' with h | h | h
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : PEqualNP.CircuitLowerBounds.GateOp.and.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : PEqualNP.CircuitLowerBounds.GateOp.or.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · rw [h] at hnr' ⊢
        have : PEqualNP.CircuitLowerBounds.GateOp.not.eval [false] = true := rfl
        rw [this] at hnr'
        rcases hgins : g.inputs with _ | ⟨a, rest⟩
        · rfl
        · rw [hgins] at hnr'
          have hav : a ≠ v := fun he => hnr' (by simp [he])
          show (!(w₁.getD a false)) = (!(w₂.getD a false))
          rw [hag a hav]
    intro gs
    induction gs with
    | nil => intro _ v w₁ w₂ _ hag _ i hi; exact hag i hi
    | cons g rest ih =>
      intro hok v w₁ w₂ hlen hag hnr i hi
      have h1 : wiresFrom (g :: rest) w₁ =
          wiresFrom rest (w₁ ++ [g.op.eval (g.inputs.map fun k0 => w₁.getD k0 false)]) := rfl
      have h2 : wiresFrom (g :: rest) w₂ =
          wiresFrom rest (w₂ ++ [g.op.eval (g.inputs.map fun k0 => w₂.getD k0 false)]) := rfl
      rw [h1, h2]
      have hge := gate_eval_agree g (hok g List.mem_cons_self).1 (hok g List.mem_cons_self).2
        w₁ w₂ v hag (hnr g List.mem_cons_self)
      apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) v _ _
        (by simp [hlen]) _ (fun g' hg' => hnr g' (List.mem_cons_of_mem _ hg')) i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hag j hj
      · by_cases heq : j = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega), hge]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨t, htA, g0, htg0, hg0⟩ :
      ∃ t0 : ℕ, t0 + A.card ≤ s ∧ ∃ g0 : (Fin n → Bool) → Bool,
        PEqualNP.MetaComplexity.HasCircuitSize n g0 t0 ∧
        ∀ x : Fin n → Bool, g0 x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
    clear * - hHE hnoAH hf hs getD_snoc_lt getD_snoc_eq ofFn_getD_lt wiresFrom_append
      wiresFrom_length wiresFrom_keep wiresFrom_agree_eff
    let sval : List Bool → Bool ⊕ ℕ → Bool := fun w st =>
      Sum.elim id (fun j => w.getD j false) st
    let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m st =>
      Sum.elim (fun _ => True) (fun j => j < m) st
    obtain ⟨simplify, simplify_ok, simplify_drop, simplify_sound⟩ :
        ∃ simplify : PEqualNP.CircuitLowerBounds.GateOp → ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ),
          (∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate),
            g ∈ (simplify op m ins).1.toList →
            g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
          (∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
            op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
            ins.length ≤ 2 →
            (∃ c : Bool, Sum.inl c ∈ ins.take (bif op.eval [false] then 1 else 2)) →
            (simplify op m ins).1 = none) ∧
          (∀ (op : PEqualNP.CircuitLowerBounds.GateOp),
            op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
            ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
            (∀ st ∈ ins, svalid w.length st) →
            svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
            sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
              op.eval (ins.map (sval w))) := by
      clear * - getD_snoc_eq
      let and2 : ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun m a b =>
        Sum.elim (fun c => (none, bif c then b else Sum.inl false))
          (fun j => Sum.elim (fun d => (none, bif d then Sum.inr j else Sum.inl false))
            (fun l => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [j, l]⟩, Sum.inr m)) b) a
      let or2 : ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun m a b =>
        Sum.elim (fun c => (none, bif c then Sum.inl true else b))
          (fun j => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr j))
            (fun l => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [j, l]⟩, Sum.inr m)) b) a
      let simpFn : PEqualNP.CircuitLowerBounds.GateOp → ℕ → List (Bool ⊕ ℕ) → Option PEqualNP.CircuitLowerBounds.Gate × (Bool ⊕ ℕ) := fun op m ins =>
        PEqualNP.CircuitLowerBounds.GateOp.casesOn op
          (List.casesOn ins (none, Sum.inl true) (fun a l1 =>
            List.casesOn l1 (none, a) (fun b l2 =>
              List.casesOn l2 (and2 m a b) (fun _ _ => (none, Sum.inl false)))))
          (List.casesOn ins (none, Sum.inl false) (fun a l1 =>
            List.casesOn l1 (none, a) (fun b l2 =>
              List.casesOn l2 (or2 m a b) (fun _ _ => (none, Sum.inl false)))))
          (List.casesOn ins (none, Sum.inl true) (fun a _ =>
            Sum.elim (fun c => (none, Sum.inl (!c)))
              (fun j => (some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [j]⟩, Sum.inr m)) a))
          (fun _ => (none, Sum.inl false))
          (none, Sum.inl false)
      refine ⟨simpFn, ?_, ?_, ?_⟩
      · intro op m ins g hg
        cases op <;> dsimp only [simpFn] at hg
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · cases hg
          · cases hg
          · rcases a with c | j <;> rcases b with d | l
            · cases hg
            · cases hg
            · cases hg
            · simp only [and2, Sum.elim_inr, Option.toList_some, List.mem_singleton] at hg
              subst hg; simp
          · cases hg
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · cases hg
          · cases hg
          · rcases a with c | j <;> rcases b with d | l
            · cases hg
            · cases hg
            · cases hg
            · simp only [or2, Sum.elim_inr, Option.toList_some, List.mem_singleton] at hg
              subst hg; simp
          · cases hg
        · rcases ins with _ | ⟨a, l⟩
          · cases hg
          · rcases a with c | j
            · cases hg
            · simp only [Sum.elim_inr, Option.toList_some, List.mem_singleton] at hg
              subst hg; simp
        · cases hg
        · cases hg
      · intro op m ins hop hlen hex_c
        obtain ⟨c, hc⟩ := hex_c
        have hop' : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
        rcases hop' with rfl | rfl | rfl
        · have htake : ins.take (bif PEqualNP.CircuitLowerBounds.GateOp.and.eval [false] then 1 else 2) = ins :=
            List.take_of_length_le hlen
          rw [htake] at hc
          rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · cases hc
          · rfl
          · rcases List.mem_cons.mp hc with rfl | hcb
            · rfl
            · rcases List.mem_singleton.mp hcb with rfl
              cases a <;> rfl
          · simp at hlen
        · have htake : ins.take (bif PEqualNP.CircuitLowerBounds.GateOp.or.eval [false] then 1 else 2) = ins :=
            List.take_of_length_le hlen
          rw [htake] at hc
          rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · cases hc
          · rfl
          · rcases List.mem_cons.mp hc with rfl | hcb
            · rfl
            · rcases List.mem_singleton.mp hcb with rfl
              cases a <;> rfl
          · simp at hlen
        · have htake : ins.take (bif PEqualNP.CircuitLowerBounds.GateOp.not.eval [false] then 1 else 2) = ins.take 1 := rfl
          rw [htake] at hc
          rcases ins with _ | ⟨a, l⟩
          · cases hc
          · rcases List.mem_singleton.mp hc with rfl
            rfl
      · intro op hop w ins hlen hv
        have hop' : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
        rcases hop' with rfl | rfl | rfl
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · exact ⟨trivial, rfl⟩
          · have ha := hv a List.mem_cons_self
            refine ⟨ha, ?_⟩
            show sval w a = PEqualNP.CircuitLowerBounds.GateOp.and.eval [sval w a]
            cases sval w a <;> rfl
          · have ha := hv a List.mem_cons_self
            have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
            rcases a with c | j
            · cases c
              · exact ⟨trivial, rfl⟩
              · refine ⟨hb, ?_⟩
                show sval w b = PEqualNP.CircuitLowerBounds.GateOp.and.eval [true, sval w b]
                cases sval w b <;> rfl
            · rcases b with d | l
              · cases d
                · refine ⟨trivial, ?_⟩
                  show false = PEqualNP.CircuitLowerBounds.GateOp.and.eval [w.getD j false, false]
                  cases w.getD j false <;> rfl
                · refine ⟨ha, ?_⟩
                  show w.getD j false = PEqualNP.CircuitLowerBounds.GateOp.and.eval [w.getD j false, true]
                  cases w.getD j false <;> rfl
              · refine ⟨Nat.lt_succ_self w.length, ?_⟩
                show (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval [w.getD j false, w.getD l false]]).getD w.length false =
                  PEqualNP.CircuitLowerBounds.GateOp.and.eval [w.getD j false, w.getD l false]
                exact getD_snoc_eq w _ false w.length rfl
          · simp at hlen
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · exact ⟨trivial, rfl⟩
          · have ha := hv a List.mem_cons_self
            refine ⟨ha, ?_⟩
            show sval w a = PEqualNP.CircuitLowerBounds.GateOp.or.eval [sval w a]
            cases sval w a <;> rfl
          · have ha := hv a List.mem_cons_self
            have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
            rcases a with c | j
            · cases c
              · refine ⟨hb, ?_⟩
                show sval w b = PEqualNP.CircuitLowerBounds.GateOp.or.eval [false, sval w b]
                cases sval w b <;> rfl
              · exact ⟨trivial, rfl⟩
            · rcases b with d | l
              · cases d
                · refine ⟨ha, ?_⟩
                  show w.getD j false = PEqualNP.CircuitLowerBounds.GateOp.or.eval [w.getD j false, false]
                  cases w.getD j false <;> rfl
                · refine ⟨trivial, ?_⟩
                  show true = PEqualNP.CircuitLowerBounds.GateOp.or.eval [w.getD j false, true]
                  cases w.getD j false <;> rfl
              · refine ⟨Nat.lt_succ_self w.length, ?_⟩
                show (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [w.getD j false, w.getD l false]]).getD w.length false =
                  PEqualNP.CircuitLowerBounds.GateOp.or.eval [w.getD j false, w.getD l false]
                exact getD_snoc_eq w _ false w.length rfl
          · simp at hlen
        · rcases ins with _ | ⟨a, l⟩
          · exact ⟨trivial, rfl⟩
          · rcases a with c | j
            · exact ⟨trivial, rfl⟩
            · refine ⟨Nat.lt_succ_self w.length, ?_⟩
              show (w ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval [w.getD j false]]).getD w.length false =
                PEqualNP.CircuitLowerBounds.GateOp.not.eval (w.getD j false :: l.map (sval w))
              rw [getD_snoc_eq w _ false w.length rfl]
              rfl
    obtain ⟨elim, elim_len_drop, elim_ok, elim_sound⟩ :
        ∃ elim : List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate,
          (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
            (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) (v : ℕ),
            v < acc.1.length → acc.1.getD v (Sum.inl false) = Sum.inl false →
            (∃ g ∈ gs, reads v g = true) →
            (elim gs acc).2.length + 1 ≤ acc.2.length + gs.length) ∧
          (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
            (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
            (∀ g ∈ acc.2, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ g ∈ (elim gs acc).2, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
          (∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
            (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) (w_old w_new : List Bool),
            acc.1.length = w_old.length →
            w_new.length = n + acc.2.length →
            (∀ i : ℕ, svalid w_new.length (acc.1.getD i (Sum.inl false)) ∧
              sval w_new (acc.1.getD i (Sum.inl false)) = w_old.getD i false) →
            ∀ i : ℕ,
              sval (wiresFrom ((elim gs acc).2.drop acc.2.length) w_new)
                ((elim gs acc).1.getD i (Sum.inl false)) =
              (wiresFrom gs w_old).getD i false) := by
      clear * - getD_snoc_lt getD_snoc_eq wiresFrom_append wiresFrom_length wiresFrom_keep
        simplify_ok simplify_drop simplify_sound
      let elimStep : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate := fun acc g =>
        let res := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
        (acc.1 ++ [res.2], acc.2 ++ res.1.toList)
      let elimFn : List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate → List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate := fun gs acc =>
        gs.foldl elimStep acc
      have opt_toList_le : ∀ o : Option PEqualNP.CircuitLowerBounds.Gate, o.toList.length ≤ 1 := by
        intro o; cases o <;> simp
      have elim_len_le : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
          (elimFn gs acc).2.length ≤ acc.2.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro acc; simp [elimFn]
        | cons g rest ih =>
          intro acc
          have hstep : elimFn (g :: rest) acc = elimFn rest (elimStep acc g) := rfl
          rw [hstep]
          have h1 := ih (elimStep acc g)
          have h2 : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
            simp only [elimStep, List.length_append]
            have := opt_toList_le (simplify g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
            omega
          simp only [List.length_cons]
          omega
      refine ⟨elimFn, ?_, ?_, ?_⟩
      · intro gs
        induction gs with
        | nil =>
          intro _ _ _ _ _ hex_g
          obtain ⟨_, hm, _⟩ := hex_g
          cases hm
        | cons g rest ih =>
          intro hok acc v hvlen hvval hex_g
          obtain ⟨g1, hg1, hr1⟩ := hex_g
          have hstep : elimFn (g :: rest) acc = elimFn rest (elimStep acc g) := rfl
          rw [hstep]
          by_cases hrg : reads v g = true
          · have hmem : v ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) :=
              List.contains_iff_mem.mp hrg
            have hinl : Sum.inl false ∈
                (g.inputs.map fun i => acc.1.getD i (Sum.inl false)).take
                  (bif g.op.eval [false] then 1 else 2) := by
              rw [← List.map_take]
              exact List.mem_map.mpr ⟨v, hmem, hvval⟩
            have hnone := simplify_drop g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
              (hok g List.mem_cons_self).1 (by simp; exact (hok g List.mem_cons_self).2)
              ⟨false, hinl⟩
            have heq2 : (elimStep acc g).2.length = acc.2.length := by
              dsimp only [elimStep]
              rw [hnone]
              simp
            have hle := elim_len_le rest (elimStep acc g)
            simp only [List.length_cons]
            omega
          · have hg1_rest : g1 ∈ rest := by
              rcases List.mem_cons.mp hg1 with rfl | hm
              · exact absurd hr1 hrg
              · exact hm
            have hvlen' : v < (elimStep acc g).1.length := by
              simp only [elimStep, List.length_append, List.length_singleton]; omega
            have hvval' : (elimStep acc g).1.getD v (Sum.inl false) = Sum.inl false := by
              simp only [elimStep]
              rw [getD_snoc_lt _ _ _ _ hvlen]
              exact hvval
            have h2 : (elimStep acc g).2.length ≤ acc.2.length + 1 := by
              simp only [elimStep, List.length_append]
              have := opt_toList_le (simplify g.op (n + acc.2.length)
                (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
              omega
            have hih := ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
              (elimStep acc g) v hvlen' hvval' ⟨g1, hg1_rest, hr1⟩
            simp only [List.length_cons]
            omega
      · intro gs
        induction gs with
        | nil => intro _ acc hacc; exact hacc
        | cons g rest ih =>
          intro hok acc hacc
          have hstep : elimFn (g :: rest) acc = elimFn rest (elimStep acc g) := rfl
          rw [hstep]
          apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          intro g' hg'
          rcases List.mem_append.mp hg' with h1 | h2
          · exact hacc g' h1
          · exact simplify_ok g.op (n + acc.2.length) _ g' h2
      · intro gs
        induction gs with
        | nil =>
          intro _ acc w_old w_new _ _ hinv i
          simp only [elimFn, List.foldl_nil, List.drop_length, wiresFrom]
          exact (hinv i).2
        | cons g rest ih =>
          intro hok acc w_old w_new hlen1 hlen2 hinv i
          have hstep_e : elimFn (g :: rest) acc = elimFn rest (elimStep acc g) := rfl
          have hstep_w : wiresFrom (g :: rest) w_old =
              wiresFrom rest (w_old ++ [g.op.eval (g.inputs.map fun k0 => w_old.getD k0 false)]) := rfl
          let ins := g.inputs.map fun k0 => acc.1.getD k0 (Sum.inl false)
          let res := simplify g.op (n + acc.2.length) ins
          have hres_eq : simplify g.op w_new.length ins = res := by rw [hlen2]
          have hsnd := simplify_sound g.op (hok g List.mem_cons_self).1 w_new ins
            (by simp [ins]; exact (hok g List.mem_cons_self).2)
            (by intro st hst; obtain ⟨k0, _, rfl⟩ := List.mem_map.mp hst; exact (hinv k0).1)
          rw [hres_eq] at hsnd
          let w_new' := wiresFrom res.1.toList w_new
          let w_old' := w_old ++ [g.op.eval (g.inputs.map fun k0 => w_old.getD k0 false)]
          have hw_new'_len : w_new'.length = n + (elimStep acc g).2.length := by
            show (wiresFrom res.1.toList w_new).length = n + (acc.2 ++ res.1.toList).length
            rw [wiresFrom_length, hlen2, List.length_append]
            omega
          have hinv' : ∀ k0 : ℕ, svalid w_new'.length ((elimStep acc g).1.getD k0 (Sum.inl false)) ∧
              sval w_new' ((elimStep acc g).1.getD k0 (Sum.inl false)) = w_old'.getD k0 false := by
            intro k0
            by_cases hklt : k0 < acc.1.length
            · have hget1 : (elimStep acc g).1.getD k0 (Sum.inl false) = acc.1.getD k0 (Sum.inl false) :=
                getD_snoc_lt acc.1 res.2 (Sum.inl false) k0 hklt
              have hget2 : w_old'.getD k0 false = w_old.getD k0 false :=
                getD_snoc_lt w_old _ false k0 (hlen1 ▸ hklt)
              rw [hget1, hget2]
              rcases hst : acc.1.getD k0 (Sum.inl false) with c | j
              · have hv2 := (hinv k0).2
                rw [hst] at hv2
                exact ⟨trivial, hv2⟩
              · have hjlt : j < w_new.length := by
                  have hv := (hinv k0).1; rw [hst] at hv; exact hv
                refine ⟨by show j < w_new'.length; rw [wiresFrom_length]; omega, ?_⟩
                have hkeep : w_new'.getD j false = w_new.getD j false :=
                  wiresFrom_keep res.1.toList w_new j hjlt
                have hv2 := (hinv k0).2
                rw [hst] at hv2
                show w_new'.getD j false = w_old.getD k0 false
                rw [hkeep]
                exact hv2
            · by_cases hkeq : k0 = acc.1.length
              · have hget1 : (elimStep acc g).1.getD k0 (Sum.inl false) = res.2 :=
                  getD_snoc_eq acc.1 res.2 (Sum.inl false) k0 hkeq
                have hget2 : w_old'.getD k0 false = g.op.eval (g.inputs.map fun m => w_old.getD m false) :=
                  getD_snoc_eq w_old _ false k0 (hlen1 ▸ hkeq)
                rw [hget1, hget2]
                refine ⟨by show svalid w_new'.length res.2; rw [wiresFrom_length]; exact hsnd.1, ?_⟩
                have hmap : ins.map (sval w_new) = g.inputs.map (fun m => w_old.getD m false) := by
                  simp only [ins, List.map_map]
                  apply List.map_congr_left
                  intro m _
                  exact (hinv m).2
                rw [hsnd.2, hmap]
              · have hget1 : (elimStep acc g).1.getD k0 (Sum.inl false) = Sum.inl false :=
                  List.getD_eq_default _ _ (by simp [elimStep]; omega)
                have hget2 : w_old'.getD k0 false = false :=
                  List.getD_eq_default _ _ (by simp [w_old']; omega)
                rw [hget1, hget2]
                exact ⟨trivial, rfl⟩
          have hih := ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
            (elimStep acc g) w_old' w_new' (by simp [elimStep, w_old', hlen1]) hw_new'_len hinv' i
          have hsub : ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (a0 : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate),
              ∃ sfx, (elimFn gs0 a0).2 = a0.2 ++ sfx := by
            intro gs0
            induction gs0 with
            | nil => intro a0; exact ⟨[], by simp [elimFn]⟩
            | cons g1 gs1 ih1 =>
              intro a0
              obtain ⟨sfx, hsfx⟩ := ih1 (elimStep a0 g1)
              refine ⟨(simplify g1.op (n + a0.2.length)
                (g1.inputs.map fun m => a0.1.getD m (Sum.inl false))).1.toList ++ sfx, ?_⟩
              have hst : elimFn (g1 :: gs1) a0 = elimFn gs1 (elimStep a0 g1) := rfl
              rw [hst, hsfx]
              simp [elimStep, List.append_assoc]
          obtain ⟨sfx, hsfx⟩ := hsub rest (elimStep acc g)
          have hdrop1 : (elimFn (g :: rest) acc).2.drop acc.2.length = res.1.toList ++ sfx := by
            rw [hstep_e, hsfx]
            show (acc.2 ++ res.1.toList ++ sfx).drop acc.2.length = res.1.toList ++ sfx
            rw [List.append_assoc, List.drop_left]
          have hdrop2 : (elimFn rest (elimStep acc g)).2.drop (elimStep acc g).2.length = sfx := by
            rw [hsfx]
            exact List.drop_left
          rw [hdrop1, wiresFrom_append, hstep_e, hstep_w]
          rw [hdrop2] at hih
          exact hih
    have stripAll : ∀ (B : Finset (Fin n)), (∀ u v : Fin n, H.Adj u v → u ∉ B) →
        ∀ (s0 : ℕ) (fB : (Fin n → Bool) → Bool),
        (∀ x : Fin n → Bool, fB x = true ↔
          (∃ b ∈ B, x b = true) ∨ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
        PEqualNP.MetaComplexity.HasCircuitSize n fB s0 →
        ∃ t0 : ℕ, t0 + B.card ≤ s0 ∧ ∃ g0 : (Fin n → Bool) → Bool,
          PEqualNP.MetaComplexity.HasCircuitSize n g0 t0 ∧
          ∀ x : Fin n → Bool, g0 x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
      intro B
      induction B using Finset.induction_on with
      | empty =>
        intro _ s0 fB hfB hs0
        refine ⟨s0, by simp, fB, hs0, ?_⟩
        intro x
        simpa using hfB x
      | @insert p B' hpB' ih =>
        intro hnoB s0 fB hfB hs0
        obtain ⟨D, hD, hDsz, hDval⟩ := hs0
        obtain ⟨u0, v0, hu0v0⟩ := hHE
        have hu0B : u0 ∉ insert p B' := hnoB u0 v0 hu0v0
        have hv0B : v0 ∉ insert p B' := hnoB v0 u0 hu0v0.symm
        have hpu0 : p ≠ u0 := fun e => hu0B (e ▸ Finset.mem_insert_self p B')
        have hpv0 : p ≠ v0 := fun e => hv0B (e ▸ Finset.mem_insert_self p B')
        let xe : Fin n → Bool := fun j => decide (j = u0 ∨ j = v0)
        have hout_ne : D.output ≠ p.val := by
          intro hout
          have h1 : D.eval (List.ofFn xe) = false := by
            show (wiresFrom D.gates (List.ofFn xe)).getD D.output false = false
            rw [hout, wiresFrom_keep _ _ _ (by simp), ofFn_getD_lt xe false p.val p.isLt]
            simp [xe, hpu0, hpv0]
          have h2 : fB xe = true :=
            (hfB xe).2 (Or.inr ⟨u0, v0, hu0v0, by simp [xe], by simp [xe]⟩)
          rw [hDval xe, h2] at h1
          cases h1
        have hread_p : ∃ g ∈ D.gates, reads p.val g = true := by
          by_contra hnr_all
          have hnr : ∀ g ∈ D.gates, reads p.val g = false := by
            intro g hg
            cases hr : reads p.val g with
            | false => rfl
            | true => exact False.elim (hnr_all ⟨g, hg, hr⟩)
          let x0 : Fin n → Bool := fun _ => false
          let xp : Fin n → Bool := fun j => decide (j = p)
          have hag : ∀ i, i ≠ p.val → (List.ofFn x0).getD i false = (List.ofFn xp).getD i false := by
            intro i hi
            by_cases hlt : i < n
            · rw [ofFn_getD_lt x0 false i hlt, ofFn_getD_lt xp false i hlt]
              have hne : (⟨i, hlt⟩ : Fin n) ≠ p := fun e => hi (congrArg Fin.val e)
              simp [x0, xp, hne]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have heq : D.eval (List.ofFn x0) = D.eval (List.ofFn xp) :=
            wiresFrom_agree_eff D.gates hD p.val (List.ofFn x0) (List.ofFn xp) (by simp) hag hnr
              D.output hout_ne
          rw [hDval x0, hDval xp] at heq
          have hf0 : fB x0 = false := by
            cases hfx : fB x0 with
            | false => rfl
            | true =>
              rcases (hfB x0).1 hfx with ⟨b, _, hb⟩ | ⟨b, _, _, hb, _⟩ <;> simp [x0] at hb
          have hfp : fB xp = true :=
            (hfB xp).2 (Or.inl ⟨p, Finset.mem_insert_self p B', by simp [xp]⟩)
          rw [hf0, hfp] at heq
          cases heq
        let init : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate :=
          (List.ofFn (fun k0 : Fin n => if k0 = p then Sum.inl false else Sum.inr k0.val), [])
        let res := elim D.gates init
        have hdrop : res.2.length + 1 ≤ D.gates.length := by
          have hd := elim_len_drop D.gates hD init p.val (by simp [init])
            (by simp [init]) hread_p
          simpa [res, init] using hd
        have hok_res : ∀ g ∈ res.2,
            g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
          elim_ok D.gates hD init (by intro _ hm; cases hm)
        have hval_res : ∀ x : Fin n → Bool,
            sval (wiresFrom res.2 (List.ofFn x)) (res.1.getD D.output (Sum.inl false)) =
              fB (Function.update x p false) := by
          intro x
          have hsnd := elim_sound D.gates hD init
            (List.ofFn (Function.update x p false)) (List.ofFn x)
            (by simp [init]) (by simp [init])
            (by
              intro i
              by_cases hlt : i < n
              · simp only [init, ofFn_getD_lt _ _ i hlt, List.length_ofFn]
                by_cases hikp : (⟨i, hlt⟩ : Fin n) = p
                · subst hikp
                  simp [svalid, sval]
                · simp [hikp, svalid, sval, hlt]
              · rw [List.getD_eq_default _ _ (by simp [init]; omega),
                  List.getD_eq_default _ _ (by simp; omega)]
                exact ⟨trivial, rfl⟩)
            D.output
          rw [← hDval (Function.update x p false)]
          exact hsnd
        let fB' : (Fin n → Bool) → Bool := fun x => fB (Function.update x p false)
        have hfB' : ∀ x : Fin n → Bool, fB' x = true ↔
            (∃ b ∈ B', x b = true) ∨ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
          intro x
          simp only [fB', hfB (Function.update x p false)]
          constructor
          · intro h
            rcases h with ⟨b, hb, hbx⟩ | ⟨u, v, huv, hux, hvx⟩
            · rcases Finset.mem_insert.mp hb with rfl | hb'
              · simp at hbx
              · have hbp : b ≠ p := fun e => hpB' (e ▸ hb')
                simp only [Function.update_of_ne hbp] at hbx
                exact Or.inl ⟨b, hb', hbx⟩
            · have hup : u ≠ p := fun e => hnoB u v huv (e ▸ Finset.mem_insert_self p B')
              have hvp : v ≠ p := fun e => hnoB v u huv.symm (e ▸ Finset.mem_insert_self p B')
              simp only [Function.update_of_ne hup, Function.update_of_ne hvp] at hux hvx
              exact Or.inr ⟨u, v, huv, hux, hvx⟩
          · intro h
            rcases h with ⟨b, hb', hbx⟩ | ⟨u, v, huv, hux, hvx⟩
            · have hbp : b ≠ p := fun e => hpB' (e ▸ hb')
              exact Or.inl ⟨b, Finset.mem_insert_of_mem hb', by simp [Function.update_of_ne hbp, hbx]⟩
            · have hup : u ≠ p := fun e => hnoB u v huv (e ▸ Finset.mem_insert_self p B')
              have hvp : v ≠ p := fun e => hnoB v u huv.symm (e ▸ Finset.mem_insert_self p B')
              exact Or.inr ⟨u, v, huv, by simp [Function.update_of_ne hup, hux],
                by simp [Function.update_of_ne hvp, hvx]⟩
        rcases hsout : res.1.getD D.output (Sum.inl false) with c | outWire
        · exfalso
          let x0 : Fin n → Bool := fun _ => false
          have hc0 := hval_res x0
          have hce := hval_res xe
          rw [hsout] at hc0 hce
          simp only [sval] at hc0 hce
          have hf0' : fB' x0 = false := by
            cases hfx : fB' x0 with
            | false => rfl
            | true =>
              rcases (hfB' x0).1 hfx with ⟨b, _, hb⟩ | ⟨b, _, _, hb, _⟩ <;> simp [x0] at hb
          have hfe' : fB' xe = true :=
            (hfB' xe).2 (Or.inr ⟨u0, v0, hu0v0, by simp [xe], by simp [xe]⟩)
          change c = fB' x0 at hc0
          change c = fB' xe at hce
          rw [hf0'] at hc0
          rw [hfe'] at hce
          rw [hc0] at hce
          cases hce
        · have hsB' : PEqualNP.MetaComplexity.HasCircuitSize n fB' res.2.length := by
            refine ⟨⟨res.2, outWire⟩, hok_res, le_rfl, ?_⟩
            intro x
            have hx := hval_res x
            rw [hsout] at hx
            exact hx
          obtain ⟨t0, ht0, g0, hg0sz, hg0⟩ :=
            ih (fun u v huv huB' => hnoB u v huv (Finset.mem_insert_of_mem huB')) res.2.length fB' hfB' hsB'
          refine ⟨t0, ?_, g0, hg0sz, hg0⟩
          rw [Finset.card_insert_of_notMem hpB']
          change D.gates.length ≤ s0 at hDsz
          omega
    exact stripAll A hnoAH s f hf hs
  have hex : ∃ m : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n g0 m := ⟨t, htg0⟩
  obtain ⟨C, hC, hCsz, hCval⟩ := Nat.find_spec hex
  have hCt : C.size ≤ t := hCsz.trans (Nat.find_min' hex htg0)
  have heval : (fun x => C.eval (List.ofFn x)) = g0 := funext hCval
  have hCspec : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro x; rw [congrFun heval x]; exact hg0 x
  have hmin : ∀ m : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn x)) m → C.size ≤ m := by
    intro m hm; rw [heval] at hm; exact hCsz.trans (Nat.find_min' hex hm)
  suffices hgoal : H.edgeSet.ncard + k ≤ C.size + 1 by
    change A.card + H.edgeSet.ncard + k ≤ s + 1
    omega
  have deleteAndRedirect : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
      (j a : ℕ) (hj : j < D.gates.length) (ha : a < n + j),
      (∀ x : Fin n → Bool,
        (wiresFrom (D.gates.take (j + 1)) (List.ofFn x)).getD (n + j) false =
          (wiresFrom (D.gates.take j) (List.ofFn x)).getD a false) →
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => D.eval (List.ofFn x)) (D.gates.length - 1) := by
    clear * - getD_snoc_lt getD_snoc_eq wiresFrom_append wiresFrom_length wiresFrom_keep
    let substWire : ℕ → ℕ → ℕ → ℕ := fun k0 b i =>
      if i < k0 then i else if i = k0 then b else i - 1
    let substGate : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun k0 b g =>
      ⟨g.op, g.inputs.map (substWire k0 b)⟩
    let deleteGate : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun D j b =>
      ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j) b),
        substWire (n + j) b D.output⟩
    have deleteGate_ok : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j b : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.FanInTwo (deleteGate D j b) := by
      intro D j b hok g hg
      rcases List.mem_append.1 hg with h1 | h1
      · exact hok g (List.mem_of_mem_take h1)
      · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 h1
        have h0 := hok g1 (List.mem_of_mem_drop hg1)
        exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
    have deleteGate_len : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j b : ℕ), j < D.gates.length →
        (deleteGate D j b).gates.length = D.gates.length - 1 := by
      intro D j b hj
      simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    intro D hD j a hj ha heq_j
    refine ⟨deleteGate D j a, deleteGate_ok D j a hD,
      by show (deleteGate D j a).gates.length ≤ D.gates.length - 1; rw [deleteGate_len D j a hj], ?_⟩
    intro x
    show ((deleteGate D j a).wires (List.ofFn x)).getD (substWire (n + j) a D.output) false =
      (D.wires (List.ofFn x)).getD D.output false
    have hsplit : D.gates = D.gates.take j ++ [D.gates[j]] ++ D.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j D.gates
      have h2 : D.gates.drop j = D.gates[j] :: D.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1
      simpa only [List.append_assoc, List.singleton_append] using h1.symm
    set w₂ := wiresFrom (D.gates.take j) (List.ofFn x) with hw₂
    set w₁ := wiresFrom [D.gates[j]] w₂ with hw₁
    have hw₂_len : w₂.length = n + j := by
      rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
    have hw₁_len : w₁.length = n + j + 1 := by
      rw [hw₁, wiresFrom_length, hw₂_len]; simp
    have take_succ_app : ∀ {α : Type} (l : List α) (k0 : ℕ) (hk0 : k0 < l.length),
        l.take (k0 + 1) = l.take k0 ++ [l[k0]] := by
      intro α l
      induction l with
      | nil => intro k0 hk0; simp at hk0
      | cons a l ih =>
        intro k0 hk0
        cases k0 with
        | zero => simp
        | succ k0 =>
          simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
          congr 1
          exact ih k0 (by simp at hk0; omega)
    have hw₁_eq : w₁ = wiresFrom (D.gates.take (j + 1)) (List.ofFn x) := by
      have htk : D.gates.take (j + 1) = D.gates.take j ++ [D.gates[j]] := take_succ_app D.gates j hj
      rw [htk, wiresFrom_append, ← hw₂]
    have hagree_j : w₁.getD (n + j) false = w₂.getD a false := by
      rw [hw₁_eq, hw₂]
      exact heq_j x
    have haux : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w₁' w₂' : List Bool),
        w₁'.length = w₂'.length + 1 → n + j ≤ w₂'.length →
        (∀ i, w₂'.getD (substWire (n + j) a i) false = w₁'.getD i false) →
        ∀ i, (wiresFrom (gs.map (substGate (n + j) a)) w₂').getD (substWire (n + j) a i) false =
          (wiresFrom gs w₁').getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro w₁' w₂' _ _ hag i
        exact hag i
      | cons g rest ih =>
        intro w₁' w₂' hlen' hk' hag'
        have hstep1 : wiresFrom (g :: rest) w₁' =
            wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)]) := rfl
        have hstep2 : wiresFrom ((g :: rest).map (substGate (n + j) a)) w₂' =
            wiresFrom (rest.map (substGate (n + j) a))
              (w₂' ++ [(substGate (n + j) a g).op.eval
                ((substGate (n + j) a g).inputs.map fun i => w₂'.getD i false)]) := rfl
        rw [hstep1, hstep2]
        have hmap : ((substGate (n + j) a g).inputs.map fun i => w₂'.getD i false) =
            (g.inputs.map fun i => w₁'.getD i false) := by
          simp only [substGate, List.map_map]
          apply List.map_congr_left
          intro i _
          exact hag' i
        rw [hmap]
        apply ih _ _ (by simp [hlen']) (by simp; omega)
        intro i
        by_cases hlti : i < w₁'.length
        · have hsublt : substWire (n + j) a i < w₂'.length := by
            dsimp [substWire]; split_ifs <;> omega
          rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlti]
          exact hag' i
        · by_cases hieq : i = w₁'.length
          · have hsubeq : substWire (n + j) a i = w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
          · have hsubge : w₂'.length < substWire (n + j) a i := by
              dsimp [substWire]; split_ifs <;> omega
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    show (wiresFrom (D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j) a)) (List.ofFn x)).getD
        (substWire (n + j) a D.output) false = (wiresFrom D.gates (List.ofFn x)).getD D.output false
    rw [wiresFrom_append, ← hw₂]
    conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
    apply haux (D.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) _ D.output
    intro u
    by_cases hult : u < n + j
    · simp only [substWire, hult, ↓reduceIte]
      have hw1e : w₁ = w₂ ++ [D.gates[j].op.eval (D.gates[j].inputs.map fun i => w₂.getD i false)] := rfl
      rw [hw1e, getD_snoc_lt _ _ _ _ (by omega)]
    · by_cases hueq : u = n + j
      · subst hueq
        simp only [substWire, lt_irrefl, ↓reduceIte]
        exact hagree_j.symm
      · have hgt : n + j < u := by omega
        have hnlt : ¬ (u < n + j) := by omega
        have hne : u ≠ n + j := by omega
        simp only [substWire, hnlt, hne, ↓reduceIte]
        rw [List.getD_eq_default w₂ false (by omega), List.getD_eq_default w₁ false (by omega)]
  have deleteDeadGate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
      (j : ℕ) (hj : j < D.gates.length),
      D.output ≠ n + j →
      (∀ j' : ℕ, (hj' : j' < D.gates.length) → j < j' → (n + j) ∉ D.gates[j'].inputs) →
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x => D.eval (List.ofFn x)) (D.gates.length - 1) := by
    clear * - getD_snoc_lt getD_snoc_eq wiresFrom_append wiresFrom_length
    let substWire : ℕ → ℕ → ℕ → ℕ := fun k0 a i =>
      if i < k0 then i else if i = k0 then a else i - 1
    let substGate : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun k0 a g =>
      ⟨g.op, g.inputs.map (substWire k0 a)⟩
    let deleteGate : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun D j a =>
      ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j) a),
        substWire (n + j) a D.output⟩
    have deleteGate_ok : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j a : ℕ),
        PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.FanInTwo (deleteGate D j a) := by
      intro D j a hok g hg
      rcases List.mem_append.1 hg with h1 | h1
      · exact hok g (List.mem_of_mem_take h1)
      · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 h1
        have h0 := hok g1 (List.mem_of_mem_drop hg1)
        exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
    have deleteGate_len : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j a : ℕ), j < D.gates.length →
        (deleteGate D j a).gates.length = D.gates.length - 1 := by
      intro D j a hj
      simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    intro D hD j hj hout hno
    refine ⟨deleteGate D j 0, deleteGate_ok D j 0 hD,
      by show (deleteGate D j 0).gates.length ≤ D.gates.length - 1; rw [deleteGate_len D j 0 hj], ?_⟩
    intro x
    show ((deleteGate D j 0).wires (List.ofFn x)).getD (substWire (n + j) 0 D.output) false =
      (D.wires (List.ofFn x)).getD D.output false
    by_cases hlt : D.output < n + D.gates.length
    · have hsplit : D.gates = D.gates.take j ++ [D.gates[j]] ++ D.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j D.gates
        have h2 : D.gates.drop j = D.gates[j] :: D.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        rw [h2] at h1
        simpa only [List.append_assoc, List.singleton_append] using h1.symm
      set w₂ := wiresFrom (D.gates.take j) (List.ofFn x) with hw₂
      set w₁ := wiresFrom [D.gates[j]] w₂ with hw₁
      have hw₂_len : w₂.length = n + j := by
        rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      have hw₁_len : w₁.length = n + j + 1 := by
        rw [hw₁, wiresFrom_length, hw₂_len]; simp
      have hno_drop : ∀ g ∈ D.gates.drop (j + 1), (n + j) ∉ g.inputs := by
        intro g hg
        obtain ⟨t0, ht0, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_drop]
        exact hno (j + 1 + t0) (by rw [List.length_drop] at ht0; omega) (by omega)
      have haux : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w₁' w₂' : List Bool),
          w₁'.length = w₂'.length + 1 → n + j ≤ w₂'.length →
          (∀ g ∈ gs, (n + j) ∉ g.inputs) →
          (∀ i < w₁'.length, i ≠ n + j → w₂'.getD (substWire (n + j) 0 i) false = w₁'.getD i false) →
          ∀ i < (wiresFrom gs w₁').length, i ≠ n + j →
            (wiresFrom (gs.map (substGate (n + j) 0)) w₂').getD (substWire (n + j) 0 i) false =
              (wiresFrom gs w₁').getD i false := by
        intro gs
        induction gs with
        | nil =>
          intro w₁' w₂' _ _ _ hag i hi hne
          exact hag i hi hne
        | cons g rest ih =>
          intro w₁' w₂' hlen' hk' hnod hag'
          have hstep1 : wiresFrom (g :: rest) w₁' =
              wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)]) := rfl
          have hstep2 : wiresFrom ((g :: rest).map (substGate (n + j) 0)) w₂' =
              wiresFrom (rest.map (substGate (n + j) 0))
                (w₂' ++ [(substGate (n + j) 0 g).op.eval
                  ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false)]) := rfl
          rw [hstep1, hstep2]
          have hmap : ((substGate (n + j) 0 g).inputs.map fun i => w₂'.getD i false) =
              (g.inputs.map fun i => w₁'.getD i false) := by
            simp only [substGate, List.map_map]
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hne : i ≠ n + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
            by_cases hlti : i < w₁'.length
            · exact hag' i hlti hne
            · have hge : w₂'.length ≤ substWire (n + j) 0 i := by
                dsimp [substWire]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
          rw [hmap]
          apply ih _ _ (by simp [hlen']) (by simp; omega)
            (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
          intro i hi hne
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlti : i < w₁'.length
          · have hsublt : substWire (n + j) 0 i < w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlti]
            exact hag' i hlti hne
          · have hieq : i = w₁'.length := by omega
            have hsubeq : substWire (n + j) 0 i = w₂'.length := by
              dsimp [substWire]; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
      show (wiresFrom (D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j) 0)) (List.ofFn x)).getD
          (substWire (n + j) 0 D.output) false = (wiresFrom D.gates (List.ofFn x)).getD D.output false
      rw [wiresFrom_append, ← hw₂]
      conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
      have hlen_rhs : (wiresFrom (D.gates.drop (j + 1)) w₁).length = n + D.gates.length := by
        rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
      apply haux (D.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ D.output (by omega) hout
      intro u hu hune
      have hltu : u < n + j := by omega
      simp only [substWire, hltu, ↓reduceIte]
      have hw1e : w₁ = w₂ ++ [D.gates[j].op.eval (D.gates[j].inputs.map fun i => w₂.getD i false)] := rfl
      rw [hw1e, getD_snoc_lt _ _ _ _ (by omega)]
    · have h1 : ((deleteGate D j 0).wires (List.ofFn x)).length =
          n + (deleteGate D j 0).gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have h2 : (D.wires (List.ofFn x)).length = n + D.gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have hge1 : n + (deleteGate D j 0).gates.length ≤ substWire (n + j) 0 D.output := by
        rw [deleteGate_len D j 0 hj]
        dsimp [substWire]
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  let r : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v => C.gates.filter (reads v.val)
  have hread_pos : ∀ v : Fin n, (∃ u : Fin n, H.Adj v u) → 1 ≤ (r v).length := by
    clear * - hC hCspec wiresFrom_keep ofFn_getD_lt wiresFrom_agree_eff
    intro v hex_u
    obtain ⟨u, huv⟩ := hex_u
    by_contra h0
    have hempty : ∀ g ∈ C.gates, reads v.val g = false := by
      intro g hg
      cases hr : reads v.val g with
      | false => rfl
      | true =>
        have hm : g ∈ r v := List.mem_filter.2 ⟨hg, hr⟩
        have hpos : 0 < (r v).length := List.length_pos_of_mem hm
        omega
    by_cases hout : C.output = v.val
    · let xv : Fin n → Bool := fun j => decide (j = v)
      have h1 : C.eval (List.ofFn xv) = true := by
        show (wiresFrom C.gates (List.ofFn xv)).getD C.output false = true
        rw [hout, wiresFrom_keep _ _ _ (by simp), ofFn_getD_lt xv false v.val v.isLt]
        simp [xv]
      obtain ⟨a, b, hab, ha, hb⟩ := (hCspec xv).1 h1
      have hav : a = v := by simpa [xv] using ha
      have hbv : b = v := by simpa [xv] using hb
      exact hab.ne (hav.trans hbv.symm)
    · let x1 : Fin n → Bool := fun j => decide (j = u)
      let x2 : Fin n → Bool := fun j => decide (j = u ∨ j = v)
      have hag : ∀ i, i ≠ v.val → (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
        intro i hi
        by_cases hlt : i < n
        · rw [ofFn_getD_lt x1 false i hlt, ofFn_getD_lt x2 false i hlt]
          have hne : (⟨i, hlt⟩ : Fin n) ≠ v := fun e => hi (congrArg Fin.val e)
          simp [x1, x2, hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have heq : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) :=
        wiresFrom_agree_eff C.gates hC v.val (List.ofFn x1) (List.ofFn x2) (by simp) hag hempty
          C.output hout
      have hf2 : C.eval (List.ofFn x2) = true :=
        (hCspec x2).2 ⟨v, u, huv, by simp [x2], by simp [x2]⟩
      have hf1 : C.eval (List.ofFn x1) = false := by
        cases hfx : C.eval (List.ofFn x1) with
        | false => rfl
        | true =>
          obtain ⟨a, b, hab, ha, hb⟩ := (hCspec x1).1 hfx
          have hau : a = u := by simpa [x1] using ha
          have hbu : b = u := by simpa [x1] using hb
          exact False.elim (hab.ne (hau.trans hbu.symm))
      rw [hf1, hf2] at heq
      cases heq
  by_cases hdeg_le : ∀ v : Fin n, (H.neighborSet v).ncard ≤ (r v).length
  · clear * - hC hmin hk_le_edges deleteDeadGate hdeg_le
    let slots : PEqualNP.CircuitLowerBounds.Circuit → List ℕ := fun D => D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
    have gateSlotBound : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
        (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 * gs.length := by
      clear * -
      intro gs
      induction gs with
      | nil => intro _; simp
      | cons g tail ih =>
        intro h
        have hg := h g List.mem_cons_self
        have ht := ih (fun t0 hm => h t0 (List.mem_cons_of_mem _ hm))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have countBound : ∀ (xs : List ℕ) (S : Finset ℕ), ∑ i ∈ S, xs.count i ≤ xs.length := by
      clear * -
      intro xs
      induction xs with
      | nil => intro S; simp
      | cons a xs ih =>
        intro S
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> have := ih S <;> omega
    have filteredSlots : ∀ (v : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (gs.filter (reads v)).length ≤ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v := by
      clear * -
      intro v gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons, List.count_append, List.filter_cons]
        by_cases h : reads v g = true
        · simp only [h, ↓reduceIte]
          have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
          have hp := List.count_pos_iff.mpr hm
          simp only [List.length_cons]
          omega
        · simp only [h, Bool.false_eq_true, ↓reduceIte]
          omega
    let cnt : ℕ → ℕ := fun i => (slots C).count i
    have hcnt_deg : ∀ v ∈ (Finset.univ : Finset (Fin n)), H.degree v ≤ cnt v.val := by
      intro v _
      have hd : H.degree v = (H.neighborSet v).ncard := (H.ncard_neighborSet v).symm
      have hrle := hdeg_le v
      have hf0 := filteredSlots v.val C.gates
      simp only [cnt, slots, List.count_cons, r] at hrle ⊢
      omega
    have internal : ∀ i ∈ Finset.range C.gates.length, 1 ≤ cnt (n + i) := by
      intro i hi
      apply List.count_pos_iff.2
      by_contra hn
      have hout : C.output ≠ n + i := fun e => hn (by simp [slots, e])
      have hno : ∀ j, (hj : j < C.gates.length) → i < j → n + i ∉ C.gates[j].inputs := by
        intro j hj _ hm
        exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj, hm⟩))
      have bad := hmin _ (deleteDeadGate C hC i (Finset.mem_range.1 hi) hout hno)
      change C.gates.length ≤ C.gates.length - 1 at bad
      have hipos : 0 < C.gates.length := lt_of_le_of_lt (Nat.zero_le i) (Finset.mem_range.1 hi)
      omega
    have hdeg_sum_edges : ∑ v : Fin n, H.degree v = 2 * H.edgeFinset.card := by
      clear * -
      let dirEdges : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => H.Adj p.1 p.2)
      let dirLt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => H.Adj p.1 p.2 ∧ p.1 < p.2)
      let dirGt : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => H.Adj p.1 p.2 ∧ p.2 < p.1)
      have hpart : dirEdges = dirLt ∪ dirGt := by
        ext p
        simp only [dirEdges, dirLt, dirGt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hadj
          rcases lt_or_gt_of_ne hadj.ne with h | h
          · exact Or.inl ⟨hadj, h⟩
          · exact Or.inr ⟨hadj, h⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint dirLt dirGt := by
        rw [Finset.disjoint_left]
        intro p h1 h2
        simp only [dirLt, dirGt, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact lt_asymm h1.2 h2.2
      have hswap : dirGt.card = dirLt.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p h
          simp only [dirGt, dirLt, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
          exact ⟨h.1.symm, h.2⟩
        · intro p1 _ p2 _ h
          exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro p h
          simp only [dirLt, Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact ⟨(p.2, p.1), by simp [dirGt, h.1.symm, h.2], by ext <;> rfl⟩
      have hbij : dirLt.card = H.edgeFinset.card := by
        refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
        · intro p h
          simp only [dirLt, Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact H.mem_edgeFinset.mpr h.1
        · intro p1 h1 p2 h2 h
          simp only [dirLt, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          rcases Sym2.eq_iff.mp h with ⟨he1, he2⟩ | ⟨he1, he2⟩
          · exact Prod.ext he1 he2
          · exact absurd (lt_trans (he1 ▸ h1.2) (he2 ▸ h2.2)) (lt_irrefl _)
        · intro e he
          induction e using Sym2.ind with
          | _ u v =>
            have huv : H.Adj u v := H.mem_edgeFinset.mp he
            rcases lt_or_gt_of_ne huv.ne with hlt | hlt
            · exact ⟨(u, v), by simp [dirLt, huv, hlt], rfl⟩
            · exact ⟨(v, u), by simp [dirLt, huv.symm, hlt], Sym2.eq_swap⟩
      have hsum_dir : ∑ v : Fin n, H.degree v = dirEdges.card := by
        have h1 : dirEdges = (Finset.univ : Finset (Fin n)).biUnion
            (fun v => (H.neighborFinset v).image (fun u => (v, u))) := by
          ext p
          rcases p with ⟨v, u⟩
          simp [dirEdges, H.mem_neighborFinset]
        rw [h1, Finset.card_biUnion]
        · refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
          rfl
        · intro v1 _ v2 _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro p ha hb
          simp only [Finset.mem_image] at ha hb
          obtain ⟨_, _, h1a⟩ := ha
          obtain ⟨_, _, h2b⟩ := hb
          exact hne ((congrArg Prod.fst h1a).trans (congrArg Prod.fst h2b).symm)
      rw [hsum_dir, hpart, Finset.card_union_of_disjoint hdisj, hswap, hbij]
      omega
    have lowerV := Finset.sum_le_sum hcnt_deg
    rw [hdeg_sum_edges, Fin.sum_univ_eq_sum_range] at lowerV
    have lowerI := Finset.sum_le_sum internal
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerI
    have countAll := countBound (slots C) (Finset.range (n + C.gates.length))
    change ∑ i ∈ Finset.range (n + C.gates.length), cnt i ≤ (slots C).length at countAll
    rw [Finset.sum_range_add] at countAll
    have len := gateSlotBound C.gates (fun g hg => (hC g hg).2)
    simp only [slots, List.length_cons] at countAll
    have hedgeEq : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    change H.edgeSet.ncard + k ≤ C.gates.length + 1
    omega
  · obtain ⟨v0, hv0not⟩ := Classical.not_forall.mp hdeg_le
    have hv0lt : (r v0).length < (H.neighborSet v0).ncard := Nat.lt_of_not_ge hv0not
    by_cases h1 : ∃ v : Fin n, (∃ u : Fin n, H.Adj v u) ∧ (r v).length = 1
    · obtain ⟨v, hv_adj, hv_len1⟩ := h1
      have hinternal : ∀ g ∈ C.gates, reads v.val g = true →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          ∃ w ∈ g.inputs, n ≤ w := by
        intro g hg hrg hop
        by_contra hno_int
        push Not at hno_int
        obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
        have hlen_g : g.inputs.length ≤ 2 := (hC g hg).2
        have htake_g : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rcases hop with ha | ho
          · rw [ha]; exact List.take_of_length_le hlen_g
          · rw [ho]; exact List.take_of_length_le hlen_g
        have hv_mem : v.val ∈ g.inputs := by
          have := List.contains_iff_mem.mp hrg
          rwa [htake_g] at this
        have hother_lt : ∀ w ∈ g.inputs, w < n := hno_int
        have h_no_self : ∀ (a : ℕ) (ha : a < n), (∀ x : Fin n → Bool,
            (wiresFrom (C.gates.take (j + 1)) (List.ofFn x)).getD (n + j) false =
              (wiresFrom (C.gates.take j) (List.ofFn x)).getD a false) → False := by
          intro a ha heq_w
          have bad := hmin _ (deleteAndRedirect C hC j a hj (by omega) heq_w)
          change C.gates.length ≤ C.gates.length - 1 at bad
          omega
        have take_succ_app : ∀ {α : Type} (l : List α) (k0 : ℕ) (hk0 : k0 < l.length),
            l.take (k0 + 1) = l.take k0 ++ [l[k0]] := by
          intro α l
          induction l with
          | nil => intro k0 hk0; simp at hk0
          | cons a l ih =>
            intro k0 hk0
            cases k0 with
            | zero => simp
            | succ k0 =>
              simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
              congr 1
              exact ih k0 (by simp at hk0; omega)
        rcases hgins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hgins] at hv_mem; cases hv_mem
        · rw [hgins] at hv_mem
          have hav : a = v.val := (List.mem_singleton.mp hv_mem).symm
          subst hav
          apply h_no_self v.val v.isLt
          intro x
          have htk : C.gates.take (j + 1) = C.gates.take j ++ [g] := by
            rw [← hgj]; exact take_succ_app C.gates j hj
          rw [htk, wiresFrom_append]
          set w0 := wiresFrom (C.gates.take j) (List.ofFn x)
          have hw0len : w0.length = n + j := by
            show (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j
            rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
          have hw0_step : wiresFrom [g] w0 = w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)] := rfl
          rw [hw0_step, getD_snoc_eq _ _ _ _ hw0len.symm, hgins]
          simp only [List.map_cons, List.map_nil]
          rcases hop with h | h <;> rw [h] <;> cases hbv : w0.getD v.val false <;> rfl
        · by_cases hab : a = b
          · subst hab
            rw [hgins] at hv_mem
            have hav : a = v.val :=
              (List.mem_cons.mp hv_mem).elim Eq.symm (fun h => (List.mem_singleton.mp h).symm)
            subst hav
            apply h_no_self v.val v.isLt
            intro x
            have htk : C.gates.take (j + 1) = C.gates.take j ++ [g] := by
              rw [← hgj]; exact take_succ_app C.gates j hj
            rw [htk, wiresFrom_append]
            set w0 := wiresFrom (C.gates.take j) (List.ofFn x)
            have hw0len : w0.length = n + j := by
              show (wiresFrom (C.gates.take j) (List.ofFn x)).length = n + j
              rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
            have hw0_step : wiresFrom [g] w0 = w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)] := rfl
            rw [hw0_step, getD_snoc_eq _ _ _ _ hw0len.symm, hgins]
            simp only [List.map_cons, List.map_nil]
            rcases hop with h | h <;> rw [h] <;> cases hbv : w0.getD v.val false <;> rfl
          · have hdeg_v2 : 2 ≤ (H.neighborFinset v).card := by
              obtain ⟨u1, hu1⟩ := hv_adj
              have hmemF : u1 ∈ H.neighborFinset v := (H.mem_neighborFinset v u1).mpr hu1
              have hpos : 0 < (H.neighborFinset v).card := Finset.card_pos.mpr ⟨u1, hmemF⟩
              have hcard_eq : (H.neighborFinset v).card = (H.neighborSet v).ncard := by
                rw [← Set.ncard_coe_finset, H.coe_neighborFinset]
              rcases hdegH v with h0 | h2 | h3 <;> omega
            obtain ⟨r1, hr1, r2, hr2, hr12⟩ := Finset.one_lt_card.mp (by omega : 1 < (H.neighborFinset v).card)
            have hvr1 : H.Adj v r1 := (H.mem_neighborFinset v r1).mp hr1
            have hvr2 : H.Adj v r2 := (H.mem_neighborFinset v r2).mp hr2
            have hu_ex : ∃ u : Fin n, u ≠ v ∧ u.val ∈ g.inputs := by
              rw [hgins] at hv_mem
              rcases List.mem_cons.mp hv_mem with rfl | hmem2
              · have hblt : b < n := hother_lt b (by rw [hgins]; simp)
                exact ⟨⟨b, hblt⟩, fun e => hab (congrArg Fin.val e).symm, by rw [hgins]; simp⟩
              · have haeq : v.val = b := List.mem_singleton.mp hmem2
                have halt : a < n := hother_lt a (by rw [hgins]; simp)
                exact ⟨⟨a, halt⟩, fun e => hab ((congrArg Fin.val e).trans haeq), by rw [hgins]; simp⟩
            obtain ⟨u, huv, hu_mem⟩ := hu_ex
            have filter_two : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (P : PEqualNP.CircuitLowerBounds.Gate → Bool) (i1 i2 : ℕ)
                (hi1 : i1 < gs.length) (hi2 : i2 < gs.length), i1 ≠ i2 → P gs[i1] = true → P gs[i2] = true →
                2 ≤ (gs.filter P).length := by
              intro gs P
              induction gs with
              | nil => intro i1 _ h1; simp at h1
              | cons q qs ih =>
                intro i1 i2 hi1 hi2 hne hp1 hp2
                cases i1 with
                | zero =>
                  cases i2 with
                  | zero => exact absurd rfl hne
                  | succ j2 =>
                    simp only [List.getElem_cons_zero] at hp1
                    simp only [List.getElem_cons_succ] at hp2
                    have hj2 : j2 < qs.length := by simpa using hi2
                    have hmem : qs[j2] ∈ qs.filter P := List.mem_filter.2 ⟨List.getElem_mem hj2, hp2⟩
                    have hpos : 0 < (qs.filter P).length := List.length_pos_of_mem hmem
                    rw [List.filter_cons, hp1]
                    simp
                    omega
                | succ j1 =>
                  cases i2 with
                  | zero =>
                    simp only [List.getElem_cons_succ] at hp1
                    simp only [List.getElem_cons_zero] at hp2
                    have hj1 : j1 < qs.length := by simpa using hi1
                    have hmem : qs[j1] ∈ qs.filter P := List.mem_filter.2 ⟨List.getElem_mem hj1, hp1⟩
                    have hpos : 0 < (qs.filter P).length := List.length_pos_of_mem hmem
                    rw [List.filter_cons, hp2]
                    simp
                    omega
                  | succ j2 =>
                    simp only [List.getElem_cons_succ] at hp1 hp2
                    have hih := ih j1 j2 (by simp at hi1; omega) (by simp at hi2; omega) (by omega) hp1 hp2
                    simp only [List.filter_cons]
                    cases P q <;> simp <;> omega
            have honly_idx : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j' ≠ j → reads v.val C.gates[j'] = false := by
              intro j' hj' hne
              cases hrj' : reads v.val C.gates[j'] with
              | false => rfl
              | true =>
                have h2 := filter_two C.gates (reads v.val) j j' hj hj' hne.symm (hgj ▸ hrg) hrj'
                change 2 ≤ (r v).length at h2
                omega
            have hout_ne : C.output ≠ v.val := by
              intro hout
              let xv : Fin n → Bool := fun j0 => decide (j0 = v)
              have h1 : C.eval (List.ofFn xv) = true := by
                show (wiresFrom C.gates (List.ofFn xv)).getD C.output false = true
                rw [hout, wiresFrom_keep _ _ _ (by simp), ofFn_getD_lt xv false v.val v.isLt]
                simp [xv]
              obtain ⟨p1, q1, hpq1, hp1, hq1⟩ := (hCspec xv).1 h1
              have hpv : p1 = v := by simpa [xv] using hp1
              have hqv : q1 = v := by simpa [xv] using hq1
              exact hpq1.ne (hpv.trans hqv.symm)
            have hstep_agree : ∀ (x1 x2 : Fin n → Bool),
                (∀ i : Fin n, i ≠ v → x1 i = x2 i) →
                (g.op.eval (g.inputs.map fun i => (wiresFrom (C.gates.take j) (List.ofFn x1)).getD i false) =
                  g.op.eval (g.inputs.map fun i => (wiresFrom (C.gates.take j) (List.ofFn x2)).getD i false)) →
                C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
              intro x1 x2 hagr hg_eq
              let pre := C.gates.take j
              let post := C.gates.drop (j + 1)
              have hsplit : C.gates = (pre ++ [g]) ++ post := by
                have h1 := List.take_append_drop j C.gates
                have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := by
                  rw [← hgj]; exact List.drop_eq_getElem_cons hj
                rw [h2] at h1
                simpa only [pre, post, List.append_assoc, List.singleton_append] using h1.symm
              have hok_pre : ∀ g' ∈ pre,
                  g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
                  g'.inputs.length ≤ 2 := fun g' hg' => hC g' (List.mem_of_mem_take hg')
              have hok_post : ∀ g' ∈ post,
                  g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
                  g'.inputs.length ≤ 2 := fun g' hg' => hC g' (List.mem_of_mem_drop hg')
              have hnr_pre : ∀ g' ∈ pre, reads v.val g' = false := by
                intro g' hg'
                obtain ⟨t0, ht0, hgt0⟩ := List.getElem_of_mem hg'
                rw [← hgt0, List.getElem_take]
                exact honly_idx t0 (by rw [List.length_take] at ht0; omega) (by rw [List.length_take] at ht0; omega)
              have hnr_post : ∀ g' ∈ post, reads v.val g' = false := by
                intro g' hg'
                obtain ⟨t0, ht0, hgt0⟩ := List.getElem_of_mem hg'
                rw [← hgt0, List.getElem_drop]
                exact honly_idx (j + 1 + t0) (by rw [List.length_drop] at ht0; omega) (by omega)
              have hag_in : ∀ i, i ≠ v.val → (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
                intro i hi
                by_cases hlt : i < n
                · rw [ofFn_getD_lt x1 false i hlt, ofFn_getD_lt x2 false i hlt]
                  exact hagr ⟨i, hlt⟩ (fun e => hi (congrArg Fin.val e))
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
              have hpre_ag := wiresFrom_agree_eff pre hok_pre v.val (List.ofFn x1) (List.ofFn x2)
                (by simp) hag_in hnr_pre
              set p1 := wiresFrom pre (List.ofFn x1)
              set p2 := wiresFrom pre (List.ofFn x2)
              have hp1len : p1.length = n + j := by
                show (wiresFrom pre (List.ofFn x1)).length = n + j
                rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
              have hp2len : p2.length = n + j := by
                show (wiresFrom pre (List.ofFn x2)).length = n + j
                rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
              have hmid_ag : ∀ i, i ≠ v.val →
                  (wiresFrom [g] p1).getD i false = (wiresFrom [g] p2).getD i false := by
                intro i hi
                have hw1 : wiresFrom [g] p1 = p1 ++ [g.op.eval (g.inputs.map fun k0 => p1.getD k0 false)] := rfl
                have hw2 : wiresFrom [g] p2 = p2 ++ [g.op.eval (g.inputs.map fun k0 => p2.getD k0 false)] := rfl
                rw [hw1, hw2]
                by_cases hlt : i < n + j
                · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
                  exact hpre_ag i hi
                · by_cases heq : i = n + j
                  · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ (by omega)]
                    exact hg_eq
                  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
              have hmid_len : (wiresFrom [g] p1).length = (wiresFrom [g] p2).length := by
                simp only [wiresFrom_length, hp1len, hp2len]
              have hpost_ag := wiresFrom_agree_eff post hok_post v.val (wiresFrom [g] p1) (wiresFrom [g] p2)
                hmid_len hmid_ag hnr_post C.output hout_ne
              show (wiresFrom C.gates (List.ofFn x1)).getD C.output false =
                (wiresFrom C.gates (List.ofFn x2)).getD C.output false
              rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_append, wiresFrom_append]
              exact hpost_ag
            rcases hop with hand | hor
            · have hr_ex : ∃ r0 : Fin n, H.Adj v r0 ∧ r0 ≠ u := by
                by_cases h1 : r1 = u
                · exact ⟨r2, hvr2, fun e => hr12 (h1.trans e.symm)⟩
                · exact ⟨r1, hvr1, h1⟩
              obtain ⟨r0, hvr0, hr0u⟩ := hr_ex
              let x1 : Fin n → Bool := fun j0 => decide (j0 = r0)
              let x2 : Fin n → Bool := fun j0 => decide (j0 = v ∨ j0 = r0)
              have hsame : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
                apply hstep_agree x1 x2
                · intro i hi; simp [x1, x2, hi]
                · have hw1u : (wiresFrom (C.gates.take j) (List.ofFn x1)).getD u.val false = false := by
                    rw [wiresFrom_keep _ _ _ (by simp [u.isLt]), ofFn_getD_lt _ _ _ u.isLt]
                    simp [x1, hr0u.symm]
                  have hw2u : (wiresFrom (C.gates.take j) (List.ofFn x2)).getD u.val false = false := by
                    rw [wiresFrom_keep _ _ _ (by simp [u.isLt]), ofFn_getD_lt _ _ _ u.isLt]
                    simp [x2, huv, hr0u.symm]
                  rw [hgins] at hu_mem ⊢
                  rcases List.mem_cons.mp hu_mem with ha_u | hb_u
                  · rw [← ha_u, hand]
                    simp only [List.map_cons, List.map_nil, hw1u, hw2u]
                    cases (wiresFrom (C.gates.take j) (List.ofFn x1)).getD b false <;>
                    cases (wiresFrom (C.gates.take j) (List.ofFn x2)).getD b false <;> rfl
                  · have hbu : u.val = b := List.mem_singleton.mp hb_u
                    rw [← hbu, hand]
                    simp only [List.map_cons, List.map_nil, hw1u, hw2u]
                    cases (wiresFrom (C.gates.take j) (List.ofFn x1)).getD a false <;>
                    cases (wiresFrom (C.gates.take j) (List.ofFn x2)).getD a false <;> rfl
              have hf2 : C.eval (List.ofFn x2) = true :=
                (hCspec x2).2 ⟨v, r0, hvr0, by simp [x2], by simp [x2]⟩
              have hf1 : C.eval (List.ofFn x1) = false := by
                cases hfx : C.eval (List.ofFn x1) with
                | false => rfl
                | true =>
                  exfalso
                  obtain ⟨p1, q1, hpq1, hp1, hq1⟩ := (hCspec x1).1 hfx
                  have hp : p1 = r0 := by simpa [x1] using hp1
                  have hq : q1 = r0 := by simpa [x1] using hq1
                  exact hpq1.ne (hp.trans hq.symm)
              rw [hf1, hf2] at hsame
              cases hsame
            · have hr_ex : ∃ r0 : Fin n, H.Adj v r0 ∧ r0 ≠ u ∧ ¬ H.Adj u r0 := by
                by_cases h1 : r1 = u
                · refine ⟨r2, hvr2, fun e => hr12 (h1.trans e.symm), fun hadj => ?_⟩
                  have g1 : G.Adj v u := (SimpleGraph.deleteIncidenceSet_adj.mp (h1 ▸ hvr1)).1
                  have g2 : G.Adj u r2 := (SimpleGraph.deleteIncidenceSet_adj.mp hadj).1
                  have g3 : G.Adj r2 v := (SimpleGraph.deleteIncidenceSet_adj.mp hvr2).1.symm
                  let cyc : G.Walk v v := SimpleGraph.Walk.cons g1 (SimpleGraph.Walk.cons g2 (SimpleGraph.Walk.cons g3 SimpleGraph.Walk.nil))
                  have hcyc : cyc.IsCycle := by
                    rw [SimpleGraph.Walk.cons_isCycle_iff]
                    refine ⟨?_, ?_⟩
                    · simp [SimpleGraph.Walk.cons_isPath_iff, g2.ne, g3.ne, (h1 ▸ hvr1).ne.symm]
                    · simp [g1.ne, g2.ne, g3.ne.symm, (h1 ▸ hvr1).ne.symm]
                  have bad := hgirth v cyc hcyc
                  simp [cyc] at bad
                · by_cases ha1 : H.Adj u r1
                  · by_cases h2 : r2 = u
                    · exfalso
                      have g1 : G.Adj v u := (SimpleGraph.deleteIncidenceSet_adj.mp (h2 ▸ hvr2)).1
                      have g2 : G.Adj u r1 := (SimpleGraph.deleteIncidenceSet_adj.mp ha1).1
                      have g3 : G.Adj r1 v := (SimpleGraph.deleteIncidenceSet_adj.mp hvr1).1.symm
                      let cyc : G.Walk v v := SimpleGraph.Walk.cons g1 (SimpleGraph.Walk.cons g2 (SimpleGraph.Walk.cons g3 SimpleGraph.Walk.nil))
                      have hcyc : cyc.IsCycle := by
                        rw [SimpleGraph.Walk.cons_isCycle_iff]
                        refine ⟨?_, ?_⟩
                        · simp [SimpleGraph.Walk.cons_isPath_iff, g2.ne, g3.ne, (h2 ▸ hvr2).ne.symm]
                        · simp [g1.ne, g2.ne, g3.ne.symm, (h2 ▸ hvr2).ne.symm]
                      have bad := hgirth v cyc hcyc
                      simp [cyc] at bad
                    · refine ⟨r2, hvr2, h2, fun ha2 => ?_⟩
                      have g1 : G.Adj v r1 := (SimpleGraph.deleteIncidenceSet_adj.mp hvr1).1
                      have g2 : G.Adj r1 u := (SimpleGraph.deleteIncidenceSet_adj.mp ha1).1.symm
                      have g3 : G.Adj u r2 := (SimpleGraph.deleteIncidenceSet_adj.mp ha2).1
                      have g4 : G.Adj r2 v := (SimpleGraph.deleteIncidenceSet_adj.mp hvr2).1.symm
                      let cyc : G.Walk v v := SimpleGraph.Walk.cons g1 (SimpleGraph.Walk.cons g2 (SimpleGraph.Walk.cons g3 (SimpleGraph.Walk.cons g4 SimpleGraph.Walk.nil)))
                      have hcyc : cyc.IsCycle := by
                        rw [SimpleGraph.Walk.cons_isCycle_iff]
                        refine ⟨?_, ?_⟩
                        · simp [SimpleGraph.Walk.cons_isPath_iff, g2.ne, g3.ne, g4.ne, hr12, huv, g1.ne.symm]
                        · simp [g1.ne, g2.ne, hr12, g1.ne.symm, g4.ne.symm, huv.symm]
                      have bad := hgirth v cyc hcyc
                      simp [cyc] at bad
                  · exact ⟨r1, hvr1, h1, ha1⟩
              obtain ⟨r0, hvr0, hr0u, hno_ur0⟩ := hr_ex
              let x1 : Fin n → Bool := fun j0 => decide (j0 = u ∨ j0 = r0)
              let x2 : Fin n → Bool := fun j0 => decide (j0 = v ∨ j0 = u ∨ j0 = r0)
              have hsame : C.eval (List.ofFn x1) = C.eval (List.ofFn x2) := by
                apply hstep_agree x1 x2
                · intro i hi; simp [x1, x2, hi]
                · have hw1u : (wiresFrom (C.gates.take j) (List.ofFn x1)).getD u.val false = true := by
                    rw [wiresFrom_keep _ _ _ (by simp [u.isLt]), ofFn_getD_lt _ _ _ u.isLt]
                    simp [x1]
                  have hw2u : (wiresFrom (C.gates.take j) (List.ofFn x2)).getD u.val false = true := by
                    rw [wiresFrom_keep _ _ _ (by simp [u.isLt]), ofFn_getD_lt _ _ _ u.isLt]
                    simp [x2]
                  rw [hgins] at hu_mem ⊢
                  rcases List.mem_cons.mp hu_mem with ha_u | hb_u
                  · rw [← ha_u, hor]
                    simp only [List.map_cons, List.map_nil, hw1u, hw2u]
                    cases (wiresFrom (C.gates.take j) (List.ofFn x1)).getD b false <;>
                    cases (wiresFrom (C.gates.take j) (List.ofFn x2)).getD b false <;> rfl
                  · have hbu : u.val = b := List.mem_singleton.mp hb_u
                    rw [← hbu, hor]
                    simp only [List.map_cons, List.map_nil, hw1u, hw2u]
                    cases (wiresFrom (C.gates.take j) (List.ofFn x1)).getD a false <;>
                    cases (wiresFrom (C.gates.take j) (List.ofFn x2)).getD a false <;> rfl
              have hf2 : C.eval (List.ofFn x2) = true :=
                (hCspec x2).2 ⟨v, r0, hvr0, by simp [x2], by simp [x2]⟩
              have hf1 : C.eval (List.ofFn x1) = false := by
                cases hfx : C.eval (List.ofFn x1) with
                | false => rfl
                | true =>
                  exfalso
                  obtain ⟨p1, q1, hpq1, hp1, hq1⟩ := (hCspec x1).1 hfx
                  rcases of_decide_eq_true hp1 with rfl | rfl <;> rcases of_decide_eq_true hq1 with rfl | rfl
                  · exact hpq1.ne rfl
                  · exact hno_ur0 hpq1
                  · exact hno_ur0 hpq1.symm
                  · exact hpq1.ne rfl
              rw [hf1, hf2] at hsame
              cases hsame
        · rw [hgins] at hlen_g; simp at hlen_g
      exact hOne n k G H z C hdegG hzdeg hgirth rfl htau hC hCspec hmin ⟨v, hv_adj, hv_len1, hinternal⟩
    · have hge2 : ∀ v : Fin n, (∃ u : Fin n, H.Adj v u) → 2 ≤ (r v).length := by
        intro v hv
        have hp := hread_pos v hv
        have hne1 : (r v).length ≠ 1 := fun e => h1 ⟨v, hv, e⟩
        omega
      have hv0nb : (H.neighborSet v0).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨u0, hu0⟩ := hv0nb
      have hv0ge2 : 2 ≤ (r v0).length := hge2 v0 ⟨u0, hu0⟩
      have hv0deg3 : (H.neighborSet v0).ncard = 3 := by
        rcases hdegH v0 with h0 | h2 | h3 <;> omega
      have hv0len2 : (r v0).length = 2 := by omega
      exact hTwo n k G H z C hdegG hzdeg hgirth rfl htau hC hCspec hmin hge2 ⟨v0, hv0deg3, hv0len2⟩
