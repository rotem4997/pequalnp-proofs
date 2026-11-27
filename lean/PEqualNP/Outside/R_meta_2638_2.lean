import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2638_2
    (hRead1 : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (C : Circuit) (r : Fin n → List Gate),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      H = G.deleteIncidenceSet z →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      FanInTwo C →
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ s : ℕ, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (∀ v : Fin n, r v = C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val) →
      (∃ v : Fin n, (∃ u : Fin n, H.Adj v u) ∧ (r v).length = 1) →
      H.edgeSet.ncard + k ≤ C.size + 1)
    (hRead2NonOr : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (C : Circuit) (r : Fin n → List Gate),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      H = G.deleteIncidenceSet z →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      FanInTwo C →
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ s : ℕ, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (∀ v : Fin n, r v = C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val) →
      (∀ v : Fin n, (∃ u : Fin n, H.Adj v u) → 2 ≤ (r v).length) →
      (∃ v : Fin n, (H.neighborSet v).ncard = 3 ∧ (r v).length = 2 ∧ ∃ g ∈ r v, g.op ≠ GateOp.or) →
      H.edgeSet.ncard + k ≤ C.size + 1)
    (hRead2AllOr : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (C : Circuit) (r : Fin n → List Gate),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      H = G.deleteIncidenceSet z →
      (∀ T : Finset (Fin n), (∀ u v : Fin n, H.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
      FanInTwo C →
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ s : ℕ, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (∀ v : Fin n, r v = C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val) →
      (∀ v : Fin n, (∃ u : Fin n, H.Adj v u) → 2 ≤ (r v).length) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 3 → (r v).length = 2 → ∀ g ∈ r v, g.op = GateOp.or) →
      (∃ v : Fin n, (H.neighborSet v).ncard = 3 ∧ (r v).length = 2) →
      H.edgeSet.ncard + k ≤ C.size + 1) :
    ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  intro n k s G A z f hdeg hgirth hnoA hE hzA hf htau hs
  let H : SimpleGraph (Fin n) := G.deleteIncidenceSet z
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
          simp [H, SimpleGraph.mem_neighborSet, SimpleGraph.deleteIncidenceSet_adj, hvz]
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
  let wiresFrom : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append : ∀ (gs₁ gs₂ : List Gate) (w : List Bool),
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    clear * -
    intro gs₁ gs₂ w
    simp [wiresFrom, List.foldl_append]
  have wiresFrom_length : ∀ (gs : List Gate) (w : List Bool),
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
  have wiresFrom_keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
    clear * - getD_snoc_lt
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g rest ih =>
      intro w i hi
      have hstep : wiresFrom (g :: rest) w =
          wiresFrom rest (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) := rfl
      rw [hstep, ih _ i (by simp; omega), getD_snoc_lt _ _ _ _ hi]
  let reads : ℕ → Gate → Bool := fun v g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
  have wiresFrom_agree_eff : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (v : ℕ) (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, i ≠ v → w₁.getD i false = w₂.getD i false) →
      (∀ g ∈ gs, reads v g = false) →
      ∀ i, i ≠ v → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    clear * - getD_snoc_lt getD_snoc_eq
    have gate_eval_agree : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
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
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
      rcases hop' with h | h | h
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : GateOp.and.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · have ht2 : g.inputs.take (bif g.op.eval [false] then 1 else 2) = g.inputs := by
          rw [h]
          have : GateOp.or.eval [false] = false := rfl
          rw [this]
          exact List.take_of_length_le hlen
        rw [ht2] at hnr'
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hag i (fun he => hnr' (he ▸ hi))
      · rw [h] at hnr' ⊢
        have : GateOp.not.eval [false] = true := rfl
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
          wiresFrom rest (w₁ ++ [g.op.eval (g.inputs.map fun k => w₁.getD k false)]) := rfl
      have h2 : wiresFrom (g :: rest) w₂ =
          wiresFrom rest (w₂ ++ [g.op.eval (g.inputs.map fun k => w₂.getD k false)]) := rfl
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
        HasCircuitSize n g0 t0 ∧
        ∀ x : Fin n → Bool, g0 x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
    clear * - hHE hnoAH hf hs getD_snoc_lt getD_snoc_eq ofFn_getD_lt wiresFrom_append
      wiresFrom_length wiresFrom_keep wiresFrom_agree_eff
    let sval : List Bool → Bool ⊕ ℕ → Bool := fun w st =>
      Sum.elim id (fun j => w.getD j false) st
    let svalid : ℕ → Bool ⊕ ℕ → Prop := fun m st =>
      Sum.elim (fun _ => True) (fun j => j < m) st
    obtain ⟨simplify, simplify_ok, simplify_drop, simplify_sound⟩ :
        ∃ simplify : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ),
          (∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (g : Gate),
            g ∈ (simplify op m ins).1.toList →
            g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          (∀ (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)),
            op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
            ins.length ≤ 2 →
            (∃ c : Bool, Sum.inl c ∈ ins.take (bif op.eval [false] then 1 else 2)) →
            (simplify op m ins).1 = none) ∧
          (∀ (op : GateOp),
            op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
            ∀ (w : List Bool) (ins : List (Bool ⊕ ℕ)), ins.length ≤ 2 →
            (∀ st ∈ ins, svalid w.length st) →
            svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
            sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2 =
              op.eval (ins.map (sval w))) := by
      clear * - getD_snoc_eq
      let and2 : ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ → Option Gate × (Bool ⊕ ℕ) := fun m a b =>
        Sum.elim (fun c => (none, bif c then b else Sum.inl false))
          (fun j => Sum.elim (fun d => (none, bif d then Sum.inr j else Sum.inl false))
            (fun l => (some ⟨GateOp.and, [j, l]⟩, Sum.inr m)) b) a
      let or2 : ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ → Option Gate × (Bool ⊕ ℕ) := fun m a b =>
        Sum.elim (fun c => (none, bif c then Sum.inl true else b))
          (fun j => Sum.elim (fun d => (none, bif d then Sum.inl true else Sum.inr j))
            (fun l => (some ⟨GateOp.or, [j, l]⟩, Sum.inr m)) b) a
      let simpFn : GateOp → ℕ → List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ) := fun op m ins =>
        GateOp.casesOn op
          (List.casesOn ins (none, Sum.inl true) (fun a l1 =>
            List.casesOn l1 (none, a) (fun b l2 =>
              List.casesOn l2 (and2 m a b) (fun _ _ => (none, Sum.inl false)))))
          (List.casesOn ins (none, Sum.inl false) (fun a l1 =>
            List.casesOn l1 (none, a) (fun b l2 =>
              List.casesOn l2 (or2 m a b) (fun _ _ => (none, Sum.inl false)))))
          (List.casesOn ins (none, Sum.inl true) (fun a _ =>
            Sum.elim (fun c => (none, Sum.inl (!c)))
              (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m)) a))
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
        have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
        rcases hop' with rfl | rfl | rfl
        · have htake : ins.take (bif GateOp.and.eval [false] then 1 else 2) = ins :=
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
        · have htake : ins.take (bif GateOp.or.eval [false] then 1 else 2) = ins :=
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
        · have htake : ins.take (bif GateOp.not.eval [false] then 1 else 2) = ins.take 1 := rfl
          rw [htake] at hc
          rcases ins with _ | ⟨a, l⟩
          · cases hc
          · rcases List.mem_singleton.mp hc with rfl
            rfl
      · intro op hop w ins hlen hv
        have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
        rcases hop' with rfl | rfl | rfl
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · exact ⟨trivial, rfl⟩
          · have ha := hv a List.mem_cons_self
            refine ⟨ha, ?_⟩
            show sval w a = GateOp.and.eval [sval w a]
            cases sval w a <;> rfl
          · have ha := hv a List.mem_cons_self
            have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
            rcases a with c | j
            · cases c
              · exact ⟨trivial, rfl⟩
              · refine ⟨hb, ?_⟩
                show sval w b = GateOp.and.eval [true, sval w b]
                cases sval w b <;> rfl
            · rcases b with d | l
              · cases d
                · refine ⟨trivial, ?_⟩
                  show false = GateOp.and.eval [w.getD j false, false]
                  cases w.getD j false <;> rfl
                · refine ⟨ha, ?_⟩
                  show w.getD j false = GateOp.and.eval [w.getD j false, true]
                  cases w.getD j false <;> rfl
              · refine ⟨Nat.lt_succ_self w.length, ?_⟩
                show (w ++ [GateOp.and.eval [w.getD j false, w.getD l false]]).getD w.length false =
                  GateOp.and.eval [w.getD j false, w.getD l false]
                exact getD_snoc_eq w _ false w.length rfl
          · simp at hlen
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
          · exact ⟨trivial, rfl⟩
          · have ha := hv a List.mem_cons_self
            refine ⟨ha, ?_⟩
            show sval w a = GateOp.or.eval [sval w a]
            cases sval w a <;> rfl
          · have ha := hv a List.mem_cons_self
            have hb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
            rcases a with c | j
            · cases c
              · refine ⟨hb, ?_⟩
                show sval w b = GateOp.or.eval [false, sval w b]
                cases sval w b <;> rfl
              · exact ⟨trivial, rfl⟩
            · rcases b with d | l
              · cases d
                · refine ⟨ha, ?_⟩
                  show w.getD j false = GateOp.or.eval [w.getD j false, false]
                  cases w.getD j false <;> rfl
                · refine ⟨trivial, ?_⟩
                  show true = GateOp.or.eval [w.getD j false, true]
                  cases w.getD j false <;> rfl
              · refine ⟨Nat.lt_succ_self w.length, ?_⟩
                show (w ++ [GateOp.or.eval [w.getD j false, w.getD l false]]).getD w.length false =
                  GateOp.or.eval [w.getD j false, w.getD l false]
                exact getD_snoc_eq w _ false w.length rfl
          · simp at hlen
        · rcases ins with _ | ⟨a, l⟩
          · exact ⟨trivial, rfl⟩
          · rcases a with c | j
            · exact ⟨trivial, rfl⟩
            · refine ⟨Nat.lt_succ_self w.length, ?_⟩
              show (w ++ [GateOp.not.eval [w.getD j false]]).getD w.length false =
                GateOp.not.eval (w.getD j false :: l.map (sval w))
              rw [getD_snoc_eq w _ false w.length rfl]
              rfl
    obtain ⟨elim, elim_len_drop, elim_ok, elim_sound⟩ :
        ∃ elim : List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate,
          (∀ (gs : List Gate),
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List Gate) (v : ℕ),
            v < acc.1.length → acc.1.getD v (Sum.inl false) = Sum.inl false →
            (∃ g ∈ gs, reads v g = true) →
            (elim gs acc).2.length + 1 ≤ acc.2.length + gs.length) ∧
          (∀ (gs : List Gate),
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List Gate),
            (∀ g ∈ acc.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ g ∈ (elim gs acc).2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          (∀ (gs : List Gate),
            (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ (acc : List (Bool ⊕ ℕ) × List Gate) (w_old w_new : List Bool),
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
      let elimStep : List (Bool ⊕ ℕ) × List Gate → Gate → List (Bool ⊕ ℕ) × List Gate := fun acc g =>
        let res := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
        (acc.1 ++ [res.2], acc.2 ++ res.1.toList)
      let elimFn : List Gate → List (Bool ⊕ ℕ) × List Gate → List (Bool ⊕ ℕ) × List Gate := fun gs acc =>
        gs.foldl elimStep acc
      have opt_toList_le : ∀ o : Option Gate, o.toList.length ≤ 1 := by
        intro o; cases o <;> simp
      have elim_len_le : ∀ (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate),
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
          have hsub : ∀ (gs0 : List Gate) (a0 : List (Bool ⊕ ℕ) × List Gate),
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
        HasCircuitSize n fB s0 →
        ∃ t0 : ℕ, t0 + B.card ≤ s0 ∧ ∃ g0 : (Fin n → Bool) → Bool,
          HasCircuitSize n g0 t0 ∧
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
        let init : List (Bool ⊕ ℕ) × List Gate :=
          (List.ofFn (fun k0 : Fin n => if k0 = p then Sum.inl false else Sum.inr k0.val), [])
        let res := elim D.gates init
        have hdrop : res.2.length + 1 ≤ D.gates.length := by
          have hd := elim_len_drop D.gates hD init p.val (by simp [init])
            (by simp [init]) hread_p
          simpa [res, init] using hd
        have hok_res : ∀ g ∈ res.2,
            g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
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
        · have hsB' : HasCircuitSize n fB' res.2.length := by
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
  have hex : ∃ m : ℕ, HasCircuitSize n g0 m := ⟨t, htg0⟩
  obtain ⟨C, hC, hCsz, hCval⟩ := Nat.find_spec hex
  have hCt : C.size ≤ t := hCsz.trans (Nat.find_min' hex htg0)
  have heval : circuitFun n C = g0 := funext hCval
  have hCspec : ∀ x : Fin n → Bool,
      circuitFun n C x = true ↔ ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro x; rw [heval]; exact hg0 x
  have hmin : ∀ m : ℕ, HasCircuitSize n (circuitFun n C) m → C.size ≤ m := by
    intro m hm; rw [heval] at hm; exact hCsz.trans (Nat.find_min' hex hm)
  suffices hgoal : H.edgeSet.ncard + k ≤ C.size + 1 by
    change A.card + H.edgeSet.ncard + k ≤ s + 1
    omega
  have deleteDeadGate : ∀ (D : Circuit) (hD : FanInTwo D) (j : ℕ) (hj : j < D.gates.length),
      D.output ≠ n + j →
      (∀ j' : ℕ, (hj' : j' < D.gates.length) → j < j' → (n + j) ∉ D.gates[j'].inputs) →
      HasCircuitSize n (circuitFun n D) (D.gates.length - 1) := by
    clear * - getD_snoc_lt getD_snoc_eq wiresFrom_append wiresFrom_length
    let substWire : ℕ → ℕ → ℕ → ℕ := fun k0 a i =>
      if i < k0 then i else if i = k0 then a else i - 1
    let substGate : ℕ → ℕ → Gate → Gate := fun k0 a g =>
      ⟨g.op, g.inputs.map (substWire k0 a)⟩
    let deleteGate : Circuit → ℕ → ℕ → Circuit := fun D j a =>
      ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j) a),
        substWire (n + j) a D.output⟩
    have deleteGate_ok : ∀ (D : Circuit) (j a : ℕ), FanInTwo D → FanInTwo (deleteGate D j a) := by
      intro D j a hok g hg
      rcases List.mem_append.1 hg with h1 | h1
      · exact hok g (List.mem_of_mem_take h1)
      · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 h1
        have h0 := hok g1 (List.mem_of_mem_drop hg1)
        exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
    have deleteGate_len : ∀ (D : Circuit) (j a : ℕ), j < D.gates.length →
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
      have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
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
  let r : Fin n → List Gate := fun v => C.gates.filter (reads v.val)
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
      have h1 : circuitFun n C xv = true := by
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
      have heq : circuitFun n C x1 = circuitFun n C x2 :=
        wiresFrom_agree_eff C.gates hC v.val (List.ofFn x1) (List.ofFn x2) (by simp) hag hempty
          C.output hout
      have hf2 : circuitFun n C x2 = true :=
        (hCspec x2).2 ⟨v, u, huv, by simp [x2], by simp [x2]⟩
      have hf1 : circuitFun n C x1 = false := by
        cases hfx : circuitFun n C x1 with
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
    let slots : Circuit → List ℕ := fun D => D.output :: D.gates.flatMap Gate.inputs
    have gateSlotBound : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
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
    have filteredSlots : ∀ (v : ℕ) (gs : List Gate),
        (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
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
    have lowerV := Finset.sum_le_sum hcnt_deg
    rw [H.sum_degrees_eq_twice_card_edges, Fin.sum_univ_eq_sum_range] at lowerV
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
    · exact hRead1 n k G H z C r hdegG hzdeg hgirth rfl htau hC hCspec hmin (fun _ => rfl) h1
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
      by_cases hnonor : ∃ v : Fin n,
          (H.neighborSet v).ncard = 3 ∧ (r v).length = 2 ∧ ∃ g ∈ r v, g.op ≠ GateOp.or
      · exact hRead2NonOr n k G H z C r hdegG hzdeg hgirth rfl htau hC hCspec hmin (fun _ => rfl) hge2 hnonor
      · have hallor : ∀ v : Fin n,
            (H.neighborSet v).ncard = 3 → (r v).length = 2 → ∀ g ∈ r v, g.op = GateOp.or := by
          intro v hv3 hv2 g hgr
          by_contra hne
          exact hnonor ⟨v, hv3, hv2, g, hgr, hne⟩
        exact hRead2AllOr n k G H z C r hdegG hzdeg hgirth rfl htau hC hCspec hmin
          (fun _ => rfl) hge2 hallor ⟨v0, hv0deg3, hv0len2⟩
