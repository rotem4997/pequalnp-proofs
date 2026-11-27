import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7385

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresG (G : List Gate) (x : Fin 9 → Bool) : List Bool := G.foldl stepW (List.ofFn x)

def FanGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def Good (G : List Gate) (u : (Fin 9 → Bool) → Bool) : Prop :=
  (∀ x, u x = false) ∨ (∀ x, u x = true) ∨
    ∃ r < 9 + G.length, ∀ x, (wiresG G x).getD r false = u x

def img (w : (Fin 9 → Bool) → List Bool) (L : ℕ) : Finset ((Fin 9 → Bool) → Bool) :=
  (Finset.range L).image (fun j x => (w x).getD j false)

theorem foldl_length (G : List Gate) :
    ∀ w : List Bool, (G.foldl stepW w).length = w.length + G.length := by
  induction G with
  | nil => intro w; simp
  | cons g G ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]
    simp [stepW]
    omega

theorem wiresG_length (G : List Gate) (x : Fin 9 → Bool) :
    (wiresG G x).length = 9 + G.length := by
  simp [wiresG, foldl_length]

theorem stepW_getD_lt (w : List Bool) (g : Gate) (j : ℕ) (h : j < w.length) :
    (stepW w g).getD j false = w.getD j false := by
  unfold stepW
  rw [List.getD_append _ _ _ _ h]

theorem stepW_getD_len (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepW]

theorem wiresG_snoc (G : List Gate) (g : Gate) (x : Fin 9 → Bool) :
    wiresG (G ++ [g]) x = stepW (wiresG G x) g := by
  simp [wiresG, List.foldl_append]

theorem good_mono (G : List Gate) (g : Gate) (u : (Fin 9 → Bool) → Bool) (h : Good G u) :
    Good (G ++ [g]) u := by
  rcases h with h | h | ⟨r, hr, hr'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨r, by simp; omega, fun x => ?_⟩)
    rw [wiresG_snoc, stepW_getD_lt _ _ _ (by rw [wiresG_length]; exact hr)]
    exact hr' x

theorem new_form (G : List Gate) (val : ℕ → (Fin 9 → Bool) → Bool) (op : GateOp) (l : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hl : l.length ≤ 2)
    (hg : ∀ i ∈ l, Good G (val i)) :
    Good G (fun x => op.eval (l.map fun i => val i x)) ∨
      ∃ g', FanGate g' ∧ ∀ x, g'.op.eval (g'.inputs.map fun i => (wiresG G x).getD i false) =
        op.eval (l.map fun i => val i x) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  match l, hl, hg with
  | [], _, _ =>
    left
    rcases hop with rfl | rfl | rfl <;> simp [Good, GateOp.eval]
  | [i], _, hg =>
    have hi := hg i (by simp)
    rcases hop with rfl | rfl | rfl
    · left; simpa [GateOp.eval] using hi
    · left; simpa [GateOp.eval] using hi
    · rcases hi with h | h | ⟨r, hr, hr'⟩
      · left; right; left; intro x; simp [GateOp.eval, h x]
      · left; left; intro x; simp [GateOp.eval, h x]
      · right
        exact ⟨⟨GateOp.not, [r]⟩, by simp [FanGate], fun x => by simp only [List.map_cons, List.map_nil, hr' x]⟩
  | [i, j], _, hg =>
    have hi := hg i (by simp)
    have hj := hg j (by simp)
    rcases hop with rfl | rfl | rfl
    · rcases hi with hi | hi | ⟨r, hr, hr'⟩
      · left; left; intro x; simp [GateOp.eval, hi x]
      · left; simpa [GateOp.eval, hi] using hj
      · rcases hj with hj | hj | ⟨s, hs, hs'⟩
        · left; left; intro x; simp [GateOp.eval, hj x]
        · left; right; right; exact ⟨r, hr, fun x => by rw [hr' x]; simp [GateOp.eval, hj x]⟩
        · right
          exact ⟨⟨GateOp.and, [r, s]⟩, by simp [FanGate],
            fun x => by simp only [List.map_cons, List.map_nil, hr' x, hs' x]⟩
    · rcases hi with hi | hi | ⟨r, hr, hr'⟩
      · left; simpa [GateOp.eval, hi] using hj
      · left; right; left; intro x; simp [GateOp.eval, hi x]
      · rcases hj with hj | hj | ⟨s, hs, hs'⟩
        · left; right; right; exact ⟨r, hr, fun x => by rw [hr' x]; simp [GateOp.eval, hj x]⟩
        · left; right; left; intro x; simp [GateOp.eval, hj x]
        · right
          exact ⟨⟨GateOp.or, [r, s]⟩, by simp [FanGate],
            fun x => by simp only [List.map_cons, List.map_nil, hr' x, hs' x]⟩
    · rcases hi with hi | hi | ⟨r, hr, hr'⟩
      · left; right; left; intro x; simp [GateOp.eval, hi x]
      · left; left; intro x; simp [GateOp.eval, hi x]
      · right
        exact ⟨⟨GateOp.not, [r]⟩, by simp [FanGate], fun x => by simp only [List.map_cons, List.map_nil, hr' x]; rfl⟩
  | _ :: _ :: _ :: _, h, _ => simp at h

theorem img_step (w : (Fin 9 → Bool) → List Bool) (L : ℕ) (hL : ∀ x, (w x).length = L)
    (g : Gate) :
    img (fun x => stepW (w x) g) (L + 1) =
      insert (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) (img w L) := by
  unfold img
  rw [Finset.range_add_one, Finset.image_insert]
  congr 1
  · funext x
    have := stepW_getD_len (w x) g
    rw [hL x] at this
    exact this
  · apply Finset.image_congr
    intro j hj
    funext x
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    exact stepW_getD_lt _ _ _ (by rw [hL x]; exact hj)

theorem main (gs : List Gate) (hfan : ∀ g ∈ gs, FanGate g) :
    ∀ (w : (Fin 9 → Bool) → List Bool) (L : ℕ), (∀ x, (w x).length = L) →
    ∀ (G : List Gate), (∀ g ∈ G, FanGate g) →
    (∀ j < L, Good G (fun x => (w x).getD j false)) →
    ∃ G' : List Gate, (∀ g ∈ G', FanGate g) ∧
      G'.length + (img w L).card ≤
        G.length + (img (fun x => gs.foldl stepW (w x)) (L + gs.length)).card ∧
      ∀ j < L + gs.length, Good G' (fun x => (gs.foldl stepW (w x)).getD j false) := by
  induction gs with
  | nil =>
    intro w L hL G hG hinv
    exact ⟨G, hG, by simp, by simpa using hinv⟩
  | cons g gs ih =>
    intro w L hL G hG hinv
    have hfg : FanGate g := hfan g (by simp)
    have hfan' : ∀ g ∈ gs, FanGate g := fun g' hg' => hfan g' (by simp [hg'])
    have hL1 : ∀ x, (stepW (w x) g).length = L + 1 := by intro x; simp [stepW, hL x]
    have himg := img_step w L hL g
    have hlen : L + (g :: gs).length = (L + 1) + gs.length := by simp; omega
    have e : (fun x => (g :: gs).foldl stepW (w x)) =
        (fun x => gs.foldl stepW (stepW (w x) g)) := rfl
    have hin : ∀ i ∈ g.inputs, Good G (fun x => (w x).getD i false) := by
      intro i _
      by_cases hi : i < L
      · exact hinv i hi
      · left; intro x
        exact List.getD_eq_default _ _ (by rw [hL x]; omega)
    have inv1 : ∀ G1 : List Gate, (∀ j < L, Good G1 (fun x => (w x).getD j false)) →
        Good G1 (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) →
        ∀ j < L + 1, Good G1 (fun x => (stepW (w x) g).getD j false) := by
      intro G1 h1 hf1 j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · have : (fun x => (stepW (w x) g).getD j false) = (fun x => (w x).getD j false) := by
          funext x; exact stepW_getD_lt _ _ _ (by rw [hL x]; exact hj)
        rw [this]; exact h1 j hj
      · have : (fun x => (stepW (w x) g).getD j false) =
            (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) := by
          funext x; rw [hj]; have := stepW_getD_len (w x) g; rw [hL x] at this; exact this
        rw [this]; exact hf1
    by_cases hmem : (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) ∈ img w L
    · have hgf : Good G (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) := by
        unfold img at hmem
        rw [Finset.mem_image] at hmem
        obtain ⟨j, hj, hjf⟩ := hmem
        rw [← hjf]; exact hinv j (Finset.mem_range.mp hj)
      obtain ⟨G', hG', hc, hinv'⟩ :=
        ih hfan' (fun x => stepW (w x) g) (L + 1) hL1 G hG (inv1 G hinv hgf)
      refine ⟨G', hG', ?_, ?_⟩
      · rw [himg, Finset.insert_eq_of_mem hmem] at hc
        rw [hlen, e]; exact hc
      · intro j hj; exact hinv' j (by omega)
    · have hcard : (img (fun x => stepW (w x) g) (L + 1)).card = (img w L).card + 1 := by
        rw [himg, Finset.card_insert_of_notMem hmem]
      rcases new_form G (fun i x => (w x).getD i false) g.op g.inputs hfg.1 hfg.2 hin with hgf | ⟨g', hg', hg'v⟩
      · obtain ⟨G', hG', hc, hinv'⟩ :=
          ih hfan' (fun x => stepW (w x) g) (L + 1) hL1 G hG (inv1 G hinv hgf)
        refine ⟨G', hG', ?_, ?_⟩
        · rw [hlen, e]; rw [hcard] at hc; omega
        · intro j hj; exact hinv' j (by omega)
      · have hG1 : ∀ g0 ∈ G ++ [g'], FanGate g0 := by
          intro g0 h0
          simp only [List.mem_append, List.mem_singleton] at h0
          rcases h0 with h0 | rfl
          · exact hG g0 h0
          · exact hg'
        have hgf : Good (G ++ [g'])
            (fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)) := by
          right; right
          refine ⟨9 + G.length, by simp, fun x => ?_⟩
          rw [wiresG_snoc]
          have := stepW_getD_len (wiresG G x) g'
          rw [wiresG_length] at this
          rw [this]; exact hg'v x
        obtain ⟨G', hG', hc, hinv'⟩ :=
          ih hfan' (fun x => stepW (w x) g) (L + 1) hL1 (G ++ [g']) hG1
            (inv1 _ (fun j hj => good_mono _ _ _ (hinv j hj)) hgf)
        refine ⟨G', hG', ?_, ?_⟩
        · rw [hlen, e]; rw [hcard] at hc
          simp only [List.length_append, List.length_singleton] at hc
          omega
        · intro j hj; exact hinv' j (by omega)

theorem final (σ : (Fin 9 → Bool) → List Bool) (hσl : ∀ x, (σ x).length = 11)
    (hσ : ∀ j < 11, Good [] (fun x => (σ x).getD j false)) (hcard : 11 ≤ (img σ 11).card)
    (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hx : ∃ x, C.eval (σ x) = false) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + 11 ≤ (Finset.image (fun (k : Fin (11 + C.size)) (x : Fin 9 → Bool) =>
        (C.wires (σ x)).getD ↑k false) Finset.univ).card ∧
      ∀ x, D.eval (List.ofFn x) = C.eval (σ x) := by
  obtain ⟨x0, hx0⟩ := hx
  have hCfan : ∀ g ∈ C.gates, FanGate g := fun g hg => hC g hg
  obtain ⟨G', hG', hc, hinv⟩ := main C.gates hCfan σ 11 hσl [] (by simp) hσ
  have himgeq : Finset.image (fun (k : Fin (11 + C.size)) (x : Fin 9 → Bool) =>
      (C.wires (σ x)).getD ↑k false) Finset.univ =
      img (fun x => C.gates.foldl stepW (σ x)) (11 + C.gates.length) := by
    ext f
    simp only [img, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k.val, k.isLt, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
  have hcard' : G'.length + 11 ≤ (Finset.image (fun (k : Fin (11 + C.size))
      (x : Fin 9 → Bool) => (C.wires (σ x)).getD ↑k false) Finset.univ).card := by
    rw [himgeq]
    simp only [List.length_nil, Nat.zero_add] at hc
    omega
  have hgood : Good G' (fun x => (C.gates.foldl stepW (σ x)).getD C.output false) := by
    by_cases ho : C.output < 11 + C.gates.length
    · exact hinv _ ho
    · left; intro x
      exact List.getD_eq_default _ _ (by rw [foldl_length, hσl]; omega)
  have hfanD : ∀ o, PEqualNP.MetaComplexity.FanInTwo ⟨G', o⟩ := fun o g hg => hG' g hg
  rcases hgood with h0 | h1 | ⟨r, hr, hr'⟩
  · refine ⟨⟨G', 9 + G'.length⟩, hfanD _, hcard', fun x => ?_⟩
    show (wiresG G' x).getD (9 + G'.length) false = C.eval (σ x)
    rw [List.getD_eq_default _ _ (by rw [wiresG_length])]
    exact (h0 x).symm
  · exfalso
    have := h1 x0
    change C.eval (σ x0) = true at this
    rw [hx0] at this
    exact Bool.false_ne_true this
  · refine ⟨⟨G', r⟩, hfanD _, hcard', fun x => ?_⟩
    show (wiresG G' x).getD r false = C.eval (σ x)
    rw [hr' x]
    rfl

def sig (x : Fin 9 → Bool) : List Bool :=
  [false, x 4, x 0, x 1, x 6, x 7, x 3, x 5, x 2, x 8, true]

theorem sig_good : ∀ j < 11, Good [] (fun x => (sig x).getD j false) := by
  intro j hj
  interval_cases j
  · left; intro x; rfl
  · right; right; exact ⟨4, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨0, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨1, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨6, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨7, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨3, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨5, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨2, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; right; exact ⟨8, by norm_num, fun x => by simp [wiresG, sig]⟩
  · right; left; intro x; rfl

def tp (t : Fin 10) : Fin 9 → Bool := fun i => decide (i.val = t.val)

theorem sig_key : ∀ j < 11, ∀ k < 11,
    (∀ t : Fin 10, (sig (tp t)).getD j false = (sig (tp t)).getD k false) → j = k := by
  decide

theorem sig_card : 11 ≤ (img sig 11).card := by
  unfold img
  rw [Finset.card_image_of_injOn]
  · simp
  · intro j hj k hk h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    exact sig_key j hj k hk (fun t => congrFun h (tp t))

end PEqualNP.Outside.L_meta_7385

theorem PEqualNP.Outside.L_meta_7385 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval [Bool.false, x3 (4 : Fin (9 : ℕ)), x3 (0 : Fin (9 : ℕ)), x3 (1 : Fin (9 : ℕ)), x3 (6 : Fin (9 : ℕ)), x3 (7 : Fin (9 : ℕ)), x3 (3 : Fin (9 : ℕ)), x3 (5 : Fin (9 : ℕ)), x3 (2 : Fin (9 : ℕ)), x3 (8 : Fin (9 : ℕ)), Bool.true] = Bool.false) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size + (11 : ℕ) ≤ (Finset.image (fun (x5 : Fin ((11 : ℕ) + x1.size)) (x6 : Fin (9 : ℕ) → Bool) => (x1.wires [Bool.false, x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)), x6 (1 : Fin (9 : ℕ)), x6 (6 : Fin (9 : ℕ)), x6 (7 : Fin (9 : ℕ)), x6 (3 : Fin (9 : ℕ)), x6 (5 : Fin (9 : ℕ)), x6 (2 : Fin (9 : ℕ)), x6 (8 : Fin (9 : ℕ)), Bool.true]).getD (↑x5) Bool.false) Finset.univ).card ∧ ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval [Bool.false, x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)), x5 (1 : Fin (9 : ℕ)), x5 (6 : Fin (9 : ℕ)), x5 (7 : Fin (9 : ℕ)), x5 (3 : Fin (9 : ℕ)), x5 (5 : Fin (9 : ℕ)), x5 (2 : Fin (9 : ℕ)), x5 (8 : Fin (9 : ℕ)), Bool.true] := by
  intro C hC hx
  exact PEqualNP.Outside.L_meta_7385.final PEqualNP.Outside.L_meta_7385.sig (fun _ => rfl)
    PEqualNP.Outside.L_meta_7385.sig_good PEqualNP.Outside.L_meta_7385.sig_card C hC hx
