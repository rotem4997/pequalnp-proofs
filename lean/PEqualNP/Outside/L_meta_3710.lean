import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3710
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

theorem ev_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ ins, f i = true → g i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map g) = true := by
  rcases hop with h' | h' <;> rw [h']
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h i hi (H i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hi hv⟩

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def sg (n g a : ℕ) (gg : Gate) : Gate :=
  { op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) }

theorem same (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (heq : (wf gs X).getD (n + g) false = (wf gs X).getD a false) :
    ∀ m, m ≤ gs.length → wf ((gs.map (sg n g a)).take m) X = wf (gs.take m) X := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hm' : m < gs.length := hm
    have t1 : (gs.map (sg n g a)).take (m + 1) = (gs.map (sg n g a)).take m ++ [sg n g a gs[m]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.getElem_map]
    have t2 : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem hm'
    rw [t1, t2, wf_snoc, wf_snoc, ih (le_of_lt hm')]
    congr 2
    show gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
        fun i => (wf (gs.take m) X).getD i false)
      = gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false)
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    show (wf (gs.take m) X).getD (if i = n + g then a else i) false = (wf (gs.take m) X).getD i false
    split_ifs with h
    · have hi' := hrb m hm' i hi
      rw [h, ← wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm'),
        ← wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm')]
      exact heq.symm
    · rfl

theorem up (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (hao : ∀ gg ∈ gs, gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hga : (wf gs X).getD (n + g) false = true → (wf gs X).getD a false = true) :
    ∀ m, m ≤ gs.length → ∀ i, (wf (gs.take m) X).getD i false = true →
      (wf ((gs.map (sg n g a)).take m) X).getD i false = true := by
  intro m
  induction m with
  | zero => intro _ i h; exact h
  | succ m ih =>
    intro hm
    have hm' : m < gs.length := hm
    have ih' := ih (le_of_lt hm')
    have t1 : (gs.map (sg n g a)).take (m + 1) = (gs.map (sg n g a)).take m ++ [sg n g a gs[m]] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hm'), List.getElem_map]
    have t2 : gs.take (m + 1) = gs.take m ++ [gs[m]] := List.take_succ_eq_append_getElem hm'
    rw [t1, t2, wf_snoc, wf_snoc]
    apply app_mono _ _ _ _ (by
      rw [wf_len, wf_len, List.length_take, List.length_take, List.length_map]) ih'
    intro j
    cases j with
    | succ j => intro h1; simp at h1
    | zero =>
      show gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false) = true →
        gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
          fun i => (wf ((gs.map (sg n g a)).take m) X).getD i false) = true
      rw [List.map_map]
      apply ev_mono gs[m].op (hao _ (List.getElem_mem hm')) gs[m].inputs
      intro i hi hp
      show (wf ((gs.map (sg n g a)).take m) X).getD (if i = n + g then a else i) false = true
      split_ifs with h
      · have hi' := hrb m hm' i hi
        apply ih'
        rw [← wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm')]
        apply hga
        rw [wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm'), ← h]
        exact hp
      · exact ih' i hp

end PEqualNP.Outside.L_meta_3710

open PEqualNP.Outside.L_meta_3710 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3710 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (g a b : ℕ) (v : Fin n),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  g < C.gates.length →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [a, b] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [b, a]) →
  (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput v))).getD b false = true →
  (∀ w : Fin n, G.Adj v w → (C.wires (List.ofFn (PEqualNP.SplitCount.unitInput w))).getD b false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + g then a else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C g a b v hAO hfun hg hop hin hbv hbN
  obtain ⟨hao, hrb, hlen2⟩ := hAO
  have hrb' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j :=
    fun j hj i hi => hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  rw [gateAt_eq C g hg] at hop hin
  have ha : a < n + g := by
    apply hrb' g hg a
    rcases hin with h | h <;> rw [h] <;> simp
  have gv : ∀ X : List Bool, X.length = n → (wf C.gates X).getD (n + g) false
      = ((wf C.gates X).getD a false && (wf C.gates X).getD b false) := by
    intro X hX
    have h1 := gate_full C.gates X g hg (by intro i hi; rw [hX]; exact hrb' g hg i hi)
    rw [hX, hop] at h1
    rw [h1]
    rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm]
  have hleg : ∀ gg ∈ C.gates, (gg.op = GateOp.and ∨ gg.op = GateOp.or) ∧ gg.inputs.length ≤ 2 :=
    fun gg hgg => ⟨hao gg hgg, le_of_eq (hlen2 gg hgg)⟩
  have hleg' : ∀ gg ∈ C.gates.map (sg n g a),
      (gg.op = GateOp.and ∨ gg.op = GateOp.or) ∧ gg.inputs.length ≤ 2 := by
    intro gg hgg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hgg
    refine ⟨hao g0 hg0, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]; exact le_of_eq (hlen2 g0 hg0)
  have SAMEx : ∀ X : List Bool, X.length = n → (wf C.gates X).getD b false = true →
      wf (C.gates.map (sg n g a)) X = wf C.gates X := by
    intro X hX hB
    have h1 := same n g a C.gates X hX hrb' ha (by rw [gv X hX, hB, Bool.and_true])
      C.gates.length (le_refl _)
    have e1 : (C.gates.map (sg n g a)).take C.gates.length = C.gates.map (sg n g a) :=
      List.take_of_length_le (by simp)
    have e2 : C.gates.take C.gates.length = C.gates := List.take_of_length_le (le_refl _)
    rw [e1, e2] at h1
    exact h1
  have UPx : ∀ X : List Bool, X.length = n → ∀ i, (wf C.gates X).getD i false = true →
      (wf (C.gates.map (sg n g a)) X).getD i false = true := by
    intro X hX i hi
    have h1 := up n g a C.gates X hX hrb' ha hao (by
      intro h2
      rw [gv X hX] at h2
      exact (Bool.and_eq_true _ _ ▸ h2).1) C.gates.length (le_refl _) i
    have e1 : (C.gates.map (sg n g a)).take C.gates.length = C.gates.map (sg n g a) :=
      List.take_of_length_le (by simp)
    have e2 : C.gates.take C.gates.length = C.gates := List.take_of_length_le (le_refl _)
    rw [e1, e2] at h1
    exact h1 hi
  show PEqualNP.MetaComplexity.circuitFun n ⟨C.gates.map (sg n g a), C.output⟩ = _
  funext x
  rw [← hfun]
  show (wf (C.gates.map (sg n g a)) (List.ofFn x)).getD C.output false
    = (wf C.gates (List.ofFn x)).getD C.output false
  by_cases hB : (wf C.gates (List.ofFn x)).getD b false = true
  · rw [SAMEx _ (by simp) hB]
  · apply Bool.eq_iff_iff.2
    constructor
    · intro h'
      have hbt : ∀ t : Fin n,
          (wf C.gates (List.ofFn (PEqualNP.SplitCount.unitInput t))).getD b false = true →
          x t = true → (wf C.gates (List.ofFn x)).getD b false = true := by
        intro t h1 hxt
        exact mono2 C.gates hleg _ _ (by simp) (ofFn_mono n _ x (fun s hs => by
          rw [of_decide_eq_true hs]; exact hxt)) b h1
      obtain ⟨y, hy⟩ : ∃ y : Fin n → Bool, y = Function.update x v true := ⟨_, rfl⟩
      have hxy : ∀ t, x t = true → y t = true := by
        intro t ht
        rw [hy]
        by_cases e : t = v
        · rw [e, Function.update_self]
        · rw [Function.update_of_ne e]; exact ht
      have h'y := mono2 _ hleg' _ _ (by simp) (ofFn_mono n x y hxy) _ h'
      have hBy : (wf C.gates (List.ofFn y)).getD b false = true :=
        mono2 C.gates hleg _ _ (by simp) (ofFn_mono n _ y (fun s hs => by
          rw [of_decide_eq_true hs, hy, Function.update_self])) b hbv
      rw [SAMEx _ (by simp) hBy] at h'y
      have hFy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true := by
        rw [← hfun]; exact h'y
      have hFy' : ∃ u w, G.Adj u w ∧ y u = true ∧ y w = true := by
        unfold PEqualNP.MetaComplexity.NestedCover.graphFun at hFy
        simpa using hFy
      obtain ⟨u, w, hadj, hu, hw⟩ := hFy'
      have hne : u ≠ w := G.ne_of_adj hadj
      have huv : u ≠ v := by
        intro e
        rw [e] at hadj hne
        have hw2 : x w = true := by
          rw [hy, Function.update_of_ne (Ne.symm hne)] at hw; exact hw
        exact hB (hbt w (hbN w hadj) hw2)
      have hwv : w ≠ v := by
        intro e
        rw [e] at hadj hne
        have hu2 : x u = true := by
          rw [hy, Function.update_of_ne hne] at hu; exact hu
        exact hB (hbt u (hbN u hadj.symm) hu2)
      rw [hy, Function.update_of_ne huv] at hu
      rw [hy, Function.update_of_ne hwv] at hw
      have hFx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
        unfold PEqualNP.MetaComplexity.NestedCover.graphFun
        rw [Bool.or_eq_true]
        right
        exact decide_eq_true ⟨u, w, hadj, hu, hw⟩
      rw [← hfun] at hFx
      exact hFx
    · exact UPx _ (by simp) _
