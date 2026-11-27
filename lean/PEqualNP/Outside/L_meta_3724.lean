import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3724
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

theorem down (n g a : ℕ) (gs : List Gate) (X : List Bool) (hX : X.length = n)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) (ha : a < n + g)
    (hao : ∀ gg ∈ gs, gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hga : (wf gs X).getD a false = true → (wf gs X).getD (n + g) false = true) :
    ∀ m, m ≤ gs.length → ∀ i, (wf ((gs.map (sg n g a)).take m) X).getD i false = true →
      (wf (gs.take m) X).getD i false = true := by
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
      show gs[m].op.eval ((gs[m].inputs.map (fun i => if i = n + g then a else i)).map
          fun i => (wf ((gs.map (sg n g a)).take m) X).getD i false) = true →
        gs[m].op.eval (gs[m].inputs.map fun i => (wf (gs.take m) X).getD i false) = true
      rw [List.map_map]
      apply ev_mono gs[m].op (hao _ (List.getElem_mem hm')) gs[m].inputs
      intro i hi hp
      have hp' : (wf ((gs.map (sg n g a)).take m) X).getD (if i = n + g then a else i) false = true := hp
      split_ifs at hp' with h
      · have hi' := hrb m hm' i hi
        rw [h, ← wire_take gs X m (n + g) (by rw [hX]; omega) (le_of_lt hm')]
        apply hga
        rw [wire_take gs X m a (by rw [hX]; omega) (le_of_lt hm')]
        exact ih' a hp'
      · exact ih' i hp'

theorem gF_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → Bool)
    (h : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true) :
    ∃ u v, G.Adj u v ∧ y u = true ∧ y v = true := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun at h
  simpa using h

theorem gF_of {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → Bool)
    (u v : Fin n) (hadj : G.Adj u v) (hu : y u = true) (hv : y v = true) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  rw [Bool.or_eq_true]
  right
  exact decide_eq_true ⟨u, v, hadj, hu, hv⟩

end PEqualNP.Outside.L_meta_3724

open PEqualNP.Outside.L_meta_3724 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3724 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (w w2 : ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  w < C.gates.length → w2 < n + w →
  (∀ u v : Fin n, G.Adj u v →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD (n + w) false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD w2 false = true) →
  (∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) → (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD w2 false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD (n + w) false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + w then w2 else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = n + w then w2 else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C w w2 hAO hfun hw hw2 hE hM
  obtain ⟨hao, hrb, hlen2⟩ := hAO
  have hrb' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j :=
    fun j hj i hi => hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  have hleg' : ∀ gg ∈ C.gates.map (sg n w w2),
      (gg.op = GateOp.and ∨ gg.op = GateOp.or) ∧ gg.inputs.length ≤ 2 := by
    intro gg hgg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hgg
    refine ⟨hao g0 hg0, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]; exact le_of_eq (hlen2 g0 hg0)
  have e1 : (C.gates.map (sg n w w2)).take C.gates.length = C.gates.map (sg n w w2) :=
    List.take_of_length_le (by simp)
  have e2 : C.gates.take C.gates.length = C.gates := List.take_of_length_le (le_refl _)
  have UPx : ∀ X : List Bool, X.length = n →
      ((wf C.gates X).getD (n + w) false = true → (wf C.gates X).getD w2 false = true) →
      ∀ i, (wf C.gates X).getD i false = true →
      (wf (C.gates.map (sg n w w2)) X).getD i false = true := by
    intro X hX hga i hi
    have h1 := up n w w2 C.gates X hX hrb' hw2 hao hga C.gates.length (le_refl _) i
    rw [e1, e2] at h1
    exact h1 hi
  have DNx : ∀ X : List Bool, X.length = n →
      ((wf C.gates X).getD w2 false = true → (wf C.gates X).getD (n + w) false = true) →
      ∀ i, (wf (C.gates.map (sg n w w2)) X).getD i false = true →
      (wf C.gates X).getD i false = true := by
    intro X hX hga i hi
    have h1 := down n w w2 C.gates X hX hrb' hw2 hao hga C.gates.length (le_refl _) i
    rw [e1, e2] at h1
    exact h1 hi
  have hCF : ∀ y : Fin n → Bool, (wf C.gates (List.ofFn y)).getD C.output false
      = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y := fun y => congrFun hfun y
  show PEqualNP.MetaComplexity.circuitFun n
    ⟨C.gates.map (sg n w w2), if C.output = n + w then w2 else C.output⟩ = _
  funext x
  show (wf (C.gates.map (sg n w w2)) (List.ofFn x)).getD
    (if C.output = n + w then w2 else C.output) false = _
  cases hF : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x with
  | true =>
    obtain ⟨u, v, hadj, hu, hv⟩ := gF_true G x hF
    have hpx : ∀ t : Fin n, (fun z : Fin n => decide (z = u ∨ z = v)) t = true → x t = true := by
      intro t ht
      rcases of_decide_eq_true ht with e | e
      · rw [e]; exact hu
      · rw [e]; exact hv
    apply mono2 _ hleg' _ _ (by simp) (ofFn_mono n _ x hpx)
    have hout : (wf C.gates (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD C.output false
        = true := by
      rw [hCF]
      exact gF_of G _ u v hadj (decide_eq_true (Or.inl rfl)) (decide_eq_true (Or.inr rfl))
    split_ifs with h
    · apply UPx _ (by simp) (hE u v hadj)
      apply hE u v hadj
      rw [← h]; exact hout
    · exact UPx _ (by simp) (hE u v hadj) _ hout
  | false =>
    cases hN : (wf (C.gates.map (sg n w w2)) (List.ofFn x)).getD
        (if C.output = n + w then w2 else C.output) false with
    | false => rfl
    | true =>
      exfalso
      have hind : ∀ u ∈ (Finset.univ.filter fun t : Fin n => x t = true),
          ∀ v ∈ (Finset.univ.filter fun t : Fin n => x t = true), ¬ G.Adj u v := by
        intro u hu v hv hadj
        have := gF_of G x u v hadj (Finset.mem_filter.1 hu).2 (Finset.mem_filter.1 hv).2
        rw [hF] at this
        exact absurd this (by decide)
      obtain ⟨M, hSM, hmax⟩ := Finite.exists_le_maximal
        (p := fun T : Finset (Fin n) => ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) hind
      have hMi := hmax.1
      have hdom : ∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v := by
        intro v hv
        by_contra hno
        have hno' : ∀ u ∈ M, ¬ G.Adj u v := fun u hu hadj => hno ⟨u, hu, hadj⟩
        have hins : ∀ a ∈ insert v M, ∀ b ∈ insert v M, ¬ G.Adj a b := by
          intro a ha b hb hadj
          rcases Finset.mem_insert.1 ha with ea | ha'
          · rcases Finset.mem_insert.1 hb with eb | hb'
            · rw [ea, eb] at hadj; exact G.ne_of_adj hadj rfl
            · rw [ea] at hadj; exact hno' b hb' hadj.symm
          · rcases Finset.mem_insert.1 hb with eb | hb'
            · rw [eb] at hadj; exact hno' a ha' hadj
            · exact hMi a ha' b hb' hadj
        exact hv (hmax.2 hins (Finset.subset_insert v M) (Finset.mem_insert_self v M))
      have hxM : ∀ t : Fin n, x t = true → (fun z : Fin n => decide (z ∈ M)) t = true := by
        intro t ht
        exact decide_eq_true (hSM (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩))
      have hNM := mono2 _ hleg' _ _ (by simp) (ofFn_mono n x _ hxM) _ hN
      have hMw := hM M hMi hdom
      have hout : (wf C.gates (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD C.output false
          = true := by
        split_ifs at hNM with h
        · rw [h]
          exact hMw (DNx _ (by simp) hMw _ hNM)
        · exact DNx _ (by simp) hMw _ hNM
      rw [hCF] at hout
      obtain ⟨u, v, hadj, hu, hv⟩ := gF_true G _ hout
      exact hMi u (of_decide_eq_true hu) v (of_decide_eq_true hv) hadj
