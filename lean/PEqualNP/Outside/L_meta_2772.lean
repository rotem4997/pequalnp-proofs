import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem snoc_mono (W : List Bool) (v v' : Bool) (h : v = true → v' = true) (i : ℕ) :
    (W ++ [v]).getD i false = true → (W ++ [v']).getD i false = true := by
  rcases Nat.lt_trichotomy i W.length with hi | hi | hi
  · rw [getD_snoc_lt _ _ _ hi, getD_snoc_lt _ _ _ hi]; exact id
  · subst hi; rw [getD_snoc_eq, getD_snoc_eq]; exact h
  · rw [getD_snoc_gt _ _ _ hi]; intro hf; exact absurd hf (by simp)

theorem opmono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b a' b' : Bool)
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    op.eval [a, b] = true → op.eval [a', b'] = true := by
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval] <;> tauto

theorem core (n g : ℕ) (gates : List Gate) (hg : g < gates.length) (o w' : ℕ) (ins' : List ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw' : w' < n + g) (x : Fin n → Bool)
    (hF : (wf gates (List.ofFn x)).getD w' false = true → (wf gates (List.ofFn x)).getD o false = true)
    (hsame : (wf (gates.take g) (List.ofFn x)).getD w' false = false →
      gates[g].op.eval (ins'.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false)
        = gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false))
    (hup : gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true →
      gates[g].op.eval (ins'.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true) :
    (wf (gates.set g ⟨gates[g].op, ins'⟩) (List.ofFn x)).getD o false
      = (wf gates (List.ofFn x)).getD o false := by
  have h2 : ∀ a : Gate, gates.set g a = gates.take g ++ a :: gates.drop (g + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hg]
  have h1 : gates = gates.take g ++ gates[g] :: gates.drop (g + 1) := by
    rw [← h2]
    exact (List.set_getElem_self _).symm
  generalize hW : wf (gates.take g) (List.ofFn x) = W at *
  have hWlen : W.length = n + g := by
    rw [← hW, wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hg)]
  have e1 : wf gates (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)]) := by
    conv_lhs => rw [h1]
    rw [wf_append, wf_cons, hW]
  have e2 : wf (gates.set g ⟨gates[g].op, ins'⟩) (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (ins'.map fun i => W.getD i false)]) := by
    rw [h2, wf_append, wf_cons, hW]
  rw [e2, e1]
  rw [e1] at hF
  cases hc : W.getD w' false
  · rw [hsame hc]
  · have hk : (wf (gates.drop (g + 1)) (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)])).getD w' false = true := by
      rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
      exact hc
    have ht := hF hk
    rw [ht]
    exact mono2 (gates.drop (g + 1)) (fun g' hg' => hleg g' (List.mem_of_mem_drop hg')) _ _ (by simp)
      (snoc_mono W _ _ hup) o ht

end PEqualNP.Outside.L_meta_2772

open PEqualNP.Outside.L_meta_2772 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' ⟨⟨hao, _, h2⟩, hrb, hg, hb, hw, hw', h1, hF⟩
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hg]
  rw [hG] at hw ⊢
  have hmem : C.gates[g] ∈ C.gates := List.getElem_mem hg
  obtain ⟨i0, i1, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hop := hao _ hmem
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  have hlt : ∀ i ∈ C.gates[g].inputs, i < n + g := by
    intro i hi
    have := hrb g hg i
    rw [hG] at this
    exact this hi
  have hwlt : w < n + g := by
    apply hlt
    rw [← hw, hin]
    interval_cases b <;> simp
  have hins : C.gates[g].inputs.set b w' = if b = 0 then [w', i1] else [i0, w'] := by
    rw [hin]
    interval_cases b <;> rfl
  have hwv : w = if b = 0 then i0 else i1 := by
    rw [← hw, hin]
    interval_cases b <;> rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hao g' h
    · rw [h]; exact hop
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    by_cases hjg : j = g
    · subst hjg
      have : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set j ⟨C.gates[j].op, C.gates[j].inputs.set b w'⟩, C.output⟩ : Circuit) j = ⟨C.gates[j].op, C.gates[j].inputs.set b w'⟩ := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, hg]
      rw [this] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hlt i h
      · rw [h]; exact hw'
    · have : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.set g ⟨C.gates[g].op, C.gates[g].inputs.set b w'⟩, C.output⟩ : Circuit) j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjg)]
      rw [this] at hi
      exact hrb j hj' i hi
  · intro g' hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact h2 g' h
    · rw [h]; simp [hin]
  · funext x
    refine core n g C.gates hg C.output w' _ hleg hw' x (hF x) ?_ ?_
    · intro hc
      have hwf : (wf (C.gates.take g) (List.ofFn x)).getD w false = false := by
        by_contra hne
        have ht : (wf (C.gates.take g) (List.ofFn x)).getD w false = true := by simpa using hne
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg)]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg), hc] at e
        exact absurd e (by simp)
      rw [hins, hin]
      rw [hwv] at hwf
      by_cases hb0 : b = 0
      · simp only [hb0, ite_true] at hwf ⊢
        simp only [List.map_cons, List.map_nil]
        rw [hc, hwf]
      · simp only [hb0, ite_false] at hwf ⊢
        simp only [List.map_cons, List.map_nil]
        rw [hc, hwf]
    · rw [hins, hin]
      by_cases hb0 : b = 0
      · simp only [hb0, ite_true, List.map_cons, List.map_nil]
        intro hv
        refine opmono _ hop _ _ _ _ (fun ht => ?_) id hv
        have hwi : w = i0 := by rw [hwv]; simp [hb0]
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg), hwi]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg)] at e
        exact e
      · simp only [hb0, ite_false, List.map_cons, List.map_nil]
        intro hv
        refine opmono _ hop _ _ _ _ id (fun ht => ?_) hv
        have hwi : w = i1 := by rw [hwv]; simp [hb0]
        have := h1 x (by
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [wire_take C.gates (List.ofFn x) g w (by simpa using hwlt) (le_of_lt hg), hwi]
          exact ht)
        have e : (wf C.gates (List.ofFn x)).getD w' false = true := this
        rw [wire_take C.gates (List.ofFn x) g w' (by simpa using hw') (le_of_lt hg)] at e
        exact e
  · simp [Circuit.size]
