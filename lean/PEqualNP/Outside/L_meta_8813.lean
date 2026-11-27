import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8813
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def ren2 (q i : ℕ) : ℕ := if q < i then i - 1 else i

def rg2 (q : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren2 q)⟩

theorem sim2 (q : ℕ) (B : List Gate) : ∀ U U' : List Bool, U.length = U'.length + 1 →
    q < U.length → (∀ g ∈ B, q ∉ g.inputs) →
    (∀ i, i ≠ q → U.getD i false = U'.getD (ren2 q i) false) →
    ∀ i, i ≠ q → (wf B U).getD i false = (wf (B.map (rg2 q)) U').getD (ren2 q i) false := by
  induction B with
  | nil => intro U U' _ _ _ h i hi; exact h i hi
  | cons g B ih =>
    intro U U' hlen hq hB h i hi
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rg2 q g).op.eval ((rg2 q g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (ren2 q)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact h t (fun e => hB g List.mem_cons_self (e ▸ ht))
    refine ih _ _ (by simp [hlen]) (by simp; omega)
      (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) ?_ i hi
    intro t ht
    rw [← hv]
    rcases Nat.lt_trichotomy t U.length with h1 | h1 | h1
    · have h2 : ren2 q t < U'.length := by
        unfold ren2
        split <;> omega
      rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ h2]
      exact h t ht
    · have e : ren2 q t = U'.length := by
        unfold ren2
        rw [if_pos (by omega)]
        omega
      rw [e, getD_snoc_eq, h1, getD_snoc_eq]
    · have e : U'.length < ren2 q t := by
        unfold ren2
        rw [if_pos (by omega)]
        omega
      rw [getD_snoc_gt _ _ _ h1, getD_snoc_gt _ _ _ e]

theorem erase_unread (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) (ho : C.output ≠ n + m) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
  refine ⟨⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hF g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hF g0 (List.mem_of_mem_drop hg0)
      refine ⟨this.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]; exact this.2
  · show (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))).length + 1 = C.gates.length
    rw [List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  · funext x
    have hX : (List.ofFn x).length = n := by simp
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hPl : (wf (C.gates.take m) (List.ofFn x)).length = n + m := by
      rw [wf_len, List.length_take, hX, Nat.min_eq_left (le_of_lt hm)]
    have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
        (wf (C.gates.take m) (List.ofFn x) ++ [C.gates[m].op.eval (C.gates[m].inputs.map
          fun i => (wf (C.gates.take m) (List.ofFn x)).getD i false)]) := by
      conv_lhs => rw [hsplit]
      rw [wf_append, wf_cons]
    have e2 : wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)
        = wf ((C.gates.drop (m + 1)).map (rg2 (n + m))) (wf (C.gates.take m) (List.ofFn x)) :=
      wf_append _ _ _
    show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)).getD
        (ren2 (n + m) C.output) false = (wf C.gates (List.ofFn x)).getD C.output false
    rw [e1, e2]
    symm
    apply sim2 (n + m) _ _ _ (by rw [List.length_append, hPl]; rfl)
      (by rw [List.length_append, hPl]; simp) hun ?_ _ ho
    intro i hi
    rcases Nat.lt_or_gt_of_ne hi with h1 | h1
    · have e : ren2 (n + m) i = i := by unfold ren2; rw [if_neg (by omega)]
      rw [e, getD_snoc_lt _ _ _ (by rw [hPl]; exact h1)]
    · have e : ren2 (n + m) i = i - 1 := by unfold ren2; rw [if_pos h1]
      rw [e, getD_snoc_gt _ _ _ (by rw [hPl]; exact h1),
        List.getD_eq_default _ _ (by rw [hPl]; omega)]

theorem noread (i : ℕ) : ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length →
    i < U.length → (∀ g ∈ gs, i ∉ g.inputs) →
    (∀ t, t ≠ i → U.getD t false = U'.getD t false) →
    ∀ t, t ≠ i → (wf gs U).getD t false = (wf gs U').getD t false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ _ h t ht; exact h t ht
  | cons g gs ih =>
    intro U U' hlen hi hg h t ht
    rw [wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun j => U.getD j false)
        = g.op.eval (g.inputs.map fun j => U'.getD j false) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      exact h j (fun e => hg g List.mem_cons_self (e ▸ hj))
    rw [hv]
    refine ih _ _ (by simp [hlen]) (by simp; omega)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ t ht
    intro s hs
    rcases Nat.lt_trichotomy s U.length with h1 | h1 | h1
    · rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ (by omega)]
      exact h s hs
    · rw [h1, getD_snoc_eq, hlen, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ h1, getD_snoc_gt _ _ _ (by omega)]

theorem erase_fun (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) (ho : C.output ≠ n + m) :
    PEqualNP.MetaComplexity.circuitFun n
      ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩
      = PEqualNP.MetaComplexity.circuitFun n C := by
  funext x
  have hX : (List.ofFn x).length = n := by simp
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hPl : (wf (C.gates.take m) (List.ofFn x)).length = n + m := by
    rw [wf_len, List.length_take, hX, Nat.min_eq_left (le_of_lt hm)]
  have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) (List.ofFn x) ++ [C.gates[m].op.eval (C.gates[m].inputs.map
        fun i => (wf (C.gates.take m) (List.ofFn x)).getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [wf_append, wf_cons]
  have e2 : wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)
      = wf ((C.gates.drop (m + 1)).map (rg2 (n + m))) (wf (C.gates.take m) (List.ofFn x)) :=
    wf_append _ _ _
  show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)).getD
      (ren2 (n + m) C.output) false = (wf C.gates (List.ofFn x)).getD C.output false
  rw [e1, e2]
  symm
  apply sim2 (n + m) _ _ _ (by rw [List.length_append, hPl]; rfl)
    (by rw [List.length_append, hPl]; simp) hun ?_ _ ho
  intro i hi
  rcases Nat.lt_or_gt_of_ne hi with h1 | h1
  · have e : ren2 (n + m) i = i := by unfold ren2; rw [if_neg (by omega)]
    rw [e, getD_snoc_lt _ _ _ (by rw [hPl]; exact h1)]
  · have e : ren2 (n + m) i = i - 1 := by unfold ren2; rw [if_pos h1]
    rw [e, getD_snoc_gt _ _ _ (by rw [hPl]; exact h1),
      List.getD_eq_default _ _ (by rw [hPl]; omega)]

theorem erase_ao (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) :
    PEqualNP.TopForm.IsAO2 n
      ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩ := by
  obtain ⟨hao, hrb, hl2⟩ := hAO
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hao g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact hao g0 (List.mem_of_mem_drop hg0)
  · intro j hj i hi
    have hj' : j < (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))).length := hj
    rw [gateAt_eq _ j hj] at hi
    have hi' : i ∈ ((C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)))[j]'hj').inputs := hi
    have hlen := hj'
    rw [List.length_append, List.length_map, List.length_take, List.length_drop,
      Nat.min_eq_left (le_of_lt hm)] at hlen
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take] at hi'
      exact hrb j (by omega) i (by rw [gateAt_eq C j (by omega)]; exact hi')
    · rw [List.getElem_append_right (by rw [List.length_take]; omega), List.getElem_map,
        List.getElem_drop] at hi'
      have hidx : m + 1 + (j - (C.gates.take m).length) = j + 1 := by
        rw [List.length_take, Nat.min_eq_left (le_of_lt hm)]; omega
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
      have hmem : C.gates[m + 1 + (j - (C.gates.take m).length)]'(by rw [hidx]; omega)
          ∈ C.gates.drop (m + 1) := by
        rw [← List.getElem_drop (h := by rw [List.length_drop, List.length_take,
          Nat.min_eq_left (le_of_lt hm)]; omega)]
        exact List.getElem_mem _
      have hne : i0 ≠ n + m := fun e => hun _ hmem (e ▸ hi0)
      have hlt := hrb (m + 1 + (j - (C.gates.take m).length)) (by rw [hidx]; omega) i0
        (by rw [gateAt_eq C _ (by rw [hidx]; omega)]; exact hi0)
      rw [hidx] at hlt
      unfold ren2
      split <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hl2 g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      show (g0.inputs.map _).length = 2
      rw [List.length_map]; exact hl2 g0 (List.mem_of_mem_drop hg0)

theorem dep_inc (N : ℕ) (S : Finset (Fin N × Fin N)) (σ : Equiv.Perm (Fin N)) (f : (Fin (N + N) → Bool) → Bool)
    (hmem : ∀ v : Fin N, (v, σ v) ∈ S)
    (hev : ∀ x : Fin (N + N) → Bool, f x = true ↔ ∃ (a : Fin N) (b : Fin N), (a, b) ∈ S ∧
      x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true) :
    ∀ i : Fin (N + N), ∃ x : Fin (N + N) → Bool, f (Function.update x i (!x i)) ≠ f x := by
  have hcn : ∀ (a b : Fin N), Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b e
    have := congrArg Fin.val e
    simp at this
    omega
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · refine ⟨fun v => decide (v = Fin.natAdd N (σ p)), ?_⟩
    have hx0 : (decide (Fin.castAdd N p = Fin.natAdd N (σ p))) = false :=
      decide_eq_false (hcn p (σ p))
    intro heq
    have hA : f (Function.update (fun v => decide (v = Fin.natAdd N (σ p))) (Fin.castAdd N p)
        (!decide (Fin.castAdd N p = Fin.natAdd N (σ p)))) = true := by
      rw [hev]
      refine ⟨p, σ p, hmem p, ?_, ?_⟩
      · rw [Function.update_self, hx0]; rfl
      · rw [Function.update_of_ne (fun e => hcn p (σ p) e.symm)]
        exact decide_eq_true rfl
    rw [heq, hev] at hA
    obtain ⟨a, b, _, ha, _⟩ := hA
    exact hcn a (σ p) (of_decide_eq_true ha)
  · refine ⟨fun v => decide (v = Fin.castAdd N (σ.symm l)), ?_⟩
    have hx0 : (decide (Fin.natAdd N l = Fin.castAdd N (σ.symm l))) = false :=
      decide_eq_false (fun e => hcn (σ.symm l) l e.symm)
    intro heq
    have hml : (σ.symm l, l) ∈ S := by
      have := hmem (σ.symm l)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hA : f (Function.update (fun v => decide (v = Fin.castAdd N (σ.symm l))) (Fin.natAdd N l)
        (!decide (Fin.natAdd N l = Fin.castAdd N (σ.symm l)))) = true := by
      rw [hev]
      refine ⟨σ.symm l, l, hml, ?_, ?_⟩
      · rw [Function.update_of_ne (fun e => hcn (σ.symm l) l e)]
        exact decide_eq_true rfl
      · rw [Function.update_self, hx0]; rfl
    rw [heq, hev] at hA
    obtain ⟨a, b, _, _, hb⟩ := hA
    exact hcn (σ.symm l) b (of_decide_eq_true hb).symm

def Dead (N : ℕ) (C : Circuit) (m : ℕ) : Prop :=
  m < C.gates.length ∧ (∀ g ∈ C.gates.drop (m + 1), N + m ∉ g.inputs) ∧ C.output ≠ N + m

theorem prune (N : ℕ) : ∀ (k : ℕ) (C : Circuit), C.gates.length = k → PEqualNP.TopForm.IsAO2 N C →
    ∃ D : Circuit, D.gates.length ≤ C.gates.length ∧ PEqualNP.TopForm.IsAO2 N D ∧
      PEqualNP.MetaComplexity.circuitFun N D = PEqualNP.MetaComplexity.circuitFun N C ∧
      ∀ m, ¬ Dead N D m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hAO
    by_cases hd : ∃ m, Dead N C m
    · obtain ⟨m, hm, hun, ho⟩ := hd
      have hlen : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (N + m))).length + 1
          = C.gates.length := by
        simp
        omega
      obtain ⟨D, hD1, hD2, hD3, hD4⟩ := ih (k - 1) (by omega)
        ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (N + m)), ren2 (N + m) C.output⟩
        (by show (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (N + m))).length = k - 1; omega)
        (erase_ao N C m hm hAO hun)
      refine ⟨D, ?_, hD2, hD3.trans (erase_fun N C m hm hun ho), hD4⟩
      have : D.gates.length ≤ (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (N + m))).length := hD1
      omega
    · push_neg at hd
      exact ⟨C, le_rfl, hAO, rfl, hd⟩

theorem full (N : ℕ) (D : Circuit) (hAO : PEqualNP.TopForm.IsAO2 N D) (hnd : ∀ m, ¬ Dead N D m)
    (hN : 0 < N)
    (hdep : ∀ i : Fin N, ∃ x : Fin N → Bool,
      PEqualNP.MetaComplexity.circuitFun N D (Function.update x i (!x i))
        ≠ PEqualNP.MetaComplexity.circuitFun N D x) :
    (D.output :: List.flatMap (fun g : Gate => g.inputs) D.gates).toFinset
      = Finset.range (N + D.gates.length) := by
  have hval : ∀ x : Fin N → Bool, PEqualNP.MetaComplexity.circuitFun N D x
      = (wf D.gates (List.ofFn x)).getD D.output false := fun x => rfl
  have hagree : ∀ (w : ℕ) (x : Fin N → Bool) (i : Fin N), i.val = w → ∀ t, t ≠ w →
      (List.ofFn (Function.update x i (!x i))).getD t false = (List.ofFn x).getD t false := by
    intro w x i hiw t ht
    by_cases htn : t < N
    · have e1 := getD_ofFn (Function.update x i (!x i)) ⟨t, htn⟩
      have e2 := getD_ofFn x ⟨t, htn⟩
      simp only at e1 e2
      rw [e1, e2, Function.update_of_ne (fun h => ht (by rw [← hiw, ← h]))]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  ext w
  simp only [List.mem_toFinset, List.mem_cons, List.mem_flatMap, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨g, hg, hwg⟩)
    · by_contra hge
      obtain ⟨x, hx⟩ := hdep ⟨0, hN⟩
      apply hx
      rw [hval, hval, List.getD_eq_default _ _ (by rw [wf_len]; simp; omega),
        List.getD_eq_default _ _ (by rw [wf_len]; simp; omega)]
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have := hAO.2.1 j hj w (by rw [gateAt_eq D j hj]; exact hwg)
      omega
  · intro hw
    by_cases hwN : w < N
    · by_contra hns
      push_neg at hns
      obtain ⟨ho, hg⟩ := hns
      obtain ⟨x, hx⟩ := hdep ⟨w, hwN⟩
      apply hx
      rw [hval, hval]
      exact noread w D.gates _ _ (by simp) (by simpa using hwN) (fun g hg' hwg => hg g hg' hwg)
        (hagree w x ⟨w, hwN⟩ rfl) D.output (fun h => ho h.symm)
    · have hm : w - N < D.gates.length := by omega
      have hnd' := hnd (w - N)
      unfold Dead at hnd'
      have hwe : N + (w - N) = w := by omega
      rw [hwe] at hnd'
      by_cases ho : w = D.output
      · exact Or.inl ho
      · right
        by_contra hno
        push_neg at hno
        exact hnd' ⟨hm, fun g hg hwg => hno g (List.mem_of_mem_drop hg) hwg, fun h => ho h.symm⟩

end PEqualNP.Outside.L_meta_8813

open PEqualNP.Outside.L_meta_8813 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8813 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size ≤ x4.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x9 ∧ (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10) ∧ (x9.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x9.gates).toFinset.card = (2 : ℕ) * x1 + x9.size := by
  intro n E σ C hn hperm hAO hF
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := prune (n + n) C.gates.length C rfl hAO
  refine ⟨D, hD1, hD2, fun x => congrFun hD3 x, ?_⟩
  have hdep := dep_inc n E σ (PEqualNP.MetaComplexity.circuitFun (n + n) D) hperm (fun x => by
    rw [hD3, hF x]
    simp)
  rw [full (n + n) D hD2 hD4 (by omega) hdep, Finset.card_range]
  show n + n + D.gates.length = 2 * n + D.gates.length
  omega
