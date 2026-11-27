import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4821
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

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

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

section
open PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem dsn_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dsn_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [dsn_eq] at hj
      rw [h1, dsn_eq, h2, dsn_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [dsn_ne _ _ _ _ hjl] at hj
      rw [dsn_ne _ _ _ _ (by omega), dsn_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [dsn_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [dsn_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact dsn_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega
end

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

end PEqualNP.Outside.L_meta_4821

open PEqualNP.Outside.L_meta_4821 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4821 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x10 ∧ x5 x10 ∧ x10.size ≤ x4.size ∧ x10.output + (1 : ℕ) = x1 + x1 + x10.size ∧ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x10.gates).toFinset = Finset.range (x1 + x1 + x10.size - (1 : ℕ)) := by
  intro N S σ C P hcard hmem hAO hC
  classical
  have hex : ∃ s, ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ P D ∧ D.size = s :=
    ⟨_, C, hAO, hC, rfl⟩
  obtain ⟨D, hD1, hD2, hmin⟩ : ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ P D ∧
      ∀ D' : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D' → P D' → D.size ≤ D'.size := by
    obtain ⟨D, h1, h2, h3⟩ := Nat.find_spec hex
    exact ⟨D, h1, h2, fun D' a b => h3 ▸ Nat.find_min' hex ⟨D', a, b, rfl⟩⟩
  have hev : ∀ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D x = true ↔
      ∃ (a : Fin N) (b : Fin N), (a, b) ∈ S ∧ x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true := by
    intro x
    have h := hD2 x
    rw [h, decide_eq_true_iff]
  have hP' : ∀ D' : Circuit, PEqualNP.MetaComplexity.circuitFun (N + N) D'
      = PEqualNP.MetaComplexity.circuitFun (N + N) D → P D' :=
    fun D' hf x => (congrFun hf x).trans (hD2 x)
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      rw [Finset.eq_empty_of_isEmpty S] at hcard
      simp at hcard
    · exact h
  have hdep := dep_inc N S σ _ hmem hev
  obtain ⟨hao, hrb, hl2⟩ := hD1
  have hFan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    refine ⟨?_, le_of_eq (hl2 g hg)⟩
    rcases hao g hg with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hsz : N + N ≤ D.size + 1 :=
    dep_lower (N + N) _ hdep D.size ⟨D, hFan, le_refl _, fun x => rfl⟩
  have hs : D.size = D.gates.length := rfl
  have hpos : 0 < D.gates.length := by omega
  have hout : D.output + 1 = N + N + D.gates.length := by
    by_contra hne
    have hle := hmin ⟨D.gates.take (D.gates.length - 1), D.output⟩ ⟨
      fun g hg => hao g (List.mem_of_mem_take hg), (by
        intro j hj i hi
        have hj' : j < (D.gates.take (D.gates.length - 1)).length := hj
        rw [gateAt_eq _ j hj] at hi
        have hi' : i ∈ ((D.gates.take (D.gates.length - 1))[j]'hj').inputs := hi
        rw [List.getElem_take] at hi'
        rw [List.length_take] at hj'
        exact hrb j (by omega) i (by rw [gateAt_eq D j (by omega)]; exact hi')),
      fun g hg => hl2 g (List.mem_of_mem_take hg)⟩ (hP' _ (by
        funext x
        have hX : (List.ofFn x).length = N + N := by simp
        show (wf (D.gates.take (D.gates.length - 1)) (List.ofFn x)).getD D.output false
          = (wf D.gates (List.ofFn x)).getD D.output false
        by_cases h1 : D.output < N + N + (D.gates.length - 1)
        · exact (wire_take D.gates (List.ofFn x) (D.gates.length - 1) D.output
            (by rw [hX]; exact h1) (by omega)).symm
        · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, hX]; omega),
            List.getD_eq_default _ _ (by rw [wf_len, hX]; omega)]))
    have hle' : D.gates.length ≤ (D.gates.take (D.gates.length - 1)).length := hle
    rw [List.length_take] at hle'
    omega
  have hreadGate : ∀ m, m + 1 < D.gates.length → ∃ g ∈ D.gates, N + N + m ∈ g.inputs := by
    intro m hm
    by_contra hno
    have hun : ∀ g ∈ D.gates.drop (m + 1), N + N + m ∉ g.inputs :=
      fun g hg hin => hno ⟨g, List.mem_of_mem_drop hg, hin⟩
    have hle := hmin _ (erase_ao (N + N) D m (by omega) ⟨hao, hrb, hl2⟩ hun)
      (hP' _ (erase_fun (N + N) D m (by omega) hun (by omega)))
    have hle' : D.gates.length ≤
        (D.gates.take m ++ (D.gates.drop (m + 1)).map (rg2 (N + N + m))).length := hle
    rw [List.length_append, List.length_map, List.length_take, List.length_drop] at hle'
    omega
  have hreadIn : ∀ i, i < N + N → ∃ g ∈ D.gates, i ∈ g.inputs := by
    intro i hi
    by_contra hno
    obtain ⟨x, hx⟩ := hdep ⟨i, hi⟩
    apply hx
    show (wf D.gates (List.ofFn (Function.update x ⟨i, hi⟩ (!x ⟨i, hi⟩)))).getD D.output false
      = (wf D.gates (List.ofFn x)).getD D.output false
    apply noread i D.gates _ _ (by simp) (by simp; exact hi)
      (fun g hg hin => hno ⟨g, hg, hin⟩) ?_ D.output (by omega)
    intro t ht
    by_cases htn : t < N + N
    · rw [show (List.ofFn (Function.update x ⟨i, hi⟩ (!x ⟨i, hi⟩))).getD t false
          = Function.update x ⟨i, hi⟩ (!x ⟨i, hi⟩) ⟨t, htn⟩ from getD_ofFn _ ⟨t, htn⟩,
        show (List.ofFn x).getD t false = x ⟨t, htn⟩ from getD_ofFn x ⟨t, htn⟩,
        Function.update_of_ne (fun e => ht (congrArg Fin.val e))]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  refine ⟨D, ⟨hao, hrb, hl2⟩, hD2, hmin C hAO hC, hout, ?_⟩
  ext t
  rw [List.mem_toFinset, List.mem_flatMap, Finset.mem_range]
  constructor
  · rintro ⟨g, hg, ht⟩
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hg
    have := hrb j hj t (by rw [gateAt_eq D j hj, e]; exact ht)
    rw [hs]
    omega
  · intro ht
    rw [hs] at ht
    by_cases htn : t < N + N
    · exact hreadIn t htn
    · have := hreadGate (t - (N + N)) (by omega)
      rw [show N + N + (t - (N + N)) = t by omega] at this
      exact this
