import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7630
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

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

theorem evalT (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem evalb (b : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = b → f' i = b) :
    op.eval (ins.map f) = b → op.eval (ins.map f') = b := by
  cases b
  · intro hf
    by_contra hc
    have hc' : op.eval (ins.map f') = true := by simpa using hc
    have h3 := evalT op hop ins f' f (fun i hi => by
      by_contra hn
      have h4 := h i (by simpa using hn)
      rw [h4] at hi
      exact absurd hi (by simp)) hc'
    rw [hf] at h3
    exact absurd h3 (by simp)
  · exact evalT op hop ins f f' h

theorem simb (b : Bool) (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    (p < n + m ∨ U'.length + B.length < p) →
    (∀ i, U.getD i false = b → U'.getD (ren n m p i) false = b) →
    ∀ i, (wf B U).getD i false = b → (wf (B.map (rg n m p)) U').getD (ren n m p i) false = b := by
  induction B with
  | nil => intro U U' _ _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig hp h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
      (by simp; omega) ?_ ?_ i
    · rcases hp with hp | hp
      · exact Or.inl hp
      · right
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
    · intro t ht
      have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = b →
          (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) = b := by
        intro hb
        show g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false) = b
        rw [List.map_map]
        exact evalb b g.op (hB g (List.mem_cons_self ..)) g.inputs _ _ (fun i hi => h i hi) hb
      rcases Nat.lt_trichotomy t U.length with htl | htl | htl
      · rw [getD_snoc_lt _ _ _ htl] at ht
        have h0 := h t ht
        by_cases htm : t = n + m
        · have e : ren n m p t = p := by unfold ren; rw [if_pos htm]
          rw [e] at h0 ⊢
          rcases hp with hp | hp
          · rw [getD_snoc_lt _ _ _ (by omega)]; exact h0
          · simp only [List.length_cons] at hp
            rw [getD_snoc_gt _ _ _ (by omega)]
            rw [List.getD_eq_default _ _ (by omega)] at h0
            exact h0
        · have h1 : ren n m p t < U'.length := by
            unfold ren
            rw [if_neg htm]
            split <;> omega
          rw [getD_snoc_lt _ _ _ h1]; exact h0
      · subst htl
        rw [getD_snoc_eq] at ht
        have e : ren n m p U.length = U'.length := by
          unfold ren
          rw [if_neg (by omega), if_pos hbig]
          omega
        rw [e, getD_snoc_eq]; exact hv ht
      · rw [getD_snoc_gt _ _ _ htl] at ht
        have e : U'.length < ren n m p t := by
          unfold ren
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        rw [getD_snoc_gt _ _ _ e]; exact ht

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hml]
  rfl

theorem erase_sim (n : ℕ) (C : Circuit) (m p : ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hml : m < C.gates.length) (hp : p < n + m ∨ p = n + C.gates.length) (x : List Bool)
    (hx : x.length = n) (b : Bool)
    (hb : (wf C.gates x).getD (n + m) false = b → (wf C.gates x).getD p false = b) (w : ℕ)
    (hw : (wf C.gates x).getD w false = b) :
    (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) x).getD (ren n m p w) false = b := by
  have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hml, List.take_append_drop]
  have hWlen : (wf (C.gates.take m) x).length = n + m := by
    rw [wf_len, hx, List.length_take, Nat.min_eq_left (le_of_lt hml)]
  have e1 : wf C.gates x = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) x ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false)]) := by
    conv_lhs => rw [h2]
    rw [wf_append, wf_cons]
  have hfull : (wf C.gates x).length = n + C.gates.length := by rw [wf_len, hx]
  rw [wf_append]
  rw [e1] at hw hb
  have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := List.length_drop
  refine simb b n m p (C.gates.drop (m + 1))
    (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) _ _ (by simp) (by simp; omega) ?_ ?_ w hw
  · rcases hp with hp | hp
    · exact Or.inl hp
    · right; rw [hWlen, hdl, hp]; omega
  · intro i hi
    unfold ren
    split
    · rename_i hinm
      subst hinm
      rw [wf_keep _ _ _ (by simp; omega)] at hb
      have h3 := hb hi
      rcases hp with hp | hp
      · rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at h3
        exact h3
      · rw [← e1, List.getD_eq_default _ _ (by rw [hfull, hp])] at h3
        rw [List.getD_eq_default _ _ (by rw [hWlen, hp]; omega)]
        exact h3
    · split
      · rw [getD_snoc_gt _ _ _ (by omega)] at hi
        rw [List.getD_eq_default _ _ (by omega)]
        exact hi
      · rw [getD_snoc_lt _ _ _ (by omega)] at hi
        exact hi

theorem gate_in (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length)
    (hop : C.gates[m].op = GateOp.and ∨ C.gates[m].op = GateOp.or) (hpin : p ∈ C.gates[m].inputs)
    (hp : p < n + m) (x : List Bool) (hx : x.length = n) :
    (wf C.gates x).getD (n + m) false = C.gates[m].op.eval [] →
    (wf C.gates x).getD p false = C.gates[m].op.eval [] := by
  subst hx
  rw [gate_val C.gates x m hml, wire_take C.gates x m p hp (le_of_lt hml)]
  rcases hop with h | h
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).all id = true → _ = true
    intro hall
    exact List.all_eq_true.1 hall _ (List.mem_map.2 ⟨p, hpin, rfl⟩)
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = false → _ = false
    intro hany
    cases hq : (wf (C.gates.take m) x).getD p false
    · rfl
    · exfalso
      have h5 : (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = true :=
        List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨p, hpin, hq⟩, rfl⟩
      rw [h5] at hany
      exact absurd hany (by simp)

theorem two_mem (l : List ℕ) (hl : l.length ≤ 2) (s o i : ℕ) (hs : s ∈ l) (ho : o ∈ l) (hi : i ∈ l)
    (hso : s ≠ o) (his : i ≠ s) : i = o := by
  match l, hl with
  | [], _ => simp at hs
  | [a], _ =>
    simp only [List.mem_singleton] at hs ho
    omega
  | [a, b], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ho hi
    omega
  | _ :: _ :: _ :: _, h => simp at h

theorem pick (n : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s < n) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (m : ℕ) (hml : m < C.gates.length)
    (hr : (C.gates[m].inputs.any fun i => decide (i ∈ S)) = true) :
    ∃ p, (p < n + m ∨ p = n + C.gates.length) ∧ p ∉ S ∧ ∀ x : List Bool, x.length = n →
      (∀ s ∈ S, x.getD s false = false) →
      (wf C.gates x).getD p false = (wf C.gates x).getD (n + m) false := by
  obtain ⟨s, hs, hsS'⟩ := List.any_eq_true.1 hr
  have hsS : s ∈ S := by simpa using hsS'
  have hlen := (hm _ (List.getElem_mem hml)).2
  have hfar : n + C.gates.length ∉ S := fun h => by have := hS _ h; omega
  have pf : ∀ x : List Bool, x.length = n → (∀ s ∈ S, x.getD s false = false) → ∀ i,
      (i ∈ S ∨ n + m ≤ i) → (wf (C.gates.take m) x).getD i false = false := by
    intro x hx hx0 i hi
    rcases hi with hi | hi
    · rw [wf_keep _ _ _ (by rw [hx]; exact hS i hi)]
      exact hx0 i hi
    · exact List.getD_eq_default _ _ (by
        rw [wf_len, hx, List.length_take, Nat.min_eq_left (le_of_lt hml)]
        exact hi)
  have gv : ∀ x : List Bool, x.length = n → (wf C.gates x).getD (n + m) false
      = C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false) := by
    intro x hx
    have h := gate_val C.gates x m hml
    rw [hx] at h
    exact h
  have far : ∀ x : List Bool, x.length = n →
      (wf C.gates x).getD (n + C.gates.length) false = false :=
    fun x hx => List.getD_eq_default _ _ (by rw [wf_len, hx])
  rcases (hm _ (List.getElem_mem hml)).1 with ha | ho
  · refine ⟨n + C.gates.length, Or.inr rfl, hfar, fun x hx hx0 => ?_⟩
    have ha' : C.gates[m].op = GateOp.and := ha
    rw [far x hx, gv x hx, ha']
    symm
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).all id = false
    rw [List.all_eq_false]
    exact ⟨false, List.mem_map.2 ⟨s, hs, pf x hx hx0 s (Or.inl hsS)⟩, by simp⟩
  · have ho' : C.gates[m].op = GateOp.or := ho
    by_cases hex : ∃ o ∈ C.gates[m].inputs, o < n + m ∧ o ∉ S
    · obtain ⟨o, ho1, ho2, ho3⟩ := hex
      refine ⟨o, Or.inl ho2, ho3, fun x hx hx0 => ?_⟩
      rw [gv x hx, ho', wire_take C.gates x m o (by rw [hx]; exact ho2) (le_of_lt hml)]
      show _ = (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id
      rw [Bool.eq_iff_iff, List.any_eq_true]
      constructor
      · intro h
        exact ⟨_, List.mem_map.2 ⟨o, ho1, rfl⟩, h⟩
      · rintro ⟨b, hb, hbt⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        have his : i ≠ s := by
          intro e
          rw [e, pf x hx hx0 s (Or.inl hsS)] at hbt
          exact absurd hbt (by simp)
        have hio := two_mem _ hlen s o i hs ho1 hi (fun e => ho3 (e ▸ hsS)) his
        rw [hio] at hbt
        exact hbt
    · refine ⟨n + C.gates.length, Or.inr rfl, hfar, fun x hx hx0 => ?_⟩
      rw [far x hx, gv x hx, ho']
      symm
      show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = false
      rw [List.any_eq_false]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      have hf : (wf (C.gates.take m) x).getD i false = false := by
        by_cases h : i < n + m
        · have hiS : i ∈ S := by
            by_contra hc
            exact hex ⟨i, hi, h, hc⟩
          exact pf x hx hx0 i (Or.inl hiS)
        · exact pf x hx hx0 i (Or.inr (by omega))
      rw [hf]
      simp

theorem cnt_map (n m p : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s < n) (hp : p ∉ S) :
    ∀ l : List Gate, ((l.map (rg n m p)).filter
        (fun g => g.inputs.any fun i => decide (i ∈ S))).length
      = (l.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length := by
  have key : ∀ g : Gate, ((rg n m p g).inputs.any fun i => decide (i ∈ S))
      = (g.inputs.any fun i => decide (i ∈ S)) := by
    intro g
    show ((g.inputs.map (ren n m p)).any fun i => decide (i ∈ S)) = _
    rw [List.any_map]
    congr 1
    funext i
    show decide (ren n m p i ∈ S) = decide (i ∈ S)
    unfold ren
    split
    · rename_i h
      rw [decide_eq_false hp, decide_eq_false (fun hh => by have := hS _ hh; omega)]
    · split
      · rw [decide_eq_false (fun hh => by have := hS _ hh; omega),
          decide_eq_false (fun hh => by have := hS _ hh; omega)]
      · rfl
  intro l
  induction l with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons, List.filter_cons, key g]
    split <;> simp [ih]

theorem strip2 (n : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s < n) : ∀ k (C : Circuit),
    (C.gates.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length = k →
    PEqualNP.MetaComplexity.Monotone2 C →
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.gates.length + k = C.gates.length ∧
      ∀ x : List Bool, x.length = n → (∀ s ∈ S, x.getD s false = false) →
        (wf D.gates x).getD D.output false = (wf C.gates x).getD C.output false := by
  intro k
  induction k with
  | zero => intro C _ hm; exact ⟨C, hm, rfl, fun _ _ _ => rfl⟩
  | succ k ih =>
    intro C hk hm
    obtain ⟨g, hgf⟩ := List.exists_mem_of_length_pos (by omega :
      0 < (C.gates.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length)
    obtain ⟨hgm, hgP⟩ := List.mem_filter.1 hgf
    obtain ⟨m, hml, rfl⟩ := List.getElem_of_mem hgm
    obtain ⟨p, hp, hpS, heq⟩ := pick n S hS C hm m hml hgP
    have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hml, List.take_append_drop]
    have c1 : (C.gates.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length
        = ((C.gates.take m).filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length + 1
          + ((C.gates.drop (m + 1)).filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length := by
      have c0 : ∀ (A B : List Gate) (g0 : Gate),
          (g0.inputs.any fun i => decide (i ∈ S)) = true →
          ((A ++ g0 :: B).filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length
            = (A.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length + 1
              + (B.filter (fun g => g.inputs.any fun i => decide (i ∈ S))).length := by
        intro A B g0 hg0
        simp only [List.filter_append, List.filter_cons, hg0, if_true, List.length_append,
          List.length_cons]
        omega
      have h3 := c0 (C.gates.take m) (C.gates.drop (m + 1)) C.gates[m] hgP
      rw [← h2] at h3
      exact h3
    have hmE : PEqualNP.MetaComplexity.Monotone2
        ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
      intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hm g (List.mem_of_mem_take hg)
      · have := hm g0 (List.mem_of_mem_drop hg0)
        exact ⟨this.1, by simpa [rg] using this.2⟩
    have cE : ((C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).filter
        (fun g => g.inputs.any fun i => decide (i ∈ S))).length = k := by
      rw [List.filter_append, List.length_append, cnt_map n m p S hS hpS]
      omega
    have hEl : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length + 1
        = C.gates.length := by
      simp
      omega
    obtain ⟨D, hD1, hD2, hD3⟩ := ih
      ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ cE hmE
    have hD2' : D.gates.length + k
        = (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length := hD2
    refine ⟨D, hD1, by omega, fun x hx hx0 => ?_⟩
    rw [hD3 x hx hx0]
    exact erase_sim n C m p hm hml hp x hx _ (fun h => (heq x hx hx0).trans h) C.output rfl

end PEqualNP.Outside.L_meta_7630

open PEqualNP.Outside.L_meta_7630 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7630 : ∀ (x1 : ℕ) (x2 : Finset ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x2, x4 < x1) → PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.any fun (x8 : ℕ) => Decidable.decide (x8 ∈ x2)) x3.gates).length = x3.size ∧ ∀ (x7 : List Bool), x7.length = x1 → (∀ x9 ∈ x2, x7.getD x9 Bool.false = Bool.false) → x6.eval x7 = x3.eval x7 := by
  intro n S C hS hm
  obtain ⟨D, hD1, hD2, hD3⟩ := strip2 n S hS _ C rfl hm
  exact ⟨D, hD1, hD2, hD3⟩
