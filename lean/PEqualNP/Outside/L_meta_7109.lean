import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7109
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_append {α : Type} (f : List α → Gate → α) (gs rest : List Gate) (w : List α) :
    run f (gs ++ rest) w = run f rest (run f gs w) := by
  simp [run, List.foldl_append]

theorem run_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) : ∀ w : List α,
    ∃ t : List α, run f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change run f gs (w ++ [f w g]) = _
    rw [ht]; simp

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix f gs w
  rw [ht]; simp [hl]

theorem run_getD_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α)
    (i : ℕ) (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := run_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem run_getD_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α)
    (p i : ℕ) (hp : p ≤ gs.length) (hi : i < w.length + p) :
    (run f (gs.take p) w).getD i d = (run f gs w).getD i d := by
  conv_rhs => rw [← List.take_append_drop p gs, run_append]
  rw [run_getD_prefix f (gs.drop p) (run f (gs.take p) w) d i
    (by rw [run_length, List.length_take, Nat.min_eq_left hp]; exact hi)]

theorem run_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) {p : ℕ}
    (hp : p < gs.length) :
    (run f gs w).getD (w.length + p) d = f (run f (gs.take p) w) (gs[p]) := by
  have hsplit : gs = (gs.take p ++ [gs[p]]) ++ gs.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) gs]
    rw [List.take_succ_eq_append_getElem hp]
  have hl : (run f (gs.take p) w).length = w.length + p := by
    rw [run_length, List.length_take, Nat.min_eq_left hp.le]
  conv_lhs => rw [hsplit, run_append, run_append]
  rw [run_getD_prefix _ _ _ _ _ (by rw [run_length, hl]; simp)]
  change ((run f (gs.take p) w) ++ [f (run f (gs.take p) w) gs[p]]).getD _ d = _
  rw [← hl]; simp

def vf : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)
def df : List ℕ → Gate → ℕ := fun d g => g.lineDegree d

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false
def deg (n : ℕ) (C : Circuit) (M : Finset ℕ) (i : ℕ) : ℕ := (C.lineDegrees n M).getD i 0

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} (hp : p < C.gates.length)
    (rb : ∀ i ∈ (gateAt C p).inputs, i < n + p) :
    val C x (n+p) = (gateAt C p).op.eval ((gateAt C p).inputs.map (val C x)) := by
  have hg : gateAt C p = C.gates[p] := List.getD_eq_getElem _ _ hp
  have key := run_gate vf C.gates (List.ofFn x) false hp
  rw [List.length_ofFn] at key
  show (run vf C.gates (List.ofFn x)).getD (n+p) false = _
  rw [key, ← hg]
  show (gateAt C p).op.eval ((gateAt C p).inputs.map fun i =>
    (run vf (C.gates.take p) (List.ofFn x)).getD i false) = _
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_getD_take vf C.gates (List.ofFn x) false p i hp.le
    (by rw [List.length_ofFn]; exact rb i hi)

theorem val_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p a b : ℕ} (hp : p < C.gates.length)
    (kind : (gateAt C p).op = GateOp.and) (ins : (gateAt C p).inputs = [a,b])
    (ha : a < n+p) (hb : b < n+p) : val C x (n+p) = (val C x a && val C x b) := by
  rw [val_gate C x hp (by rw [ins]; intro i hi; simp at hi; omega), kind, ins]
  simp [GateOp.eval]

theorem val_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p a b : ℕ} (hp : p < C.gates.length)
    (kind : (gateAt C p).op = GateOp.or) (ins : (gateAt C p).inputs = [a,b])
    (ha : a < n+p) (hb : b < n+p) : val C x (n+p) = (val C x a || val C x b) := by
  rw [val_gate C x hp (by rw [ins]; intro i hi; simp at hi; omega), kind, ins]
  simp [GateOp.eval]

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  show (run vf C.gates (List.ofFn x)).getD w false = _
  rw [run_getD_prefix _ _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ}
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  show (run vf C.gates (List.ofFn x)).getD w false = _
  rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; exact hw)]

theorem deg_gate (n : ℕ) (C : Circuit) (M : Finset ℕ) {p : ℕ} (hp : p < C.gates.length)
    (rb : ∀ i ∈ (gateAt C p).inputs, i < n + p) :
    deg n C M (n+p) = (gateAt C p).lineDegree (C.lineDegrees n M) := by
  have hg : gateAt C p = C.gates[p] := List.getD_eq_getElem _ _ hp
  have key := run_gate df C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0) 0 hp
  rw [List.length_map, List.length_range] at key
  show (run df C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0)).getD (n+p) 0 = _
  rw [key, ← hg]
  show Gate.lineDegree _ _ = _
  unfold Gate.lineDegree
  have e : (gateAt C p).inputs.map (fun i => (run df (C.gates.take p)
      ((List.range n).map fun i => if i ∈ M then 1 else 0)).getD i 0) =
      (gateAt C p).inputs.map (fun i => (C.lineDegrees n M).getD i 0) := by
    apply List.map_congr_left
    intro i hi
    exact run_getD_take df C.gates _ 0 p i hp.le
      (by rw [List.length_map, List.length_range]; exact rb i hi)
  rw [e]

theorem deg_and (n : ℕ) (C : Circuit) (M : Finset ℕ) {p a b : ℕ} (hp : p < C.gates.length)
    (kind : (gateAt C p).op = GateOp.and) (ins : (gateAt C p).inputs = [a,b])
    (ha : a < n+p) (hb : b < n+p) : deg n C M (n+p) = deg n C M a + deg n C M b := by
  rw [deg_gate n C M hp (by rw [ins]; intro i hi; simp at hi; omega)]
  unfold Gate.lineDegree
  rw [if_pos kind, ins]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

theorem deg_or (n : ℕ) (C : Circuit) (M : Finset ℕ) {p a b : ℕ} (hp : p < C.gates.length)
    (kind : (gateAt C p).op = GateOp.or) (ins : (gateAt C p).inputs = [a,b])
    (ha : a < n+p) (hb : b < n+p) :
    deg n C M (n+p) = max (deg n C M a) (max (deg n C M b) 0) := by
  rw [deg_gate n C M hp (by rw [ins]; intro i hi; simp at hi; omega)]
  unfold Gate.lineDegree
  rw [if_neg (by rw [kind]; intro e; cases e), ins]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  rfl

theorem deg_input (n : ℕ) (C : Circuit) (M : Finset ℕ) {w : ℕ} (hw : w < n) :
    deg n C M w = if w ∈ M then 1 else 0 := by
  show (run df C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0)).getD w 0 = _
  rw [run_getD_prefix _ _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem arity (n : ℕ) (C : Circuit) (ao : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a,b] := by
  have mem : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
  have ar := ao.2.2 _ mem
  rcases e : (gateAt C j).inputs with _|⟨a,_|⟨b,t⟩⟩ <;> simp_all

theorem zero_indep {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (u v : Fin n) :
    ∀ w, deg n C {(u : ℕ)} w = 0 → val C (pairInput u v) w = val C (pairInput v v) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro h0
  by_cases hw : w < n
  · have hd := deg_input n C {(u : ℕ)} hw
    have hne : w ≠ (u : ℕ) := by
      intro e
      rw [hd, if_pos (by simp [e])] at h0
      exact absurd h0 one_ne_zero
    rw [val_input C _ hw, val_input C _ hw]
    have hne' : (⟨w, hw⟩ : Fin n) ≠ u := by intro e; apply hne; rw [← e]
    simp [pairInput, hne']
  · by_cases hl : w < n + C.gates.length
    · have hp : w - n < C.gates.length := by omega
      obtain ⟨a,b,ins⟩ := arity n C ao (w-n) hp
      have ha : a < n + (w-n) := ao.2.1 _ hp a (by simp [ins])
      have hb : b < n + (w-n) := ao.2.1 _ hp b (by simp [ins])
      have hwe : n + (w - n) = w := by omega
      have mem : gateAt C (w-n) ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hp]; exact List.getElem_mem _
      rcases ao.1 _ mem with kind | kind
      · have hd := deg_and n C {(u : ℕ)} hp kind ins ha hb
        rw [hwe] at hd
        rw [hd] at h0
        have e1 := ih a (by omega) (by omega)
        have e2 := ih b (by omega) (by omega)
        rw [← hwe, val_and C _ hp kind ins ha hb, val_and C _ hp kind ins ha hb, e1, e2]
      · have hd := deg_or n C {(u : ℕ)} hp kind ins ha hb
        rw [hwe] at hd
        rw [hd] at h0
        have l1 := le_max_left (deg n C {(u : ℕ)} a) (max (deg n C {(u : ℕ)} b) 0)
        have l2 := le_max_left (deg n C {(u : ℕ)} b) 0
        have l3 := le_max_right (deg n C {(u : ℕ)} a) (max (deg n C {(u : ℕ)} b) 0)
        have e1 := ih a (by omega) (by omega)
        have e2 := ih b (by omega) (by omega)
        rw [← hwe, val_or C _ hp kind ins ha hb, val_or C _ hp kind ins ha hb, e1, e2]
    · rw [val_beyond C _ (by omega), val_beyond C _ (by omega)]

theorem coneSuffix (n : Nat) (gs : List Gate) (cs : List (List Nat)) :
    ∃ t, gs.foldl (coneStep n) cs=cs++t ∧ t.length=gs.length := by
  induction gs generalizing cs with
  | nil => exact ⟨[],by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (coneStep n cs g)
    rw [List.foldl_cons,ht]
    unfold coneStep
    exact ⟨_,List.append_assoc _ _ _,by simp [hl]⟩

theorem cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  obtain ⟨t,ht,hl⟩ := coneSuffix n C.gates []
  unfold cones; rw [ht]; simp [hl]

theorem cone_char (n : ℕ) (C : Circuit) (i k : ℕ) (h : InCone n C i k) :
    k < C.gates.length ∧ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  have hk : k < C.gates.length := by
    by_contra hk; push_neg at hk
    unfold InCone at h
    rw [List.getD_eq_default _ _ (by rw [cones_length]; exact hk)] at h
    simp at h
  refine ⟨hk, ?_⟩
  let cs := (C.gates.take k).foldl (coneStep n) []
  obtain ⟨t,ht,hl⟩ := coneSuffix n (C.gates.take k) []
  have len : cs.length=k := by simp [cs,ht,hl,List.length_take,Nat.min_eq_left hk.le]
  let g := gateAt C k
  let anc := (g.inputs.filter (fun w => decide (n≤w ∧ w<n+cs.length))).flatMap
    (fun w => (w-n)::cs.getD (w-n) [])
  have list : C.gates=(C.gates.take k++[g])++C.gates.drop (k+1) := by
    calc C.gates = C.gates.take (k+1)++C.gates.drop (k+1) := (List.take_append_drop _ _).symm
         _ = _ := by
          rw [List.take_succ_eq_append_getElem hk,show g=C.gates[k] from List.getD_eq_getElem _ _ hk]
  obtain ⟨rest,hr,_⟩ := coneSuffix n (C.gates.drop (k+1)) (coneStep n cs g)
  have shape : cones n C=(cs++[anc])++rest := by
    unfold cones
    conv_lhs => rw [list,List.foldl_append,List.foldl_append]
    exact hr
  have hget : ∀ m < k, (cones n C).getD m [] = cs.getD m [] := by
    intro m hm
    rw [shape, List.getD_append _ _ _ _ (by simp [len]; omega),
      List.getD_append _ _ _ _ (by omega)]
  unfold InCone at h
  rw [shape, List.getD_append _ _ _ _ (by simp [len])] at h
  have h' : i ∈ anc := by
    have e : (cs ++ [anc]).getD k [] = anc := by
      rw [← len, List.getD_append_right _ _ _ _ (le_refl _)]; simp
    rw [e] at h; exact h
  obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp h'
  obtain ⟨hwin, hwr⟩ := List.mem_filter.mp hw
  have hr2 : n ≤ w ∧ w < n + k := by rw [← len]; simpa using hwr
  refine ⟨w, hwin, hr2.1, hr2.2, ?_⟩
  rcases List.mem_cons.mp hi with e | e
  · exact Or.inl e
  · right; unfold InCone; rw [hget _ (by omega)]; exact e

theorem deg_le_reader (n : ℕ) (C : Circuit) (ao : IsAO2 n C) (M : Finset ℕ) (k : ℕ)
    (hk : k < C.gates.length) (w : ℕ) (hw : w ∈ (gateAt C k).inputs) :
    deg n C M w ≤ deg n C M (n+k) := by
  obtain ⟨a,b,ins⟩ := arity n C ao k hk
  have ha : a < n + k := ao.2.1 _ hk a (by simp [ins])
  have hb : b < n + k := ao.2.1 _ hk b (by simp [ins])
  have mem : gateAt C k ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  rw [ins] at hw
  have hw' : w = a ∨ w = b := by simpa using hw
  rcases ao.1 _ mem with kind | kind
  · rw [deg_and n C M hk kind ins ha hb]
    rcases hw' with rfl | rfl <;> omega
  · rw [deg_or n C M hk kind ins ha hb]
    have l1 := le_max_left (deg n C M a) (max (deg n C M b) 0)
    have l2 := le_max_left (deg n C M b) 0
    have l3 := le_max_right (deg n C M a) (max (deg n C M b) 0)
    rcases hw' with rfl | rfl <;> omega

theorem cone_mono (n : ℕ) (C : Circuit) (ao : IsAO2 n C) (M : Finset ℕ) :
    ∀ k i, InCone n C i k → deg n C M (n+i) ≤ deg n C M (n+k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i h
  obtain ⟨hk, w, hw, h1, h2, h3⟩ := cone_char n C i k h
  have step := deg_le_reader n C ao M k hk w hw
  have hw' : n + (w - n) = w := by omega
  rcases h3 with e | e
  · rw [e, hw']; exact step
  · have := ih (w - n) (by omega) i e
    rw [hw'] at this; omega

end PEqualNP.Outside.L_meta_7109
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_7109

theorem PEqualNP.Outside.L_meta_7109 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → x1 + x5 = x2.output ∨ PEqualNP.EdgeOwnership.InCone x1 x2 x5 (x2.output - x1) → PEqualNP.EdgeOwnership.gateVal x1 x2 x5 (PEqualNP.EdgeOwnership.pairInput x3 x4) = Bool.true → (∀ (x10 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x5 x10) (PEqualNP.EdgeOwnership.pairInput x3 x3) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal x1 x2 (PEqualNP.TopForm.opnd x2 x5 x10) (PEqualNP.EdgeOwnership.pairInput x4 x4) = Bool.false) → (2 : ℕ) ≤ x2.lineDeg x1 {↑x3} ∧ (2 : ℕ) ≤ x2.lineDeg x1 {↑x4} := by
  intro n C u v j ao kind hout pair singles
  have hj : j < C.gates.length := by
    by_contra! h
    change (C.gates.getD j _).op = _ at kind
    rw [List.getD_eq_default _ _ h] at kind
    contradiction
  obtain ⟨a, b, ins⟩ := arity n C ao j hj
  have ha : a < n + j := ao.2.1 j hj a (by simp [ins])
  have hb : b < n + j := ao.2.1 j hj b (by simp [ins])
  have pv : ∀ x y : Fin n, pairInput x y = pairInput u v →
      val C (pairInput x y) a = true ∧ val C (pairInput x y) b = true := by
    intro x y hxy
    have h1 : val C (pairInput u v) (n+j) = true := pair
    rw [val_and C _ hj kind ins ha hb] at h1
    rw [hxy]; simpa using h1
  have o0 : opnd C j 0 = a := by simp [opnd, ins]
  have o1 : opnd C j 1 = b := by simp [opnd, ins]
  have s0 := singles 0
  have s1 := singles 1
  rw [o0] at s0
  rw [o1] at s1
  change val C (pairInput u u) a = false ∧ val C (pairInput v v) a = false at s0
  change val C (pairInput u u) b = false ∧ val C (pairInput v v) b = false at s1
  have swap : pairInput v u = pairInput u v := by
    funext w; simp [pairInput, or_comm]
  have pos : ∀ (x y : Fin n) (c : ℕ), val C (pairInput x y) c = true →
      val C (pairInput y y) c = false → 1 ≤ deg n C {(x : ℕ)} c := by
    intro x y c h1 h2
    by_contra h3
    have h4 := zero_indep C ao x y c (by omega)
    rw [h1, h2] at h4
    exact Bool.noConfusion h4
  have outd : ∀ M, deg n C M (n+j) ≤ C.lineDeg n M := by
    intro M
    show _ ≤ deg n C M C.output
    rcases hout with e | e
    · rw [← e]
    · obtain ⟨_, w, _, h1, h2, _⟩ := cone_char n C j _ e
      have hoe : n + (C.output - n) = C.output := by omega
      have := cone_mono n C ao M _ j e
      rw [hoe] at this; exact this
  constructor
  · have d1 := pos u v a (pv u v rfl).1 s0.2
    have d2 := pos u v b (pv u v rfl).2 s1.2
    have := outd {(u : ℕ)}
    rw [deg_and n C _ hj kind ins ha hb] at this
    omega
  · have d1 := pos v u a (pv v u swap).1 s0.1
    have d2 := pos v u b (pv v u swap).2 s1.1
    have := outd {(v : ℕ)}
    rw [deg_and n C _ hj kind ins ha hb] at this
    omega
