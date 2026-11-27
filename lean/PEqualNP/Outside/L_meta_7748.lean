import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7748

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : Bool) (f g : ℕ → Bool) (l : List ℕ) (h : ∀ i, f i = b → g i = b) :
    op.eval (l.map f) = b → op.eval (l.map g) = b := by
  rcases hop with rfl | rfl
  · cases b <;> simp only [GateOp.eval, List.all_map, List.all_eq_true,
      List.all_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩
    · exact fun H x hx => h x (H x hx)
  · cases b <;> simp only [GateOp.eval, List.any_map, List.any_eq_true,
      List.any_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun H x hx => h x (H x hx)
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩

theorem main_fold (n m p : ℕ) (b : Bool) (B : List Gate)
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hp : p < n + m ∨ w'.length + B.length ≤ p)
    (hI : ∀ i, w.getD i false = b → w'.getD (eraseRedirect n m p i) false = b) :
    ∀ i, (B.foldl step w).getD i false = b →
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false = b := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    simp only [List.length_cons] at hp
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      simp only [step, getD_snoc, List.map_map]
      have hx := op_mono g.op hg b (fun i => w.getD i false)
        (fun i => w'.getD (eraseRedirect n m p i) false) g.inputs hI
      have hIi := hI i
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      by_cases h1 : i < w.length
      · rw [if_pos h1]
        intro hb
        have h3 := hIi hb
        by_cases hr1 : r < w'.length
        · rw [if_pos hr1]; exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg hr1, if_neg (by omega)]
          rw [getD_big _ _ (by omega)] at h3
          exact h3
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · rw [if_pos h2]
          intro hb
          have h3 := hx hb
          have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_neg (by omega), if_pos h4]
          exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
          exact id


theorem erase_main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       x4 < x1 + x3 ∨ x4 = x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;         PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size + (1 : ℕ) = x2.size ∧ ∀ (x9 : List Bool), x9.length = x1 → ∀ (x11 : Bool), (PEqualNP.LowMerge.wireVal x2 x9 (x1 + x3) = x11 → PEqualNP.LowMerge.wireVal x2 x9 x4 = x11) → ∀ (x13 : ℕ), PEqualNP.LowMerge.wireVal x2 x9 x13 = x11 → PEqualNP.LowMerge.wireVal x8 x9 (PEqualNP.CircuitMoves.eraseRedirect x1 x3 x4 x13) = x11 := by
  intro n C m p hM hm hp
  have hm' : m < C.gates.length := hm
  have hsize : C.size = C.gates.length := rfl
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM g' (List.mem_of_mem_drop hg')
      exact ⟨this.1, by simpa using this.2⟩
  · simp only [eraseGate, if_pos hm', Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  · intro x hx b hyp i
    simp only [PEqualNP.LowMerge.wireVal, wires_eq] at hyp ⊢
    have key : C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
        (step ((C.gates.take m).foldl step x) C.gates[m]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    rw [key] at hyp ⊢
    simp only [eraseGate, if_pos hm']
    rw [List.foldl_append]
    have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
      rw [fold_len, hx, List.length_take]; omega
    have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := by simp
    apply main_fold n m p b _ (fun g hg => (hM g (List.mem_of_mem_drop hg)).1)
    · simp [step]
    · omega
    · rw [hWA, hdl]; rcases hp with hp | hp
      · left; exact hp
      · right; rw [hp, hsize]; omega
    · intro j
      generalize hWAd : List.foldl step x (List.take m C.gates) = WA at *
      rw [fold_stab _ _ _ (by simp [step]; omega)] at hyp
      unfold eraseRedirect
      by_cases h1 : j = n + m
      · subst h1; rw [if_pos rfl]
        intro hb
        have h2 := hyp hb
        rcases hp with hp | hp
        · rw [fold_stab _ _ _ (by simp [step]; omega)] at h2
          simp only [step, getD_snoc, hWA, if_pos hp] at h2; exact h2
        · rw [getD_big _ _ (by rw [fold_len]; simp [step]; omega)] at h2
          rw [getD_big _ _ (by omega)]; exact h2
      · rw [if_neg h1]
        simp only [step, getD_snoc, hWA]
        by_cases h3 : j < n + m
        · rw [if_pos h3, if_neg (by omega)]; exact id
        · rw [if_neg h3, if_neg h1, if_pos (by omega), getD_big _ _ (by omega)]; exact id

theorem main_fold2 (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, n + m ∉ g.inputs) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hI : ∀ i, i ≠ n + m → w.getD i false = w'.getD (eraseRedirect n m p i) false) :
    ∀ i, i ≠ n + m → (B.foldl step w).getD i false =
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · intro i hi
      simp only [step, getD_snoc, List.map_map]
      have hx : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map ((fun i => w'.getD i false) ∘ eraseRedirect n m p)) := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hI a (fun h => hg (h ▸ ha))
      have hIi := hI i hi
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      rw [if_neg hi] at hr
      by_cases h1 : i < w.length
      · have hr1 : r < w'.length := by split_ifs at hr <;> omega
        rw [if_pos h1, if_pos hr1]; exact hIi
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_pos h2, if_neg (by omega), if_pos h4]
          exact hx
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]

theorem split_fold (C : Circuit) (x : List Bool) (m : ℕ) (hm : m < C.gates.length) :
    C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
      (step ((C.gates.take m).foldl step x) C.gates[m]) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]

theorem unread (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hu : ∀ k, m < k → ∀ hk : k < C.gates.length, n + m ∉ C.gates[k].inputs)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i ≠ n + m) :
    PEqualNP.LowMerge.wireVal C x i =
      PEqualNP.LowMerge.wireVal (eraseGate n C m p) x (eraseRedirect n m p i) := by
  simp only [PEqualNP.LowMerge.wireVal, wires_eq]
  rw [split_fold C x m hm]
  simp only [eraseGate, if_pos hm]
  rw [List.foldl_append]
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  apply main_fold2 n m p _ _ _ _ _ _ _ i hi
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    simp only [List.getElem_drop]
    exact hu _ (by omega) _
  · simp [step]
  · omega
  · intro j hj
    generalize List.foldl step x (List.take m C.gates) = WA at *
    unfold eraseRedirect
    rw [if_neg hj]
    simp only [step, getD_snoc, hWA]
    by_cases h3 : j < n + m
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_neg hj, if_pos (by omega), getD_big _ _ (by omega)]

theorem gate_val (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.LowMerge.wireVal C x (x.length + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
        if i < x.length + k then PEqualNP.LowMerge.wireVal C x i else false) := by
  simp only [PEqualNP.LowMerge.wireVal, wires_eq]
  rw [split_fold C x k hk]
  have hWA : (List.foldl step x (List.take k C.gates)).length = x.length + k := by
    rw [fold_len, List.length_take]; omega
  generalize List.foldl step x (List.take k C.gates) = WA at *
  rw [fold_stab _ _ _ (by simp [step]; omega)]
  simp only [step, getD_snoc, hWA, if_neg (lt_irrefl _), if_true]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : i < x.length + k
  · rw [if_pos h, fold_stab _ _ _ (by simp [step]; omega)]
    simp only [step, getD_snoc, hWA, if_pos h]
  · rw [if_neg h, getD_big _ _ (by omega)]

def V (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  PEqualNP.LowMerge.wireVal C (List.ofFn x) i

theorem gateV (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    V n C x (n + k) = C.gates[k].op.eval (C.gates[k].inputs.map fun i =>
        if i < n + k then V n C x i else false) := by
  have := gate_val C (List.ofFn x) k hk
  simp only [List.length_ofFn] at this
  exact this

theorem V_top (n : ℕ) (C : Circuit) (x : Fin n → Bool) : V n C x (n + C.size) = false := by
  unfold V PEqualNP.LowMerge.wireVal
  apply getD_big
  rw [wires_eq, fold_len]; simp [Circuit.size]

theorem fun_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = V n C x C.output := rfl

theorem and0 : GateOp.and.eval [] = true := rfl
theorem or0 : GateOp.or.eval [] = false := rfl
theorem and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl
theorem or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
theorem and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by cases a <;> cases b <;> rfl
theorem or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by cases a <;> cases b <;> rfl

section
variable (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
  (hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D →
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C →
    C.size ≤ D.size)
include hM hmin

theorem noEq (m : ℕ) (hm : m < C.gates.length) (p : ℕ) (hp : p < n + m ∨ p = n + C.size)
    (h : ∀ x : Fin n → Bool, V n C x (n + m) = V n C x p) : False := by
  obtain ⟨hM', hs, hv⟩ := erase_main n C m p hM hm hp
  have hf : PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m p) =
      PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    have h1 := hv (List.ofFn x) (by simp) (V n C x C.output) (fun hh => by
      have := h x; unfold V at this; rw [← this]; exact hh) C.output rfl
    rw [fun_eq, fun_eq]
    have ho : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
      simp [eraseGate, hm]
    rw [ho]; exact h1
  have := hmin _ hM' hf
  omega

theorem noFalse (m : ℕ) (hm : m < C.gates.length)
    (h : ∀ x : Fin n → Bool, V n C x (n + m) = false) : False :=
  noEq n C hM hmin m hm _ (Or.inr rfl) (fun x => by rw [h x, V_top])

theorem noTrue (hne : ∃ a b : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C a ≠ PEqualNP.MetaComplexity.circuitFun n C b)
    (m : ℕ) (hm : m < C.gates.length)
    (h : ∀ x : Fin n → Bool, V n C x (n + m) = true) : False := by
  have hu : ∀ k, m < k → ∀ hk : k < C.gates.length, n + m ∉ C.gates[k].inputs := by
    intro k hmk hk hmem
    have hG := fun x => gateV n C x k hk
    obtain ⟨hop, hlen⟩ := hM _ (List.getElem_mem hk)
    have hlt : n + m < n + k := by omega
    have hE : ∀ p, p < n + k → (∀ x : Fin n → Bool, V n C x (n + k) = V n C x p) → False :=
      fun p hp hh => noEq n C hM hmin k hk p (Or.inl hp) hh
    have hF := noFalse n C hM hmin k hk
    rcases hin : C.gates[k].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · rw [hin] at hmem; simp at hmem
    · rw [hin] at hmem hG
      simp only [List.mem_singleton] at hmem
      subst hmem
      refine hE (n + m) hlt (fun x => ?_)
      rw [hG x]
      rcases hop with ho | ho <;> rw [ho] <;> simp [and1, or1, hlt]
    · rw [hin] at hmem hG
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hop with ho | ho <;> rw [ho] at hG <;>
        simp only [List.map_cons, List.map_nil, and2, or2] at hG
      · rcases hmem with rfl | rfl
        · by_cases hb : b < n + k
          · refine hE b hb (fun x => ?_)
            rw [hG x]; simp [hlt, hb, h x]
          · refine hF (fun x => ?_)
            rw [hG x]; simp [hb]
        · by_cases hb : a < n + k
          · refine hE a hb (fun x => ?_)
            rw [hG x]; simp [hlt, hb, h x]
          · refine hF (fun x => ?_)
            rw [hG x]; simp [hb]
      · refine hE (n + m) hlt (fun x => ?_)
        rw [hG x, h x]
        rcases hmem with rfl | rfl <;> simp [hlt, h x]
    · rw [hin] at hlen; simp at hlen
  have hout : C.output ≠ n + m := by
    intro ho
    obtain ⟨a, b, hab⟩ := hne
    apply hab
    rw [fun_eq, fun_eq, ho, h a, h b]
  obtain ⟨hM', hs, -⟩ := erase_main n C m (n + C.size) hM hm (Or.inr rfl)
  have hf : PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m (n + C.size)) =
      PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    rw [fun_eq, fun_eq]
    have ho : (eraseGate n C m (n + C.size)).output =
        eraseRedirect n m (n + C.size) C.output := by
      simp [eraseGate, hm]
    rw [ho]
    exact (unread n C m _ hm hu (List.ofFn x) (by simp) C.output hout).symm
  have := hmin _ hM' hf
  omega

theorem core (hne : ∃ a b : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C a ≠ PEqualNP.MetaComplexity.circuitFun n C b)
    (k : ℕ) (hk : k < C.gates.length) :
    C.gates[k].inputs.length = 2 ∧ ∀ i ∈ C.gates[k].inputs, i < n + k := by
  have hG := fun x => gateV n C x k hk
  obtain ⟨hop, hlen⟩ := hM _ (List.getElem_mem hk)
  have hE : ∀ p, p < n + k → (∀ x : Fin n → Bool, V n C x (n + k) = V n C x p) → False :=
    fun p hp hh => noEq n C hM hmin k hk p (Or.inl hp) hh
  have hF := noFalse n C hM hmin k hk
  have hT := noTrue n C hM hmin hne k hk
  rcases hin : C.gates[k].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rw [hin] at hG
    exfalso
    rcases hop with ho | ho <;> rw [ho] at hG <;>
      simp only [List.map_nil, and0, or0] at hG
    · exact hT hG
    · exact hF hG
  · rw [hin] at hG
    exfalso
    have hG' : ∀ x, V n C x (n + k) = if a < n + k then V n C x a else false := by
      intro x; rw [hG x]
      rcases hop with ho | ho <;> rw [ho] <;> simp only [List.map_cons, List.map_nil, and1, or1]
    by_cases ha : a < n + k
    · exact hE a ha (fun x => by rw [hG' x, if_pos ha])
    · exact hF (fun x => by rw [hG' x, if_neg ha])
  · rw [hin] at hG
    refine ⟨rfl, ?_⟩
    by_contra hbad
    have hab : ¬ (a < n + k ∧ b < n + k) := by
      intro ⟨h1, h2⟩; apply hbad
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    rcases hop with ho | ho <;> rw [ho] at hG <;>
      simp only [List.map_cons, List.map_nil, and2, or2] at hG
    · refine hF (fun x => ?_)
      rw [hG x]
      by_cases ha : a < n + k
      · have hb : ¬ b < n + k := fun hb => hab ⟨ha, hb⟩
        simp [hb]
      · simp [ha]
    · by_cases ha : a < n + k
      · have hb : ¬ b < n + k := fun hb => hab ⟨ha, hb⟩
        exact hE a ha (fun x => by rw [hG x]; simp [ha, hb])
      · by_cases hb : b < n + k
        · exact hE b hb (fun x => by rw [hG x]; simp [ha, hb])
        · exact hF (fun x => by rw [hG x]; simp [ha, hb])
  · rw [hin] at hlen; simp at hlen

end

theorem minAO2 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 → x2.size ≤ x5.size) → PEqualNP.TopForm.IsAO2 x1 x2 := by
  intro n C hM hne hmin
  have hc := core n C hM hmin hne
  refine ⟨fun g hg => ?_, ?_, ?_⟩
  · have := (hM g hg).1
    simpa using this
  · intro j hj i hi
    have h : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
    rw [h] at hi
    exact (hc j hj).2 i hi
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    exact (hc t ht).1



end PEqualNP.Outside.L_meta_7748

open PEqualNP.Outside.L_meta_7748 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_7748 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ¬PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x5 ∧ x5.size + (1 : ℕ) ≤ x1.size ∧ ∀ (x6 : Fin (42 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6) := by
  intro C hM hnA hf
  classical
  have h1 : C.eval (List.ofFn fun _ : Fin 42 => true) = true :=
    (hf _).2 ⟨⟨0, by omega⟩, ⟨21, by omega⟩, by decide, rfl, rfl⟩
  have h2 : C.eval (List.ofFn fun _ : Fin 42 => false) ≠ true := fun h => by
    obtain ⟨_, _, _, h, _⟩ := (hf _).1 h
    simp at h
  have hne : ∃ a b : Fin 42 → Bool, circuitFun 42 C a ≠ circuitFun 42 C b :=
    ⟨fun _ => true, fun _ => false, fun h => h2 (by
      have h3 : C.eval (List.ofFn fun _ : Fin 42 => true) =
        C.eval (List.ofFn fun _ : Fin 42 => false) := h
      rw [← h3]; exact h1)⟩
  have hex : ∃ s, ∃ D : Circuit, Monotone2 D ∧ circuitFun 42 D = circuitFun 42 C ∧
      D.size = s := ⟨C.size, C, hM, rfl, rfl⟩
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, Monotone2 E → circuitFun 42 E = circuitFun 42 D →
      D.size ≤ E.size := fun E hE hEf => by
    rw [hDs]; exact Nat.find_min' hex ⟨E, hE, hEf.trans hDf, rfl⟩
  have hDA := PEqualNP.Outside.L_meta_7748.minAO2 42 D hD (by rw [hDf]; exact hne) hmin
  refine ⟨D, hDA, ?_, fun x => congrFun hDf x⟩
  have hle : D.size ≤ C.size := hmin C hM hDf.symm
  by_contra hcon
  apply hnA
  exact PEqualNP.Outside.L_meta_7748.minAO2 42 C hM hne (fun E hE hEf => by
    have := hmin E hE (hEf.trans hDf.symm); omega)
