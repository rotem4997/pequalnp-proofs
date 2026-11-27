import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2654


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A removed wire redirects to `r`, and subsequent wires shift down by one.
def remap (n r j : Nat) : Nat :=
  if j < n then j else if j = n then r else j - 1

def remapGate (n r : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n r)⟩

def remapCircuit (n r : Nat) (gs : List Gate) (o : Nat) : Circuit :=
  ⟨gs.map (remapGate n r), remap n r o⟩

private theorem getD_left (a b : List Bool) (i : Nat) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_right (a b : List Bool) (i : Nat) (h : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getD_missing (a : List Bool) (i : Nat) (h : a.length ≤ i) :
    a.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

private theorem read_remap (x s : List Bool) (r j : Nat)
    (hr : r < x.length ∨ x.length + s.length ≤ r) :
    (x ++ (x.getD r false :: s)).getD j false =
      (x ++ s).getD (remap x.length r j) false := by
  by_cases hj : j < x.length
  · rw [remap, ite_eq_left hj, getD_left _ _ _ hj, getD_left _ _ _ hj]
  · by_cases he : j = x.length
    · subst j
      rw [remap, ite_eq_right hj, ite_eq_left rfl, getD_right _ _ _ (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      rcases hr with h | h
      · exact (getD_left _ _ _ h).symm
      · rw [getD_missing x r (by omega),
            getD_missing (x ++ s) r (by simpa using h)]
    · have hleft : x.length ≤ j := by omega
      have hright : x.length ≤ j - 1 := by omega
      have hsub : j - x.length = (j - 1 - x.length) + 1 := by omega
      rw [remap, ite_eq_right hj, ite_eq_right he, getD_right _ _ _ hleft,
          getD_right _ _ _ hright, hsub, List.getD_cons_succ]

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_tail (x : List Bool) (gs : List Gate) (s : List Bool) (r o : Nat)
    (hr : r < x.length ∨ x.length + s.length + gs.length ≤ r) :
    (gs.foldl advance (x ++ (x.getD r false :: s))).getD o false =
      ((gs.map (remapGate x.length r)).foldl advance (x ++ s)).getD
        (remap x.length r o) false := by
  induction gs generalizing s with
  | nil =>
    exact read_remap x s r o (by simpa using hr)
  | cons g gs ih =>
    have hrNow : r < x.length ∨ x.length + s.length ≤ r := by
      rcases hr with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    let b := g.op.eval (g.inputs.map fun i =>
      (x ++ (x.getD r false :: s)).getD i false)
    have hgate :
        (remapGate x.length r g).op.eval
          ((remapGate x.length r g).inputs.map fun i => (x ++ s).getD i false) = b := by
      simp only [remapGate, List.map_map, b]
      congr 1
      exact List.map_congr_left (fun i _ => (read_remap x s r i hrNow).symm)
    have hrNext : r < x.length ∨ x.length + (s ++ [b]).length + gs.length ≤ r := by
      rcases hr with h | h
      · exact Or.inl h
      · right
        simp only [List.length_cons] at h
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    simp only [List.foldl_cons, List.map_cons, advance, hgate]
    change (gs.foldl advance ((x ++ (x.getD r false :: s)) ++ [b])).getD o false =
      ((gs.map (remapGate x.length r)).foldl advance ((x ++ s) ++ [b])).getD
        (remap x.length r o) false
    simpa only [List.append_assoc, List.cons_append] using ih (s ++ [b]) hrNext

theorem remap_eval (x : List Bool) (gs : List Gate) (o r : Nat)
    (hr : r < x.length ∨ x.length + gs.length ≤ r) :
    (remapCircuit x.length r gs o).eval x =
      (Circuit.mk gs o).eval (x ++ [x.getD r false]) := by
  change ((gs.map (remapGate x.length r)).foldl advance x).getD
      (remap x.length r o) false =
    (gs.foldl advance (x ++ [x.getD r false])).getD o false
  simpa only [List.append_nil] using (read_tail x gs [] r o (by simpa using hr)).symm

theorem remap_size (n r : Nat) (gs : List Gate) (o : Nat) :
    (remapCircuit n r gs o).size = gs.length := by
  simp [remapCircuit, Circuit.size]

theorem remap_monotone (n r : Nat) (gs : List Gate) (o : Nat)
    (h : Monotone2 (Circuit.mk gs o)) : Monotone2 (remapCircuit n r gs o) := by
  intro g hg
  obtain ⟨orig, horig, rfl⟩ :=
    List.mem_map.mp (show g ∈ gs.map (remapGate n r) from hg)
  simpa only [remapGate, List.length_map] using h orig horig




open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def tailValue {n : Nat} (tail : List Gate) (out : Nat) (x : Fin n → Bool) (t : Bool) : Bool :=
  (tail.foldl step (List.ofFn x ++ [t])).getD out false

def edgeOn {n : Nat} (edges : List (Nat × Nat)) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

private def Below (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

private theorem append_below {a b : List Bool} (hlen : a.length = b.length)
    (h : Below a b) {x y : Bool} (hxy : x = true → y = true) :
    Below (a ++ [x]) (b ++ [y]) := by
  intro i hi
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  by_cases he : i = a.length
  · subst i
    have hx : x = true := by simpa using hi
    rw [hlen]
    simpa using hxy hx
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

private theorem value_below (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    {a b : List Bool} (h : Below a b)
    (ha : g.op.eval (g.inputs.map fun i => a.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hAnd | hOr
  · rw [hAnd, GateOp.eval, List.all_eq_true] at ha ⊢
    intro q hq
    rcases List.mem_map.mp hq with ⟨i, hi, rfl⟩
    exact h i (ha _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [hOr, GateOp.eval, List.any_eq_true] at ha ⊢
    obtain ⟨q, hq, hqa⟩ := ha
    rcases List.mem_map.mp hq with ⟨i, hi, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hqa⟩

private theorem fold_below (tail : List Gate)
    (hg : ∀ g ∈ tail, g.op = .and ∨ g.op = .or) {a b : List Bool}
    (hlen : a.length = b.length) (h : Below a b) :
    Below (tail.foldl step a) (tail.foldl step b) := by
  induction tail generalizing a b with
  | nil => exact h
  | cons g tail ih =>
    change Below (tail.foldl step (step a g)) (tail.foldl step (step b g))
    exact ih (fun t ht => hg t (List.mem_cons_of_mem _ ht))
      (by simp [step, hlen]) (append_below hlen h (value_below g (hg g (by simp)) h))

private theorem inputs_below {n : Nat} {x y : Fin n → Bool}
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
    exact h ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simpa using hlt)] at hi
    contradiction

theorem tailValue_below {n : Nat} (tail : List Gate) (out : Nat)
    (hg : ∀ g ∈ tail, g.op = .and ∨ g.op = .or) {x y : Fin n → Bool} {u v : Bool}
    (h : ∀ i, x i = true → y i = true) (huv : u = true → v = true) :
    tailValue tail out x u = true → tailValue tail out y v = true :=
  fold_below tail hg (by simp) (append_below (by simp) (inputs_below h) huv) out

theorem eval_tail_false_nonedge {n : Nat} (edges : List (Nat × Nat)) (tail : List Gate)
    (out : Nat) (a b : Fin n) (hab : a ≠ b)
    (hne : ¬ ((a.val, b.val) ∈ edges ∨ (b.val, a.val) ∈ edges))
    (hg : ∀ g ∈ tail, g.op = .and ∨ g.op = .or)
    (hc : ∀ x : Fin n → Bool, tailValue tail out x (x a && x b) = true ↔ edgeOn edges x)
    (x : Fin n → Bool) :
    tailValue tail out x false = true ↔ edgeOn edges x := by
  constructor
  · intro h
    exact (hc x).mp (tailValue_below tail out hg (fun _ h => h) (by simp) h)
  · rintro ⟨u, v, hev, hu, hv⟩
    let y : Fin n → Bool := fun i => decide (i = u ∨ i = v)
    have hy : edgeOn edges y := ⟨u, v, hev, by simp [y], by simp [y]⟩
    have hyx : ∀ i, y i = true → x i = true := by
      intro i hi
      have hi' : i = u ∨ i = v := by simpa [y] using hi
      rcases hi' with rfl | rfl
      · exact hu
      · exact hv
    have hfalse : (y a && y b) = false := by
      cases h : y a && y b
      · rfl
      · exfalso
        have ha : a = u ∨ a = v := by simpa [y] using (Bool.and_eq_true_iff.mp h).1
        have hb : b = u ∨ b = v := by simpa [y] using (Bool.and_eq_true_iff.mp h).2
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact hab (ha.trans hb.symm)
        · exact hne (Or.inl (by simpa [ha, hb] using hev))
        · exact hne (Or.inr (by simpa [ha, hb] using hev))
        · exact hab (ha.trans hb.symm)
    have h := (hc y).mpr hy
    rw [hfalse] at h
    exact tailValue_below tail out hg hyx (fun h => h) h

theorem eval_tail_diag {n : Nat} (tail : List Gate) (out : Nat) (x : Fin n → Bool) (a : Fin n) :
    tailValue tail out x (x a && x a) = tailValue tail out x (x a) := by
  cases x a <;> rfl

theorem eval_cons_and {n : Nat} (C : Circuit) (tail : List Gate)
    (a b : Fin n) (hg : C.gates = ⟨.and, [a.val,b.val]⟩ :: tail) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = tailValue tail C.output x (x a && x b) := by
  have hget (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  unfold Circuit.eval Circuit.wires
  rw [hg]
  change (tail.foldl step ((List.ofFn x) ++ [(_ : GateOp).eval
      ([a.val,b.val].map fun i => (List.ofFn x).getD i false)])).getD C.output false = _
  have he : GateOp.and.eval ([a.val,b.val].map fun i => (List.ofFn x).getD i false) =
      (x a && x b) := by
    simp only [List.map_cons, List.map_nil, hget, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  rw [he]
  rfl




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem inputAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

theorem dropFirstAnd {n : ℕ} (edges : List (ℕ × ℕ)) (C : Circuit) (tail : List Gate)
    (p q : ℕ) (hGates : C.gates = ⟨.and, [p, q]⟩ :: tail)
    (hp : p < n) (hq : q < n) (hne : ¬ ((p, q) ∈ edges ∨ (q, p) ∈ edges))
    (hMono : Monotone2 C)
    (hCorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ edgeOn edges x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ edgeOn edges x := by
  let u : Fin n := ⟨p, hp⟩
  let v : Fin n := ⟨q, hq⟩
  have hTailMono : Monotone2 (Circuit.mk tail C.output) := by
    intro g hg
    apply hMono g
    rw [hGates]
    exact List.mem_cons_of_mem _ hg
  have hTailOps : ∀ g ∈ tail, g.op = .and ∨ g.op = .or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hTailMono g hg).1
  have hOrig (x : Fin n → Bool) :
      tailValue tail C.output x (x u && x v) = true ↔
        edgeOn edges x := by
    rw [← eval_cons_and C tail u v hGates x]
    exact hCorrect x
  let redirect := if p = q then p else n + tail.length
  let D := remapCircuit n redirect tail C.output
  refine ⟨D, remap_monotone n redirect tail C.output hTailMono, ?_, ?_⟩
  · change (remapCircuit n redirect tail C.output).size + 1 ≤ C.size
    rw [remap_size]
    simp [Circuit.size, hGates]
  · intro x
    have hLength : (List.ofFn x).length = n := List.length_ofFn
    have hRedirect : redirect < (List.ofFn x).length ∨ (List.ofFn x).length + tail.length ≤ redirect := by
      rw [hLength]
      by_cases hEq : p = q
      · simp [redirect, hEq, hq]
      · simp [redirect, hEq]
    have hEval := remap_eval (List.ofFn x) tail C.output redirect hRedirect
    rw [hLength] at hEval
    change (remapCircuit n redirect tail C.output).eval (List.ofFn x) = true ↔ _
    rw [hEval]
    change tailValue tail C.output x ((List.ofFn x).getD redirect false) = true ↔ _
    by_cases hEq : p = q
    · have hUV : u = v := Fin.ext hEq
      have hU : (List.ofFn x).getD p false = x u := inputAt x u
      have hValue : redirect = p := by simp [redirect, hEq]
      rw [hValue, hU]
      simpa only [← hUV, Bool.and_self] using hOrig x
    · have hOutside : (List.ofFn x).length ≤ redirect := by
        rw [hLength]
        simp [redirect, hEq]
      rw [List.getD_eq_default _ _ hOutside]
      exact eval_tail_false_nonedge edges tail C.output u v
        (fun huv => hEq (congrArg Fin.val huv)) hne hTailOps hOrig x


end PEqualNP.Outside.L_meta_2654

theorem PEqualNP.Outside.L_meta_2654 :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x3.gates = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } :: x4 → x5 < (14 : ℕ) → x6 < (14 : ℕ) → ¬((x5, x6) ∈ x1 ∨ (x6, x5) ∈ x1) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x12 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x12) = Bool.true ↔ x2 x12) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size + (1 : ℕ) ≤ x3.size ∧ ∀ (x14 : Fin (14 : ℕ) → Bool), x13.eval (List.ofFn x14) = Bool.true ↔ x2 x14 := by
  dsimp only
  intro C tail p q hGates hp hq hne hMono hCorrect
  exact PEqualNP.Outside.L_meta_2654.dropFirstAnd _ C tail p q hGates hp hq hne hMono hCorrect
