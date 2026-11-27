import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def read (g : Gate) (w : List Bool) : Bool :=
  (g.inputs.map fun i => w.getD i false).headD false

def Good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) : ∀ x : List Bool,
    (run gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih =>
    intro x
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma all_mono (l : List ℕ) (a b : ℕ → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (l.map a).all id = true → (l.map b).all id = true := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    exact fun hi => ⟨h i hi.1, ih hi.2⟩

lemma any_mono (l : List ℕ) (a b : ℕ → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (l.map a).any id = true → (l.map b).any id = true := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    exact fun hi => hi.elim (fun hi => Or.inl (h i hi)) (fun hi => Or.inr (ih hi))

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    exact all_mono _ _ _ h
  · rw [hg]
    exact any_mono _ _ _ h

lemma append_mono (a b : List Bool) (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true)
    (u v : Bool) (huv : u = true → v = true) :
    ∀ i, (a ++ [u]).getD i false = true → (b ++ [v]).getD i false = true := by
  intro i hi
  by_cases hil : i < a.length
  · rw [List.getD_append _ _ _ _ hil] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases hie : i = a.length
    · subst i
      have hu : u = true := by simpa using hi
      simpa [hlen] using huv hu
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi

lemma run_mono (gs : List Gate) (hgood : Good gs) :
    ∀ (a b : List Bool), a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hlen h
    apply ih (fun g' hg' => hgood g' (List.mem_cons_of_mem _ hg'))
    · simp [hlen]
    · exact append_mono a b hlen h _ _ (gate_mono g (hgood g List.mem_cons_self) a b h)

lemma read_mono (g : Gate) (a b : List Bool)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    read g a = true → read g b = true := by
  cases hi : g.inputs with
  | nil => simp [read, hi]
  | cons i l => simpa [read, hi] using h i

lemma ofFn_mono {n : ℕ} (a b : Fin n → Bool)
    (h : ∀ i, a i = true → b i = true) :
    ∀ i, (List.ofFn a).getD i false = true → (List.ofFn b).getD i false = true := by
  intro i hi
  by_cases hin : i < n
  · have ha : a ⟨i, hin⟩ = true := by simpa [hin] using hi
    simpa [hin] using h ⟨i, hin⟩ ha
  · simp [hin] at hi

lemma good_snoc (gs : List Gate) (g : Gate) (h : Good gs)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) : Good (gs ++ [g]) := by
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · exact h k hk
  · have hkg := List.mem_singleton.mp hk
    subst k
    exact hg

lemma prefixes {n : ℕ} (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hallowed : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hy : y ∈ X) (hleast : ∀ z ∈ X, ∀ p, y p = true → z p = true)
    (hfalse : ∀ j g, C[j]? = some g → g.op = GateOp.not →
      read g (run (C.take j) (List.ofFn y)) = false →
      ∀ z ∈ X, read g (run (C.take j) (List.ofFn z)) = false)
    (hreplace : ∀ j g, C[j]? = some g →
      (g.op = GateOp.not →
        (read g (run (C.take j) (List.ofFn y)) = true →
          C'[j]? = some (⟨GateOp.or, []⟩ : Gate)) ∧
        (read g (run (C.take j) (List.ofFn y)) = false →
          C'[j]? = some (⟨GateOp.and, []⟩ : Gate))) ∧
      (g.op ≠ GateOp.not → C'[j]? = some g)) :
    ∀ j, j ≤ C.length → Good (C'.take j) ∧
      ∀ z ∈ X, run (C'.take j) (List.ofFn z) = run (C.take j) (List.ofFn z) := by
  intro j
  induction j with
  | zero =>
    intro _
    constructor
    · intro g hg; simp at hg
    · intro z _; rfl
  | succ j ih =>
    intro hj
    obtain ⟨hgood, heq⟩ := ih (by omega)
    have hjlt : j < C.length := by omega
    let g := C[j]
    have hg : C[j]? = some g := by simp [g, hjlt]
    have hstep : C.take (j + 1) = C.take j ++ [g] := by rw [List.take_add_one, hg]; rfl
    have hp := hreplace j g hg
    have ha := (hallowed g (List.getElem_mem hjlt)).1
    by_cases hn : g.op = GateOp.not
    · cases hb : read g (run (C.take j) (List.ofFn y)) with
      | false =>
        have hn' := (hp.1 hn).2 hb
        have hstep' : C'.take (j + 1) = C'.take j ++ [(⟨GateOp.and, []⟩ : Gate)] := by
          rw [List.take_add_one, hn']; rfl
        constructor
        · rw [hstep']
          exact good_snoc _ _ hgood (Or.inl rfl)
        · intro z hz
          have hzread := hfalse j g hg hn hb z hz
          have hv : GateOp.and.eval ([] : List Bool) =
              g.op.eval (g.inputs.map fun i => (run (C.take j) (List.ofFn z)).getD i false) := by
            rw [hn]
            change true = !(read g (run (C.take j) (List.ofFn z)))
            rw [hzread]
            rfl
          rw [hstep', hstep, run_snoc, run_snoc, heq z hz]
          simp only [List.map_nil, hv]
      | true =>
        have hn' := (hp.1 hn).1 hb
        have hstep' : C'.take (j + 1) = C'.take j ++ [(⟨GateOp.or, []⟩ : Gate)] := by
          rw [List.take_add_one, hn']; rfl
        constructor
        · rw [hstep']
          exact good_snoc _ _ hgood (Or.inr rfl)
        · intro z hz
          have horder := run_mono (C'.take j) hgood (List.ofFn y) (List.ofFn z)
            (by simp) (ofFn_mono y z (hleast z hz))
          have hr := read_mono g _ _ horder
          rw [heq y hy, heq z hz] at hr
          have hzread := hr hb
          have hv : GateOp.or.eval ([] : List Bool) =
              g.op.eval (g.inputs.map fun i => (run (C.take j) (List.ofFn z)).getD i false) := by
            rw [hn]
            change false = !(read g (run (C.take j) (List.ofFn z)))
            rw [hzread]
            rfl
          rw [hstep', hstep, run_snoc, run_snoc, heq z hz]
          simp only [List.map_nil, hv]
    · have hn' := hp.2 hn
      have hstep' : C'.take (j + 1) = C'.take j ++ [g] := by rw [List.take_add_one, hn']; rfl
      have hgm : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases ha with ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr ha
        · exact False.elim (hn ha)
      constructor
      · rw [hstep']; exact good_snoc _ _ hgood hgm
      · intro z hz
        rw [hstep', hstep, run_snoc, run_snoc, heq z hz]

end PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hallowed hy hleast hfalse hlen hreplace x hx w
  have h := (PEqualNP.Outside.L_meta_749.prefixes C C' X y hallowed hy hleast hfalse hreplace
    C.length (le_refl _)).2 x hx
  have ht : C'.take C.length = C' := by rw [← hlen, List.take_length]
  rw [ht, List.take_length] at h
  exact congrArg (fun l : List Bool => l.getD w false) h
