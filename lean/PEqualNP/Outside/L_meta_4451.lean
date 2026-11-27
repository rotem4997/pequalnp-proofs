import Mathlib
import PEqualNP.Defs

-- Fixing one input of an AND/OR circuit to false and propagating the constant. Every old
-- wire gets an image: the constant false, or a wire of the new circuit. An AND gate with a
-- false operand is false, an OR gate with a false operand is the other operand, and a gate
-- whose two operands are wires is kept. The new circuit is below the old one everywhere and
-- equal to it where the fixed input is false; it is smaller as soon as one gate reads the
-- fixed input. The shape of the propagation follows our gate elimination file, which
-- adapted PEqualNP/Outside/L_meta_2513.lean of this repository (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

-- The value of an image: none is the constant false, some p is the new wire p.
def ival (V : List Bool) : Option ℕ → Bool
  | none => false
  | some p => V.getD p false

theorem ival_append (V t : List Bool) : ∀ e : Option ℕ, (∀ p, e = some p → p < V.length) →
    ival (V ++ t) e = ival V e
  | none, _ => rfl
  | some p, h => List.getD_append _ _ _ _ (h p rfl)

-- The image of a gate that is not kept, from the image of its surviving operand.
def pass (op : GateOp) (e : Option ℕ) : Option ℕ :=
  match op with
  | GateOp.and => none
  | _ => e

-- The image of a gate from the images of its two operands; m is the next new wire.
def stepIm (op : GateOp) (m : ℕ) : Option ℕ → Option ℕ → Option ℕ
  | some _, some _ => some m
  | some p, none => pass op (some p)
  | none, iq => pass op iq

-- The gate that is kept, if any.
def stepOut (op : GateOp) : Option ℕ → Option ℕ → List Gate
  | some p, some q => [⟨op, [p, q]⟩]
  | _, _ => []

def step (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate) : List (Option ℕ) × List Gate :=
  (s.1 ++ [stepIm g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
      (s.1.getD (g.inputs.getD 1 0) none)],
    s.2 ++ stepOut g.op (s.1.getD (g.inputs.getD 0 0) none) (s.1.getD (g.inputs.getD 1 0) none))

theorem stepOut_length (op : GateOp) (ip iq : Option ℕ) : (stepOut op ip iq).length ≤ 1 := by
  cases ip <;> cases iq <;> simp [stepOut]

theorem stepOut_full (op : GateOp) (ip iq : Option ℕ) (h : (stepOut op ip iq).length = 1) :
    ip ≠ none ∧ iq ≠ none := by
  cases ip <;> cases iq <;> simp [stepOut] at h ⊢

-- The value of the new image is the gate applied to the values of the operand images.
theorem entry_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (V : List Bool)
    (ip iq : Option ℕ) :
    ival (wiresFrom (stepOut op ip iq) V) (stepIm op V.length ip iq)
      = op.eval [ival V ip, ival V iq] := by
  rcases hop with rfl | rfl <;> cases ip <;> cases iq <;>
    simp [stepIm, stepOut, pass, wiresFrom, ival, GateOp.eval]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v bp bq : Bool)
    (hu : u = true → bp = true) (hv : v = true → bq = true) (h : op.eval [u, v] = true) :
    op.eval [bp, bq] = true := by
  rcases hop with rfl | rfl <;> cases u <;> cases v <;> cases bp <;> cases bq <;>
    simp_all [GateOp.eval]

theorem stepIm_lt (op : GateOp) (B : ℕ) (ip iq : Option ℕ) (hp : ∀ p, ip = some p → p < B)
    (hq : ∀ p, iq = some p → p < B) :
    ∀ p, stepIm op B ip iq = some p → p < B + (stepOut op ip iq).length := by
  intro p h
  cases ip with
  | none =>
    cases op <;> simp only [stepIm, pass] at h
    all_goals first
      | exact Nat.lt_of_lt_of_le (hq p h) (Nat.le_add_right _ _)
      | simp at h
  | some p1 =>
    cases iq with
    | none =>
      cases op <;> simp only [stepIm, pass] at h
      all_goals first
        | exact Nat.lt_of_lt_of_le (hp p h) (Nat.le_add_right _ _)
        | simp at h
    | some q1 =>
      simp only [stepIm, Option.some.injEq] at h
      subst h
      simp [stepOut]

-- The invariant of the new circuit that does not depend on the input.
def Good (n : ℕ) (s : List (Option ℕ) × List Gate) : Prop :=
  (∀ i p, s.1.getD i none = some p → p < n + s.2.length) ∧
  (∀ g ∈ s.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < s.2.length, ∀ i ∈ (s.2.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

theorem good_step (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Good n s) : Good n (step n s g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hlt := stepIm_lt g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
    (s.1.getD (g.inputs.getD 1 0) none) (fun p hp => h1 _ p hp) (fun p hp => h1 _ p hp)
  refine ⟨?_, ?_, ?_⟩
  · intro i p hp
    show p < n + (s.2 ++ stepOut g.op _ _).length
    rw [List.length_append, ← Nat.add_assoc]
    by_cases hil : i = s.1.length
    · subst hil
      have hp' : stepIm g.op (n + s.2.length) (s.1.getD (g.inputs.getD 0 0) none)
          (s.1.getD (g.inputs.getD 1 0) none) = some p := by
        rw [← hp]
        exact (getD_snoc_eq _ _ _).symm
      exact hlt p hp'
    · have hp' : s.1.getD i none = some p := by
        rw [← hp]
        exact (getD_snoc_ne _ _ _ _ hil).symm
      exact Nat.lt_of_lt_of_le (h1 i p hp') (Nat.le_add_right _ _)
  · intro g' hg'
    rcases List.mem_append.1 hg' with hin | hin
    · exact h2 g' hin
    · cases hip : s.1.getD (g.inputs.getD 0 0) none <;>
        cases hiq : s.1.getD (g.inputs.getD 1 0) none <;>
        simp only [hip, hiq, stepOut, List.mem_singleton, List.not_mem_nil] at hin
      subst hin
      exact ⟨hop, rfl⟩
  · intro j hj i hi
    by_cases hjl : j < s.2.length
    · rw [show (step n s g).2 = s.2 ++ stepOut g.op _ _ from rfl,
        List.getD_append _ _ _ _ hjl] at hi
      exact h3 j hjl i hi
    · cases hip : s.1.getD (g.inputs.getD 0 0) none <;>
        cases hiq : s.1.getD (g.inputs.getD 1 0) none <;>
        simp only [step, hip, hiq, stepOut, List.append_nil, List.length_append,
          List.length_singleton] at hj hi
      all_goals try omega
      rename_i p1 q1
      have hje : j = s.2.length := by omega
      subst hje
      rw [getD_snoc_eq] at hi
      rcases List.mem_cons.1 hi with rfl | hi2
      · exact h1 _ _ hip
      · rcases List.mem_cons.1 hi2 with rfl | hi3
        · exact h1 _ _ hiq
        · simp at hi3

theorem good_fold (n : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Good n s →
      Good n (gs.foldl (step n) s) := by
  induction gs with
  | nil => intro s _ h; exact h
  | cons g gs ih =>
    intro s hok h
    exact ih (step n s g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (good_step n s g (hok g List.mem_cons_self) h)

-- The invariant on an input X: W holds the old wires, the images are below them, and equal
-- to them when the fixed input a is false.
def Sem (a : ℕ) (X : List Bool) (s : List (Option ℕ) × List Gate) (W : List Bool) : Prop :=
  s.1.length = W.length ∧
  (∀ i, ival (wiresFrom s.2 X) (s.1.getD i none) = true → W.getD i false = true) ∧
  (X.getD a false = false → ∀ i, ival (wiresFrom s.2 X) (s.1.getD i none) = W.getD i false)

theorem sem_step (n a : ℕ) (X : List Bool) (hX : X.length = n)
    (s : List (Option ℕ) × List Gate) (W : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hg : Good n s) (h : Sem a X s W) :
    Sem a X (step n s g) (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := by
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · obtain ⟨hl, hS1, hS2⟩ := h
    have hop' : op = GateOp.and ∨ op = GateOp.or := hop
    have lV : (wiresFrom s.2 X).length = n + s.2.length := by rw [length_wiresFrom, hX]
    have hnew : wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X
        = wiresFrom (stepOut op (s.1.getD p none) (s.1.getD q none)) (wiresFrom s.2 X) :=
      wiresFrom_append _ _ _
    obtain ⟨t, ht, -⟩ := wiresFrom_prefix (stepOut op (s.1.getD p none) (s.1.getD q none))
      (wiresFrom s.2 X)
    have hval := entry_val op hop' (wiresFrom s.2 X) (s.1.getD p none) (s.1.getD q none)
    rw [lV] at hval
    have stable : ∀ i, ival (wiresFrom s.2 X ++ t) (s.1.getD i none)
        = ival (wiresFrom s.2 X) (s.1.getD i none) := fun i =>
      ival_append _ t _ (fun p' hp' => by rw [lV]; exact hg.1 i p' hp')
    refine ⟨by simp [step, hl], ?_, ?_⟩
    · intro i
      show ival (wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X)
          ((s.1 ++ [stepIm op (n + s.2.length) (s.1.getD p none) (s.1.getD q none)]).getD i none)
            = true →
          (W ++ [op.eval [W.getD p false, W.getD q false]]).getD i false = true
      rw [hnew]
      by_cases hil : i = s.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq, hval]
        exact eval_mono op hop' _ _ _ _ (hS1 p) (hS1 q)
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega), ht, stable]
        exact hS1 i
    · intro hxa i
      show ival (wiresFrom (s.2 ++ stepOut op (s.1.getD p none) (s.1.getD q none)) X)
          ((s.1 ++ [stepIm op (n + s.2.length) (s.1.getD p none) (s.1.getD q none)]).getD i none)
            = (W ++ [op.eval [W.getD p false, W.getD q false]]).getD i false
      rw [hnew]
      by_cases hil : i = s.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq, hval, hS2 hxa p, hS2 hxa q]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega), ht, stable]
        exact hS2 hxa i
  · simp at hlen

theorem sem_fold (n a : ℕ) (X : List Bool) (hX : X.length = n) (gs : List Gate) :
    ∀ (s : List (Option ℕ) × List Gate) (W : List Bool),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      Good n s → Sem a X s W → Sem a X (gs.foldl (step n) s) (wiresFrom gs W) := by
  induction gs with
  | nil => intro s W _ _ h; exact h
  | cons g gs ih =>
    intro s W hok hg h
    have hgo := hok g List.mem_cons_self
    exact ih (step n s g) _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (good_step n s g hgo.1 hg) (sem_step n a X hX s W g hgo.1 hgo.2 hg h)

-- The images of the input wires: wire a is the constant false, every other wire is itself.
def init (n a : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = a then none else some i

theorem init_length (n a : ℕ) : (init n a).length = n := by
  simp [init]

theorem init_getD (n a k : ℕ) :
    (init n a).getD k none = if k < n ∧ k ≠ a then some k else none := by
  by_cases hk : k < n
  · by_cases hv : k = a
    · subst hv
      simp [init, hk]
    · simp [init, hk, hv]
  · rw [List.getD_eq_default _ _ (by rw [init_length]; omega)]
    simp [hk]

theorem good_init (n a : ℕ) : Good n (init n a, []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i p hp
    have hp' : (init n a).getD i none = some p := hp
    rw [init_getD] at hp'
    split at hp'
    · rename_i hc
      simp only [Option.some.injEq] at hp'
      subst hp'
      exact Nat.lt_of_lt_of_le hc.1 (Nat.le_add_right _ _)
    · simp at hp'
  · intro g hg
    simp at hg
  · intro j hj
    simp at hj

theorem sem_init (n a : ℕ) (X : List Bool) (hX : X.length = n) : Sem a X (init n a, []) X := by
  refine ⟨by simp [init_length, hX], ?_, ?_⟩
  · intro i
    show ival X ((init n a).getD i none) = true → X.getD i false = true
    rw [init_getD]
    split
    · exact id
    · intro h
      simp [ival] at h
  · intro hxa i
    show ival X ((init n a).getD i none) = X.getD i false
    rw [init_getD]
    split
    · rfl
    · rename_i hc
      show false = X.getD i false
      by_cases hi : i < n
      · have hia : i = a := by
          by_contra hne
          exact hc ⟨hi, hne⟩
        rw [hia, hxa]
      · rw [List.getD_eq_default _ _ (by omega)]

-- The number of gates kept.
theorem step_snd_len (n : ℕ) (s : List (Option ℕ) × List Gate) (g : Gate) :
    (step n s g).2.length ≤ s.2.length + 1 := by
  have := stepOut_length g.op (s.1.getD (g.inputs.getD 0 0) none)
    (s.1.getD (g.inputs.getD 1 0) none)
  simp only [step, List.length_append]
  omega

theorem fold_snd_len (n : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    (gs.foldl (step n) s).2.length ≤ s.2.length + gs.length := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    have h1 := ih (step n s g)
    have h2 := step_snd_len n s g
    simp only [List.foldl_cons, List.length_cons]
    omega

-- If every gate is kept, no gate reads the fixed input.
theorem fold_full (n a : ℕ) (gs : List Gate) : ∀ s : List (Option ℕ) × List Gate,
    a < s.1.length → s.1.getD a none = none → (∀ g ∈ gs, g.inputs.length = 2) →
    (gs.foldl (step n) s).2.length = s.2.length + gs.length → ∀ g ∈ gs, a ∉ g.inputs := by
  induction gs with
  | nil => intro s _ _ _ _ g hg; simp at hg
  | cons g gs ih =>
    intro s ha hna hlen hfull g' hg'
    have h1 := fold_snd_len n gs (step n s g)
    have h2 := step_snd_len n s g
    simp only [List.foldl_cons, List.length_cons] at hfull
    have e1 : (step n s g).2.length = s.2.length + 1 := by omega
    have e2 : (gs.foldl (step n) (step n s g)).2.length = (step n s g).2.length + gs.length := by
      omega
    rcases List.mem_cons.1 hg' with heq | hin
    · subst heq
      have e3 : (stepOut g'.op (s.1.getD (g'.inputs.getD 0 0) none)
          (s.1.getD (g'.inputs.getD 1 0) none)).length = 1 := by
        simp only [step, List.length_append] at e1
        omega
      obtain ⟨hp, hq⟩ := stepOut_full _ _ _ e3
      have hl2 := hlen g' List.mem_cons_self
      obtain ⟨op, inputs⟩ := g'
      rcases inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩
      · simp at hl2
      · simp at hl2
      · intro hmem
        rcases List.mem_cons.1 hmem with rfl | hmem2
        · exact hp hna
        · rcases List.mem_cons.1 hmem2 with rfl | hmem3
          · exact hq hna
          · simp at hmem3
      · simp at hl2
    · exact ih (step n s g) (by simp only [step, List.length_append, List.length_singleton]; omega)
        (by
          show (s.1 ++ [_]).getD a none = none
          rw [getD_snoc_ne _ _ _ _ (by omega)]
          exact hna)
        (fun g0 hg0 => hlen g0 (List.mem_cons_of_mem _ hg0)) e2 g' hin

-- If no gate reads wire a, the other wires do not depend on it.
theorem off_fold (a : ℕ) (gs : List Gate) : ∀ W W' : List Bool, W.length = W'.length →
    (∀ g ∈ gs, a ∉ g.inputs) → (∀ i, i ≠ a → W.getD i false = W'.getD i false) →
    ∀ i, i ≠ a → (wiresFrom gs W).getD i false = (wiresFrom gs W').getD i false := by
  induction gs with
  | nil => intro W W' _ _ h; exact h
  | cons g gs ih =>
    intro W W' hl hno h
    have hv : g.op.eval (g.inputs.map fun i => W.getD i false)
        = g.op.eval (g.inputs.map fun i => W'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact h k (fun hka => hno g List.mem_cons_self (hka ▸ hk))
    have hstep : ∀ i, i ≠ a →
        (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD i false
          = (W' ++ [g.op.eval (g.inputs.map fun i => W'.getD i false)]).getD i false := by
      intro i hi
      rw [hv]
      by_cases hil : i = W.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        exact h i hi
    exact ih _ _ (by simp [hl]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) hstep

-- The output of the new circuit: the image of the old output, or a wire that is not there.
def outIdx (m : ℕ) : Option ℕ → ℕ
  | none => m
  | some p => p

theorem eval_out (n : ℕ) (out : List Gate) (e : Option ℕ) (X : List Bool) (hX : X.length = n) :
    (Circuit.mk out (outIdx (n + out.length) e)).eval X = ival (wiresFrom out X) e := by
  cases e with
  | none =>
    show (wiresFrom out X).getD (n + out.length) false = false
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom, hX])
  | some p => rfl

theorem erase (n : ℕ) (C : Circuit) (a b : Fin n) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (_hab : a ≠ b) (h1 : circuitFun n C (fun i => decide (i = a)) = false)
    (h2 : circuitFun n C (fun i => decide (i = b)) = false)
    (h3 : circuitFun n C (fun i => decide (i = a ∨ i = b)) = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
      ∀ x : Fin n → Bool, x a = false → circuitFun n D x = circuitFun n C x := by
  obtain ⟨hand, -, hlen2⟩ := hAO
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hand g hg, hlen2 g hg⟩
  have hgood : Good n (C.gates.foldl (step n) (init n a, [])) :=
    good_fold n C.gates _ (fun g hg => (hok g hg).1) (good_init n a)
  have hsem : ∀ X : List Bool, X.length = n →
      Sem a X (C.gates.foldl (step n) (init n a, [])) (wiresFrom C.gates X) :=
    fun X hX => sem_fold n a X hX C.gates _ _ hok (good_init n a) (sem_init n a X hX)
  have hD : ∀ x : Fin n → Bool,
      circuitFun n ⟨(C.gates.foldl (step n) (init n a, [])).2,
        outIdx (n + (C.gates.foldl (step n) (init n a, [])).2.length)
          ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none)⟩ x
      = ival (wiresFrom (C.gates.foldl (step n) (init n a, [])).2 (List.ofFn x))
          ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none) :=
    fun x => eval_out n _ _ _ (by simp)
  refine ⟨⟨(C.gates.foldl (step n) (init n a, [])).2,
    outIdx (n + (C.gates.foldl (step n) (init n a, [])).2.length)
      ((C.gates.foldl (step n) (init n a, [])).1.getD C.output none)⟩,
    ⟨fun g hg => (hgood.2.1 g hg).1, hgood.2.2, fun g hg => (hgood.2.1 g hg).2⟩, ?_, ?_, ?_⟩
  · show (C.gates.foldl (step n) (init n a, [])).2.length < C.gates.length
    have hle := fold_snd_len n C.gates (init n a, [])
    by_contra hnot
    have heq : (C.gates.foldl (step n) (init n a, [])).2.length
        = (init n a, ([] : List Gate)).2.length + C.gates.length := by
      simp only [List.length_nil] at hle ⊢
      omega
    have hno := fold_full n a C.gates (init n a, []) (by simp [init_length])
      (by
        show (init n a).getD a none = none
        rw [init_getD]
        simp)
      hlen2 heq
    by_cases ho : C.output = (a : ℕ)
    · have h1' : (wiresFrom C.gates (List.ofFn fun i => decide (i = a))).getD C.output false
          = false := h1
      obtain ⟨t, ht, -⟩ := wiresFrom_prefix C.gates (List.ofFn fun i => decide (i = a))
      rw [ht, ho, List.getD_append _ _ _ _ (by simp), ofFn_getD] at h1'
      simp at h1'
    · have hagree := off_fold a C.gates (List.ofFn fun i => decide (i = a ∨ i = b))
        (List.ofFn fun i => decide (i = b)) (by simp) hno
        (by
          intro i hi
          rw [ofFn_getD, ofFn_getD]
          by_cases hin : i < n
          · have hne : (⟨i, hin⟩ : Fin n) ≠ a := fun h => hi (congrArg Fin.val h)
            simp [hin, hne]
          · simp [hin])
        C.output ho
      have h3' : (wiresFrom C.gates (List.ofFn fun i => decide (i = a ∨ i = b))).getD
          C.output false = true := h3
      have h2' : (wiresFrom C.gates (List.ofFn fun i => decide (i = b))).getD C.output false
          = false := h2
      rw [hagree, h2'] at h3'
      exact Bool.false_ne_true h3'
  · intro x hx
    rw [hD x] at hx
    exact (hsem (List.ofFn x) (by simp)).2.1 C.output hx
  · intro x hxa
    rw [hD x]
    exact (hsem (List.ofFn x) (by simp)).2.2 (by rw [ofFn_getD]; simp [hxa]) C.output

end PEqualNP.Outside.L_meta_4451

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n0 C0 a0 b0 hAO hab h1 h2 h3
  exact PEqualNP.Outside.L_meta_4451.erase n0 C0 a0 b0 hAO hab h1 h2 h3
