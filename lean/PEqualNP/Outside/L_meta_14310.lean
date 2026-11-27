import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_14310

abbrev Fn (X : Type) := X → Bool
abbrev Pool (X : Type) := Fn X → Prop
def inv {X : Type} (f : Fn X) : Fn X := fun x => !(f x)
def both {X : Type} (f g : Fn X) : Fn X := fun x => f x && g x
def extend {X : Type} (R : Pool X) (f : Fn X) : Pool X := fun g => R g ∨ g = f ∨ g = inv f
def Stable {X : Type} (R : Pool X) : Prop :=
  (∀ b : Bool, R (fun _ => b)) ∧ ∀ g, R g → R (inv g)

theorem doubleInv {X : Type} (g : Fn X) : inv (inv g) = g := by funext x; simp [inv]

theorem stableExt {X : Type} {R : Pool X} (st : Stable R) (f : Fn X) : Stable (extend R f) := by
  refine ⟨fun b => Or.inl (st.1 b), ?_⟩
  intro g h
  rcases h with h | rfl | rfl
  · exact Or.inl (st.2 g h)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv f))

def Can {X : Type} (f : Fn X) : ℕ → Pool X → Prop
  | 0, R => R f
  | k + 1, R => Can f k R ∨ ∃ a b, R a ∧ R b ∧ Can f k (extend R (both a b))

theorem Can.ready {X : Type} {f : Fn X} {R : Pool X} (h : R f) : Can f 0 R := h
theorem Can.skip {X : Type} {f : Fn X} {R : Pool X} {k : ℕ} (h : Can f k R) : Can f (k + 1) R :=
  Or.inl h
theorem Can.gate {X : Type} {f : Fn X} {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
    (h : Can f k (extend R (both a b))) : Can f (k + 1) R := Or.inr ⟨a, b, ha, hb, h⟩

theorem Can.ind {X : Type} {f : Fn X} {motive : ∀ k R, Can f k R → Prop}
    (ready : ∀ {R : Pool X} (hf : R f), motive 0 R (Can.ready hf))
    (skip : ∀ {k : ℕ} {R : Pool X} (h : Can f k R), motive k R h → motive (k + 1) R (Can.skip h))
    (gate : ∀ {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
      (h : Can f k (extend R (both a b))), motive k (extend R (both a b)) h →
      motive (k + 1) R (Can.gate a b ha hb h))
    {k : ℕ} {R : Pool X} (h : Can f k R) : motive k R h := by
  induction k generalizing R with
  | zero => exact ready h
  | succ k ih =>
    rcases h with old | ⟨a, b, ha, hb, tail⟩
    · exact skip old (ih old)
    · exact gate a b ha hb tail (ih tail)

def liftF {X : Type} (f : Fn X) : Fn (X × Bool) := fun y => f y.1
def slice {X : Type} (b : Bool) (f : Fn (X × Bool)) : Fn X := fun x => f (x, b)
def bitInput {X : Type} : Fn (X × Bool) := fun y => y.2

theorem mapRestrict {X : Type} {f : Fn (X × Bool)} {k : ℕ} {S : Pool (X × Bool)}
    (h : Can f k S) (v : Bool) (R : Pool X) (st : Stable R)
    (hr : ∀ z, S z → R (slice v z)) : Can (slice v f) k R := by
  induction h using Can.ind generalizing R with
  | ready hf => exact .ready (hr _ hf)
  | skip _ ih => exact .skip (ih R st hr)
  | gate a b ha hb _ ih =>
    apply Can.gate (slice v a) (slice v b) (hr a ha) (hr b hb)
    apply ih _ (stableExt st _)
    intro z hz
    rcases hz with hz | rfl | rfl
    · exact Or.inl (hr _ hz)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def lifted {X : Type} (R : Pool X) (z : Fn (X × Bool)) := ∃ g, R g ∧ z = liftF g
def fixedAt {X : Type} (v : Bool) (z : Fn (X × Bool)) := ∃ c : Bool, slice v z = fun _ => c

theorem dropOne {X : Type} {f : Fn (X × Bool)} {S : Pool (X × Bool)} {k : ℕ}
    (h : Can f k S) (v : Bool) (dep : ∀ g, f ≠ liftF g) (nc : ¬ fixedAt v f)
    (R : Pool X) (st : Stable R) (hs : ∀ z, S z → lifted R z ∨ fixedAt v z) :
    ∃ t, t + 1 ≤ k ∧ Can (slice v f) t R := by
  have value {Q : Pool X} (sq : Stable Q) {z : Fn (X × Bool)}
      (hz : lifted Q z ∨ fixedAt v z) : Q (slice v z) := by
    rcases hz with ⟨g, hg, rfl⟩ | ⟨c, hc⟩
    · exact hg
    · rw [hc]; exact sq.1 c
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g, _, e⟩ | hconst
    · exact (dep g e).elim
    · exact (nc hconst).elim
  | skip _ ih =>
    obtain ⟨t, sz, pr⟩ := ih R st hs
    exact ⟨t, by omega, pr⟩
  | @gate k S a b ha hb rest ih =>
    have aa := hs a ha
    have bb := hs b hb
    have save (ok : R (slice v (both a b))) : ∃ t, t + 1 ≤ k + 1 ∧ Can (slice v f) t R := by
      refine ⟨k, le_rfl, mapRestrict rest v R st ?_⟩
      intro z hz
      rcases hz with hz | rfl | rfl
      · exact value st (hs _ hz)
      · exact ok
      · exact st.2 _ ok
    rcases aa with ⟨u, hu, rfl⟩ | ⟨c, hc⟩
    · rcases bb with ⟨w, hw, rfl⟩ | ⟨d, hd⟩
      · let T := extend R (both u w)
        obtain ⟨t, sz, pr⟩ := ih T (stableExt st _) (by
          intro z hz
          rcases hz with hz | rfl | rfl
          · rcases hs _ hz with ⟨g, hg, rfl⟩ | c
            · exact Or.inl ⟨g, Or.inl hg, rfl⟩
            · exact Or.inr c
          · exact Or.inl ⟨both u w, Or.inr (Or.inl rfl), rfl⟩
          · exact Or.inl ⟨inv (both u w), Or.inr (Or.inr rfl), rfl⟩)
        exact ⟨t + 1, by omega, Can.gate u w hu hw pr⟩
      · apply save
        change R (both u (slice v b))
        rw [hd]
        cases d
        · have e : both u (fun _ => false) = (fun _ => false) := by funext x; simp [both]
          rw [e]; exact st.1 false
        · have e : both u (fun _ => true) = u := by funext x; simp [both]
          rw [e]; exact hu
    · apply save
      change R (both (slice v a) (slice v b))
      rw [hc]
      cases c
      · exact st.1 false
      · exact value st bb

theorem dropTwo {X : Type} {f : Fn (X × Bool)} {S : Pool (X × Bool)} {k : ℕ}
    (h : Can f k S) (dep : ∀ g, f ≠ liftF g) (nc : ∀ v, ¬ fixedAt v f)
    (R : Pool X) (st : Stable R)
    (hs : ∀ z, S z → lifted R z ∨ z = bitInput ∨ z = inv bitInput) :
    ∃ v t, t + 2 ≤ k ∧ Can (slice v f) t R := by
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g, _, e⟩ | e | e
    · exact (dep g e).elim
    · exact (nc false ⟨false, by rw [e]; rfl⟩).elim
    · exact (nc false ⟨true, by rw [e]; rfl⟩).elim
  | skip _ ih =>
    obtain ⟨v, t, sz, pr⟩ := ih R st hs
    exact ⟨v, t, by omega, pr⟩
  | @gate k S a b ha hb rest ih =>
    have save (v : Bool) (zero : slice v (both a b) = fun _ => false) :
        ∃ v t, t + 2 ≤ k + 1 ∧ Can (slice v f) t R := by
      have extra : ∀ z, extend S (both a b) z → lifted R z ∨ fixedAt v z := by
        intro z hz
        rcases hz with hz | rfl | rfl
        · rcases hs _ hz with old | rfl | rfl
          · exact Or.inl old
          · exact Or.inr ⟨v, rfl⟩
          · exact Or.inr ⟨!v, rfl⟩
        · exact Or.inr ⟨false, zero⟩
        · refine Or.inr ⟨true, ?_⟩
          change inv (slice v (both a b)) = _
          rw [zero]; rfl
      obtain ⟨t, sz, pr⟩ := dropOne rest v dep (nc v) R st extra
      exact ⟨v, t, by omega, pr⟩
    rcases hs a ha with ⟨u, hu, rfl⟩ | rfl | rfl
    · rcases hs b hb with ⟨w, hw, rfl⟩ | rfl | rfl
      · obtain ⟨v, t, sz, pr⟩ := ih (extend R (both u w)) (stableExt st _) (by
          intro z hz
          rcases hz with hz | rfl | rfl
          · rcases hs _ hz with ⟨g, hg, rfl⟩ | e
            · exact Or.inl ⟨g, Or.inl hg, rfl⟩
            · exact Or.inr e
          · exact Or.inl ⟨both u w, Or.inr (Or.inl rfl), rfl⟩
          · exact Or.inl ⟨inv (both u w), Or.inr (Or.inr rfl), rfl⟩)
        exact ⟨v, t + 1, by omega, Can.gate u w hu hw pr⟩
      · apply save false; funext x; simp [slice, both, bitInput]
      · apply save true; funext x; simp [slice, both, inv, bitInput]
    · exact save false rfl
    · exact save true rfl

open PEqualNP.CircuitLowerBounds

def useBinary (g : Gate) := match g.op with | .not => false | _ => true
def cost (gs : List Gate) := (gs.filter useBinary).length
def readF {X : Type} (w : List (Fn X)) (i : ℕ) : Fn X := w.getD i (fun _ => false)
def outF {X : Type} (w : List (Fn X)) (g : Gate) : Fn X :=
  fun x => g.op.eval (g.inputs.map (fun i => readF w i x))
def traceF {X : Type} (gs : List Gate) (w : List (Fn X)) : List (Fn X) :=
  gs.foldl (fun old g => old ++ [outF old g]) w
def fan (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem readIn {X : Type} {w : List (Fn X)} {R : Pool X} (st : Stable R)
    (hw : ∀ u ∈ w, R u) (i : ℕ) : R (readF w i) := by
  by_cases h : i < w.length
  · rw [readF, List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · rw [readF, List.getD_eq_default _ _ (by omega)]; exact st.1 false

theorem gateClass {X : Type} (w : List (Fn X)) (g : Gate) (hg : fan g) (R : Pool X)
    (st : Stable R) (hw : ∀ u ∈ w, R u) :
    if useBinary g then R (outF w g) ∨
      ∃ a b, R a ∧ R b ∧ (outF w g = both a b ∨ outF w g = inv (both a b))
    else R (outF w g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, len⟩ := hg
  change (op = .and ∨ op = .or ∨ op = .not) at hop
  change ins.length ≤ 2 at len
  rcases hop with rfl | rfl | rfl
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 true)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF, GateOp.eval]
      | cons j t =>
        have hnil : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        exact Or.inr ⟨readF w i, readF w j, readIn st hw i, readIn st hw j, Or.inl (by funext x; simp [outF, GateOp.eval, both])⟩
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 false)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF, GateOp.eval]
      | cons j t =>
        have hnil : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        refine Or.inr ⟨inv (readF w i), inv (readF w j), st.2 _ (readIn st hw i),
          st.2 _ (readIn st hw j), Or.inr ?_⟩
        funext x
        simp [outF, GateOp.eval, inv, both]
  · cases ins with
    | nil => exact st.1 true
    | cons i t => exact st.2 _ (readIn st hw i)

theorem comp {X : Type} (gs : List Gate) (o : ℕ) (legal : ∀ g ∈ gs, fan g)
    (w : List (Fn X)) (R : Pool X) (st : Stable R) (hw : ∀ u ∈ w, R u) :
    Can (readF (traceF gs w) o) (cost gs) R := by
  induction gs generalizing w R with
  | nil => exact Can.ready (readIn st hw o)
  | cons g gs ih =>
    have cont := ih (fun u hu => legal u (List.mem_cons_of_mem _ hu))
    have cl := gateClass w g (legal g List.mem_cons_self) R st hw
    change Can (readF (traceF gs (w ++ [outF w g])) o) _ R
    have same (h : R (outF w g)) : Can (readF (traceF gs (w ++ [outF w g])) o) (cost gs) R := by
      apply cont _ R st
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · obtain rfl := List.mem_singleton.mp hz
        exact h
    cases hb : useBinary g with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at cl
      simpa [cost, hb] using same cl
    | true =>
      simp only [hb, ite_true] at cl
      have len : cost (g :: gs) = cost gs + 1 := by simp [cost, hb]
      rw [len]
      rcases cl with h | ⟨a, b, ha, hb', eq⟩
      · exact Can.skip (same h)
      · apply Can.gate a b ha hb'
        apply cont _ _ (stableExt st _)
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact Or.inl (hw z hz)
        · obtain rfl := List.mem_singleton.mp hz
          exact Or.inr eq

theorem readAt {X : Type} (w : List (Fn X)) (i : ℕ) (x : X) :
    (w.map (fun z => z x)).getD i false = readF w i x := by
  by_cases h : i < w.length
  · simp [readF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [readF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega : w.length ≤ i)]

theorem traceAt {X : Type} (gs : List Gate) (w : List (Fn X)) (x : X) :
    (traceF gs w).map (fun z => z x) =
      gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map (fun i => old.getD i false))])
        (w.map (fun z => z x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (traceF gs (w ++ [outF w g])).map _ = _
    rw [ih, List.foldl_cons]
    simp only [List.map_append, List.map_cons, List.map_nil, outF, readAt]

abbrev BaseX := Fin 6 → Bool

def coreFn (x : BaseX) : Bool :=
  (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) ||
  (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5)

def prim (z : Fn BaseX) : Prop :=
  (∃ b : Bool, z = fun _ => b) ∨ ∃ i : Fin 6, z = (fun x => x i) ∨ z = inv (fun x => x i)

theorem stablePrim : Stable prim := by
  refine ⟨fun b => Or.inl ⟨b, rfl⟩, ?_⟩
  intro z h
  rcases h with ⟨v, rfl⟩ | ⟨i, rfl | rfl⟩
  · exact Or.inl ⟨!v, rfl⟩
  · exact Or.inr ⟨i, Or.inr rfl⟩
  · exact Or.inr ⟨i, Or.inl (doubleInv _)⟩

def extendInput {X : Type} (R : Pool X) : Pool (X × Bool) :=
  fun z => lifted R z ∨ z = bitInput ∨ z = inv bitInput

theorem stableInput {X : Type} {R : Pool X} (st : Stable R) : Stable (extendInput R) := by
  refine ⟨fun b => Or.inl ⟨fun _ => b, st.1 b, rfl⟩, ?_⟩
  intro z h
  rcases h with ⟨g, hg, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨inv g, st.2 _ hg, rfl⟩
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv _))

abbrev World := (BaseX × Bool) × Bool

def input (y : World) : Fin 8 → Bool :=
  ![y.1.1 0, y.1.1 1, y.1.1 2, y.2, y.1.1 3, y.1.1 4, y.1.2, y.1.1 5]

def wires : List (Fn World) := List.ofFn (fun i : Fin 8 => fun y => input y i)

def full (y : World) : Bool :=
  coreFn y.1.1 || (y.1.2 && (y.2 || y.1.1 1 || y.1.1 2 || y.1.1 5))

theorem knownWires : ∀ z ∈ wires, extendInput (extendInput prim) z := by
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  have p (j : Fin 6) : extendInput (extendInput prim) (liftF (liftF (fun x : BaseX => x j))) :=
    Or.inl ⟨_, Or.inl ⟨_, Or.inr ⟨j, Or.inl rfl⟩, rfl⟩, rfl⟩
  fin_cases i
  · exact p 0
  · exact p 1
  · exact p 2
  · exact Or.inr (Or.inl rfl)
  · exact p 3
  · exact p 4
  · exact Or.inl ⟨bitInput, Or.inr (Or.inl rfl), rfl⟩
  · exact p 5

theorem genuine {X : Type} {f : Fn (X × Bool)} (x : X) (h : f (x, false) ≠ f (x, true)) :
    ∀ g, f ≠ liftF g := by
  intro g he
  exact h (he ▸ rfl)

theorem varying {X : Type} {f : Fn (X × Bool)} (v : Bool) (x y : X)
    (h : f (x, v) ≠ f (y, v)) : ¬ fixedAt v f := by
  rintro ⟨c, eq⟩
  exact h ((congrFun eq x).trans (congrFun eq y).symm)

theorem eliminationBound (bound : ∀ k, Can coreFn k prim → 9 ≤ k)
    {s : ℕ} (h : Can full s (extendInput (extendInput prim))) : 12 ≤ s := by
  let low : BaseX := fun _ => false
  let high : BaseX := fun _ => true
  have dep := genuine (f := full) (low, true) (by decide)
  have nc (v : Bool) : ¬ fixedAt v full := by
    apply varying v (low, false) (high, false)
    cases v <;> decide
  obtain ⟨v, t, sv, ht⟩ := dropTwo h dep nc _ (stableInput stablePrim) (fun _ h => h)
  have dep' := genuine (f := slice v full) (![false, true, false, false, false, false] : BaseX) (by cases v <;> decide)
  have nc' : ¬ fixedAt false (slice v full) := by
    apply varying false low high
    cases v <;> decide
  obtain ⟨u, tu, hu⟩ := dropOne ht false dep' nc' prim stablePrim (by
    intro z hz
    rcases hz with h | rfl | rfl
    · exact Or.inl h
    · exact Or.inr ⟨false, rfl⟩
    · exact Or.inr ⟨true, rfl⟩)
  have eq : slice false (slice v full) = coreFn := by funext x; simp [slice, full]
  rw [eq] at hu
  have := bound u hu
  omega

def graph (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def upper : List Gate := [
  ⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [3, 7]⟩,
  ⟨.and, [6, 11]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [4, 14]⟩,
  ⟨.or, [0, 2]⟩, ⟨.and, [5, 16]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 17]⟩,
  ⟨.or, [18, 19]⟩]

set_option maxRecDepth 20000 in
theorem upper_eq : ∀ x : Fin 8 → Bool, Circuit.eval ⟨upper, 20⟩ (List.ofFn x) = graph x := by decide +kernel

set_option maxRecDepth 20000 in
theorem emb_eq : ∀ (x : BaseX) (b v : Bool), graph (input ((x, b), v)) = full ((x, b), v) := by decide +kernel

theorem circuitLower (bound : ∀ k, Can coreFn k prim → 9 ≤ k) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, fan g) (ev : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = graph x) :
    12 ≤ cost gs := by
  have program := comp gs o legal wires _ (stableInput (stableInput stablePrim)) knownWires
  have eq : readF (traceF gs wires) o = full := by
    funext y
    rw [← readAt, traceAt]
    have inp : wires.map (fun z => z y) = List.ofFn (input y) := by simp [wires]
    rw [inp]
    exact (ev (input y)).trans (emb_eq y.1.1 y.1.2 y.2)
  rw [eq] at program
  exact eliminationBound bound program

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {g : α} {ws : List α}
    (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem nat_beq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simp only [true_iff]
    intro he; subst he
    exact Bool.noConfusion ((Nat.beq_refl a).symm.trans h)
  · simp only [Bool.true_eq_false, false_iff, not_not]
    exact Nat.eq_of_beq_eq_true h

theorem nat_blt_false {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · have : a + 1 ≤ b := Nat.ble_eq.mp hb
    omega

def M64 : ℕ := 0xffffffffffffffff

theorem M64_eq : M64 = 2 ^ 64 - 1 := by decide

theorem M64_testBit (i : ℕ) : M64.testBit i = decide (i < 64) := by
  rw [M64_eq, Nat.testBit_two_pow_sub_one]

def inv64 (w : ℕ) : ℕ := w ^^^ M64

theorem inv64_testBit (w i : ℕ) : (inv64 w).testBit i = xor (w.testBit i) (decide (i < 64)) := by
  simp [inv64, Nat.testBit_xor, M64_testBit]

theorem inv64_inv64 (w : ℕ) : inv64 (inv64 w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [inv64_testBit]

def masked (w : ℕ) : Prop := ∀ i, 64 ≤ i → w.testBit i = false

theorem masked_zero : masked 0 := by intro i _; simp
theorem masked_M64 : masked M64 := by intro i hi; rw [M64_testBit]; simp; omega
theorem masked_inv64 {w : ℕ} (h : masked w) : masked (inv64 w) := by
  intro i hi; rw [inv64_testBit, h i hi]; simp; omega
theorem masked_and {a b : ℕ} (ha : masked a) : masked (a &&& b) := by
  intro i hi; simp [Nat.testBit_and, ha i hi]
theorem masked_or {a b : ℕ} (ha : masked a) (hb : masked b) : masked (a ||| b) := by
  intro i hi; simp [Nat.testBit_or, ha i hi, hb i hi]

theorem and_M64 {w : ℕ} (h : masked w) : w &&& M64 = w := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, M64_testBit]
  by_cases hi : i < 64
  · simp [hi]
  · simp [hi, h i (by omega)]

theorem M64_and {w : ℕ} (h : masked w) : M64 &&& w = w := by
  rw [Nat.and_comm]; exact and_M64 h

theorem and_inv64_self {w : ℕ} (h : masked w) : w &&& inv64 w = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, inv64_testBit, Nat.zero_testBit]
  by_cases hi : i < 64
  · cases w.testBit i <;> simp [hi]
  · simp [h i (by omega)]

theorem inv64_and_self {w : ℕ} (h : masked w) : inv64 w &&& w = 0 := by
  rw [Nat.and_comm]; exact and_inv64_self h

theorem inv64_or {a b : ℕ} (ha : masked a) (hb : masked b) :
    inv64 (a ||| b) = inv64 a &&& inv64 b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [inv64_testBit, Nat.testBit_or, Nat.testBit_and, inv64_testBit, inv64_testBit]
  by_cases hi : i < 64
  · cases a.testBit i <;> cases b.testBit i <;> simp [hi]
  · simp [ha i (by omega), hb i (by omega), hi]

def ops4 (a b : ℕ) : List ℕ :=
  [a &&& b, a ||| b, a &&& inv64 b, b &&& inv64 a]

def basicOps (a b : ℕ) : Finset ℕ :=
  ((ops4 a b).filter (fun z => !Nat.beq z 0 && !Nat.beq z M64)).toFinset

theorem mem_basicOps {a b z : ℕ} :
    z ∈ basicOps a b ↔ z ∈ ops4 a b ∧ z ≠ 0 ∧ z ≠ M64 := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    nat_beq_false]

theorem basicOps_swap (a b : ℕ) : basicOps a b = basicOps b a := by
  ext z
  simp only [mem_basicOps, ops4, List.mem_cons, List.not_mem_nil, or_false]
  rw [Nat.and_comm a b, Nat.or_comm a b]
  tauto

theorem basicOps_masked {a b z : ℕ} (ha : masked a) (hb : masked b) (hz : z ∈ basicOps a b) :
    masked z := by
  have hm := (mem_basicOps.mp hz).1
  simp only [ops4, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact masked_and ha
  · exact masked_or ha hb
  · exact masked_and ha
  · exact masked_and hb

theorem basicOps_bit0 {a b z : ℕ} (ha : a.testBit 0 = false) (hb : b.testBit 0 = false)
    (hz : z ∈ basicOps a b) : z.testBit 0 = false := by
  have hm := (mem_basicOps.mp hz).1
  simp only [ops4, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rw [Nat.testBit_and, ha]; rfl
  · rw [Nat.testBit_or, ha, hb]; rfl
  · rw [Nat.testBit_and, ha]; rfl
  · rw [Nat.testBit_and, hb]; rfl

def holds (av : Finset ℕ) (z : ℕ) : Prop :=
  masked z ∧ (z = 0 ∨ z = M64 ∨ ∃ a ∈ av, z = a ∨ z = inv64 a)

theorem holds_insert {av : Finset ℕ} {z a : ℕ} (h : holds av z) : holds (insert a av) z := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset ℕ} {z : ℕ} (h : holds av z) : holds av (inv64 z) := by
  refine ⟨masked_inv64 h.1, ?_⟩
  rcases h.2 with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl (by decide))
  · exact .inl (by decide)
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl (inv64_inv64 a)⟩)

def reachable (av : Finset ℕ) (z : ℕ) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem and_reach {av : Finset ℕ} {x y : ℕ} (hav : ∀ a ∈ av, masked a)
    (hx : holds av x) (hy : holds av y) : reachable av (x &&& y) := by
  have h0 : holds av 0 := ⟨masked_zero, .inl rfl⟩
  have hM : holds av M64 := ⟨masked_M64, .inr (.inl rfl)⟩
  rcases hx.2 with rfl | rfl | ⟨a, ha, ea⟩
  · rw [Nat.zero_and]; exact .inl h0
  · rw [M64_and hy.1]; exact .inl hy
  rcases hy.2 with rfl | rfl | ⟨b, hb, eb⟩
  · rw [Nat.and_zero]; exact .inl h0
  · rw [and_M64 hx.1]; exact .inl hx
  have ma := hav a ha
  have mb := hav b hb
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
    · rw [Nat.and_self]; exact .inl ⟨ma, .inr (.inr ⟨a, ha, .inl rfl⟩)⟩
    · rw [and_inv64_self ma]; exact .inl h0
    · rw [inv64_and_self ma]; exact .inl h0
    · rw [Nat.and_self]; exact .inl ⟨masked_inv64 ma, .inr (.inr ⟨a, ha, .inr rfl⟩)⟩
  have add (w : ℕ) (hw : w ∈ ops4 a b) (mw : masked w) (z : ℕ) (hz : z = w ∨ z = inv64 w) :
      reachable av z := by
    by_cases h0' : w = 0
    · rcases hz with rfl | rfl
      · exact .inl (h0' ▸ h0)
      · rw [h0']; exact .inl (show holds av (inv64 0) from holds_not h0)
    by_cases hM' : w = M64
    · rcases hz with rfl | rfl
      · exact .inl (hM' ▸ hM)
      · rw [hM']; exact .inl (show holds av (inv64 M64) from holds_not hM)
    have hmem : w ∈ basicOps a b := mem_basicOps.mpr ⟨hw, h0', hM'⟩
    have mz : masked z := by rcases hz with rfl | rfl; exact mw; exact masked_inv64 mw
    exact .inr ⟨a, ha, b, hb, h, w, hmem, ⟨mz, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add (a &&& b) (by simp [ops4]) (masked_and ma) _ (.inl rfl)
  · exact add (a &&& inv64 b) (by simp [ops4]) (masked_and ma) _ (.inl rfl)
  · exact add (b &&& inv64 a) (by simp [ops4]) (masked_and mb) _ (.inl (Nat.and_comm ..))
  · exact add (a ||| b) (by simp [ops4]) (masked_or ma mb) _ (.inr (inv64_or ma mb).symm)

def bits6 (i : Fin 64) : BaseX := fun j => i.val.testBit j.val

def repr6 (f : Fn BaseX) (w : ℕ) : Prop :=
  masked w ∧ ∀ i : Fin 64, w.testBit i.val = f (bits6 i)

theorem repr6_and {a b : Fn BaseX} {wa wb : ℕ} (ha : repr6 a wa) (hb : repr6 b wb) :
    repr6 (both a b) (wa &&& wb) := by
  refine ⟨masked_and ha.1, fun i => ?_⟩
  simp [Nat.testBit_and, ha.2 i, hb.2 i, both]

theorem repr6_inv {f : Fn BaseX} {w : ℕ} (h : repr6 f w) : repr6 (inv f) (inv64 w) := by
  refine ⟨masked_inv64 h.1, fun i => ?_⟩
  simp [inv64_testBit, i.isLt, h.2 i, inv]

theorem repr6_eq {f : Fn BaseX} {w1 w2 : ℕ} (h1 : repr6 f w1) (h2 : repr6 f w2) : w1 = w2 := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 64
  · exact (h1.2 ⟨i, hi⟩).trans (h2.2 ⟨i, hi⟩).symm
  · exact (h1.1 i (by omega)).trans (h2.1 i (by omega)).symm

def represents (R : Pool BaseX) (av : Finset ℕ) : Prop :=
  ∀ f, R f → ∃ w, holds av w ∧ repr6 f w

theorem reprExtend {R : Pool BaseX} {av : Finset ℕ} {f : Fn BaseX} {w : ℕ}
    (hr : represents R av) (ha : holds av w) (hw : repr6 f w) : represents (extend R f) av := by
  intro z hz
  rcases hz with h | rfl | rfl
  · exact hr _ h
  · exact ⟨_, ha, hw⟩
  · exact ⟨_, holds_not ha, repr6_inv hw⟩

theorem reprInsert {R : Pool BaseX} {av : Finset ℕ} (z : ℕ) (hr : represents R av) :
    represents R (insert z av) := by
  intro f hf
  obtain ⟨w, hold, rep⟩ := hr f hf
  exact ⟨w, holds_insert hold, rep⟩

theorem signCompile {y : ℕ} (hy : repr6 coreFn y) (hy0 : y.testBit 0 = false)
    (hyne0 : y ≠ 0) (hyneM : y ≠ M64) {R : Pool BaseX} {k : ℕ} (h : Can coreFn k R)
    (av : Finset ℕ) (hav : ∀ a ∈ av, masked a ∧ a.testBit 0 = false) (hr : represents R av) :
    build basicOps y k av := by
  induction h using Can.ind generalizing av with
  | ready hf =>
    obtain ⟨w, hold, rep⟩ := hr _ hf
    have eq : w = y := repr6_eq rep hy
    rw [eq] at hold
    rcases hold.2 with h0 | hM | ⟨t, ht, rfl | he⟩
    · exact (hyne0 h0).elim
    · exact (hyneM hM).elim
    · exact ht
    · exfalso
      have ht0 := (hav t ht).2
      have h0 := congrArg (fun z => z.testBit 0) he
      rw [hy0, inv64_testBit, ht0] at h0
      exact Bool.noConfusion h0
  | skip _ ih =>
    exact Or.inl (ih av hav hr)
  | gate a b ha hb _ ih =>
    obtain ⟨wa, ha', ra⟩ := hr a ha
    obtain ⟨wb, hb', rb⟩ := hr b hb
    have rep := repr6_and ra rb
    rcases and_reach (fun u hu => (hav u hu).1) ha' hb' with old | ⟨x, hx, u, hu, ne, z, hop, hz⟩
    · exact Or.inl (ih av hav (reprExtend hr old rep))
    · have hav' : ∀ v ∈ insert z av, masked v ∧ v.testBit 0 = false := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨basicOps_masked (hav x hx).1 (hav u hu).1 hop,
            basicOps_bit0 (hav x hx).2 (hav u hu).2 hop⟩
        · exact hav v hv
      exact Or.inr ⟨x, hx, u, hu, ne, z, hop, ih (insert z av) hav' (reprExtend (reprInsert z hr) hz rep)⟩

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

def ofSortedFuel : ℕ → List (List ℕ) → BT
  | 0, _ => .lf
  | _, [] => .lf
  | f + 1, xs =>
    let m := xs.length / 2
    match xs.drop m with
    | [] => .lf
    | k :: r => .nd (ofSortedFuel f (xs.take m)) k (ofSortedFuel f r)

def ofSorted (xs : List (List ℕ)) : BT := ofSortedFuel 12 xs

theorem toList_ofSortedFuel : ∀ (f : ℕ) (xs : List (List ℕ)), xs.length < 2 ^ f →
    (ofSortedFuel f xs).toList = xs
  | 0, xs, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | f + 1, [], _ => rfl
  | f + 1, a :: t, h => by
    unfold ofSortedFuel
    dsimp only
    set xs := a :: t
    set m := xs.length / 2
    have hm : m < xs.length := by simp [m, xs]; omega
    have hne : xs.drop m ≠ [] := by
      intro he
      have := congrArg List.length he
      simp at this; omega
    cases hd : xs.drop m with
    | nil => exact (hne hd).elim
    | cons k r =>
      simp only [BT.toList]
      have hlen_l : (xs.take m).length < 2 ^ f := by
        simp [m]; omega
      have hlen_r : r.length < 2 ^ f := by
        have hdl := congrArg List.length hd
        simp [m] at hdl; omega
      rw [toList_ofSortedFuel f (xs.take m) hlen_l, toList_ofSortedFuel f r hlen_r, ← hd]
      exact List.take_append_drop m xs

def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def via (y : ℕ) (pD : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws

def prsOK (y : ℕ) (pD : List (ℕ × ℕ)) : Bool :=
  pD.all fun dr =>
    Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor M64 (Nat.shiftRight M64 dr.1))) 0

theorem ops_differs (i j : ℕ) (hm : M64.testBit i = M64.testBit j) (a b z : ℕ)
    (hz : z ∈ basicOps a b) (hd : z.testBit i ≠ z.testBit j) :
    a.testBit i ≠ a.testBit j ∨ b.testBit i ≠ b.testBit j := by
  have h1 := (mem_basicOps.mp hz).1
  simp only [ops4, List.mem_cons, List.not_mem_nil, or_false] at h1
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  rcases h1 with rfl | rfl | rfl | rfl
  · simp [Nat.testBit_and, ha, hb]
  · simp [Nat.testBit_or, ha, hb]
  · simp [Nat.testBit_and, inv64, Nat.testBit_xor, ha, hb, hm]
  · simp [Nat.testBit_and, inv64, Nat.testBit_xor, ha, hb, hm]

theorem via_sound {y : ℕ} {pD : List (ℕ × ℕ)} (hp : prsOK y pD = true) {t : ℕ}
    {ws : List ℕ} (hnd : ws.Nodup) (hl : live basicOps y t ws.toFinset) :
    via y pD t ws = true := by
  have hlen : ws.length ≤ t + 1 := by
    have hc := live_card hl
    rwa [List.toFinset_card_of_nodup hnd] at hc
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨by rw [Nat.ble_eq]; exact hlen, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right
      have heq := singleton_list hnd hl
      rw [heq]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := List.all_eq_true.1 hp dr hdr
    simp only [Bool.and_eq_true] at h12
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (M64 ^^^ (M64 >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : M64.testBit i = M64.testBit (dr.1 + i) := by
      cases h1 : M64.testBit i <;> cases h2 : M64.testBit (dr.1 + i) <;> simp_all
    have hdy : y.testBit i ≠ y.testBit (dr.1 + i) := by
      intro he; rw [he] at hy; simp at hy
    obtain ⟨w, hw, hdw⟩ := live_separates (fun w => w.testBit i ≠ w.testBit (dr.1 + i))
      hdy (ops_differs i (dr.1 + i) hmm) hl
    exact accD_of dr.1 i ws w (List.mem_toFinset.mp hw) hdw

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_zero (pi : List ℕ) : actL pi 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [actL_testBit, Nat.zero_testBit]
  cases pi[k]? <;> simp

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem actL_masked (pi : List ℕ) (hlen : pi.length = 64) (w : ℕ) : masked (actL pi w) := by
  intro k hk
  rw [actL_testBit, List.getElem?_eq_none (by omega)]
  rfl

theorem actL_involution (pi : List ℕ) (hlen : pi.length = 64)
    (hinv : ∀ k : Fin 64, (pi[k.val]?.bind fun j => pi[j]?) = some k.val)
    {w : ℕ} (hw : masked w) : actL pi (actL pi w) = w := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 64
  · have hb := hinv ⟨k, hk⟩
    rw [actL_testBit]
    cases h1 : pi[k]? with
    | none => simp [h1] at hb
    | some j =>
      simp only [h1, Option.bind_some] at hb
      simp [actL_testBit, hb]
  · rw [actL_masked pi hlen _ k (by omega), hw k (by omega)]

theorem actL_inj (pi : List ℕ) (hlen : pi.length = 64)
    (hinv : ∀ k : Fin 64, (pi[k.val]?.bind fun j => pi[j]?) = some k.val)
    {a b : ℕ} (ha : masked a) (hb : masked b) (he : actL pi a = actL pi b) : a = b := by
  have h1 := congrArg (actL pi) he
  rwa [actL_involution pi hlen hinv ha, actL_involution pi hlen hinv hb] at h1

theorem live_act {y : ℕ} (pi : List ℕ) (hlen : pi.length = 64)
    (hinv : ∀ k : Fin 64, (pi[k.val]?.bind fun j => pi[j]?) = some k.val)
    (hM : actL pi M64 = M64) (hY : actL pi y = y)
    {t : ℕ} {s : Finset ℕ} (hs : ∀ w ∈ s, masked w) (hl : live basicOps y t s) :
    live basicOps y t (s.image (actL pi)) := by
  induction t generalizing s with
  | zero =>
    change s = {y} at hl
    subst hl; simp [live, hY]
  | succ t ih =>
    rcases hl with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih hs skip)
    · have ma : masked a := hs a (by simp)
      have mb : masked b := hs b (by simp)
      have mz : masked z := basicOps_masked ma mb hz
      have hrest : ∀ w ∈ rest, masked w := fun w hw => hs w (by simp [hw])
      have hne : actL pi a ≠ actL pi b := fun e => hab (actL_inj pi hlen hinv ma mb e)
      have hz' : actL pi z ∈ basicOps (actL pi a) (actL pi b) := by
        obtain ⟨hm, hz0, hzM⟩ := mem_basicOps.mp hz
        refine mem_basicOps.mpr ⟨?_, fun e => hz0 (actL_inj pi hlen hinv mz masked_zero (e.trans (actL_zero pi).symm)),
          fun e => hzM (actL_inj pi hlen hinv mz masked_M64 (e.trans hM.symm))⟩
        simp only [ops4, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        rcases hm with rfl | rfl | rfl | rfl
        · exact Or.inl (actL_and pi a b)
        · exact Or.inr (Or.inl (actL_or pi a b))
        · exact Or.inr (Or.inr (Or.inl (by rw [inv64, inv64, actL_and, actL_xor, hM])))
        · exact Or.inr (Or.inr (Or.inr (by rw [inv64, inv64, actL_and, actL_xor, hM])))
      have hout' : actL pi z ∉ (insert a (insert b rest)).image (actL pi) := by
        intro hm
        obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
        exact hout ((actL_inj pi hlen hinv (hs w hw) mz he) ▸ hw)
      have htail_m : ∀ w ∈ insert z rest, masked w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact mz
        · exact hrest w hw
      have htail := ih htail_m tail
      simp only [Finset.image_insert] at hout' htail ⊢
      exact Or.inr ⟨actL pi a, by simp, actL pi b, by simp, hne, actL pi z, hz', hout',
        rest.image (actL pi), rfl, htail⟩

def checkPair (y : ℕ) (pD : List (ℕ × ℕ)) (pi : List ℕ) (T : BT)
    (t extra : ℕ) (ws : List ℕ) (a b : ℕ) (r : List ℕ) : Bool :=
  (ops4 a b).all fun z =>
    if Nat.beq z 0 || Nat.beq z M64 || ws.contains z then true
    else
      let chk (ys : List ℕ) : Bool :=
        !via y pD t ys || T.mem (t :: isort ys) || T.mem (t :: isort (ys.map (actL pi)))
      chk (z :: r) &&
      (Nat.beq extra 0 || (chk (z :: a :: r) && chk (z :: b :: r))) &&
      (Nat.blt extra 2 || chk (z :: a :: b :: r))

def stepOK (y : ℕ) (pD : List (ℕ × ℕ)) (pi : List ℕ) (T : BT) : List ℕ → Bool
  | [] => false
  | 0 :: _ => false
  | (t + 1) :: es =>
    !leqL es [y] &&
    (pairs es).all (fun (a, b, r) => checkPair y pD pi T t (t + 2 - es.length) es a b r)

theorem closure_sound {y : ℕ} {pD : List (ℕ × ℕ)} {pi : List ℕ} (T : BT)
    (hp : prsOK y pD = true) (hlen : pi.length = 64)
    (hinv : ∀ k : Fin 64, (pi[k.val]?.bind fun j => pi[j]?) = some k.val)
    (hM : actL pi M64 = M64) (hY : actL pi y = y)
    (hT : ∀ x, T.mem x = true → stepOK y pD pi T x = true) :
    ∀ t (ws : List ℕ), ws.Nodup → (∀ w ∈ ws, masked w) →
      live basicOps y t ws.toFinset → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _ _ _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · have hs := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hnd hm hl
    cases hmem : T.mem ((t + 1) :: isort ws)
    · rfl
    · exfalso
      have hs := hT _ hmem
      set es := isort ws
      have hperm : es.Perm ws := List.perm_insertionSort _ _
      have hend : es.Nodup := hperm.nodup_iff.mpr hnd
      have heset : es.toFinset = ws.toFinset := by ext u; simp [hperm.mem_iff]
      have hem : ∀ w ∈ es, masked w := fun w hw => hm w (hperm.mem_iff.mp hw)
      have hle : live basicOps y (t + 1) es.toFinset := heset.symm ▸ hl
      simp only [stepOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hs
      rcases first_live hle with done | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hset, tail⟩
      · have heq := singleton_list hend done
        rw [heq, leqL_self] at hs
        exact Bool.noConfusion hs.1
      · obtain ⟨r, hpr, hp2⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go (a b : ℕ) (perm : es.Perm (a :: b :: r))
            (hset' : es.toFinset = insert a (insert b rest))
            (hz' : z ∈ basicOps a b) (hm_p : (a, b, r) ∈ pairs es) : False := by
          obtain ⟨kept, hkc, hkn, hkfin⟩ := recover_kept perm hend hset'
          have hznot : z ∉ kept := by
            intro hu
            apply hout
            rw [hset']
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hkfin ▸ List.mem_toFinset.mpr hu))
          have hys_nd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznot, hkn⟩
          have hys_live : live basicOps y t (z :: kept).toFinset := by simpa [hkfin] using tail
          have hys_m : ∀ w ∈ z :: kept, masked w := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · have hae : a ∈ es := perm.mem_iff.mpr (by simp)
              have hbe : b ∈ es := perm.mem_iff.mpr (by simp)
              exact basicOps_masked (hem a hae) (hem b hbe) hz'
            · apply hem w
              rw [← List.mem_toFinset, hset']
              exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hkfin ▸ List.mem_toFinset.mpr hw))
          have hys_len : (z :: kept).length ≤ t + 1 := by
            have hc := live_card hys_live
            rwa [List.toFinset_card_of_nodup hys_nd] at hc
          have hvia := via_sound hp hys_nd hys_live
          have hih1 := ih (z :: kept) hys_nd hys_m hys_live
          have hmap_nd : ((z :: kept).map (actL pi)).Nodup := by
            refine List.Nodup.map_on ?_ hys_nd
            intro u hu v hv he
            exact actL_inj pi hlen hinv (hys_m u hu) (hys_m v hv) he
          have hmap_m : ∀ w ∈ (z :: kept).map (actL pi), masked w := by
            intro w hw
            obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
            exact actL_masked pi hlen u
          have hmap_fin : ((z :: kept).map (actL pi)).toFinset = (z :: kept).toFinset.image (actL pi) := by
            ext u; simp
          have hmap_live : live basicOps y t ((z :: kept).map (actL pi)).toFinset := by
            rw [hmap_fin]
            exact live_act pi hlen hinv hM hY (fun w hw => hys_m w (List.mem_toFinset.mp hw)) hys_live
          have hih2 := ih _ hmap_nd hmap_m hmap_live
          have hcp := hs.2 (a, b, r) hm_p
          unfold checkPair at hcp
          obtain ⟨hz_ops, hz0, hzM⟩ := mem_basicOps.mp hz'
          have hcz := List.all_eq_true.1 hcp z hz_ops
          have hc0 : Nat.beq z 0 = false := nat_beq_false.mpr hz0
          have hcM : Nat.beq z M64 = false := nat_beq_false.mpr hzM
          have hce : es.contains z = false := by
            simp only [List.contains_eq_mem, decide_eq_false_iff_not]
            exact fun hm => hout (List.mem_toFinset.mpr hm)
          have hcond : (Nat.beq z 0 || Nat.beq z M64 || es.contains z) = false := by
            rw [hc0, hcM, hce]; rfl
          rw [hcond] at hcz
          simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true] at hcz
          have hchk_elim :
              (((!via y pD t (z :: kept)) = true ∨ T.mem (t :: isort (z :: kept)) = true) ∨
                T.mem (t :: isort ((z :: kept).map (actL pi))) = true) → False := by
            intro h
            rcases h with (h | h) | h
            · rw [hvia] at h; exact Bool.noConfusion h
            · rw [hih1] at h; exact Bool.noConfusion h
            · rw [hih2] at h; exact Bool.noConfusion h
          have hlen_es : es.length = r.length + 2 := by
            have := perm.length_eq; simp at this; omega
          simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkc
          rcases hkc with rfl | rfl | rfl | rfl
          · exact hchk_elim hcz.1.1
          · simp only [List.length_cons] at hys_len
            have hex : Nat.beq (t + 2 - es.length) 0 = false := nat_beq_false.mpr (by omega)
            rcases hcz.1.2 with h0 | ⟨h1, _⟩
            · rw [hex] at h0; exact Bool.noConfusion h0
            · exact hchk_elim h1
          · simp only [List.length_cons] at hys_len
            have hex : Nat.beq (t + 2 - es.length) 0 = false := nat_beq_false.mpr (by omega)
            rcases hcz.1.2 with h0 | ⟨_, h2⟩
            · rw [hex] at h0; exact Bool.noConfusion h0
            · exact hchk_elim h2
          · simp only [List.length_cons] at hys_len
            have hex : Nat.blt (t + 2 - es.length) 2 = false := nat_blt_false (by omega)
            rcases hcz.2 with h0 | h3
            · rw [hex] at h0; exact Bool.noConfusion h0
            · exact hchk_elim h3
        rcases hpr with hdirect | hswap
        · exact go a b hp2 hset hz hdirect
        · exact go b a (hp2.trans (.swap _ _ _)) (by rw [hset, Finset.insert_comm])
            (basicOps_swap a b ▸ hz) hswap

def rootOK (y : ℕ) (pD : List (ℕ × ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD cap zs || T.mem (cap :: isort zs)

theorem certBound {y : ℕ} {xs : List ℕ} {pD : List (ℕ × ℕ)} {pi : List ℕ} {T : BT} {cap : ℕ}
    (hnd : xs.Nodup) (hxm : ∀ w ∈ xs, masked w)
    (hp : prsOK y pD = true) (hlen : pi.length = 64)
    (hinv : ∀ k : Fin 64, (pi[k.val]?.bind fun j => pi[j]?) = some k.val)
    (hM : actL pi M64 = M64) (hY : actL pi y = y)
    (hT : ∀ x, T.mem x = true → stepOK y pD pi T x = true)
    (hroot : xs.sublists.all (rootOK y pD T cap) = true)
    {k : ℕ} (hk : k ≤ cap) (hb : build basicOps y k xs.toFinset) : False := by
  have lift : ∀ {a b : ℕ}, a ≤ b → build basicOps y a xs.toFinset → build basicOps y b xs.toFinset := by
    intro a b le hr
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  obtain ⟨s, hs, hl⟩ := compress (lift hk hb)
  let ws := xs.filter (· ∈ s)
  have hsub : ws.Sublist xs := List.filter_sublist
  have hws_nd : ws.Nodup := hnd.filter _
  have hws_m : ∀ w ∈ ws, masked w := fun w hw => hxm w (hsub.subset hw)
  have hws_eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hws_live : live basicOps y cap ws.toFinset := hws_eq.symm ▸ hl
  have hv := via_sound hp hws_nd hws_live
  have hc := closure_sound T hp hlen hinv hM hY hT cap ws hws_nd hws_m hws_live
  have hr := List.all_eq_true.1 hroot ws (List.mem_sublists.mpr hsub)
  unfold rootOK at hr
  rw [hv, hc] at hr
  simp at hr

def Y_ : Nat := 0xfffefffcfefaee00

def XS_ : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def PD_ : List (Nat × Nat) := [(7,0x1020307071bdc),(10,0x1004301c550bb),(9,0x1008300859377),(5,0x10803190d3970),(3,0x120036125b3c0),(18,0x34105d1be),(14,0x10007010915eb),(20,0x3110521ef),(12,0x10013013501ae),(34,0x10551ff),(2,0x14003c1445580),(28,0x3011511cf),(4,0x11003311540e0),(6,0x104030d0105b8),(8,0x10103020414ee),(17,0x38104917d),(15,0x10001010313f5),(24,0x3000512fe),(1,0x1800281879900),(31,0x1010711f9),(16,0x2010610fa),(32,0x10411fc)]

def PI_ : List Nat := [0,4,2,6,1,5,3,7,32,36,34,38,33,37,35,39,16,20,18,22,17,21,19,23,48,52,50,54,49,53,51,55,8,12,10,14,9,13,11,15,40,44,42,46,41,45,43,47,24,28,26,30,25,29,27,31,56,60,58,62,57,61,59,63]

def K_0 : List (List Nat) := [[3,0xcccccccccccccccc,0xfafafaf0fafaaa00,0xff00ff00ff00ff00,0xffffffff00000000],[4,0x22222222aaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[4,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffffffffcccccccc],[4,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffffffff00000000],[4,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfffaff00fffaff00,0xfffffffffafa0000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafa0000fafa0000,0xfff0fff0ff00ff00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xfffffffffafa0000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0fff0ff00,0xffff0000ffff0000,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfefeccccfefecccc,0xff00ff00ff00ff00,0xfffffffffafa0000],[4,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[4,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[4,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffffee00ee00],[4,0xaaaaaaaaaaaaaaaa,0xfafa0000fafa0000,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xfcfcccccfcfccccc,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffffccccffff0000,0xffffffffcccccccc],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcf0fcf0,0xff00ff00ff00ff00,0xffffccccffffcc00,0xffffffff00000000],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[4,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfccccc,0xfff0fff0fff0ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xcccccccccccccccc,0xfafaaaaafafaaaaa,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xcccccccccccccccc,0xfafaaaaafafaaaaa,0xfff0fff0fff0fff0,0xffffff00ffffff00,0xffffffff00000000],[4,0xcccccccccccccccc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaa00],[4,0xcccccccccccccccc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[4,0xcccccccceeeeeeee,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeeaaeeaaeeaaeeaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeecceecceecceecc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeeeecccceeeeeeee,0xfafaf0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeeeeeecceeeeeecc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeeeeeeeeeeaaeeaa,0xfcfcfcfcfcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[4,0xeeeeeeeeeeeeeeee,0xfafa0000fafa0000,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaa,0x5555555500000000,0xaaaa0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xaaaaaaaa,0x5555555500000000,0xcccccccc44444444,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000]]
def K_1 : List (List Nat) := [[5,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f050505050,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff5555ffff0000],[5,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0x5555555500000000,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0x55555555aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0x5555ffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0xaaaa0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xdddddddd00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf5f5f5f500000000,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff55ff5500000000,0xffff0000ffff0000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0f0,0xf0f0f0ff0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcfcfcf00000000,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xfafafafa,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xff00ff00,0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[5,0xff00ff00,0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[5,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccffccff00000000,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[5,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0fff0ff00000000,0xffff0000ffff0000],[5,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xfffcfffc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xffff0000,0xffff00000000,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0xffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0xffff00000000,0xaaaaffffaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0xffffffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0x5555ffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xffff0000,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccffff00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0f0ffff00000000,0xff00ff00ff00ff00]]
def K_2 : List (List Nat) := [[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ffff00000000],[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffffffff00000000],[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xffff0000,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa,0xf0f00000f0f0,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffffff0f00000],[5,0xaaaa0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xfefe0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xff000000ff00,0xffff0000ffff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000],[5,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0ff0000f0ff0000,0xffffffff00000000],[5,0xfffa0000fffa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xffffffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xffffffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xa000aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc000ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x220022aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x300030f0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xcc00cccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xf000f0f0f0f0f0,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xff0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffff0000,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa00aaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcc00cccccccccc,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffff0000,0xffffffff00000000],[5,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000]]
def K_3 : List (List Nat) := [[5,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffffffff00000000],[5,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffffffff00000000],[5,0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x2020202aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3000300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x3030000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x404cccc0404cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x404cccc0404cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x500ff000500ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xffffffff00000000],[5,0x500ff000500ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[5,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[5,0xa0a0a0a0a0a0a0a,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0a0a0a0a0a,0xecececececececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0a0a0a0a0a,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0a0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0a0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0a2a2a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaa0aaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xc0c0c0ccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xf000f00ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xf0f0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f050505050,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a0a0aaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0a2a2a0a0a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaa0a0a0aaa0a,0xcccccccccccccccc,0xf0f000f0f0f000f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaa0a0a0aaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaaaa0a0aaaaa,0xc0ccccc0c0ccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaaaa0a0aaaaa,0xf00ff000f00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaaaa0a0aaaaa,0xf0fffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xa0aaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xa0aaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0ff00fff0ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaaaa0a0aaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcccccfcfccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_4 : List (List Nat) := [[5,0xa0aaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaa0aaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaa0aaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[5,0xc0c0c0c0c0c0c0c,0xaaaaeeeeaaaaeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c0c0c0c0c,0xeaeaeaeaeaeaeaea,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c0c0c0c0c,0xeeaaeeaaeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0c4c4c4c4c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0ccc0ccc0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0ffff0000,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c0c0ccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafaaaaaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0c4c4c0c0c4c4c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccc0c0c0ccc0c,0xaaaaaaaaaaaaaaaa,0xf0f000f0f0f000f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccc0c0c0ccc0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f03030f0f03030,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfff0ff00fff0ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccc0c0ccccc,0xf0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xc0ccccccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xccc0ccccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xccccccc0ccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f000f000f00,0xff00ff00ff00ff0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f000f0f0f000f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000f000f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f00ff00ff00,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000],[5,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfffff0f0ffff0000,0xffffffff00000000]]
def K_5 : List (List Nat) := [[5,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xf000f00ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafaaaaaaaaa,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f000f0f0f000f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0ff0000f0ff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffff00ffffff00,0xffffffff00000000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcccccfcfccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff000f00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaa,0xffff0000ffff0000,0xffffffff00000000],[5,0xf00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f00000f0f0000,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffffffff0000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffffff0f00000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffff0f0ffff0000,0xffffffff00000000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0ff00ff00,0xffffffff00000000],[5,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xf0f0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xf0f000f0f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f03030f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f00000000,0xf0f0f0ff0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0ffff0000],[5,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0f0f0000],[5,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xf0f0f0f00000000,0xcccccccccccccccc,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f05050000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0f0f0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0f0f0f0f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0f0f0ff0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0f0f0ff0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0ff0f00f0ff0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000]]
def K_6 : List (List Nat) := [[5,0xf0ff0f00f0ff0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0ff00fff0ff00,0xffff0000ffff0000],[5,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcccccfcfccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xf0fffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xff00ff00ff00ff0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xff00ff00ff00ff0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xfff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xfffffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x22220000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22220000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000],[5,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222222222222222,0xcccccccccccccccc,0xf8f8f8f8f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222222222222222,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222222222aa22aa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222222222aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x222222222a2a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0x30303030f0f0f0f0,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0x33003300ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0x33330000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[5,0x22222222aaaaaaaa,0xcccccccc44444444,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22222222aaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2222aaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x222a222a222a222a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22aa222222aa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22aa22aa22aa22aa,0x33ff000033ff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x22aa22aa22aa22aa,0x33ff33ff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x22aa22aa22aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22aa22aa22aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0x22aa22aa22aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[5,0x22aa22aa22aa22aa,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_7 : List (List Nat) := [[5,0x22aa22aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x22aaaaaa22aaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2a0a2a0a2a0a2a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2a2a22222a2a2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2a2a2a2a2a2a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2a2a2a2aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2a2aaaaa2a2aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x2aaa2aaa2aaa2aaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3300330033003300,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffff00ff00],[5,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x33003300ff00ff00,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000],[5,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffcccccccc],[5,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffccccffff0000,0xffffffff00000000],[5,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x33003300ff00ff00,0xcccccccccccccccc,0xeeeeeeeeaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x3300ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x3303330333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3333000033ff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3333000033ff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffcccccccc],[5,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffffffff00000000],[5,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x33330000ffff0000,0xcccccccccccccccc,0xeeeeeeeeaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3333333333223322,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3333333333333300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x33333333cccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x33333333cccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3333cccc3333cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3333cccc3333cccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x33ff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3c3c3c3c3c3c3c3c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3c3c3c3c3c3c3c3c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x3f003f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x3f00ff003f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000]]
def K_8 : List (List Nat) := [[5,0x3f3f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3f3fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x3fff00003fff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x3fff3fff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0x4c0c4c0c4c0c4c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x4c4c4c4c4c4c4c4c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x4c4c4c4ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x4c4ccccc4c4ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x5a5a5a5a5a5a5a5a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x5f005f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x5f00ff005f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0x5f5f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0x88aa88aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x88cc88cccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x8a8a8a8aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x8a8aaaaa8a8aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x8c8c8c8ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0x8c8ccccc8c8ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa0aaa0aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa2a2a2a2aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xa2aaa2aaa2aaa2aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa00aa0aaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa0aaa0aaa0a,0xcc0ccc0ccc0ccc0c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa0aaa0aaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa0aaa0aaa0a,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa0aaa0aaa0a,0xccfcccfcccfcccfc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaa0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa0aaaaaaa0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa22aa22aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa2aaa2aaa2aaa2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaa8aaa8aaa8aaa8a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f00000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffffffff0f00000],[5,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[5,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffaaaaaaaa,0xffffffffffff0000],[5,0xaaaa0000aaaa0000,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaa0000,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_9 : List (List Nat) := [[5,0xaaaa0000aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[5,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[5,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000aaaaaaaa,0xeeeecccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0000fafa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaa0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffffff0000],[5,0xaaaa0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffaaaaaaaa],[5,0xaaaa00aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2200aaaa2200,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2222aaaa2222,0xcccccccccccccccc,0xf0f03030f0f03030,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2222aaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2222aaaa2222,0xcccccccccccccccc,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2222aaaa2222,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2222aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa22aaaaaa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa2a2aaaaa2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaa8888aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaa0a0aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaa2a2aaaaa2a2,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaa00],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa00aaaaaa00,0xeeeeeecceeeeeecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa00aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa0aaaaaaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa22aaaaaa22,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaa88aaaaaa88,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaa0aaaaaaa0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaa22aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaa2a2a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaa0aaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_10 : List (List Nat) := [[5,0xaaaaaaaaaaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xaaff0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xaf00af00ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xaf00ff00af00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xafaf0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xafafffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaaaaaaaaaa,0xbb00bb00ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xbbbb0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xbbff0000bbff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xbbffbbff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccc0ccc0c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccc0ccc0c,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc0ccccccc0ccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc44cccccc44cccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc4ccc4ccc4ccc4c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcc8ccc8ccc8ccc8c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccc00cccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccc0c0ccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccc4c4ccccc4c4c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccc0ccccccc0c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[5,0xaaaaaaaaaaaaaaaa,0xcccccccc44444444,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xfcfcfcfcfcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc0ccc0c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccc88cc88,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccff0000ffff0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcf00cf00ff00ff00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcf00ff00cf00ff00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcf0000ffff0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000]]
def K_11 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcfffff00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeee0000ffff0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xef00ef00ef00ef00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xfffffffffafa0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfbfb0000fbfb0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfefe0000fefe0000,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000f00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff003300ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff000f00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff005500ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00cc00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ee00ee00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0f0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff330000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaa0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffa0000fffa0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0000aa00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0000cc00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00330000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00aa0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff02020202],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0a000a00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0a0a0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff0c000c00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff22002200],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff22220000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff30300000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff44004400],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff50500000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff88008800],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff88880000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffa000a000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffa0a00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000]]
def K_12 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaa00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffc000c000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffc0c00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffee00ee00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffffafa0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0f00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffffaa00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0300ffff0300,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0404ffff0404,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0500ffff0500,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0a00ffff0a00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0c00ffff0c00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0c0cffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0f00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0f00ffff0f00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff2200ffff2200,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff3300ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff8800ffff8800,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff8888ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffa000ffffa000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffffaa00aa00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaf00ffffaf00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffffcc00cc00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcf00ffffcf00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffee00ffffee00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0ffff0000,0xfffffffff0f0f0f0],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xfffffffff0f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffff0f00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffaa00,0xffffffff00000000]]
def K_13 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xfffffffff0f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffffaaaa0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0fafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0faf0fa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f2f2f2f2,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0fcf0f0f0fc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f3f0f0f0f3f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f4f4f0f0f4f4,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f5f0f0f0f5f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f8f8f0f0f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0faf0f0f0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fcf0f0f0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fff0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fff0f0f0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fffcf0f0fffc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f8f0f8f0f8f0f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0faf0f0f0faf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0fcf0fcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf2f0f2f0f2f0f2f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf2f2f0f0f2f2f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf3f0f3f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf4f0f4f0f4f0f4f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf4f4f4f4f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf5f0f5f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f0f8f0f8f0f8f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f0f0f8f8f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f8f8f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f8f8f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f8f8fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_14 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8fcfcf8f8fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0f0f0faf0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0fff0faf0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf8faf8faf8faf8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafa0000fafa0000,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafa0000fafa0000,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf8f8fafaf8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xfffff0f0ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0f0f0fcf0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcf0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcfcfcf0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fff0fcf0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf8fcf8fcf8fcf8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcf0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffffccccffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xfff0ff00fff0ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfef0fef0fef0fef0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_15 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffffff00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0fff0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0faf0faf0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fcf0fcf0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xfffffffff0f00000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfffcfffcf0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccccceeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccceeccee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccccccccccffcccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccccececece,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccccccccecececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccccccceeeeeeee,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccccccccfcfccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccccececccccecec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcccceecccccceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccccffcccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xccfcccfcccfcccfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[5,0xaaaaaaaaaaaaaaaa,0xcecccecccecccecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcececccccececccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xcfcccfcccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeccceccceccceccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xececccccececcccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xecececececececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xecececececececec,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xececececeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xee00ee00ee00ee00,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeecccccceecccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeecceecccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[5,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_16 : List (List Nat) := [[5,0xaaaaaaaaaaaaaaaa,0xeecceecceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeceeeceeeceeec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeececeeeeecec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeecceeeeeecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf8f8f8f8f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xfefeccccfefecccc,0xff00ff00ff00ff00,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfefeccccfefecccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00cc00cc00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff33ff33cc00cc00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffcccccccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffffff00ff00],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffffff00ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcceecceecc,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffffcc00cc00],[5,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffffcccccccc,0xffffffffff00ff00],[5,0xaaaaaaaaaaaaaaaa,0xfafafafafafafafa,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xfcfcccccfcfccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaaaaaaaaaaaaa,0xfcfcfcfccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[5,0xaaaaaaaaaaaaaaaa,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[5,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffccffcccccccccc,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xaaaaeeeeaaaaeeee,0xcccccccccccccccc,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xaafaaafaaafaaafa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccccc,0xeaeaeaeaeaeaeaea,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccccc,0xeeaaeeaaeeaaeeaa,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccccc,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[5,0xcccccccccccccccc,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000]]
def K_17 : List (List Nat) := [[5,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[5,0xeeeeeeeeeeeeeeee,0xfafafafafafafafa,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc00cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22222222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x30303030,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x33003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x33330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x44444444,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x50505050,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x55005500,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x55550000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x88888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0x5555000055550000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0x5555555500000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xaaaaaaaa,0x5555555500000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaa00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccc44444444,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f050505050,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_18 : List (List Nat) := [[6,0xaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc00cc00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xcc00cc00cc00cc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xcccccccc,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[6,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xeeeeeeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xf0f0f0f0,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xf0f0f0f0,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0x3030303030303030,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0],[6,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xfafafafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfcfcfcfc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xff00ff00,0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[6,0xff00ff00,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffff00ff00],[6,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xffaaffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_19 : List (List Nat) := [[6,0xffccffcc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfff0fff0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffff0000,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0xffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[6,0xffff0000,0xffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xffff0000,0xffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0xff000000ff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff000000000000,0xffffffff00000000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffffff0000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffff0f0fffff0f0,0xffffffff00000000],[6,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[6,0xffffaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffffcccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfffff0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffffff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a00000a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c00000c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0000000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x222200002222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x330000003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x888800008888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a00000a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa000000aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa,0xf0f00000f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaa0000aaaa,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa,0x5555000055550000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaa0000aaaa,0x5555000055550000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[6,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[6,0xaaaa0000aaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_20 : List (List Nat) := [[6,0xaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc000000cc00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xcccc0000cccc,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaa2222aaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcccccccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xff0000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0x5500550055005500,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f000f0f0f000f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fff0f0f0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffcc0000ffcc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfff00000fff0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xffff0000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xcc00cccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_21 : List (List Nat) := [[6,0xff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0x202020202020202,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x300030003000300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x303000003030000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x303030300000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x404040404040404,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x500050005000500,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x505000005050000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x808080808080808,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa000a000a000a00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a00000a0a0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0x5050505050505050,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0x5500550055005500,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[6,0xa0a0a0aaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0aaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0aaaaa0a0aaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0aaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0aaaaa0a0aaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaa0aaa0aaa0aaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc000c000c000c00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c00000c0c0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0x3030303030303030,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0x3030303030303030,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0x4444444444444444,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_22 : List (List Nat) := [[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[6,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[6,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0c0c0ccccccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xc0ccccc0c0ccccc,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xccc0ccc0ccc0ccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xe0e0e0e0e0e0e0e,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0000000f000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f0000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf000f000f000f000,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0ff0000f0ff0000,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0f00ffff0f00,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[6,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf000f00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf00ff000f00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0a0f0a0f0a0f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0c0f0c0f0c0f0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f000000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0x3030303030303030,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000],[6,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_23 : List (List Nat) := [[6,0xf0f0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0c0c0f0f0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f000f0f0f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffffff0000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[6,0xf0f0f0f0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xf0f0f0f0f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffff0000],[6,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[6,0xf0fffff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfff00000fff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xfff0fff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2020202020202020,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2200220022002200,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222000022220000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222200000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0x8888888888888888,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222222222222222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[6,0x22222222aaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22222222aaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22222222aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2222aaaa2222aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22aa22aa22aa22aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22aa22aa22aa22aa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x22aa22aa22aa22aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2a2a2a2a2a2a2a2a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_24 : List (List Nat) := [[6,0x2a2a2a2a2a2a2a2a,0xc0c0c0c0c0c0c0c0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x2a2a2a2a2a2a2a2a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3232323232323232,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300000033000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x33003300ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0x3300ff003300ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3322332233223322,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3330333033303330,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[6,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[6,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x33330000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0x3333222233332222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333330033333300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[6,0x3f003f003f003f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3f3f00003f3f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x3f3f3f3f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x4c4c4c4c4c4c4c4c,0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x4c4c4c4c4c4c4c4c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x4c4c4c4c4c4c4c4c,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x5f005f005f005f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x5f5f00005f5f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8080808080808080,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8800880088008800,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_25 : List (List Nat) := [[6,0x8888000088880000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888888800000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888888888888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888888888888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f8f8f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888888888888888,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888888888888888,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x88888888aaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x88888888cccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888aaaa8888aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8888cccc8888cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x88aa88aa88aa88aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x88cc88cc88cc88cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8a8a8a8a8a8a8a8a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0x8c8c8c8c8c8c8c8c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa000a000a000a000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a00000a0a00000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xecececececececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0aaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0a0a0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa0a0aaaaa0a0aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa2a2a2a2a2a2a2a2,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xa8a8a8a8a8a8a8a8,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa000000aa000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa0000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00aaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aa00ff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00aaaaaa00aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa00ff00aa00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa0aaa0aaa0aaa0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_26 : List (List Nat) := [[6,0xaa0aaa0aaa0aaa0a,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa22aa22aa22aa22,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaa88aa88aa88aa88,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaa0aaa0aaa0aaa0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa000000000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffffff00000000],[6,0xaaaa0000aaaa0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[6,0xaaaa0000aaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000aaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaa00aaaaaa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa0a0aaaaa0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa2222aaaa2222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa2222aaaa2222,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaa8888aaaa8888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaa0a0aaaaa0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaa00aaaaaa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaa00aaaaaa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa],[6,0xaaaaaaaa00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa],[6,0xaaaaaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa22222222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaa88888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaa0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_27 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaeeeeeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaaaaafafafafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffaaffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaffffaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaeeeeaaaaeeee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaffaaaaaaffaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaaaffffaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaeeaaeeaaeeaaee,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaafaaafaaafaaafa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaff0000aaff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaffaaaaaaffaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaffaaff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaaffaaffaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaeaeaeaeaeaeaeae,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xaf00af00af00af00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xafaaafaaafaaafaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xafaf0000afaf0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xafafafaf00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xafafafafaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbabababababababa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbb00bb00bb00bb00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbbaabbaabbaabbaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbbbb0000bbbb0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbbbbaaaabbbbaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbbbbbbbb00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xbbbbbbbbaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xc8c8c8c8c8c8c8c8,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc000000cc000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc0000000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccc00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000]]
def K_28 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00cccccccc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cc00ff00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00cccccc00cccc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc00ff00cc00ff00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccc0ccc0c,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc0ccc0ccc0ccc0c,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc44cc44cc44cc44,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcc88cc88cc88cc88,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xccc0ccc0ccc0ccc0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0000cccccccc,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0000ffff0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc0c0ccccc0c0c,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccc8888cccc8888,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccc00cccccc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccccccfcfcfcfc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccccccffccffcc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccccccffffcccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcccceeeecccceeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccffccccccffcc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcececececececece,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcf00cf00cf00cf00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcccfcccfcccfcc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcf0000cfcf0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcfcccccfcfcccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcfcfcf00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcfcfcfcfcccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeaeaeaeaeaeaeaea,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xecececececececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xee00ee00ee00ee00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeaaeeaaeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeee0000eeee0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_29 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeaaaaeeeeaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeee00000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeecccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfa00fa00fa00fa00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfaaafaaafaaafaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafa0000fafa0000,0xff00ff00ff00ff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00000000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff00ff00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ffff0000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000f00ff000f00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff003300ff003300,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff005500ff005500,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00aa00ff00aa00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00cc00ff00cc00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00f000ff00f000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffff00ff00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffffff00ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff000000ff00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff000f000f00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0033003300,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0055005500,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00aa00aa00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00cc00cc00,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00f000f000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ff00ffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ff00ffccffcc,0xffff0000ffff0000,0xffffffff00000000]]
def K_30 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ff00fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ff00ffffff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ffaaff00ffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ffccff00ffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00fff0ff00fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ffffff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0aff0aff0aff0a,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0cff0cff0cff0c,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0f0000ff0f0000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0fff00ff0fff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff0fff0fff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff22ff22ff22ff22,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff30ff30ff30ff30,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff330000ff330000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff33ff00ff33ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff33ff33ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff44ff44ff44ff44,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff50ff50ff50ff50,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff550000ff550000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff55ff00ff55ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff55ff55ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff88ff88ff88ff88,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffa0ffa0ffa0ffa0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaa0000ffaa0000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaaaaaffaaaaaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaff00ffaaff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffc0ffc0ffc0ffc0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffcc0000ffcc0000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccccccffcccccc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccff00ffccff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff00000fff00000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0f0f0fff0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0ff00fff0ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_31 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffafffafffafffa,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfffcfffcfffcfffc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ff000000,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0000ffffaaaa,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0000ffffcccc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0000fffff0f0,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0000ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0a0affff0a0a,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0c0cffff0c0c,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0f00ffff0f00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0f0fffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff2222ffff2222,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff3300ffff3300,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff8888ffff8888,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffa0a0ffffa0a0,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaa00ffffaa00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffcc00ffffcc00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffeeeeffffeeee,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffafafffffafa,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ff00ff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffaaffffffaa,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffccffffffcc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffff0fffffff0,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffaaffaa],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffccffcc],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffffff00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaa00aa00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaa0000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xffffffffff00ff00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffaaaaaaaa,0xffffffffffff0000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcc00cc00],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc,0xffffffffff00ff00]]
def K_32 : List (List Nat) := [[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f00000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffffff0f0f0f0,0xffffffffffff0000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0f00ffff0f00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa00ffffaa00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffcc00ffffcc00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffccccffffcccc,0xffffff00ffffff00,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffff00ffffff00,0xffffffff00000000,0xffffffffffff0000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0fafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fcfcf0f0fcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0fff0f0f0fff0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf8f8f8f8f8f8f8f8,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf0faf0faf0faf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafaf0f0fafaf0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcf0fcf0fcf0fcf0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcf0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff0000000000,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0],[6,0xaaaaaaaaaaaaaaaa,0xcccccccceeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xecececececececec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xeecceecceecceecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xeeeecccceeeecccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[6,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[7,0xaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xcccccccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xf0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]
def K_33 : List (List Nat) := [[7,0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xff000000ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xa0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xf000f000f000f00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xf0f00000f0f0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xf0f0f0f00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0x2222222222222222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0x3333000033330000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0x8888888888888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000],[7,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[8,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]]

def allK : List (List Nat) := K_0 ++ K_1 ++ K_2 ++ K_3 ++ K_4 ++ K_5 ++ K_6 ++ K_7 ++ K_8 ++ K_9 ++ K_10 ++ K_11 ++ K_12 ++ K_13 ++ K_14 ++ K_15 ++ K_16 ++ K_17 ++ K_18 ++ K_19 ++ K_20 ++ K_21 ++ K_22 ++ K_23 ++ K_24 ++ K_25 ++ K_26 ++ K_27 ++ K_28 ++ K_29 ++ K_30 ++ K_31 ++ K_32 ++ K_33

def T_ : BT := ofSorted allK

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_0 : K_0.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_1 : K_1.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_2 : K_2.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_3 : K_3.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_4 : K_4.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_5 : K_5.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_6 : K_6.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_7 : K_7.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_8 : K_8.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_9 : K_9.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_10 : K_10.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_11 : K_11.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_12 : K_12.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_13 : K_13.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_14 : K_14.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_15 : K_15.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_16 : K_16.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_17 : K_17.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_18 : K_18.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_19 : K_19.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_20 : K_20.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_21 : K_21.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_22 : K_22.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_23 : K_23.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_24 : K_24.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_25 : K_25.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_26 : K_26.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_27 : K_27.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_28 : K_28.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_29 : K_29.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_30 : K_30.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_31 : K_31.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_32 : K_32.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ck_33 : K_33.all (stepOK Y_ PD_ PI_ T_) = true := by decide +kernel

theorem allOK : allK.all (stepOK Y_ PD_ PI_ T_) = true := by
  simp only [allK, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ck_0, ck_1⟩, ck_2⟩, ck_3⟩, ck_4⟩, ck_5⟩, ck_6⟩, ck_7⟩, ck_8⟩, ck_9⟩, ck_10⟩, ck_11⟩, ck_12⟩, ck_13⟩, ck_14⟩, ck_15⟩, ck_16⟩, ck_17⟩, ck_18⟩, ck_19⟩, ck_20⟩, ck_21⟩, ck_22⟩, ck_23⟩, ck_24⟩, ck_25⟩, ck_26⟩, ck_27⟩, ck_28⟩, ck_29⟩, ck_30⟩, ck_31⟩, ck_32⟩, ck_33⟩

theorem hK_len : allK.length < 2 ^ 12 := by decide +kernel

theorem hK_toList : T_.toList = allK := toList_ofSortedFuel 12 allK hK_len

theorem hT_step : ∀ x, T_.mem x = true → stepOK Y_ PD_ PI_ T_ x = true := by
  intro x hx
  have hm := BT.mem_toList T_ x hx
  rw [hK_toList] at hm
  exact List.all_eq_true.1 allOK x hm

theorem hY_repr : repr6 coreFn Y_ := by
  have hlt : Y_ < 2 ^ 64 := by decide
  refine ⟨fun i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (show 0 < 2 by decide) hi)), ?_⟩
  decide +kernel

theorem hXS_m : ∀ w ∈ XS_, masked w ∧ w.testBit 0 = false := by
  intro w hw
  have hlt : w < 2 ^ 64 := by
    have : XS_.all (fun u => decide (u < 2 ^ 64)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.1 this w hw)
  have hb0 : w.testBit 0 = false := by
    have h1 : XS_.all (fun u => !u.testBit 0) = true := by decide +kernel
    have h2 := List.all_eq_true.1 h1 w hw
    cases hb : w.testBit 0
    · rfl
    · rw [hb] at h2; exact Bool.noConfusion h2
  exact ⟨fun i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (show 0 < 2 by decide) hi)), hb0⟩

theorem hXS_repr : represents prim XS_.toFinset := by
  intro f hf
  rcases hf with ⟨v, rfl⟩ | ⟨i, rfl | rfl⟩
  · cases v
    · exact ⟨0, ⟨masked_zero, .inl rfl⟩, ⟨masked_zero, by decide +kernel⟩⟩
    · exact ⟨M64, ⟨masked_M64, .inr (.inl rfl)⟩, ⟨masked_M64, by decide +kernel⟩⟩
  · let w := XS_.getD i.val 0
    have hw_mem : w ∈ XS_ := by fin_cases i <;> decide
    have hrep : repr6 (fun x : BaseX => x i) w := by
      refine ⟨(hXS_m w hw_mem).1, ?_⟩
      fin_cases i <;> decide +kernel
    exact ⟨w, ⟨(hXS_m w hw_mem).1, .inr (.inr ⟨w, List.mem_toFinset.mpr hw_mem, .inl rfl⟩)⟩, hrep⟩
  · let w := XS_.getD i.val 0
    have hw_mem : w ∈ XS_ := by fin_cases i <;> decide
    have hrep : repr6 (fun x : BaseX => x i) w := by
      refine ⟨(hXS_m w hw_mem).1, ?_⟩
      fin_cases i <;> decide +kernel
    exact ⟨inv64 w, holds_not ⟨(hXS_m w hw_mem).1, .inr (.inr ⟨w, List.mem_toFinset.mpr hw_mem, .inl rfl⟩)⟩, repr6_inv hrep⟩

theorem hprs : prsOK Y_ PD_ = true := by decide +kernel
theorem hpi_len : PI_.length = 64 := by decide
theorem hpi_inv : ∀ k : Fin 64, (PI_[k.val]?.bind fun j => PI_[j]?) = some k.val := by decide +kernel
theorem hpi_M : actL PI_ M64 = M64 := by decide +kernel
theorem hpi_Y : actL PI_ Y_ = Y_ := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hroot : XS_.sublists.all (rootOK Y_ PD_ T_ 8) = true := by decide +kernel

theorem coreBound (k : ℕ) (h : Can coreFn k prim) : 9 ≤ k := by
  by_contra! bad
  have hb := signCompile hY_repr (by decide) (by decide) (by decide) h XS_.toFinset
    (fun a ha => hXS_m a (List.mem_toFinset.mp ha)) hXS_repr
  exact certBound (by decide) (fun w hw => (hXS_m w hw).1) hprs hpi_len hpi_inv hpi_M hpi_Y
    hT_step hroot (by omega) hb

theorem finish : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ ev
  by_cases neg : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g, hg, hn⟩ := neg
    have lt : cost gs < gs.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [useBinary, hn]⟩
    have lb := circuitLower coreBound gs o legal ev
    exact ⟨upper, 20, by simp [upper], by change 13 ≤ gs.length; omega, upper_eq⟩
  · refine ⟨gs, o, ?_, le_rfl, ev⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    rcases op with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_14310

theorem PEqualNP.Outside.L_meta_14310 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_14310.finish
