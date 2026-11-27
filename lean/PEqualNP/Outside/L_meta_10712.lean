import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10712
abbrev Fn (X : Type) := X → Bool
abbrev Pool (X : Type) := Fn X → Prop
def inv {X : Type} (f : Fn X) : Fn X := fun x => !(f x)
def both {X : Type} (f g : Fn X) : Fn X := fun x => f x && g x
def extend {X : Type} (R : Pool X) (f : Fn X) : Pool X := fun g => R g ∨ g=f ∨ g=inv f
def Stable {X : Type} (R : Pool X) : Prop :=
  (∀ b : Bool, R (fun _ => b)) ∧ ∀ g, R g → R (inv g)
theorem doubleInv {X : Type} (g : Fn X) : inv (inv g) = g := by funext x; simp [inv]
theorem stableExt {X : Type} {R : Pool X} (st : Stable R) (f : Fn X) : Stable (extend R f) := by
  refine ⟨fun b => Or.inl (st.1 b),?_⟩
  intro g h
  rcases h with h|rfl|rfl
  · exact Or.inl (st.2 g h)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv f))
def Can {X : Type} (f : Fn X) : ℕ → Pool X → Prop
  | 0, R => R f
  | k+1, R => Can f k R ∨ ∃ a b, R a ∧ R b ∧ Can f k (extend R (both a b))
theorem Can.ready {X : Type} {f : Fn X} {R : Pool X} (h : R f) : Can f 0 R := h
theorem Can.skip {X : Type} {f : Fn X} {R : Pool X} {k : ℕ} (h : Can f k R) : Can f (k+1) R :=
  Or.inl h
theorem Can.gate {X : Type} {f : Fn X} {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
    (h : Can f k (extend R (both a b))) : Can f (k+1) R := Or.inr ⟨a,b,ha,hb,h⟩
theorem Can.ind {X : Type} {f : Fn X} {motive : ∀ k R, Can f k R → Prop}
    (ready : ∀ {R : Pool X} (hf : R f), motive 0 R (Can.ready hf))
    (skip : ∀ {k : ℕ} {R : Pool X} (h : Can f k R), motive k R h → motive (k+1) R (Can.skip h))
    (gate : ∀ {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
      (h : Can f k (extend R (both a b))), motive k (extend R (both a b)) h →
      motive (k+1) R (Can.gate a b ha hb h))
    {k : ℕ} {R : Pool X} (h : Can f k R) : motive k R h := by
  induction k generalizing R with
  | zero => exact ready h
  | succ k ih =>
    rcases h with old|⟨a,b,ha,hb,tail⟩
    · exact skip old (ih old)
    · exact gate a b ha hb tail (ih tail)

def liftF {X : Type} (f : Fn X) : Fn (X × Bool) := fun y => f y.1
def slice {X : Type} (b : Bool) (f : Fn (X × Bool)) : Fn X := fun x => f (x,b)
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
    rcases hz with hz|rfl|rfl
    · exact Or.inl (hr _ hz)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def lifted {X : Type} (R : Pool X) (z : Fn (X × Bool)) := ∃ g, R g ∧ z=liftF g
def fixedAt {X : Type} (v : Bool) (z : Fn (X × Bool)) := ∃ c : Bool, slice v z=fun _ => c

theorem dropOne {X : Type} {f : Fn (X × Bool)} {S : Pool (X × Bool)} {k : ℕ}
    (h : Can f k S) (v : Bool) (dep : ∀ g, f ≠ liftF g) (nc : ¬ fixedAt v f)
    (R : Pool X) (st : Stable R) (hs : ∀ z, S z → lifted R z ∨ fixedAt v z) :
    ∃ t, t+1 ≤ k ∧ Can (slice v f) t R := by
  have value {Q : Pool X} (sq : Stable Q) {z : Fn (X × Bool)}
      (hz : lifted Q z ∨ fixedAt v z) : Q (slice v z) := by
    rcases hz with ⟨g,hg,rfl⟩|⟨c,hc⟩
    · exact hg
    · rw [hc]; exact sq.1 c
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g,_,e⟩|hconst
    · exact (dep g e).elim
    · exact (nc hconst).elim
  | skip _ ih =>
    obtain ⟨t,sz,pr⟩ := ih R st hs
    exact ⟨t,by omega,pr⟩
  | @gate k S a b ha hb rest ih =>
    have aa := hs a ha
    have bb := hs b hb
    have save (ok : R (slice v (both a b))) : ∃ t, t+1 ≤ k+1 ∧ Can (slice v f) t R := by
      refine ⟨k,le_rfl,mapRestrict rest v R st ?_⟩
      intro z hz
      rcases hz with hz|rfl|rfl
      · exact value st (hs _ hz)
      · exact ok
      · exact st.2 _ ok
    rcases aa with ⟨u,hu,rfl⟩|⟨c,hc⟩
    · rcases bb with ⟨w,hw,rfl⟩|⟨d,hd⟩
      · let T := extend R (both u w)
        obtain ⟨t,sz,pr⟩ := ih T (stableExt st _) (by
          intro z hz
          rcases hz with hz|rfl|rfl
          · rcases hs _ hz with ⟨g,hg,rfl⟩|c
            · exact Or.inl ⟨g,Or.inl hg,rfl⟩
            · exact Or.inr c
          · exact Or.inl ⟨both u w,Or.inr (Or.inl rfl),rfl⟩
          · exact Or.inl ⟨inv (both u w),Or.inr (Or.inr rfl),rfl⟩)
        exact ⟨t+1,by omega,Can.gate u w hu hw pr⟩
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
    (hs : ∀ z, S z → lifted R z ∨ z=bitInput ∨ z=inv bitInput) :
    ∃ v t, t+2 ≤ k ∧ Can (slice v f) t R := by
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨g,_,e⟩|e|e
    · exact (dep g e).elim
    · exact (nc false ⟨false, by rw [e]; rfl⟩).elim
    · exact (nc false ⟨true, by rw [e]; rfl⟩).elim
  | skip _ ih =>
    obtain ⟨v,t,sz,pr⟩ := ih R st hs
    exact ⟨v,t,by omega,pr⟩
  | @gate k S a b ha hb rest ih =>
    have save (v : Bool) (zero : slice v (both a b) = fun _ => false) :
        ∃ v t, t+2 ≤ k+1 ∧ Can (slice v f) t R := by
      have extra : ∀ z, extend S (both a b) z → lifted R z ∨ fixedAt v z := by
        intro z hz
        rcases hz with hz|rfl|rfl
        · rcases hs _ hz with old|rfl|rfl
          · exact Or.inl old
          · exact Or.inr ⟨v,rfl⟩
          · exact Or.inr ⟨!v,rfl⟩
        · exact Or.inr ⟨false,zero⟩
        · refine Or.inr ⟨true,?_⟩
          change inv (slice v (both a b)) = _
          rw [zero]; rfl
      obtain ⟨t,sz,pr⟩ := dropOne rest v dep (nc v) R st extra
      exact ⟨v,t,by omega,pr⟩
    rcases hs a ha with ⟨u,hu,rfl⟩|rfl|rfl
    · rcases hs b hb with ⟨w,hw,rfl⟩|rfl|rfl
      · obtain ⟨v,t,sz,pr⟩ := ih (extend R (both u w)) (stableExt st _) (by
          intro z hz
          rcases hz with hz|rfl|rfl
          · rcases hs _ hz with ⟨g,hg,rfl⟩|e
            · exact Or.inl ⟨g,Or.inl hg,rfl⟩
            · exact Or.inr e
          · exact Or.inl ⟨both u w,Or.inr (Or.inl rfl),rfl⟩
          · exact Or.inl ⟨inv (both u w),Or.inr (Or.inr rfl),rfl⟩)
        exact ⟨v,t+1,by omega,Can.gate u w hu hw pr⟩
      · apply save false; funext x; simp [slice,both,bitInput]
      · apply save true; funext x; simp [slice,both,inv,bitInput]
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
  · rw [readF,List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · rw [readF,List.getD_eq_default _ _ (by omega)]; exact st.1 false

theorem gateClass {X : Type} (w : List (Fn X)) (g : Gate) (hg : fan g) (R : Pool X)
    (st : Stable R) (hw : ∀ u ∈ w, R u) :
    if useBinary g then R (outF w g) ∨
      ∃ a b, R a ∧ R b ∧ (outF w g = both a b ∨ outF w g = inv (both a b))
    else R (outF w g) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,len⟩ := hg
  change (op = .and ∨ op = .or ∨ op = .not) at hop
  change ins.length ≤ 2 at len
  rcases hop with rfl|rfl|rfl
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 true)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        exact Or.inr ⟨readF w i,readF w j,readIn st hw i,readIn st hw j,Or.inl (by funext x; simp [outF,GateOp.eval,both])⟩
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 false)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        refine Or.inr ⟨inv (readF w i),inv (readF w j),st.2 _ (readIn st hw i),
          st.2 _ (readIn st hw j),Or.inr ?_⟩
        funext x
        simp [outF,GateOp.eval,inv,both]
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
      rcases List.mem_append.mp hz with hz|hz
      · exact hw z hz
      · obtain rfl := List.mem_singleton.mp hz
        exact h
    cases hb : useBinary g with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at cl
      simpa [cost,hb] using same cl
    | true =>
      simp only [hb,ite_true] at cl
      have len : cost (g::gs)=cost gs+1 := by simp [cost,hb]
      rw [len]
      rcases cl with h|⟨a,b,ha,hb',eq⟩
      · exact Can.skip (same h)
      · apply Can.gate a b ha hb'
        apply cont _ _ (stableExt st _)
        intro z hz
        rcases List.mem_append.mp hz with hz|hz
        · exact Or.inl (hw z hz)
        · obtain rfl := List.mem_singleton.mp hz
          exact Or.inr eq

theorem readAt {X : Type} (w : List (Fn X)) (i : ℕ) (x : X) :
    (w.map (fun z => z x)).getD i false = readF w i x := by
  by_cases h : i < w.length
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (by omega : w.length ≤ i)]

theorem traceAt {X : Type} (gs : List Gate) (w : List (Fn X)) (x : X) :
    (traceF gs w).map (fun z => z x) =
      gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map (fun i => old.getD i false))])
        (w.map (fun z => z x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (traceF gs (w ++ [outF w g])).map _ = _
    rw [ih,List.foldl_cons]
    simp only [List.map_append,List.map_cons,List.map_nil,outF,readAt]


abbrev BaseX := Fin 5 → Bool
def bow (x : BaseX) : Bool :=
  (x 0 && (x 1 || x 2 || x 3 || x 4)) || (x 1 && x 2) || (x 3 && x 4)
def prim (z : Fn BaseX) : Prop :=
  (∃ b : Bool, z=fun _ => b) ∨ ∃ i : Fin 5, z=(fun x => x i) ∨ z=inv (fun x => x i)
theorem stablePrim : Stable prim := by
  refine ⟨fun b => Or.inl ⟨b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨!v,rfl⟩
  · exact Or.inr ⟨i,Or.inr rfl⟩
  · exact Or.inr ⟨i,Or.inl (doubleInv _)⟩
def extendInput {X : Type} (R : Pool X) : Pool (X × Bool) :=
  fun z => lifted R z ∨ z=bitInput ∨ z=inv bitInput
theorem stableInput {X : Type} {R : Pool X} (st : Stable R) : Stable (extendInput R) := by
  refine ⟨fun b => Or.inl ⟨fun _ => b,st.1 b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨g,hg,rfl⟩|rfl|rfl
  · exact Or.inl ⟨inv g,st.2 _ hg,rfl⟩
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv _))
abbrev World := (BaseX × Bool) × Bool
def input (y : World) : Fin 7 → Bool :=
  ![y.1.1 1,y.1.1 3,y.2,y.1.1 2,y.1.1 4,y.1.1 0,y.1.2]
def wires : List (Fn World) := List.ofFn (fun i : Fin 7 => fun y => input y i)
def full (y : World) : Bool :=
  bow y.1.1 || (y.1.2 && (y.2 || y.1.1 0 || y.1.1 1 || y.1.1 2 || y.1.1 3 || y.1.1 4))
theorem knownWires : ∀ z ∈ wires, extendInput (extendInput prim) z := by
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  have p (j : Fin 5) : extendInput (extendInput prim) (liftF (liftF (fun x : BaseX => x j))) :=
    Or.inl ⟨_,Or.inl ⟨_,Or.inr ⟨j,Or.inl rfl⟩,rfl⟩,rfl⟩
  fin_cases i
  · exact p 1
  · exact p 3
  · exact Or.inr (Or.inl rfl)
  · exact p 2
  · exact p 4
  · exact p 0
  · exact Or.inl ⟨bitInput,Or.inr (Or.inl rfl),rfl⟩
theorem genuine {X : Type} {f : Fn (X × Bool)} (x : X) (h : f (x,false) ≠ f (x,true)) :
    ∀ g, f ≠ liftF g := by
  intro g he
  exact h (he ▸ rfl)
theorem varying {X : Type} {f : Fn (X × Bool)} (v : Bool) (x y : X)
    (h : f (x,v) ≠ f (y,v)) : ¬ fixedAt v f := by
  rintro ⟨c,eq⟩
  exact h ((congrFun eq x).trans (congrFun eq y).symm)
theorem needsEleven (bound : ∀ k, Can bow k prim → 8 ≤ k)
    {s : ℕ} (h : Can full s (extendInput (extendInput prim))) : 11 ≤ s := by
  let low : BaseX := fun _ => false
  let high : BaseX := fun _ => true
  have dep := genuine (f:=full) (low,true) (by decide)
  have nc (v : Bool) : ¬ fixedAt v full := by
    apply varying v (low,false) (high,false)
    cases v <;> decide
  obtain ⟨v,t,sv,ht⟩ := dropTwo h dep nc _ (stableInput stablePrim) (fun _ h => h)
  have dep' := genuine (f:=slice v full) (![false,true,false,false,false] : BaseX) (by cases v <;> decide)
  have nc' : ¬ fixedAt false (slice v full) := by
    apply varying false low high
    cases v <;> decide
  obtain ⟨u,tu,hu⟩ := dropOne ht false dep' nc' prim stablePrim (by
    intro z hz
    rcases hz with h|rfl|rfl
    · exact Or.inl h
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inr ⟨true,rfl⟩)
  have eq : slice false (slice v full) = bow := by funext x; simp [slice,full]
  rw [eq] at hu
  have := bound u hu
  omega

def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def upper : List Gate := [⟨.and, [1,4]⟩, ⟨.or, [5,6]⟩, ⟨.or, [7,8]⟩, ⟨.or, [2,5]⟩, ⟨.and, [10,6]⟩, ⟨.or, [11,4]⟩, ⟨.or, [1,3]⟩, ⟨.or, [12,13]⟩, ⟨.and, [9,14]⟩, ⟨.or, [15,0]⟩, ⟨.or, [9,3]⟩, ⟨.and, [16,17]⟩]

set_option maxRecDepth 10000 in
theorem upper_eq : ∀ x : Fin 7 → Bool, Circuit.eval ⟨upper,18⟩ (List.ofFn x) = graph x := by decide +kernel
set_option maxRecDepth 12000 in
theorem emb_eq : ∀ (x : BaseX) (b v : Bool), graph (input ((x,b),v)) = full ((x,b),v) := by decide +kernel

theorem circuitLower (bound : ∀ k, Can bow k prim → 8 ≤ k) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, fan g) (ev : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x) :
    11 ≤ cost gs := by
  have program := comp gs o legal wires _ (stableInput (stableInput stablePrim)) knownWires
  have eq : readF (traceF gs wires) o = full := by
    funext y
    rw [← readAt,traceAt]
    have inp : wires.map (fun z => z y) = List.ofFn (input y) := by simp [wires]
    rw [inp]
    exact (ev (input y)).trans (emb_eq y.1.1 y.1.2 y.2)
  rw [eq] at program
  exact needsEleven bound program

theorem finish (bound : ∀ k, Can bow k prim → 8 ≤ k) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ ev
  by_cases neg : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hg,hn⟩ := neg
    have lt : cost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [useBinary,hn]⟩
    have lb := circuitLower bound gs o legal ev
    exact ⟨upper,18,by simp [upper],by change 12 ≤ gs.length; omega,upper_eq⟩
  · refine ⟨gs,o,?_,le_rfl,ev⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    refine ⟨?_,len⟩
    rcases op with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g,hg,h⟩).elim

-- The live-wire search below adapts the signed separation argument of L_meta_9146.
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
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
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

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 440
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 220 := ((x >>> 220) ^^^ x).setWidth 220
def cuts (ws : List W) : BitVec 220 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 220) ++ (0 : BitVec 220)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 220) (w : W) : Prop :=
  w.getLsbD (220+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 220) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 220+i.val < 440 := by omega
  have hi' : i.val < 440 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 220) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 220)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
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

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 440 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 440)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))


def rowList : List W := [0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000]


def sampled (i : Fin 440) (j : Fin 5) : Bool :=
  (rowList.getD j.val 0)[i.val]
def repr (f : Fn BaseX) (w : W) : Prop := ∀ i : Fin 440, w[i.val] = f (sampled i)
theorem reprAnd {a b : Fn BaseX} {wa wb : W} (ha : repr a wa) (hb : repr b wb) :
    repr (both a b) (wa &&& wb) := by
  intro i
  simp only [BitVec.getElem_and,ha i,hb i,both]
theorem reprInv {f : Fn BaseX} {w : W} (h : repr f w) : repr (inv f) (~~~w) := by
  intro i
  simp only [BitVec.getElem_not,h i,inv]
set_option maxRecDepth 12000 in
theorem sampleBow : repr bow (~~~goal) := by unfold repr; decide +kernel

def represents (R : Pool BaseX) (av : Finset W) : Prop :=
  ∀ f, R f → ∃ w, holds av w ∧ repr f w
theorem reprExtend {R : Pool BaseX} {av : Finset W} {f : Fn BaseX} {w : W}
    (hr : represents R av) (ha : holds av w) (hw : repr f w) : represents (extend R f) av := by
  intro z hz
  rcases hz with h|rfl|rfl
  · exact hr _ h
  · exact ⟨_,ha,hw⟩
  · exact ⟨_,holds_not ha,reprInv hw⟩
theorem reprInsert {R : Pool BaseX} {av : Finset W} (z : W) (hr : represents R av) :
    represents R (insert z av) := by
  intro f hf
  obtain ⟨w,hold,rep⟩ := hr f hf
  exact ⟨w,holds_insert hold,rep⟩
theorem signCompile {R : Pool BaseX} {k : ℕ} (h : Can bow k R)
    (av : Finset W) (hr : represents R av) :
    ∃ t, (t=goal ∨ t= ~~~goal) ∧ build basicOps t k av := by
  induction h using Can.ind generalizing av with
  | ready hf =>
    obtain ⟨w,hold,rep⟩ := hr _ hf
    have eq : w= ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      exact (rep ⟨j,hj⟩).trans (sampleBow ⟨j,hj⟩).symm
    rw [eq] at hold
    rcases hold with zero|ones|⟨t,ht,he|he⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t,Or.inr he.symm,ht⟩
    · exact ⟨t,Or.inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) he.symm),ht⟩
  | skip _ ih =>
    obtain ⟨t,eq,h⟩ := ih av hr
    exact ⟨t,eq,Or.inl h⟩
  | gate a b ha hb _ ih =>
    obtain ⟨wa,ha',ra⟩ := hr a ha
    obtain ⟨wb,hb',rb⟩ := hr b hb
    have rep := reprAnd ra rb
    rcases and_reach ha' hb' with old|⟨x,hx,y,hy,ne,z,hop,hz⟩
    · obtain ⟨t,eq,h⟩ := ih av (reprExtend hr old rep)
      exact ⟨t,eq,Or.inl h⟩
    · obtain ⟨t,eq,h⟩ := ih (insert z av) (reprExtend (reprInsert z hr) hz rep)
      exact ⟨t,eq,Or.inr ⟨x,hx,y,hy,ne,z,hop,h⟩⟩

theorem primRep : represents prim rowList.toFinset := by
  intro f hf
  rcases hf with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · cases v
    · exact ⟨0,Or.inl rfl,by unfold repr; decide +kernel⟩
    · exact ⟨~~~0,Or.inr (Or.inl rfl),by unfold repr; decide +kernel⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨w,Or.inr (Or.inr ⟨w,hw,Or.inl rfl⟩),fun _ => rfl⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨~~~w,Or.inr (Or.inr ⟨w,hw,Or.inr rfl⟩),reprInv (w:=w) (fun _ => rfl)⟩

theorem bowBound (rejected : search 7 rowList = false) (k : ℕ) (h : Can bow k prim) : 8 ≤ k := by
  by_contra! bad
  obtain ⟨t,ht,run⟩ := signCompile h _ primRep
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a rowList.toFinset) :
      build basicOps t b rowList.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := search_complete ht 7 rowList (by decide) (lift (by omega) run)
  exact Bool.noConfusion (rejected.symm.trans yes)
def nextCheck (ws : List W) (e : ℕ) (next : ℕ → List W → Bool) : Bool :=
  (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch e next a b r)

theorem optChecked {k e : ℕ} {ws : List W} (kids : List (ℕ × List W))
    (all : ∀ t ∈ kids, optimized k t.1 t.2 = false)
    (check : nextCheck ws e (fun i w => !kids.contains (i,w)) = false) :
    optimized (k+1) e ws = false := by
  by_contra! h
  have imp {i w} (ok : optimized k i w = true) : (!kids.contains (i,w)) = true := by
    simp only [Bool.not_eq_true', List.contains_eq_mem]
    by_contra! hm
    have hh := all (i,w) (by simpa using hm)
    simp_all
  have yes : optimized (k+1) e ws = true := by cases he : optimized (k+1) e ws <;> simp_all
  change nextCheck ws e (optimized k) = true at yes
  unfold nextCheck at yes check
  simp only [Bool.or_eq_true, List.any_eq_true] at yes
  have h' : ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a,b,r) => dispatch e (fun i w => !kids.contains (i,w)) a b r)) = true := by
    simp only [Bool.or_eq_true,List.any_eq_true]
    rcases yes with h|⟨⟨a,b,r⟩,hm,hd⟩
    · exact Or.inl h
    · refine Or.inr ⟨(a,b,r),hm,?_⟩
      unfold dispatch at hd ⊢
      rw [List.any_eq_true] at hd ⊢
      obtain ⟨z,hz,ok⟩ := hd
      refine ⟨z,hz,?_⟩
      dsimp only at ok ⊢
      simp only [Bool.or_eq_true,Bool.and_eq_true] at ok ⊢
      rcases ok with ((⟨c,t⟩ | ⟨c,(⟨v,t⟩|⟨v,t⟩)⟩) | ⟨c,t⟩)
      · exact Or.inl (Or.inl ⟨c,imp t⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inl ⟨v,imp t⟩⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inr ⟨v,imp t⟩⟩)
      · exact Or.inr ⟨c,imp t⟩
  exact Bool.noConfusion (check.symm.trans h')

theorem certifyRoot (h : optimized 7 3 rowList = false) : search 7 rowList = false := by
  have uni : rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) = [rowList] := by decide +kernel
  by_contra! hh
  have ok0 : search 7 rowList = true := by cases he : search 7 rowList <;> simp_all
  unfold search at ok0
  obtain ⟨w,hw,ok⟩ := List.any_eq_true.mp ok0
  change ((decide (w.length ≤ 8) && (cuts w == -1)) && optimized 7 (8-w.length) w) = true at ok
  obtain ⟨good,done⟩ := Bool.and_eq_true_iff.mp ok
  have hw' : w ∈ rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) := List.mem_filter.mpr ⟨hw,good⟩
  rw [uni] at hw'
  obtain rfl := List.mem_singleton.mp hw'
  exact Bool.noConfusion (h.symm.trans done)
def branch0 : ℕ × List W := (1,[0xffc0000000ffc0000000ffc00003ff003ff00000ffc00ffc00003ff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject0 : optimized 6 branch0.1 branch0.2 = false := by decide +kernel
def branch1 : ℕ × List W := (1,[0x4992649926499264992649926499264992649926499264992649926fffffffc00fffffffc00fffffffffffffffffffffffffffffffffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject1 : optimized 6 branch1.1 branch1.2 = false := by decide +kernel
def branch2 : ℕ × List W := (1,[0x8020080200802008020080200802008020080200802008020080200000ffc0000000ffc0000000ffc00ffc00003ff003ff00000ffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject2 : optimized 6 branch2.1 branch2.2 = false := by decide +kernel
def branch3 : ℕ × List W := (1,[0x4912449124491244912449124491244912449124491244912449124003ff00000003ff00000003ff0000000000ffc0000000003ff00000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject3 : optimized 6 branch3.1 branch3.2 = false := by decide +kernel
def branch4 : ℕ × List W := (1,[0xffc00ffc000000000000ffc00ffc00003ff003ff00000ffc00ffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject4 : optimized 6 branch4.1 branch4.2 = false := by decide +kernel
def branch5 : ℕ × List W := (1,[0x92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4affffffffffffc00ffc00fffffffffffffffffffffffffffffffffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject5 : optimized 6 branch5.1 branch5.2 = false := by decide +kernel
def branch6 : ℕ × List W := (1,[0x802008020080200802008020080200802008020080200802008020000000000ffc00ffc0000000003ffffc0000000fffff00000003ff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject6 : optimized 6 branch6.1 branch6.2 = false := by decide +kernel
def branch7 : ℕ × List W := (1,[0x9224892248922489224892248922489224892248922489224892248003ff003ff0000000000003ff0000000000ffc0000000003ff00000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject7 : optimized 6 branch7.1 branch7.2 = false := by decide +kernel
def branch8 : ℕ × List W := (1,[0xffc00ffc00ffc00ffc000000000000003ff003fffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject8 : optimized 6 branch8.1 branch8.2 = false := by decide +kernel
def branch9 : ℕ × List W := (1,[0x1c8721c8721c8721c8721c8721c8721c8721c8721c8721c8721c872ffffffffffffffffffffffc00ffffffffffffffffffffffc00fffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject9 : optimized 6 branch9.1 branch9.2 = false := by decide +kernel
def branch10 : ℕ × List W := (1,[0x8020080200802008020080200802008020080200802008020080200000000000000000000ffc00fffffffc000000000000ffc00fffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject10 : optimized 6 branch10.1 branch10.2 = false := by decide +kernel
def branch11 : ℕ × List W := (1,[0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070003ff003ff003ff003ff000000000000000ffc00000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject11 : optimized 6 branch11.1 branch11.2 = false := by decide +kernel
def branch12 : ℕ × List W := (1,[0xffc00ffc00ffc00ffc00ffc00fffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject12 : optimized 6 branch12.1 branch12.2 = false := by decide +kernel
def branch13 : ℕ × List W := (1,[0xe0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82fffffffffffffffffffffffffffffffffff003fffffffffc00fffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject13 : optimized 6 branch13.1 branch13.2 = false := by decide +kernel
def branch14 : ℕ × List W := (1,[0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000003ff003fffffffffc00fffff, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject14 : optimized 6 branch14.1 branch14.2 = false := by decide +kernel
def branch15 : ℕ × List W := (1,[0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380003ff003ff003ff003ff003ff000000000000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject15 : optimized 6 branch15.1 branch15.2 = false := by decide +kernel
def branch16 : ℕ × List W := (1,[0xfffff000000000000000fffff00000003ffffc0000000fffff00000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject16 : optimized 6 branch16.1 branch16.2 = false := by decide +kernel
def branch17 : ℕ × List W := (1,[0xdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cfffffffffffffff00000ffffffffff003fffffffffc00ffffffffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject17 : optimized 6 branch17.1 branch17.2 = false := by decide +kernel
def branch18 : ℕ × List W := (1,[0x49124491244912449124491244912449124491244912449124491240000000000fffff0000000000003ff0000000000ffc0000000003ff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject18 : optimized 6 branch18.1 branch18.2 = false := by decide +kernel
def branch19 : ℕ × List W := (1,[0x922489224892248922489224892248922489224892248922489224800000fffff000000000000000ffc0000000003ff0000000000ffc00, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject19 : optimized 6 branch19.1 branch19.2 = false := by decide +kernel
def branch20 : ℕ × List W := (1,[0x802008020080200802008020080200802008020080200802008020fffff00000fffff000000000000000003ffffc00ffc000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject20 : optimized 6 branch20.1 branch20.2 = false := by decide +kernel
def branch21 : ℕ × List W := (1,[0x5d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d174fffffffffffffffffffffffff003ff003fffffffffffffffff003ff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject21 : optimized 6 branch21.1 branch21.2 = false := by decide +kernel
def branch22 : ℕ × List W := (1,[0x411044110441104411044110441104411044110441104411044110400000000000000000000fffff003ff000000000000000fffff003ff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject22 : optimized 6 branch22.1 branch22.2 = false := by decide +kernel
def branch23 : ℕ × List W := (1,[0x140501405014050140501405014050140501405014050140501405000000fffff00000fffff000000000000000003ff003ff0000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject23 : optimized 6 branch23.1 branch23.2 = false := by decide +kernel
def branch24 : ℕ × List W := (1,[0x4010040100401004010040100401004010040100401004010040100fffff00000fffff00000fffff003ff0000000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject24 : optimized 6 branch24.1 branch24.2 = false := by decide +kernel
def branch25 : ℕ × List W := (1,[0xe93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4fffffffffffffffffffffffffffffffffffffc00ffc00fffff003ff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject25 : optimized 6 branch25.1 branch25.2 = false := by decide +kernel
def branch26 : ℕ × List W := (1,[0x902409024090240902409024090240902409024090240902409024000000000000000000000000000000003ffffc00ffc00fffff003ff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject26 : optimized 6 branch26.1 branch26.2 = false := by decide +kernel
def branch27 : ℕ × List W := (1,[0xa0280a0280a0280a0280a0280a0280a0280a0280a0280a0280a028000000fffff00000fffff00000ffc00ffc0000000000000000000000, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject27 : optimized 6 branch27.1 branch27.2 = false := by decide +kernel
def branch28 : ℕ × List W := (1,[0x1004010040100401004010040100401004010040100401004010040ffffffffff00000000000000000000003fffffff000000000000000, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject28 : optimized 6 branch28.1 branch28.2 = false := by decide +kernel
def branch29 : ℕ × List W := (1,[0x9e2789e2789e2789e2789e2789e2789e2789e2789e2789e2789e278fffffffffffffffffffffffffffc00003fffffffffffffffffffc00, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject29 : optimized 6 branch29.1 branch29.2 = false := by decide +kernel
def branch30 : ℕ × List W := (1,[0x822088220882208822088220882208822088220882208822088220800000000000000000000fffffffc00000000000000000fffffffc00, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject30 : optimized 6 branch30.1 branch30.2 = false := by decide +kernel
def branch31 : ℕ × List W := (1,[0xc0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300000000000ffffffffff00000000000000000000fffff0000000000, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject31 : optimized 6 branch31.1 branch31.2 = false := by decide +kernel
def branch32 : ℕ × List W := (1,[0x8020080200802008020080200802008020080200802008020080200ffffffffff0000000000fffffffc000000000000000000000000000, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject32 : optimized 6 branch32.1 branch32.2 = false := by decide +kernel
def branch33 : ℕ × List W := (1,[0xf23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8ffffffffffffffffffffffffffffffffffffffff00000fffffffc00, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject33 : optimized 6 branch33.1 branch33.2 = false := by decide +kernel
def branch34 : ℕ × List W := (1,[0x1204812048120481204812048120481204812048120481204812048000000000000000000000000000000003fffffff00000fffffffc00, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject34 : optimized 6 branch34.1 branch34.2 = false := by decide +kernel
def branch35 : ℕ × List W := (1,[0x60180601806018060180601806018060180601806018060180601800000000000ffffffffff00000003ffffc0000000000000000000000, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject35 : optimized 6 branch35.1 branch35.2 = false := by decide +kernel
def branch36 : ℕ × List W := (1,[0xffffffffffffffffffff00000000000000000000000000000000000, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject36 : optimized 6 branch36.1 branch36.2 = false := by decide +kernel
def branch37 : ℕ × List W := (1,[0xfc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fffffffffffffffffffffffffffffffffffffffffffff0000000000, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject37 : optimized 6 branch37.1 branch37.2 = false := by decide +kernel
def branch38 : ℕ × List W := (1,[0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070000000000000000000000000000000003ffffffffffff0000000000, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject38 : optimized 6 branch38.1 branch38.2 = false := by decide +kernel
def branch39 : ℕ × List W := (1,[0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e038000000000000000000000ffffffffffffc0000000000000000000000, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000, 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem reject39 : optimized 6 branch39.1 branch39.2 = false := by decide +kernel
def firstBranches : List (ℕ × List W) := [branch0, branch1, branch2, branch3, branch4, branch5, branch6, branch7, branch8, branch9, branch10, branch11, branch12, branch13, branch14, branch15, branch16, branch17, branch18, branch19, branch20, branch21, branch22, branch23, branch24, branch25, branch26, branch27, branch28, branch29, branch30, branch31, branch32, branch33, branch34, branch35, branch36, branch37, branch38, branch39]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem smallReject : search 7 rowList = false := by
  apply certifyRoot
  apply optChecked firstBranches
  · intro t ht
    simp only [firstBranches,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact reject0
    · exact reject1
    · exact reject2
    · exact reject3
    · exact reject4
    · exact reject5
    · exact reject6
    · exact reject7
    · exact reject8
    · exact reject9
    · exact reject10
    · exact reject11
    · exact reject12
    · exact reject13
    · exact reject14
    · exact reject15
    · exact reject16
    · exact reject17
    · exact reject18
    · exact reject19
    · exact reject20
    · exact reject21
    · exact reject22
    · exact reject23
    · exact reject24
    · exact reject25
    · exact reject26
    · exact reject27
    · exact reject28
    · exact reject29
    · exact reject30
    · exact reject31
    · exact reject32
    · exact reject33
    · exact reject34
    · exact reject35
    · exact reject36
    · exact reject37
    · exact reject38
    · exact reject39
  · decide +kernel
end PEqualNP.Outside.L_meta_10712

theorem PEqualNP.Outside.L_meta_10712 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_10712.finish (PEqualNP.Outside.L_meta_10712.bowBound PEqualNP.Outside.L_meta_10712.smallReject)
