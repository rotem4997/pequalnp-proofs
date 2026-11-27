import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4439_aux.Prefix

def inputs (x : Fin 9 → Bool) : Fin 10 → Bool := Fin.snoc x (x 4 || x 6)

def extended (x : Fin 9 → Bool) (b : Bool) : Fin 11 → Bool := Fin.snoc (inputs x) b

def Signal (b : (Fin 9 → Bool) → Bool) : Prop :=
  (∀ x, b x = false) ∨
  (∃ i : Fin 10, ∀ x, b x = inputs x i) ∨
  (∃ i j : Fin 10, i < j ∧ ∀ x, b x = (inputs x i || inputs x j))

private theorem inputs_eq (x : Fin 9 → Bool) :
    List.ofFn (inputs x) = List.ofFn x ++ [x 4 || x 6] := by
  rw [List.ofFn_succ_last]
  simp only [inputs,Fin.snoc_castSucc,Fin.snoc_last]

private theorem extended_eq (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (extended x b) = List.ofFn (inputs x) ++ [b] := by
  rw [List.ofFn_succ_last]
  simp only [extended,Fin.snoc_castSucc,Fin.snoc_last]

private def read (i : ℕ) (x : Fin 9 → Bool) : Bool := (List.ofFn (inputs x)).getD i false

private theorem get_input {m : ℕ} (f : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn f).getD i false = f ⟨i,h⟩ := by simp [List.getD_eq_getElem?_getD,h]

private theorem read_lt (i : ℕ) (h : i < 10) (x : Fin 9 → Bool) :
    read i x = inputs x ⟨i,h⟩ := get_input (inputs x) i h

private theorem read_ge (i : ℕ) (h : 10 ≤ i) (x : Fin 9 → Bool) :
    read i x = false := List.getD_eq_default _ _ (by simpa using h)

def evalOr (ops : List ℕ) (x : Fin 9 → Bool) : Bool :=
  GateOp.or.eval (ops.map (fun i => (List.ofFn (inputs x)).getD i false))

theorem classify (ops : List ℕ) (arity : ops.length ≤ 2) : Signal (evalOr ops) := by
  rcases ops with _ | ⟨i, _ | ⟨j, _ | ⟨k,rest⟩⟩⟩
  · exact Or.inl fun _ => rfl
  · by_cases h : i < 10
    · exact Or.inr (Or.inl ⟨⟨i,h⟩,fun x => by simpa [evalOr,GateOp.eval,read] using read_lt i h x⟩)
    · exact Or.inl fun x => by simpa [evalOr,GateOp.eval,read] using read_ge i (by omega) x
  · have eq (x : Fin 9 → Bool) : evalOr [i,j] x = (read i x || read j x) := by simp [evalOr,GateOp.eval,read]
    by_cases hi : i < 10 <;> by_cases hj : j < 10
    · rcases lt_trichotomy i j with h | rfl | h
      · exact Or.inr (Or.inr ⟨⟨i,hi⟩,⟨j,hj⟩,h,fun x => by rw [eq, read_lt i hi,read_lt j hj]⟩)
      · exact Or.inr (Or.inl ⟨⟨i,hi⟩,fun x => by simp [eq,read_lt i hi]⟩)
      · exact Or.inr (Or.inr ⟨⟨j,hj⟩,⟨i,hi⟩,h,fun x => by rw [eq, read_lt i hi,read_lt j hj,Bool.or_comm]⟩)
    · exact Or.inr (Or.inl ⟨⟨i,hi⟩,fun x => by simp [eq,read_lt i hi,read_ge j (by omega)]⟩)
    · exact Or.inr (Or.inl ⟨⟨j,hj⟩,fun x => by simp [eq,read_lt j hj,read_ge i (by omega)]⟩)
    · exact Or.inl fun x => by simp [eq,read_ge i (by omega),read_ge j (by omega)]
  · simp at arity

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w

private theorem preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map (fun j => w.getD j false))
    change (run gs (w ++ [b])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem stripTwo (C : Circuit) (legal : FanInTwo C)
    (wire : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6))
    (second : C.gates[1]?.map (fun g => g.op) = some GateOp.or) :
    ∃ (b : (Fin 9 → Bool) → Bool) (D : Circuit), Signal b ∧ D.gates = C.gates.drop 2 ∧
      D.output = C.output ∧ D.size + 2 = C.size ∧ FanInTwo D ∧
      ∀ x : Fin 9 → Bool, circuitFun 11 D (extended x (b x)) = circuitFun 9 C x := by
  obtain ⟨gs,out⟩ := C
  rcases gs with _ | ⟨g, _ | ⟨h,gs⟩⟩
  · simp at second
  · simp at second
  · have hop : h.op = GateOp.or := by simpa using second
    have arity := (legal h (by simp)).2
    refine ⟨evalOr h.inputs,⟨gs,out⟩,classify _ arity,rfl,rfl,?_,?_,?_⟩
    · simp [Circuit.size]
    · intro z hz
      exact legal z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
    · intro x
      let first := g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))
      let w := List.ofFn x ++ [first]
      let b := h.op.eval (h.inputs.map fun i => w.getD i false)
      have h9 := wire x
      change (run (h::gs) w).getD 9 false = _ at h9
      rw [preserves _ _ _ (by simp [w])] at h9
      have hfirst : first = (x 4 || x 6) := by simpa [w,List.getD_eq_getElem?_getD] using h9
      have hw : w = List.ofFn (inputs x) := by rw [inputs_eq]; exact congrArg (fun v : Bool => List.ofFn x ++ [v]) hfirst
      have hb : b = evalOr h.inputs x := by dsimp [b,evalOr]; rw [hop,hw]
      change (run gs (List.ofFn (extended x (evalOr h.inputs x)))).getD out false =
        (run gs (w ++ [b])).getD out false
      rw [extended_eq,hw,hb]

end PEqualNP.Outside.L_meta_4439_aux.Prefix

namespace PEqualNP.Outside.L_meta_4439_aux.Prefix

def inputSupport : Fin 10 → Finset (Fin 9) :=
  Fin.lastCases {4,6} (fun i => {i})

def anyOn (S : Finset (Fin 9)) (x : Fin 9 → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

private theorem supportValue (x : Fin 9 → Bool) (i : Fin 10) : inputs x i = anyOn (inputSupport i) x := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [inputs, Fin.snoc_last,inputSupport,Fin.lastCases_last]
    change (x 4 || x 6) = anyOn ({4,6} : Finset (Fin 9)) x
    apply Bool.eq_iff_iff.mpr
    simp [anyOn]
  · simp only [inputs,Fin.snoc_castSucc,inputSupport,Fin.lastCases_castSucc]
    simp [anyOn]

theorem any_union (s t : Finset (Fin 9)) (x : Fin 9 → Bool) :
    anyOn (s ∪ t) x = (anyOn s x || anyOn t x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [anyOn, decide_eq_true_eq, Finset.mem_union, Bool.or_eq_true]
  grind

def supports : Finset (Finset (Fin 9)) :=
  insert ∅ ((Finset.univ.image inputSupport) ∪
    (Finset.univ.image fun p : Fin 10 × Fin 10 => inputSupport p.1 ∪ inputSupport p.2))

theorem support_iff (b : (Fin 9 → Bool) → Bool) :
    Signal b ↔ ∃ S ∈ supports, b = anyOn S := by
  constructor
  · rintro (zero | ⟨i,single⟩ | ⟨i,j,_,pair⟩)
    · exact ⟨∅,Finset.mem_insert_self .., funext fun x => by simp [zero,anyOn]⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
        funext fun x => (single x).trans (supportValue x i)⟩
    · refine ⟨_,Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i,j)))),?_⟩
      exact funext fun x => by rw [pair,any_union,← supportValue,← supportValue]
  · rintro ⟨S,mem,rfl⟩
    rcases Finset.mem_insert.mp mem with rfl | mem
    · exact Or.inl fun x => by simp [anyOn]
    rcases Finset.mem_union.mp mem with single | pairs
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp single
      exact Or.inr (Or.inl ⟨i,fun x => (supportValue x i).symm⟩)
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp pairs
    rcases lt_trichotomy i j with h | rfl | h
    · exact Or.inr (Or.inr ⟨i,j,h,fun x => by simp only [any_union,← supportValue]⟩)
    · exact Or.inr (Or.inl ⟨i,fun x => by simp [← supportValue]⟩)
    · exact Or.inr (Or.inr ⟨j,i,h,fun x => by simp only [any_union,← supportValue]; rw [Bool.or_comm]⟩)

end PEqualNP.Outside.L_meta_4439_aux.Prefix

-- Input relabeling from the checked L-meta-548 proof, Apache-2.0.
namespace PEqualNP.Outside.L_meta_4439_aux.Prefix.Rename
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4439_aux.Prefix.Rename

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4439_aux.Prefix

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def sigma : Fin 4 → Fin 9 → Fin 9 :=
  ![![0,1,2,3,4,5,6,7,8],
   ![1,0,5,8,6,2,4,7,3],
   ![3,8,5,0,4,2,6,7,1],
   ![8,3,2,1,6,5,4,7,0]]

def reps : List ℕ := [0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208]

def ofMask (m : ℕ) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => m.testBit i.val = true)

def maskValue (m : ℕ) (x : Fin 9 → Bool) : Bool :=
  decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true)

theorem maskValue_eq (m : ℕ) (x : Fin 9 → Bool) : anyOn (ofMask m) x = maskValue m x := by
  simp [ofMask,maskValue,anyOn]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem orbit_complete : ∀ S ∈ supports, ∃ k : Fin 4, ∃ m ∈ reps, S.image (sigma k) = ofMask m := by
  decide +kernel

private theorem target_perm (k : Fin 4) (x : Fin 9 → Bool) : target (x ∘ sigma k) = target x := by
  fin_cases k
  · rfl
  · change (x 1 && x 0 || x 0 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 1 || x 1 && x 2 || x 0 && x 4 || x 5 && x 7 || x 8 && x 3 || x 2 && x 7 || x 4 && x 3 || x 3 && x 2) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    ac_rfl
  · change (x 3 && x 8 || x 8 && x 5 || x 5 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 || x 8 && x 6 || x 5 && x 7 || x 0 && x 1 || x 2 && x 7 || x 6 && x 1 || x 1 && x 2) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    ac_rfl
  · change (x 8 && x 3 || x 3 && x 2 || x 2 && x 1 || x 1 && x 6 || x 6 && x 8 || x 8 && x 5 || x 3 && x 4 || x 2 && x 7 || x 1 && x 0 || x 5 && x 7 || x 4 && x 0 || x 0 && x 5) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    ac_rfl

private theorem header_perm (k : Fin 4) (x : Fin 9 → Bool) :
    ((x ∘ sigma k) 4 || (x ∘ sigma k) 6) = (x 4 || x 6) := by
  fin_cases k <;> simp [sigma,Bool.or_comm]

private theorem any_image (k : Fin 4) (S : Finset (Fin 9)) (x : Fin 9 → Bool) :
    anyOn (S.image (sigma k)) x = anyOn S (x ∘ sigma k) := by
  apply Bool.eq_iff_iff.mpr
  simp [anyOn]

def sigma10 (k : Fin 4) : Fin 10 → Fin 10 :=
  Fin.lastCases (Fin.last 9) (fun j => (sigma k j).castSucc)

def sigma11 (k : Fin 4) : Fin 11 → Fin 11 :=
  Fin.lastCases (Fin.last 10) (fun j => (sigma10 k j).castSucc)

private theorem inputs_perm (k : Fin 4) (x : Fin 9 → Bool) (j : Fin 10) :
    inputs x (sigma10 k j) = inputs (x ∘ sigma k) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [inputs,sigma10,Fin.lastCases_last,Fin.snoc_last,header_perm]
  · simp only [inputs,sigma10,Fin.lastCases_castSucc,Fin.snoc_castSucc,Function.comp_apply]

private theorem extension_perm (k : Fin 4) (S : Finset (Fin 9)) (x : Fin 9 → Bool) :
    (extended x (anyOn (S.image (sigma k)) x)) ∘ sigma11 k =
      extended (x ∘ sigma k) (anyOn S (x ∘ sigma k)) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Function.comp_apply,extended,sigma11,Fin.lastCases_last,Fin.snoc_last,any_image]
  · simp only [Function.comp_apply,extended,sigma11,Fin.lastCases_castSucc,Fin.snoc_castSucc,inputs_perm]

def Tail (S : Finset (Fin 9)) (s : ℕ) : Prop :=
  ∃ D : Circuit, FanInTwo D ∧ D.size ≤ s ∧
    ∀ x : Fin 9 → Bool, circuitFun 11 D (extended x (anyOn S x)) = target x

theorem transport {S : Finset (Fin 9)} {s : ℕ} (k : Fin 4) (h : Tail S s) :
    Tail (S.image (sigma k)) s := by
  obtain ⟨D,legal,sz,hd⟩ := h
  let D' := Rename.relabel 11 11 (sigma11 k) D
  refine ⟨D',?_,?_,?_⟩
  · intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    exact ⟨(legal z hz).1,by simpa [Rename.relGate] using (legal z hz).2⟩
  · simpa [D',Rename.relabel,Circuit.size] using sz
  · intro x
    let y := extended x (anyOn (S.image (sigma k)) x)
    have val : circuitFun 11 D' y = circuitFun 11 D (y ∘ sigma11 k) :=
      (Rename.rel_fold 11 11 (sigma11 k) D.gates _ _ (Rename.rel_init 11 11 (sigma11 k) y)).2.2 D.output
    rw [val,show y ∘ sigma11 k = _ from extension_perm k S x,hd,target_perm]

theorem representativeTail {S : Finset (Fin 9)} (mem : S ∈ supports) {s : ℕ} (h : Tail S s) :
    ∃ m ∈ reps, Tail (ofMask m) s := by
  obtain ⟨k,m,hm,eq⟩ := orbit_complete S mem
  exact ⟨m,hm,eq ▸ transport k h⟩

end PEqualNP.Outside.L_meta_4439_aux.Prefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4439_aux.Prefix

theorem canonicalTail (C : Circuit) (legal : FanInTwo C)
    (wire : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6))
    (spec : circuitFun 9 C = target)
    (second : C.gates[1]?.map (fun g => g.op) = some GateOp.or) (small : C.size ≤ 15) :
    ∃ m ∈ reps, ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧ ∀ x : Fin 9 → Bool,
      circuitFun 11 D (Fin.snoc (Fin.snoc x (x 4 || x 6)) (maskValue m x)) = target x := by
  obtain ⟨b,D,classB,_,_,sz,ok,val⟩ := stripTwo C legal wire second
  obtain ⟨S,mem,rfl⟩ := (support_iff b).1 classB
  have tail : Tail S 13 := ⟨D,ok,by omega,fun x => (val x).trans (congrFun spec x)⟩
  obtain ⟨m,hm,D',legal',small',out⟩ := representativeTail mem tail
  exact ⟨m,hm,D',legal',small',fun x => by simpa only [extended,inputs,maskValue_eq] using out x⟩

end PEqualNP.Outside.L_meta_4439_aux.Prefix

open PEqualNP.Outside.L_meta_4439_aux.Prefix

theorem PEqualNP.Outside.L_meta_4439 :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → x2.size ≤ (15 : ℕ) → ∃ x8 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (16 : ℕ), (128 : ℕ), (80 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size ≤ (13 : ℕ) ∧ ∀ (x10 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x9 (Fin.snoc (Fin.snoc x10 (x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x11 : Fin (9 : ℕ)), x8.testBit ↑x11 = Bool.true ∧ x10 x11 = Bool.true))) = x1 x10 := by
  intro f C legal wire spec second small
  have same : PEqualNP.Outside.L_meta_4439_aux.Prefix.target = f := by
    change PEqualNP.Outside.L_meta_4439_aux.Prefix.target = (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    decide +kernel
  obtain ⟨m,mem,D,ok,bound,works⟩ := canonicalTail C legal wire (spec.trans same.symm) second small
  exact ⟨m,mem,D,ok,bound,fun x => (works x).trans (congrFun same x)⟩
