import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2521_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Row := Fin 9 → Bool
abbrev RowSet := Finset Row

def source (A : RowSet) : List RowSet :=
  (List.ofFn fun j : Fin 9 => A.filter (fun x => x j=true)) ++ [∅]

-- Every wire denotes the subset of sampled rows on which it is true.
def gateSet (A : RowSet) (w : List RowSet) (g : Gate) : RowSet :=
  let rd := fun i => w.getD i ∅
  match g.op,g.inputs with
  | .and, [] => A \ ∅
  | .and, [a] => rd a
  | .and, a::b::_ => rd a ∩ rd b
  | .or, [] => ∅
  | .or, [a] => rd a
  | .or, a::b::_ => rd a ∪ rd b
  | .not, [] => A \ ∅
  | .not, a::_ => A \ rd a
  | _,_ => ∅

def hist (A : RowSet) : List Gate → List RowSet → List RowSet
  | [], _ => []
  | g::gs, w => let v := gateSet A w g; v :: hist A gs (w++[v])

def Good (g : Gate) : Prop :=
  (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2

def choice (A : RowSet) (w : List RowSet) (v : RowSet) : Prop :=
  ∃ a b : ℕ, v = w.getD a ∅ ∪ w.getD b ∅ ∨ v = w.getD a ∅ ∩ w.getD b ∅ ∨
    v = A \ w.getD a ∅

theorem choice_calc (A : RowSet) (w : List RowSet) (g : Gate) (ok : Good g) :
    choice A w (gateSet A w g) := by
  -- The first absent index denotes the empty set even when no input is read.
  obtain ⟨op,ins⟩ := g
  rcases ok with ⟨ops,len⟩
  change op=.and ∨ op=.or ∨ op=.not at ops
  change ins.length≤2 at len
  cases ins with
  | nil =>
    refine ⟨w.length,w.length,?_⟩
    rcases ops with rfl|rfl|rfl <;> simp [gateSet]
  | cons a tail =>
    cases tail with
    | nil =>
      refine ⟨a,a,?_⟩
      rcases ops with rfl|rfl|rfl <;> simp [gateSet]
    | cons b rest =>
      refine ⟨a,b,?_⟩
      rcases ops with rfl|rfl|rfl <;> simp [gateSet]

theorem hist_length (A : RowSet) (gs : List Gate) (w : List RowSet) : (hist A gs w).length=gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [hist,ih]

theorem hist_choice (A : RowSet) (gs : List Gate) (w : List RowSet) (ok : ∀ g∈gs, Good g) :
    ∀ j < (hist A gs w).length, choice A (w++(hist A gs w).take j) ((hist A gs w).getD j ∅) := by
  induction gs generalizing w with
  | nil => simp [hist]
  | cons g gs ih =>
    intro j hj
    cases j with
    | zero => simpa [hist] using choice_calc A w g (ok g List.mem_cons_self)
    | succ j =>
      let v := gateSet A w g
      have hj' : j<(hist A gs (w++[v])).length := by simpa [hist,v] using hj
      have h := ih (w++[v]) (fun q hq => ok q (List.mem_cons_of_mem _ hq)) j hj'
      simpa [hist,v,List.append_assoc,List.getD_eq_getElem?_getD] using h

theorem read_map (w : List RowSet) (x : Row) (i : ℕ) :
    (w.map (fun s => decide (x∈s))).getD i false = decide (x∈w.getD i ∅) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp

theorem mem_calc (A : RowSet) (x : Row) (hx : x∈A) (w : List RowSet) (g : Gate) (ok : Good g) :
    decide (x∈gateSet A w g) = g.op.eval (g.inputs.map fun i => decide (x∈w.getD i ∅)) := by
  rcases g with ⟨op,ins⟩
  rcases ok with ⟨ops,len⟩
  change op=.and ∨ op=.or ∨ op=.not at ops
  change ins.length≤2 at len
  match ins with
  | [] => rcases ops with rfl|rfl|rfl <;> simp [gateSet,GateOp.eval,hx]
  | [a] => rcases ops with rfl|rfl|rfl <;> simp [gateSet,GateOp.eval,hx]
  | [a,b] => rcases ops with rfl|rfl|rfl <;> simp [gateSet,GateOp.eval,hx]
  | _::_::_::_ => simp at len

theorem evaluate (A : RowSet) (x : Row) (hx : x∈A) (gs : List Gate) (w : List RowSet)
    (ok : ∀ g∈gs, Good g) :
    (w ++ hist A gs w).map (fun s => decide (x∈s)) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
        (w.map (fun s => decide (x∈s))) := by
  induction gs generalizing w with
  | nil => simp [hist]
  | cons g gs ih =>
    let v := gateSet A w g
    have reassoc : w++hist A (g::gs) w = (w++[v])++hist A gs (w++[v]) := by simp [hist,v]
    rw [reassoc, ih (w++[v]) (fun q hq => ok q (List.mem_cons_of_mem _ hq)),List.foldl_cons]
    simp only [List.map_append,List.map_cons,List.map_nil,read_map]
    rw [show decide (x∈v)=_ from mem_calc A x hx w g (ok g List.mem_cons_self)]

theorem source_bits (A : RowSet) (x : Row) (hx : x∈A) :
    (source A).map (fun s => decide (x∈s)) = List.ofFn x ++ [false] := by
  simp [source,hx]

end PEqualNP.Outside.L_meta_2521_aux

open PEqualNP.Outside.L_meta_2521_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2521 :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ) → Bool)),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∃ (x4 : List (Finset (Fin (9 : ℕ) → Bool))),       have x5 : ℕ → List (Finset (Fin (9 : ℕ) → Bool)) := fun (x5 : ℕ) => (List.ofFn fun (x6 : Fin (9 : ℕ)) => {x7 ∈ x2 | x7 x6 = Bool.true}) ++ [∅] ++ List.take x5 x4;       x4.length = x1.size ∧         (∀ x6 < x4.length,             have x8 : ℕ → Finset (Fin (9 : ℕ) → Bool) := fun (x8 : ℕ) => (x5 x6).getD x8 ∅;             ∃ (x9 : ℕ) (x10 : ℕ), x4.getD x6 ∅ = x8 x9 ∪ x8 x10 ∨ x4.getD x6 ∅ = x8 x9 ∩ x8 x10 ∨ x4.getD x6 ∅ = x2 \ x8 x9) ∧           ∀ x6 ∈ x2, x1.eval (List.ofFn x6 ++ [Bool.false]) = Bool.true ↔ x6 ∈ (x5 x4.length).getD x1.output ∅ := by
  intro C A hf
  let f := hist A C.gates (source A)
  have good : ∀ g∈C.gates, Good g := hf
  refine ⟨f,hist_length _ _ _,?_,?_⟩
  · intro j hj
    exact hist_choice A C.gates (source A) good j hj
  · intro x hx
    have e := congrArg (fun v : List Bool => v.getD C.output false)
      (evaluate A x hx C.gates (source A) good)
    change ((source A ++ f).map (fun s => decide (x∈s))).getD C.output false =
      (C.wires ((source A).map (fun s => decide (x∈s)))).getD C.output false at e
    rw [read_map,source_bits A x hx] at e
    change C.eval (List.ofFn x ++ [false])=true ↔ x∈(source A++f.take f.length).getD C.output ∅
    rw [List.take_length]
    change (C.wires (List.ofFn x ++ [false])).getD C.output false=true ↔ _
    rw [← e,decide_eq_true_eq]
