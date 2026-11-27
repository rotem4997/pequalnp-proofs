import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17124

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Terms (n : ℕ) := List (List (Fin n))

def observe (x : Fin n → Bool) (p : Terms n) : Bool := p.any (fun l => l.all x)

def product (p q : Terms n) : Terms n := p.flatMap fun a => q.map fun b => a ++ b

theorem observeAppend (x : Fin n → Bool) (p q : Terms n) :
    observe x (p ++ q) = (observe x p || observe x q) := by
  simp only [observe, List.any_append]

theorem observeRowProduct (x : Fin n → Bool) (a : List (Fin n)) (q : Terms n) :
    observe x (q.map fun b => a ++ b) = (a.all x && observe x q) := by
  induction q with
  | nil => simp [observe]
  | cons b q ih =>
    have step :
        ((a.all x && b.all x) || (a.all x && observe x q)) =
          (a.all x && (b.all x || observe x q)) := by
      cases h : a.all x <;> simp [h]
    calc
      observe x ((b :: q).map fun b => a ++ b) =
          ((a.all x && b.all x) || observe x (q.map fun b => a ++ b)) := by
        simp only [List.map_cons, observe, List.any_cons, List.all_append]
      _ = (a.all x && (b.all x || observe x q)) := by rw [ih]; exact step
      _ = (a.all x && observe x (b :: q)) := rfl

theorem observeProduct (x : Fin n → Bool) (p q : Terms n) :
    observe x (product p q) = (observe x p && observe x q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change observe x ((q.map fun b => a ++ b) ++ product p q) =
      ((a.all x || observe x p) && observe x q)
    rw [observeAppend, observeRowProduct, ih]
    cases h : observe x q <;> simp [h]

def pureFamily (p : Terms n) : Finset (Finset (Fin n)) := (p.map List.toFinset).toFinset

theorem observe_of_subset (x : Fin n → Bool) (p q : Terms n) (sub : pureFamily p ⊆ pureFamily q)
    (yes : observe x p = true) : observe x q = true := by
  obtain ⟨a, ma, ok⟩ := List.any_eq_true.mp yes
  have ha : a.toFinset ∈ pureFamily p :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ma, rfl⟩)
  obtain ⟨b, mb, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (sub ha))
  apply List.any_eq_true.mpr
  refine ⟨b, mb, List.all_eq_true.mpr ?_⟩
  intro i mi
  have h : i ∈ b.toFinset := List.mem_toFinset.mpr mi
  rw [eq] at h
  exact List.all_eq_true.mp ok i (List.mem_toFinset.mp h)

theorem observe_same (x : Fin n → Bool) (p q : Terms n) (eq : pureFamily p = pureFamily q) :
    observe x p = observe x q := by
  cases hp : observe x p <;> cases hq : observe x q
  · rfl
  · have hn := observe_of_subset x q p (by rw [eq]) hq
    simp [hp] at hn
  · have hn := observe_of_subset x p q (by rw [eq]) hp
    simp [hq] at hn
  · rfl

def allTerms (xs : List (Terms n)) : Terms n := xs.foldr product [[]]
def anyTerms (xs : List (Terms n)) : Terms n := xs.foldr List.append []

theorem allMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (allTerms xs) = (xs.map (observe x)).all id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (product p (allTerms tail)) =
      (observe x p && (tail.map (observe x)).all id)
    rw [observeProduct, ih]

theorem anyMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (anyTerms xs) = (xs.map (observe x)).any id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (p ++ anyTerms tail) =
      (observe x p || (tail.map (observe x)).any id)
    rw [observeAppend, ih]

theorem observedRead (x : Fin n → Bool) (xs : List (Terms n)) (i : ℕ) :
    observe x (xs.getD i []) = (xs.map (observe x)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]


def termGate {n : ℕ} (op : GateOp) (xs : List (Terms n)) : Terms n :=
  match op with
  | .and => allTerms xs
  | .or => anyTerms xs
  | _ => []

theorem gateMatches (x : Fin n → Bool) (g : Gate) (ws : List (Terms n))
    (ops : g.op = .and ∨ g.op = .or) :
    observe x (termGate g.op (g.inputs.map (fun i => ws.getD i []))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe x)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i [])).map (observe x) =
      g.inputs.map (fun i => (ws.map (observe x)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead x ws i
  rcases ops with h | h
  · rw [h]
    change observe x (allTerms _) = _
    rw [allMatches, reads]
    rfl
  · rw [h]
    change observe x (anyTerms _) = _
    rw [anyMatches, reads]
    rfl

def symbolicRun {n : ℕ} : List Gate → List (Terms n) → List (Terms n)
  | [], ws => ws
  | g :: gs, ws => symbolicRun gs (ws ++ [termGate g.op (g.inputs.map (fun i => ws.getD i []))])

theorem runMatches (x : Fin n → Bool) (gs : List Gate) (ws : List (Terms n))
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (symbolicRun gs ws).map (observe x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (observe x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [symbolicRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches x g ws (ops g (by simp))]

def termInput {n : ℕ} (i : Fin n) : Terms n := [[i]]

theorem termInputMatches (x : Fin n → Bool) (i : Fin n) :
    observe x (termInput i) = x i := by
  simp [observe, termInput]

def circuitTerms (n : ℕ) (C : Circuit) : Terms n :=
  (symbolicRun C.gates (List.ofFn termInput)).getD C.output []

theorem circuitMatches (C : Circuit) (x : Fin n → Bool)
    (ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    observe x (circuitTerms n C) = C.eval (List.ofFn x) := by
  have inputs : (List.ofFn termInput).map (observe x) = List.ofFn x := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin n → Bool => List.ofFn f) (funext (termInputMatches x))
  unfold circuitTerms Circuit.eval Circuit.wires
  rw [observedRead, runMatches x C.gates _ ops, inputs]

def witness : Circuit :=
  ⟨[⟨.and, [0, 9]⟩,⟨.and, [15, 14]⟩,⟨.and, [0, 10]⟩,⟨.and, [17, 13]⟩,⟨.and, [0, 11]⟩,⟨.and, [19, 12]⟩,⟨.and, [1, 6]⟩,⟨.and, [21, 14]⟩,⟨.and, [1, 7]⟩,⟨.and, [23, 13]⟩,⟨.and, [1, 8]⟩,⟨.and, [25, 12]⟩,⟨.and, [2, 5]⟩,⟨.and, [27, 14]⟩,⟨.and, [2, 7]⟩,⟨.and, [29, 11]⟩,⟨.and, [2, 8]⟩,⟨.and, [31, 10]⟩,⟨.and, [3, 5]⟩,⟨.and, [33, 13]⟩,⟨.and, [3, 6]⟩,⟨.and, [35, 11]⟩,⟨.and, [3, 8]⟩,⟨.and, [37, 9]⟩,⟨.and, [4, 5]⟩,⟨.and, [39, 12]⟩,⟨.and, [4, 6]⟩,⟨.and, [41, 10]⟩,⟨.and, [4, 7]⟩,⟨.and, [43, 9]⟩,⟨.or, [20, 40]⟩,⟨.or, [26, 40]⟩,⟨.or, [28, 42]⟩,⟨.or, [34, 44]⟩,⟨.or, [16, 32]⟩,⟨.or, [22, 30]⟩,⟨.or, [28, 44]⟩,⟨.or, [30, 32]⟩,⟨.or, [34, 42]⟩,⟨.or, [36, 38]⟩,⟨.or, [42, 44]⟩,⟨.or, [45, 47]⟩,⟨.or, [45, 48]⟩,⟨.or, [46, 51]⟩,⟨.or, [46, 53]⟩,⟨.or, [47, 48]⟩,⟨.or, [52, 59]⟩,⟨.and, [16, 61]⟩,⟨.or, [50, 54]⟩,⟨.or, [63, 58]⟩,⟨.and, [18, 64]⟩,⟨.or, [20, 26]⟩,⟨.and, [66, 60]⟩,⟨.or, [52, 57]⟩,⟨.and, [22, 68]⟩,⟨.or, [49, 54]⟩,⟨.or, [70, 56]⟩,⟨.and, [24, 71]⟩,⟨.or, [28, 34]⟩,⟨.and, [73, 55]⟩,⟨.and, [30, 59]⟩,⟨.and, [32, 57]⟩,⟨.or, [49, 58]⟩,⟨.and, [36, 77]⟩,⟨.or, [50, 56]⟩,⟨.and, [38, 79]⟩,⟨.or, [62, 65]⟩,⟨.or, [81, 67]⟩,⟨.or, [82, 69]⟩,⟨.or, [83, 72]⟩,⟨.or, [84, 74]⟩,⟨.or, [85, 75]⟩,⟨.or, [86, 76]⟩,⟨.or, [87, 78]⟩,⟨.or, [88, 80]⟩], 89⟩

def expected : Terms 15 := [[0,4,5,9,12,14],[0,3,5,9,13,14],[0,4,5,10,12,13],[0,2,5,10,13,14],[0,3,5,11,12,13],[0,2,5,11,12,14],[0,4,6,9,10,14],[0,3,6,9,11,14],[0,4,6,10,11,12],[0,1,6,11,12,14],[0,3,6,10,11,13],[0,1,6,10,13,14],[0,4,7,9,10,13],[0,2,7,10,11,13],[0,4,7,9,11,12],[0,1,7,11,12,13],[0,2,7,9,11,14],[0,1,7,9,13,14],[0,3,8,9,11,12],[0,2,8,10,11,12],[0,3,8,9,10,13],[0,1,8,10,12,13],[0,2,8,9,10,14],[0,1,8,9,12,14],[1,4,5,6,12,14],[1,3,5,6,13,14],[1,4,5,7,12,13],[1,2,5,7,13,14],[1,3,5,8,12,13],[1,2,5,8,12,14],[1,4,6,7,9,14],[1,3,6,8,9,14],[1,4,7,8,9,12],[1,3,7,8,9,13],[1,4,6,7,10,13],[1,2,7,8,10,13],[1,4,6,8,10,12],[1,2,6,8,10,14],[1,3,6,8,11,12],[1,2,7,8,11,12],[1,3,6,7,11,13],[1,2,6,7,11,14],[2,4,5,6,10,14],[2,3,5,6,11,14],[2,4,6,7,10,11],[2,3,6,8,10,11],[2,4,5,7,9,14],[2,3,5,8,9,14],[2,4,7,8,9,10],[2,3,7,8,9,11],[2,4,5,7,11,12],[2,4,5,8,10,12],[2,3,5,8,10,13],[2,3,5,7,11,13],[3,4,5,7,9,13],[3,4,6,7,9,11],[3,4,5,6,10,13],[3,4,6,8,9,10],[3,4,5,6,11,12],[3,4,5,8,9,12]]

set_option maxRecDepth 8000 in
theorem permitted : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or := by
  simp [witness]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 18000000 in
theorem termsMatch : pureFamily (circuitTerms 15 witness) = pureFamily expected := by
  decide +kernel

theorem correctness (x : Fin 15 → Bool) :
    witness.eval (List.ofFn x) = observe x expected :=
  (circuitMatches witness x permitted).symm.trans
    (observe_same x (circuitTerms 15 witness) expected termsMatch)


def officialTerms : Terms 15 := [[0,4,5,9,12,14],[0,3,5,9,13,14],[0,4,5,10,12,13],[0,2,5,10,13,14],[0,3,5,11,12,13],[0,2,5,11,12,14],[0,4,6,9,10,14],[0,3,6,9,11,14],[0,4,6,10,11,12],[0,1,6,11,12,14],[0,3,6,10,11,13],[0,1,6,10,13,14],[0,4,7,9,10,13],[0,2,7,10,11,13],[0,4,7,9,11,12],[0,1,7,11,12,13],[0,2,7,9,11,14],[0,1,7,9,13,14],[0,3,8,9,11,12],[0,2,8,10,11,12],[0,3,8,9,10,13],[0,1,8,10,12,13],[0,2,8,9,10,14],[0,1,8,9,12,14],[1,4,5,6,12,14],[1,3,5,6,13,14],[1,4,5,7,12,13],[1,2,5,7,13,14],[1,3,5,8,12,13],[1,2,5,8,12,14],[1,4,6,7,9,14],[1,3,6,8,9,14],[1,4,7,8,9,12],[1,3,7,8,9,13],[1,4,6,7,10,13],[1,2,7,8,10,13],[1,4,6,8,10,12],[1,2,6,8,10,14],[1,3,6,8,11,12],[1,2,7,8,11,12],[1,3,6,7,11,13],[1,2,6,7,11,14],[2,4,5,6,10,14],[2,3,5,6,11,14],[2,4,6,7,10,11],[2,3,6,8,10,11],[2,4,5,7,9,14],[2,3,5,8,9,14],[2,4,7,8,9,10],[2,3,7,8,9,11],[2,4,5,7,11,12],[2,4,5,8,10,12],[2,3,5,8,10,13],[2,3,5,7,11,13],[3,4,5,7,9,13],[3,4,6,7,9,11],[3,4,5,6,10,13],[3,4,6,8,9,10],[3,4,5,6,11,12],[3,4,5,8,9,12]]

set_option maxRecDepth 12000 in
theorem sameTerms : pureFamily expected = pureFamily officialTerms := by
  decide +kernel

end PEqualNP.Outside.L_meta_17124

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17124 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.L_meta_17124 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (x 0 && x 4 && x 5 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 5 && x 9 && x 13 && x 14) || (x 0 && x 4 && x 5 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 5 && x 10 && x 13 && x 14) || (x 0 && x 3 && x 5 && x 11 && x 12 && x 13) || (x 0 && x 2 && x 5 && x 11 && x 12 && x 14) || (x 0 && x 4 && x 6 && x 9 && x 10 && x 14) || (x 0 && x 3 && x 6 && x 9 && x 11 && x 14) || (x 0 && x 4 && x 6 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 3 && x 6 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 6 && x 10 && x 13 && x 14) || (x 0 && x 4 && x 7 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 7 && x 10 && x 11 && x 13) || (x 0 && x 4 && x 7 && x 9 && x 11 && x 12) || (x 0 && x 1 && x 7 && x 11 && x 12 && x 13) || (x 0 && x 2 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 3 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 8 && x 9 && x 12 && x 14) || (x 1 && x 4 && x 5 && x 6 && x 12 && x 14) || (x 1 && x 3 && x 5 && x 6 && x 13 && x 14) || (x 1 && x 4 && x 5 && x 7 && x 12 && x 13) || (x 1 && x 2 && x 5 && x 7 && x 13 && x 14) || (x 1 && x 3 && x 5 && x 8 && x 12 && x 13) || (x 1 && x 2 && x 5 && x 8 && x 12 && x 14) || (x 1 && x 4 && x 6 && x 7 && x 9 && x 14) || (x 1 && x 3 && x 6 && x 8 && x 9 && x 14) || (x 1 && x 4 && x 7 && x 8 && x 9 && x 12) || (x 1 && x 3 && x 7 && x 8 && x 9 && x 13) || (x 1 && x 4 && x 6 && x 7 && x 10 && x 13) || (x 1 && x 2 && x 7 && x 8 && x 10 && x 13) || (x 1 && x 4 && x 6 && x 8 && x 10 && x 12) || (x 1 && x 2 && x 6 && x 8 && x 10 && x 14) || (x 1 && x 3 && x 6 && x 8 && x 11 && x 12) || (x 1 && x 2 && x 7 && x 8 && x 11 && x 12) || (x 1 && x 3 && x 6 && x 7 && x 11 && x 13) || (x 1 && x 2 && x 6 && x 7 && x 11 && x 14) || (x 2 && x 4 && x 5 && x 6 && x 10 && x 14) || (x 2 && x 3 && x 5 && x 6 && x 11 && x 14) || (x 2 && x 4 && x 6 && x 7 && x 10 && x 11) || (x 2 && x 3 && x 6 && x 8 && x 10 && x 11) || (x 2 && x 4 && x 5 && x 7 && x 9 && x 14) || (x 2 && x 3 && x 5 && x 8 && x 9 && x 14) || (x 2 && x 4 && x 7 && x 8 && x 9 && x 10) || (x 2 && x 3 && x 7 && x 8 && x 9 && x 11) || (x 2 && x 4 && x 5 && x 7 && x 11 && x 12) || (x 2 && x 4 && x 5 && x 8 && x 10 && x 12) || (x 2 && x 3 && x 5 && x 8 && x 10 && x 13) || (x 2 && x 3 && x 5 && x 7 && x 11 && x 13) || (x 3 && x 4 && x 5 && x 7 && x 9 && x 13) || (x 3 && x 4 && x 6 && x 7 && x 9 && x 11) || (x 3 && x 4 && x 5 && x 6 && x 10 && x 13) || (x 3 && x 4 && x 6 && x 8 && x 9 && x 10) || (x 3 && x 4 && x 5 && x 6 && x 11 && x 12) || (x 3 && x 4 && x 5 && x 8 && x 9 && x 12)) 76 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [witness, FanInTwo]
  · intro x
    rw [correctness, observe_same x expected officialTerms sameTerms]
    simp only [observe, officialTerms, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.or_false, Bool.and_assoc, Bool.or_assoc]
