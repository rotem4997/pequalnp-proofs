import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2504_732
    (paidBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 13 ≤ C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (ordinary : ¬ HasCircuitSize 9 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 14)
    (monotoneCase : ∀ C : Circuit, Monotone2 C → C.size = 14 → C.output = 23 →
      C.gates.countP (fun g => (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs).any
        fun i => decide (i=6)) = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (oneNegation : ∀ C : Circuit, FanInTwo C → C.size = 14 → C.output = 23 →
      C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) = 1 →
      C.gates.countP (fun g => (if g.op.eval [false,false] = true then g.inputs.take 1 else g.inputs).any
        fun i => decide (i=6)) = 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  intro reads bank base C fan size readers low
  by_contra no
  have high (y : Fin 8 → Bool) : C.eval (bank true y) = (base y || y 0 || y 3) := by
    by_contra bad
    exact no ⟨y,bad⟩
  let row := fun (x : Fin 9 → Bool) => (![x 1,x 0,x 5,x 8,x 2,x 4,x 7,x 3] : Fin 8 → Bool)
  let f := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have order : ∀ x : Fin 9 → Bool, bank (x 6) (row x) = List.ofFn x ++ [x 0 || x 6] := by
    dsimp only [bank,row]
    decide +kernel
  have truth : ∀ x : Fin 9 → Bool,
      (if x 6 then base (row x) || row x 0 || row x 3 else base (row x)) = f x := by
    dsimp only [base,row,f]
    decide +kernel
  have agrees (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 6]) = f x := by
    rw [← order x, ← truth x]
    cases b : x 6 with
    | false => exact low (row x)
    | true => exact high (row x)
  let gate : Gate := ⟨.or,[0,6]⟩
  let full := fun (gs : List Gate) (o : ℕ) => Circuit.mk (gate :: gs) o
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have legal (gs : List Gate) (o : ℕ) (h : FanInTwo ⟨gs,o⟩) : FanInTwo (full gs o) := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hm
    · simp [gate]
    · exact h g hm
  have fullEval (gs : List Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (full gs o).eval (List.ofFn x) = (Circuit.mk gs o).eval (List.ofFn x ++ [x 0 || x 6]) := by
    have head (y : Fin 9 → Bool) : step (List.ofFn y) gate = List.ofFn y ++ [y 0 || y 6] := by
      change List.ofFn y ++ [[(List.ofFn y).getD 0 false,(List.ofFn y).getD 6 false].any id] = _
      simp [List.getD_eq_getElem?_getD]
    change (gs.foldl step (step (List.ofFn x) gate)).getD o false = _
    rw [head]
    rfl
  have len : C.gates.length = 14 := by
    change C.gates.length ≤ 14 at size
    by_contra h
    apply ordinary
    exact ⟨_,legal _ _ fan, by change (gate :: C.gates).length ≤ 14; simp; omega,
      fun x => (fullEval _ _ x).trans (agrees x)⟩
  have lengths (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have out : C.output = 23 := by
    by_contra different
    have ne : C.gates ≠ [] := fun h => by simp [h] at len
    obtain ⟨gs,last,parts⟩ : ∃ gs last, C.gates=gs++[last] := ⟨_,_,(List.dropLast_concat_getLast ne).symm⟩
    have gl : gs.length = 13 := by simp [parts] at len; omega
    have hf : FanInTwo ⟨gs,C.output⟩ := by
      intro g hg; apply fan g; simp [parts,hg]
    apply ordinary
    refine ⟨_,legal _ _ hf,by change (gate :: gs).length ≤ 14; simp [gl],?_⟩
    intro x
    rw [fullEval]
    let u := List.ofFn x ++ [x 0 || x 6]
    have wl : (gs.foldl step u).length = 23 := by rw [lengths,gl]; simp [u]
    have eq := agrees x
    change (C.gates.foldl step u).getD C.output false = _ at eq
    rw [parts,List.foldl_append] at eq
    change (gs.foldl step u ++ [_]).getD C.output false = _ at eq
    change (gs.foldl step u).getD C.output false = _
    by_cases lt : C.output < 23
    · rwa [List.getD_append _ _ _ _ (by omega)] at eq
    · rw [List.getD_eq_default _ _ (by omega)]
      rw [List.getD_eq_default _ _ (by simp [wl]; omega)] at eq
      exact eq
  have uniqueReader : C.gates.countP reads = 1 := by
    by_contra hn
    have nz : C.gates.countP reads = 0 := by omega
    have unused (g : Gate) (hg : g ∈ C.gates) : reads g ≠ true := by
      intro h
      have pos : 0 < C.gates.countP reads := List.countP_pos_iff.mpr ⟨g,hg,h⟩
      omega
    have stable (g : Gate) (hg : g ∈ C.gates) (u v : List Bool)
        (eq : ∀ i, i ≠ 6 → u.getD i false = v.getD i false) :
        g.op.eval (g.inputs.map fun i => u.getD i false) = g.op.eval (g.inputs.map fun i => v.getD i false) := by
      let ins := if g.op.eval [false,false]=true then g.inputs.take 1 else g.inputs
      have reduce (l : List Bool) : g.op.eval (g.inputs.map fun i => l.getD i false) =
          g.op.eval (ins.map fun i => l.getD i false) := by
        obtain ⟨op,_⟩ := fan g hg
        rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not by simpa using op) with e | e | e
        · dsimp only [ins]; rw [e]; rfl
        · dsimp only [ins]; rw [e]; rfl
        · dsimp only [ins]; rw [e]; cases g.inputs <;> rfl
      rw [reduce u, reduce v]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      apply eq i
      intro e
      exact unused g hg (List.any_eq_true.mpr ⟨i,hi,decide_eq_true e⟩)
    have run (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ C.gates) (u v : List Bool) (ll : u.length=v.length)
        (eq : ∀ i, i≠6 → u.getD i false=v.getD i false) :
        ∀ i, i≠6 → (gs.foldl step u).getD i false = (gs.foldl step v).getD i false := by
      induction gs generalizing u v with
      | nil => exact eq
      | cons g gs ih =>
        have ev := stable g (sub _ List.mem_cons_self) u v eq
        apply ih (fun a ha => sub _ (List.mem_cons_of_mem _ ha)) (step u g) (step v g) (by simp [step,ll])
        intro i hi
        by_cases lt : i < u.length
        · dsimp only [step]
          rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (by omega)]
          exact eq i hi
        · dsimp only [step]
          rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),ll,ev]
    let y : Fin 8 → Bool := fun i => decide (i=1 ∨ i=3)
    have same : ∀ i : Fin 10, i.val≠6 → (bank false y).getD i.val false = (bank true y).getD i.val false := by
      dsimp only [bank,y]
      decide +kernel
    have eq (i : ℕ) (hi : i ≠ 6) : (bank false y).getD i false = (bank true y).getD i false := by
      by_cases h : i < 10
      · exact same ⟨i,h⟩ hi
      · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
            List.getD_eq_default _ _ (by change 10 ≤ i; omega)]
    have val : C.eval (bank false y) = C.eval (bank true y) :=
      run C.gates (fun _ h => h) (bank false y) (bank true y) rfl eq C.output (by omega)
    rw [low y,high y] at val
    exact (by decide +kernel : (base y) ≠ (base y || y 0 || y 3)) val
  let neg : Gate → Bool := fun g => GateOp.rec false false true (fun _ => false) false g.op
  let paid : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  have account (gs : List Gate) : gs.countP paid + gs.countP neg = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases g with | mk op ins => cases op <;> simp_all [neg,paid] <;> omega
  have total : C.gates.countP paid + C.gates.countP neg = C.size := account C.gates
  have count : 13 ≤ C.gates.countP paid := paidBound C fan agrees
  by_cases z : C.gates.countP neg = 0
  · have mono : Monotone2 C := by
      intro g hg
      obtain ⟨op,arity⟩ := fan g hg
      rcases (show g.op = .and ∨ g.op = .or ∨ g.op = .not by simpa using op) with e | e | e
      · exact ⟨by simp [e], arity⟩
      · exact ⟨by simp [e], arity⟩
      · have hn : neg g = true := by simp [neg,e]
        have pos : 0 < C.gates.countP neg := List.countP_pos_iff.mpr ⟨g,hg,hn⟩
        omega
    obtain ⟨x,ne⟩ := monotoneCase C mono len out uniqueReader
    exact ne (agrees x)
  · obtain ⟨x,ne⟩ := oneNegation C fan len out (by change C.gates.countP neg = 1; omega) uniqueReader
    exact ne (agrees x)
