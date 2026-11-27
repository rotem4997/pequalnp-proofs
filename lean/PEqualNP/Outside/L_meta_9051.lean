import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9051

open PEqualNP.CircuitLowerBounds PEqualNP.AndCount

def isAndOp (op : GateOp) : Bool :=
  GateOp.casesOn op true false false (fun _ => false) false

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : w < l.length) :
    (l ++ [a]).getD w d = l.getD w d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

lemma getD_snoc_gt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : l.length < w) :
    (l ++ [a]).getD w d = d := by
  rw [List.getD_eq_default]
  simp
  omega

lemma gateValFuel_stable {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d1 d2 : ℕ) (i : Fin A.size), i.val < d1 → i.val < d2 →
      A.gateValFuel U d1 i = A.gateValFuel U d2 i := by
  intro d1
  induction d1 with
  | zero => intro d2 i hi; omega
  | succ d1 ih =>
    intro d2 i h1 h2
    cases d2 with
    | zero => omega
    | succ d2 =>
      simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
      congr 1
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩

lemma gateVal_eq {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin A.size) :
    A.gateVal U i =
      (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateVal U) &&
       AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateVal U)) := by
  unfold AndCountCircuit.gateVal
  have h1 : A.gateValFuel U A.size i = A.gateValFuel U (i.val + 1) i :=
    gateValFuel_stable A U A.size (i.val + 1) i i.isLt (by omega)
  rw [h1]
  simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩

lemma gateValFuel_withOut {n : ℕ} (A : AndCountCircuit n)
    (Bout : Finset (Fin n)) (Fout : Finset (Fin A.size)) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin A.size),
      ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d i =
        A.gateValFuel U d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
    have hfn : ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d =
        A.gateValFuel U d := funext ih
    rw [hfn]

def evalRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    Option (Finset (Fin n) × Finset (Fin A.size)) → Bool
  | none => true
  | some (B, F) => decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, A.gateVal U j = true)

def orRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k))
  | none, _ => none
  | _, none => none
  | some (B1, F1), some (B2, F2) => some (B1 ∪ B2, F1 ∪ F2)

lemma evalRep_orRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n))
    (r1 r2 : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep A U (orRep r1 r2) = (evalRep A U r1 || evalRep A U r2) := by
  cases r1 with
  | none => simp [orRep, evalRep]
  | some p1 =>
    rcases p1 with ⟨B1, F1⟩
    cases r2 with
    | none => simp [orRep, evalRep]
    | some p2 =>
      rcases p2 with ⟨B2, F2⟩
      rw [Bool.eq_iff_iff]
      simp only [orRep, evalRep, decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩)
        · rcases Finset.mem_union.mp hv with h | h
          · exact Or.inl (Or.inl ⟨v, h, hvu⟩)
          · exact Or.inr (Or.inl ⟨v, h, hvu⟩)
        · rcases Finset.mem_union.mp hj with h | h
          · exact Or.inl (Or.inr ⟨j, h, hju⟩)
          · exact Or.inr (Or.inr ⟨j, h, hju⟩)
      · rintro ((⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩) | (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩))
        · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_left _ hj, hju⟩
        · exact Or.inl ⟨v, Finset.mem_union_right _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_right _ hj, hju⟩

def liftRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin (k + 1)))
  | none => none
  | some (B, F) => some (B, F.map Fin.castSuccEmb)

abbrev snocCircuit {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) : AndCountCircuit n where
  size := A.size + 1
  leftVars i := if h : i.val < A.size then A.leftVars ⟨i.val, h⟩ else B1
  leftGates i := if h : i.val < A.size then (A.leftGates ⟨i.val, h⟩).map Fin.castSuccEmb else F1.map Fin.castSuccEmb
  rightVars i := if h : i.val < A.size then A.rightVars ⟨i.val, h⟩ else B2
  rightGates i := if h : i.val < A.size then (A.rightGates ⟨i.val, h⟩).map Fin.castSuccEmb else F2.map Fin.castSuccEmb
  outVars := A.outVars
  outGates := A.outGates.map Fin.castSuccEmb

lemma snocCircuit_wellFormed {n : ℕ} (A : AndCountCircuit n) (hWF : A.WellFormed)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) :
    (snocCircuit A B1 F1 B2 F2).WellFormed := by
  intro i
  by_cases hi : i.val < A.size
  · constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).1 j0 hj0
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).2 j0 hj0
  · have hieq : i.val = A.size := by have : i.val < A.size + 1 := i.isLt; omega
    constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega

lemma snocCircuit_gateVal_castSucc {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    ∀ (k : ℕ) (hk : k < A.size),
      (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.castSucc ⟨k, hk⟩) = A.gateVal U ⟨k, hk⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    rw [gateVal_eq (snocCircuit A B1 F1 B2 F2) U (Fin.castSucc ⟨k, hk⟩), gateVal_eq A U ⟨k, hk⟩]
    simp only [snocCircuit, Fin.val_castSucc, hk, ↓reduceDIte, AndCountCircuit.sideTrue]
    congr 1
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval

lemma snocCircuit_gateVal_last {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.last A.size) =
      (evalRep A U (some (B1, F1)) && evalRep A U (some (B2, F2))) := by
  rw [gateVal_eq]
  simp only [snocCircuit, Fin.val_last, lt_irrefl, ↓reduceDIte, AndCountCircuit.sideTrue, evalRep]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma evalRep_liftRep {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) (r : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep (snocCircuit A B1 F1 B2 F2) U (liftRep r) = evalRep A U r := by
  cases r with
  | none => rfl
  | some p =>
    rcases p with ⟨B, F⟩
    simp only [liftRep, evalRep, decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma any_map_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    (l.map f).any id = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, id]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma step_same_circuit {n : ℕ} (gs : List Gate) (g : Gate) (A : AndCountCircuit n)
    (rep : List (Option (Finset (Fin n) × Finset (Fin A.size))))
    (hlen : rep.length = n + gs.length)
    (hval : ∀ (U : Finset (Fin n)) (w : ℕ),
      (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U (rep.getD w (some (∅, ∅))))
    (rnew : Option (Finset (Fin n) × Finset (Fin A.size)))
    (hnew : ∀ U : Finset (Fin n),
      g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun j : Fin n => decide (j ∈ U))).getD i false) =
        evalRep A U rnew) :
    ∀ (U : Finset (Fin n)) (w : ℕ),
      (run (gs ++ [g]) (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U ((rep ++ [rnew]).getD w (some (∅, ∅))) := by
  intro U w
  rw [run_snoc]
  have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
    rw [run_length, List.length_ofFn]
  rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
  · rw [getD_snoc_lt _ _ _ w (by omega), getD_snoc_lt _ _ _ w (by omega)]
    exact hval U w
  · rw [← hrl, getD_snoc_eq, hrl, ← hlen, getD_snoc_eq]
    exact hnew U
  · rw [getD_snoc_gt _ _ _ w (by omega), getD_snoc_gt _ _ _ w (by omega)]
    simp [evalRep]

lemma build_aux (n : ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (A : AndCountCircuit n) (rep : List (Option (Finset (Fin n) × Finset (Fin A.size)))),
      A.WellFormed ∧
      A.size ≤ gs.countP (fun g => isAndOp g.op) ∧
      rep.length = n + gs.length ∧
      ∀ (U : Finset (Fin n)) (w : ℕ),
        (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
          evalRep A U (rep.getD w (some (∅, ∅))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let A0 : AndCountCircuit n :=
      { size := 0
        leftVars := Fin.elim0
        leftGates := Fin.elim0
        rightVars := Fin.elim0
        rightGates := Fin.elim0
        outVars := ∅
        outGates := ∅ }
    let rep0 : List (Option (Finset (Fin n) × Finset (Fin 0))) :=
      List.ofFn fun i : Fin n => some ({i}, ∅)
    refine ⟨A0, rep0, fun i => Fin.elim0 i, by simp [A0], by simp [rep0], ?_⟩
    intro U w
    simp only [run, List.foldl_nil]
    by_cases hw : w < n
    · rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp [rep0, hw])]
      simp [rep0, evalRep]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_eq_default _ _ (by simp [rep0]; omega)]
      simp [evalRep]
  | append_singleton gs g ih =>
    have hMgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_append_left _ hg')
    obtain ⟨A, rep, hWF, hsz, hlen, hval⟩ := ih hMgs
    obtain ⟨hop, hglen⟩ := hM g (List.mem_append_right _ List.mem_cons_self)
    have hcnt : (gs ++ [g]).countP (fun g' => isAndOp g'.op) =
        gs.countP (fun g' => isAndOp g'.op) + (if isAndOp g.op then 1 else 0) := by
      simp [List.countP_append]
    let getR : ℕ → Option (Finset (Fin n) × Finset (Fin A.size)) :=
      fun u => rep.getD u (some (∅, ∅))
    rcases hop with hand | hor
    · have hisA : isAndOp g.op = true := by simp [isAndOp, hand]
      rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
      · refine ⟨A, rep ++ [none], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval none fun U => by
          simp [hand, hins, GateOp.eval, evalRep]
      · refine ⟨A, rep ++ [getR u], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval (getR u) fun U => by
          simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, id]
          exact hval U u
      · cases hru : getR u with
        | none =>
          refine ⟨A, rep ++ [getR v], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
          exact step_same_circuit gs g A rep hlen hval (getR v) fun U => by
            simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
              List.all_cons, List.all_nil, Bool.and_true, id]
            rw [hval U u, hval U v]
            change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (getR v)
            rw [hru]; simp [evalRep]
        | some p1 =>
          cases hrv : getR v with
          | none =>
            refine ⟨A, rep ++ [some p1], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
            exact step_same_circuit gs g A rep hlen hval (some p1) fun U => by
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (some p1)
              rw [hru, hrv]; simp [evalRep]
          | some p2 =>
            rcases p1 with ⟨B1, F1⟩
            rcases p2 with ⟨B2, F2⟩
            refine ⟨snocCircuit A B1 F1 B2 F2, rep.map liftRep ++ [some (∅, {Fin.last A.size})],
              snocCircuit_wellFormed A hWF B1 F1 B2 F2,
              by show A.size + 1 ≤ _; rw [hcnt, hisA]; simp; omega,
              by simp [hlen]; omega, ?_⟩
            intro U w
            rw [run_snoc]
            have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
              rw [run_length, List.length_ofFn]
            have hmlen : (rep.map liftRep).length = n + gs.length := by rw [List.length_map, hlen]
            rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
            · rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [hval U w]
              rw [List.getD_eq_getElem _ _ (by omega : w < (rep.map liftRep).length), List.getElem_map, evalRep_liftRep]
              rw [List.getD_eq_getElem _ _ (by omega : w < rep.length)]
            · rw [← hrl, getD_snoc_eq, hrl, ← hmlen, getD_snoc_eq]
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) =
                evalRep (snocCircuit A B1 F1 B2 F2) U (some (∅, {Fin.last A.size}))
              rw [hru, hrv]
              simp only [evalRep, Finset.notMem_empty, false_and, exists_false, false_or,
                Finset.mem_singleton, exists_eq_left]
              rw [snocCircuit_gateVal_last]
              simp only [evalRep]
              exact Bool.decide_eq_true.symm
            · rw [getD_snoc_gt _ _ _ w (by omega)]
              rw [getD_snoc_gt _ _ _ w (by omega)]
              simp [evalRep]
      · rw [hins] at hglen; simp at hglen
    · let rnew := g.inputs.foldl (fun acc u => orRep acc (getR u)) (some (∅, ∅))
      have hfold : ∀ (U : Finset (Fin n)) (xs : List ℕ)
          (init : Option (Finset (Fin n) × Finset (Fin A.size))),
          evalRep A U (xs.foldl (fun acc u => orRep acc (getR u)) init) =
            (evalRep A U init || xs.any fun u => evalRep A U (getR u)) := by
        intro U xs
        induction xs with
        | nil => intro init; simp
        | cons a t iht =>
          intro init
          simp only [List.foldl_cons, List.any_cons]
          rw [iht (orRep init (getR a)), evalRep_orRep, Bool.or_assoc]
      refine ⟨A, rep ++ [rnew], hWF, by rw [hcnt]; omega, by simp [hlen]; omega, ?_⟩
      exact step_same_circuit gs g A rep hlen hval rnew fun U => by
        simp only [hor, GateOp.eval]
        dsimp only [rnew]
        rw [hfold U g.inputs (some (∅, ∅))]
        have hemp : evalRep A U (some (∅, ∅)) = false := by simp [evalRep]
        rw [hemp, Bool.false_or]
        exact any_map_congr g.inputs _ _ fun u _ => hval U u

end PEqualNP.Outside.L_meta_9051

theorem PEqualNP.Outside.L_meta_9051 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin x1 → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit x1), x6.WellFormed ∧ x6.Computes x2 ∧ x6.size ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x3.gates := by
  intro n G C hM heval
  obtain ⟨A, rep, hWF, hsz, _, hval⟩ := PEqualNP.Outside.L_meta_9051.build_aux n C.gates hM
  cases hrout : rep.getD C.output (some (∅, ∅)) with
  | none =>
    exfalso
    have h0 := hval ∅ C.output
    rw [hrout] at h0
    have h0' : C.eval (List.ofFn fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n)))) = true := h0
    rw [heval] at h0'
    rcases h0' with ⟨a, _, _, ha, _⟩
    simp at ha
  | some p =>
    rcases p with ⟨Bout, Fout⟩
    let A' : PEqualNP.AndCount.AndCountCircuit n := { A with outVars := Bout, outGates := Fout }
    refine ⟨A', hWF, ?_, hsz⟩
    intro U
    have h1 := hval U C.output
    rw [hrout] at h1
    have h2 : A'.eval U = PEqualNP.Outside.L_meta_9051.evalRep A U (some (Bout, Fout)) := by
      simp only [PEqualNP.AndCount.AndCountCircuit.eval, PEqualNP.Outside.L_meta_9051.evalRep, A',
        PEqualNP.AndCount.AndCountCircuit.gateVal]
      have hgv : ∀ j : Fin A.size,
          ({ A with outVars := Bout, outGates := Fout } : PEqualNP.AndCount.AndCountCircuit n).gateValFuel U A.size j =
            A.gateValFuel U A.size j :=
        PEqualNP.Outside.L_meta_9051.gateValFuel_withOut A Bout Fout U A.size
      simp only [hgv]
      rfl
    rw [h2, ← h1]
    have h3 := heval (fun i : Fin n => decide (i ∈ U))
    change C.eval (List.ofFn fun i : Fin n => decide (i ∈ U)) = true ↔ _
    rw [h3]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, hab⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, b, hab, decide_eq_true ha, decide_eq_true hb⟩
