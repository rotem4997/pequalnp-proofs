import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2806_29
  (baseline : 
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x, C.eval (X x) ≠ F x)
  (signedCase : 
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    ∀ (j : Fin 9) (C : Circuit), j≠0 → j≠6 → FanInTwo C → C.size ≤ 13 →
    ∃ x, C.eval ((X x).set j.val (!(x j))) ≠ F x)
  (internalCase : 
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    ∀ (j : Fin 9) (C : Circuit) (k : ℕ) (d : Bool), j≠0 → j≠6 → FanInTwo C →
    C.size ≤ 13 → 10 ≤ k → k < 10+C.size →
    (∀ g ∈ C.gates.take (k+1-10), j.val ∉ g.inputs) →
    (∀ x y, (∀ i, i≠j → x i=y i) → F x ≠ F y → (C.wires (X x)).getD k false = !d) →
    ∃ x, let a := (C.wires (X x)).getD k false
         C.eval ((X x).set j.val (if d then x j || a else x j && a)) ≠ F x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 ≤ (10 : ℕ) + x4.size →               x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not →                 x6.inputs.length ≤ (2 : ℕ) →                   ↑x3 ∈ x6.inputs →                     (∀ x16 ∈ List.take (x5 - (10 : ℕ)) x4.gates, ↑x3 ∉ x16.inputs) →                       ∃ (x17 : Fin (9 : ℕ) → Bool),                         have x18 : List Bool := x2 x17;                         x4.eval (x18.set (↑x3) (x6.op.eval (List.map (fun (x19 : ℕ) => if x19 < x5 then (x4.wires x18).getD x19 Bool.false else Bool.false) x6.inputs))) ≠ x1 x17 := by
  have localAnd (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  have localOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let addOr (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
  let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
  let witnessTable : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8, 0, 2, 2, 2, 2, 2, 2, 2, 4, 4, 16, 0, 4, 4, 4, 4, 4, 4, 8, 1, 1, 1, 0, 1, 1, 1, 1, 8, 128, 1, 1, 1, 1, 0, 1, 1, 1, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 32, 4, 4, 4, 4, 0, 4, 4, 8, 8, 8, 32, 8, 8, 8, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 9, 20, 36, 64, 129, 257, 1, 9, 2, 0, 8, 18, 34, 72, 128, 258, 9, 5, 18, 4, 0, 16, 36, 68, 144, 256, 5, 1, 10, 5, 8, 0, 40, 65, 129, 257, 1, 1, 130, 5, 9, 144, 0, 65, 128, 256, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 34, 4, 40, 20, 32, 68, 0, 260, 5, 9, 10, 36, 8, 48, 32, 64, 136, 0, 9]
  let witness (j : Fin 9) (k : Fin 10) (v : Bool) :=
    witnessTable.getD ((if v then 90 else 0) + 10*j.val + k.val) 0

  have maskingRows : ∀ (j : Fin 9) (k : Fin 10) (v : Bool), j ≠ 0 → j ≠ 6 → j.val ≠ k.val →
      let m := witness j k v
      let x := bits m
      let y := bits (m ||| (1 <<< j.val))
      graph x = false ∧ graph y = true ∧
        (addOr x).getD k.val false = v ∧ (addOr y).getD k.val false = v ∧
        (addOr x).set j.val v = (addOr y).set j.val v := by
    decide +kernel

  have preWire (C : Circuit) (xs : List Bool) (n : ℕ) (hn : n<xs.length) :
      (C.wires xs).getD n false = xs.getD n false := by
    obtain ⟨gs,out⟩ := C
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs out).wires (xs ++ [_])).getD n false = _
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hn]

  let reader (C : Circuit) (x : Fin 9 → Bool) (q i : ℕ) :=
    if i<q then (C.wires (addOr x)).getD i false else false

  have rawReader (C : Circuit) (x : Fin 9 → Bool) (q : ℕ) (hq : 10≤q) (k : Fin 10) :
      reader C x q k.val = (addOr x).getD k.val false := by
    simp only [reader,show k.val < q by omega,ite_true]
    exact preWire _ _ _ (by simp [addOr])

  let gateBool (useOr : Bool) := if useOr then GateOp.or else GateOp.and

  have lostRaw (C : Circuit) (j : Fin 9) (k : Fin 10) (d swap : Bool) (q : ℕ) (hq : 10≤q)
      (j0 : j ≠ 0) (j6 : j ≠ 6) (jk : j.val ≠ k.val) :
      let op := gateBool d
      let ins := if swap then [j.val,k.val] else [k.val,j.val]
      ∃ x : Fin 9 → Bool, C.eval ((addOr x).set j.val (op.eval (ins.map (reader C x q)))) ≠ graph x := by
    dsimp only
    let m := witness j k d
    let x := bits m
    let y := bits (m ||| (1 <<< j.val))
    obtain ⟨hX,hY,hkX,hkY,hxy⟩ := maskingRows j k d j0 j6 jk
    have crush (z : Fin 9 → Bool) (hz : (addOr z).getD k.val false = d) :
        (gateBool d).eval ((if swap then [j.val,k.val] else [k.val,j.val]).map (reader C z q)) = d := by
      have hk := (rawReader C z q hq k).trans hz
      cases d <;> cases swap <;> simp [gateBool,localAnd,localOr,hk]
    by_contra! h
    have a := h x
    have b := h y
    rw [crush x hkX,hX] at a
    rw [crush y hkY,hY] at b
    exact Bool.noConfusion (a.symm.trans ((congrArg C.eval hxy).trans b))


  have equalOff {j : Fin 9} {x y : Fin 9 → Bool} (h : ∀ i, i≠j → x i=y i)
      (j0 : j≠0) (j6 : j≠6) (i : ℕ) (ne : i≠j.val) :
      (addOr x)[i]? = (addOr y)[i]? := by
    unfold addOr
    have eq0 := h 0 (Ne.symm j0)
    have eq6 := h 6 (Ne.symm j6)
    by_cases hi : i<9
    · rw [List.getElem?_append_left (by simpa using hi),List.getElem?_append_left (by simpa using hi)]
      simp only [List.getElem?_ofFn,hi, dite_true]
      exact congrArg some (h ⟨i,hi⟩ (fun e => ne (congrArg Fin.val e)))
    · rw [List.getElem?_append_right (show (List.ofFn x).length ≤ i by simpa using Nat.le_of_not_gt hi),
        List.getElem?_append_right (show (List.ofFn y).length ≤ i by simpa using Nat.le_of_not_gt hi),eq0,eq6]
      simp only [List.length_ofFn]

  have eraseSame {j : Fin 9} {x y : Fin 9 → Bool} (h : ∀ i, i≠j → x i=y i)
      (j0 : j≠0) (j6 : j≠6) (b : Bool) :
      (addOr x).set j.val b = (addOr y).set j.val b := by
    apply List.ext_getElem?
    intro i
    by_cases hji : j.val=i
    · subst i
      rw [List.getElem?_set_self (by simp [addOr]; omega),List.getElem?_set_self (by simp [addOr]; omega)]
    · rw [List.getElem?_set_ne hji,List.getElem?_set_ne hji]
      exact equalOff h j0 j6 i (Ne.symm hji)

  let run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

  have wireOff (gs : List Gate) (a b : List Bool) (j : ℕ)
      (len : a.length=b.length) (h : ∀ i, i≠j → a[i]?=b[i]?)
      (hn : ∀ g∈gs, j∉g.inputs) : ∀ i, i≠j → (run gs a)[i]?=(run gs b)[i]? := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      have vals : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have ne : i≠j := fun he => hn g (by simp) (he ▸ hi)
        simp only [List.getD_eq_getElem?_getD,h i ne]
      change ∀ i, i≠j → (run gs (a ++ [_]))[i]?=(run gs (b ++ [_]))[i]?
      rw [vals]
      apply ih
      · simp [len]
      · intro i hi
        by_cases hl : i<a.length
        · rw [List.getElem?_append_left hl,List.getElem?_append_left (by omega),h i hi]
        · rw [List.getElem?_append_right (show a.length ≤ i by omega),
            List.getElem?_append_right (show b.length ≤ i by omega),len]
      · exact fun g hg => hn _ (by simp [hg])

  have readerOff (D : Circuit) (q : ℕ) (j : Fin 9) (j0 : j≠0) (j6 : j≠6)
      (x y : Fin 9 → Bool) (h : ∀ i, i≠j → x i=y i)
      (hq : 10≤q) (upper : q≤10+D.size) (hn : ∀ g∈D.gates.take (q-10), j.val∉g.inputs)
      (i : ℕ) (hi : i≠j.val) : reader D x q i = reader D y q i := by
    by_cases earlier : i<q
    · let gs := D.gates.take (q-10)
      let rest := D.gates.drop (q-10)
      have eq : gs ++ rest = D.gates := List.take_append_drop ..
      have length (z : Fin 9 → Bool) : (run gs (addOr z)).length=q := by
        have extLen (l : List Gate) (w : List Bool) : (run l w).length = w.length+l.length := by
          induction l generalizing w with
          | nil => exact (Nat.add_zero _).symm
          | cons g l ih =>
            change (run l (w ++ [_])).length = _
            rw [ih]; simp; omega
        have := upper
        change q ≤ 10+D.gates.length at this
        simp [extLen, gs,List.length_take,addOr]; omega
      have preserved (z : Fin 9 → Bool) : (D.wires (addOr z)).getD i false = (run gs (addOr z)).getD i false := by
        unfold Circuit.wires
        rw [← eq,List.foldl_append]
        exact preWire ⟨rest,0⟩ _ i (length z ▸ earlier)
      simp only [reader,earlier,ite_true]
      rw [preserved x,preserved y]
      simp only [List.getD_eq_getElem?_getD]
      rw [wireOff gs _ _ _ (by simp [addOr]) (equalOff h j0 j6) hn i hi]
    · simp [reader,earlier]


  have mustToggle (C : Circuit) (j : Fin 9) (j0 : j≠0) (j6 : j≠6)
      (mask : (Fin 9 → Bool) → Bool)
      (ok : ∀ x, C.eval ((addOr x).set j.val (mask x)) = graph x)
      (x y : Fin 9 → Bool) (hxy : ∀ i, i≠j → x i=y i) (changeF : graph x ≠ graph y) :
      mask x ≠ mask y := by
    intro eq
    apply changeF
    rw [← ok x, ← ok y, eq, eraseSame hxy j0 j6]

  have pivotalRows (j : Fin 9) (j0 : j≠0) (j6 : j≠6) :
      ∃ x y : Fin 9 → Bool, (∀ i, i≠j → x i=y i) ∧ graph x≠graph y := by
    have h : ∀ (j : Fin 9), j≠0 → j≠6 →
        let m := witness j 9 false
        (∀ i : Fin 9, i≠j → bits m i = bits (m ||| (1 <<< j.val)) i) ∧
        graph (bits m) ≠ graph (bits (m ||| (1 <<< j.val))) := by decide +kernel
    exact ⟨_,_,h j j0 j6⟩

  have mustPass (C : Circuit) (j : Fin 9) (j0 : j≠0) (j6 : j≠6)
      (q k : ℕ) (kdiff : k≠j.val) (hq : 10≤q) (upper : q≤10+C.size)
      (hn : ∀ g ∈ C.gates.take (q-10), j.val ∉ g.inputs) (d swap : Bool)
      (ok : ∀ x, C.eval ((addOr x).set j.val
        ((gateBool d).eval ((if swap then [j.val,k] else [k,j.val]).map (reader C x q)))) = graph x)
      (x y : Fin 9 → Bool) (off : ∀ i, i≠j → x i=y i) (different : graph x≠graph y) :
      reader C x q k = !d := by
    have hk := readerOff C q j j0 j6 x y off hq upper hn k kdiff
    have toggle := mustToggle C j j0 j6 _ ok x y off different
    by_contra miss
    have value : reader C x q k = d := by
      cases d <;> cases h : reader C x q k <;> simp_all
    have yvalue := hk.symm.trans value
    apply toggle
    cases d <;> cases swap <;> simp [gateBool,localAnd,localOr,value,yvalue]

  have noIgnoredNot (C : Circuit) (j : Fin 9) (j0 : j≠0) (j6 : j≠6)
      (q k : ℕ) (kdiff : k≠j.val) (hq : 10≤q) (upper : q≤10+C.size)
      (hn : ∀ g ∈ C.gates.take (q-10), j.val ∉ g.inputs) :
      ∃ x, C.eval ((addOr x).set j.val (!(reader C x q k))) ≠ graph x := by
    by_contra! all
    obtain ⟨x,y,h,he⟩ := pivotalRows j j0 j6
    have toggle := mustToggle C j j0 j6 _ all x y h he
    exact toggle (congrArg Bool.not (readerOff C q j j0 j6 x y h hq upper hn k kdiff))
  intro F X j C q g j0 j6 hf hs hq hu opOK length inp early
  by_contra! works
  let Coded := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have coded : ∀ x, graph x = Coded x := by decide +kernel
  have fixed : ∀ x, C.eval ((addOr x).set j.val (g.op.eval (g.inputs.map (reader C x q)))) = graph x := fun x => Classical.not_not.mp (works x)
  have self (x : Fin 9 → Bool) : reader C x q j.val=x j := by
    rw [rawReader C x q hq (⟨j.val,by omega⟩ : Fin 10)]
    unfold addOr
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have replaceSelf (x : Fin 9 → Bool) : (addOr x).set j.val (x j) = addOr x := by
    apply List.ext_getElem?
    intro i
    by_cases ji : j.val=i
    · subst i
      rw [List.getElem?_set_self (by simp [addOr]; omega)]
      unfold addOr
      rw [List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp),List.getElem_ofFn]
    · exact List.getElem?_set_ne ji
  have noBase : ¬ ∀ x, C.eval (addOr x)=graph x := by
    obtain ⟨x,hx⟩ := baseline C hf hs
    intro ok
    exact hx ((ok x).trans (coded x))
  have noSigned : ¬ ∀ x, C.eval ((addOr x).set j.val (!(x j)))=graph x := by
    obtain ⟨x,hx⟩ := signedCase j C j0 j6 hf hs
    intro ok
    exact hx ((ok x).trans (coded x))
  have both (k : ℕ) (d swap : Bool) (vals : ∀ x, C.eval ((addOr x).set j.val
        ((gateBool d).eval ((if swap then [j.val,k] else [k,j.val]).map (reader C x q)))) = graph x) : False := by
    have evalFormula (a b : Bool) : (gateBool d).eval (if swap then [a,b] else [b,a]) =
        (if d then a || b else a && b) := by cases d <;> cases swap <;> cases a <;> cases b <;> rfl
    have row (x : Fin 9 → Bool) := vals x
    have evalEq (x : Fin 9 → Bool) : (gateBool d).eval
        ((if swap then [j.val,k] else [k,j.val]).map (reader C x q)) =
        (if d then x j || reader C x q k else x j && reader C x q k) := by
      rw [←self x,←evalFormula]
      cases swap <;> rfl
    by_cases same : k=j.val
    · subst k
      apply noBase
      intro x
      have eq := row x
      rw [evalEq,self] at eq
      cases d <;> simpa [replaceSelf] using eq
    by_cases isRaw : k<10
    · obtain ⟨x,hx⟩ := lostRaw C j ⟨k,isRaw⟩ d swap q hq j0 j6 (Ne.symm same)
      exact hx (vals x)
    by_cases inside : k<q
    · have cut : k < 10+C.size := by omega
      have pre : ∀ a∈C.gates.take (k+1-10), j.val∉a.inputs := by
        intro a ha
        exact early a ((List.take_sublist_take_left (l := C.gates) (show k+1-10≤q-10 by omega)).subset ha)
      have pin := mustPass C j j0 j6 q k same hq hu early d swap vals
      obtain ⟨x,hx⟩ := internalCase j C k d j0 j6 hf hs (by omega) cut pre (by
        intro x y off diff
        have dg : graph x ≠ graph y := by simpa only [coded] using diff
        simpa only [reader,inside,ite_true,addOr] using pin x y off dg)
      have eq := row x
      rw [evalEq] at eq
      exact hx (by simpa only [reader,inside,ite_true,coded,addOr,Coded] using eq)
    · cases d with
      | true =>
        apply noBase
        intro x
        have eq := row x; rw [evalEq] at eq
        simpa [reader,inside,replaceSelf] using eq
      | false =>
        obtain ⟨x,y,off,delta⟩ := pivotalRows j j0 j6
        have pin := mustPass C j j0 j6 q k same hq hu early false swap vals x y off delta
        simp [reader,inside] at pin
  rcases opOK with hop|hop|hop
  all_goals cases h : g.inputs with
  | nil => simp [h] at inp
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : a=j.val := by simpa [h,eq_comm] using inp
      subst a
      first
      | apply noBase; intro x; have e := fixed x; rw [hop,h] at e
        change C.eval ((addOr x).set j.val (reader C x q j.val && true)) = graph x at e
        simpa [self,replaceSelf] using e
      | apply noBase; intro x; have e := fixed x; rw [hop,h] at e
        change C.eval ((addOr x).set j.val (reader C x q j.val || false)) = graph x at e
        simpa [self,replaceSelf] using e
      | apply noSigned; intro x; have e := fixed x; rw [hop,h] at e
        change C.eval ((addOr x).set j.val (!(reader C x q j.val))) = graph x at e
        simpa [self] using e
    | cons b rest =>
      cases rest with
      | cons c cs => simp [h] at length
      | nil =>
        have which : a=j.val ∨ b=j.val := by simpa [h,eq_comm] using inp
        rcases which with rfl|rfl
        all_goals first
        | apply both _ false true; simpa only [gateBool,Bool.false_eq_true,ite_false,ite_true,hop,h] using fixed
        | apply both _ false false; simpa only [gateBool,Bool.false_eq_true,ite_false,ite_true,hop,h] using fixed
        | apply both _ true true; simpa only [gateBool,ite_true,hop,h] using fixed
        | apply both _ true false; simpa only [gateBool,Bool.false_eq_true,ite_true,ite_false,hop,h] using fixed
        | apply noSigned; intro x; have e := fixed x; rw [hop,h] at e
          change C.eval ((addOr x).set j.val (!(reader C x q j.val))) = graph x at e
          simpa [self] using e
        | by_cases same : a=j.val
          · subst a; apply noSigned; intro x; have e := fixed x; rw [hop,h] at e
            change C.eval ((addOr x).set j.val (!(reader C x q j.val))) = graph x at e
            simpa [self] using e
          · obtain ⟨x,hx⟩ := noIgnoredNot C j j0 j6 q a same hq hu early
            apply hx
            have e := fixed x; rw [hop,h] at e; exact e
