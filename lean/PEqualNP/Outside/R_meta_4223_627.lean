import Mathlib
import PEqualNP.Defs

-- Replace the three sole OR readers by delayed inputs, leaving at most twelve ordinary gates.
-- The first twelve bits record edges and the last twelve record maximal independent sets.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_4223_627
    (mask : ∀ (n : ℕ) (C : Circuit) (a : Fin n) (r : Fin C.size),
      (∀ j, j<C.gates.length → ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
         ∀w∈(gateAt C j).inputs,w<n+j) →
      (∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r) →
      (gateAt C r.val).op=.or → a.val∈(gateAt C r.val).inputs → C.output≠a.val →
      ∀x y : Fin n → Bool,(∀i,i≠a → x i=y i) → y a=true →
        circuitFun n C x ≠ circuitFun n C y → ∀b∈(gateAt C r.val).inputs,
          (C.wires (List.ofFn x)).getD b false=false)
    (exclude : ¬ ∃ (mate : Fin 3 → BitVec 24) (v : List (BitVec 24)),
      let tags := fun (a : Fin 3) => ([11083800,903232,13500800] : List (BitVec 24)).getD a.val 0
      let src := fun (prev : List (BitVec 24)) =>
        [5521449,8532035,3227782,430612,111904,15732224] ++ prev ++
          (((List.finRange 3).filter fun a => mate a ∈ prev).map fun a => tags a ||| mate a)
      v.length≤12 ∧ (∀a,mate a∈v ∧ (mate a &&& (~~~ (4095 : BitVec 24)) &&& (~~~ (tags a)))=0) ∧
      (∀j : Fin v.length,∃ x∈src (v.take j.val),∃y∈src (v.take j.val),
          v.get j=x &&& y ∨ v.get j=x ||| y) ∧ (4095 : BitVec 24)∈v) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∀ (x8 : Fin x1.size), (x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  have evalAnd (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  have sizeEq (C : Circuit) : C.size=C.gates.length := rfl

  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have foldl_len (gs : List Gate) (w : List Bool) :
      (gs.foldl stepW w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepW w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepW w g).length := by simp [stepW]; omega
      rw [ih (stepW w g) hlt]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have foldl_char (gs : List Gate) (w : List Bool) :
      ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
        (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    induction gs using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton gs g ih =>
      intro j hj
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen := foldl_len gs w
      simp only [List.length_append, List.length_singleton] at hj
      have key : ∀ i, i < w.length + gs.length →
          (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
        intro i hi
        change ((gs.foldl stepW w) ++ [_]).getD i false = (gs.foldl stepW w).getD i false
        rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hi)]
      rcases Nat.lt_or_ge j gs.length with h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [e1, key _ (by omega), ih j h]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i (by omega)]
        · rfl
      · have hj' : j = gs.length := by omega
        subst hj'
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
            g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
          change ((gs.foldl stepW w) ++ [_]).getD (w.length+gs.length) false = _
          rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self, List.getD_cons_zero]
        rw [e2]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [key i hi]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega)]
          rfl

  let wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD w false

  have wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

  have wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
      wv n C x w = x ⟨w, hw⟩ := by
    unfold wv
    rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
    simp [List.getD_eq_getElem?_getD, hw]

  let AOB (n : ℕ) (C : Circuit) : Prop :=
    ∀ j, j < C.gates.length →
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        ∀ i ∈ (gateAt C j).inputs, i < n + j

  have wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
      (hj : j < C.gates.length) :
      wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
    have h := foldl_char C.gates (List.ofFn x) j hj
    simp only [List.length_ofFn] at h
    unfold wv gateAt
    rw [wires_eq, h]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [if_pos ((hC j hj).2 i hi)]

  let drun (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
      drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
    rfl

  have gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f1 f2 : ℕ → Bool)
      (h : ∀ r, f1 r = true → f2 r = true) :
      g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
    rcases hop with hop | hop
    · rw [hop]
      simp only [evalAnd,evalOr, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      exact fun h1 r hr => h r (h1 r hr)
    · rw [hop]
      simp only [evalAnd,evalOr, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨r, hr, h1⟩
      exact ⟨r, hr, h r h1⟩

  have run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∀ i, l1.getD i false = true → l2.getD i false = true) →
      ∀ i, (drun gs l1).getD i false = true → (drun gs l2).getD i false = true := by
    induction gs with
    | nil => intro l1 l2 _ h; exact h
    | cons g gs ih =>
      intro l1 l2 hl h
      rw [drun_cons, drun_cons]
      apply ih (fun g' hg' => hgs g' (by simp [hg']))
      · simp [hl]
      · intro i hi
        rcases lt_trichotomy i l1.length with h1 | h1 | h1
        · rw [List.getD_append _ _ _ _ h1] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · subst h1
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]
          exact gate_mono g (hgs g (by simp)) _ _ h hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          exact absurd hi (by simp)

  have wireOrder (d : ℕ) (C : Circuit) (mono : Monotone2 C) (x y : Fin d → Bool)
      (order : ∀ i, x i = true → y i = true) : ∀ w, wv d C x w = true → wv d C y w = true := by
    have gs : ∀g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g hg => by simpa using (mono g hg).1
    have prior : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      intro i
      by_cases hi : i<d
      · simpa [List.getD_eq_getElem?_getD,hi] using order ⟨i,hi⟩
      · simp [List.getD_eq_getElem?_getD,hi]
    exact run_mono C.gates gs _ _ (by simp) prior

  have pastEnd {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n+C.size≤w) :
      wv n C x w=false := by
    unfold wv
    rw [wires_eq,List.getD_eq_getElem?_getD,List.getElem?_eq_none]
    · rfl
    · simpa only [foldl_len,List.length_ofFn,sizeEq] using hw

  have partnerFalse {n : ℕ} (C : Circuit) (norm : AOB n C) (a : Fin n) (r : Fin C.size)
      (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (op : (gateAt C r.val).op=.or) (aMem : a.val∈(gateAt C r.val).inputs)
      (b : ℕ) (bMem : b∈(gateAt C r.val).inputs) (out : C.output≠a.val)
      (x y : Fin n → Bool) (other : ∀i,i≠a → x i=y i) (on : y a=true)
      (critical : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) : wv n C x b=false := by
    exact mask n C a r norm unique op aMem out x y other on critical b bMem

  let edgeTarget (x : Fin 9 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2

  let pairRow (b c : Fin 9) (i : Fin 9) : Bool := decide (i=b ∨ i=c)
  let switched (a : Fin 9) (x : Fin 9 → Bool) (i : Fin 9) : Bool := decide (i=a) || x i

  have witnesses : ∀ a ∈ ([4,6,7] : List (Fin 9)), ∀ b : Fin 9, b≠a →
      ∃c : Fin 9, edgeTarget (pairRow b c)=false ∧ edgeTarget (switched a (pairRow b c))=true := by
    decide +kernel

  have freshMate (C : Circuit) (norm : AOB 9 C)
      (funEq : circuitFun 9 C=edgeTarget) (a : Fin 9) (marked : a∈([4,6,7] : List (Fin 9)))
      (r : Fin C.size) (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (op : (gateAt C r.val).op=.or) (aMem : a.val∈(gateAt C r.val).inputs)
      (b : ℕ) (bMem : b∈(gateAt C r.val).inputs) (diff : b≠a.val) : 9≤b := by
    by_contra! raw
    let v : Fin 9 := ⟨b,raw⟩
    obtain ⟨c,off,on⟩ := witnesses a marked v (fun eq => diff (congrArg Fin.val eq))
    have out : C.output≠a.val := by
      intro eq
      let singleton := fun i : Fin 9 => decide (i=a)
      have zero : ∀j : Fin 9, edgeTarget (fun i => decide (i=j))=false := by decide +kernel
      have value := (congrFun funEq singleton).trans (zero a)
      change wv 9 C singleton C.output=false at value
      rw [eq,wv_input _ _ _ _ a.isLt] at value
      simp [singleton] at value
    have critical : C.eval (List.ofFn (pairRow v c)) ≠ C.eval (List.ofFn (switched a (pairRow v c))) := by
      change circuitFun 9 C _ ≠ circuitFun 9 C _
      rw [funEq,off,on]
      decide
    have forced := partnerFalse C norm a r unique op aMem b bMem out (pairRow v c) (switched a (pairRow v c))
      (fun i hi => by simp [switched,hi]) (by simp [switched]) critical
    rw [wv_input _ _ _ _ raw] at forced
    simp [pairRow,v] at forced

  let single (v : Fin 9) (i : Fin 9) : Bool := decide (i=v)

  have outputNotRaw (C : Circuit) (ok : circuitFun 9 C=edgeTarget) (a : Fin 9) : C.output≠a.val := by
    intro eq
    have zero : ∀ j : Fin 9, edgeTarget (single j)=false := by decide +kernel
    have value := (congrFun ok (single a)).trans (zero a)
    change wv 9 C (single a) C.output=false at value
    rw [eq,wv_input _ _ _ _ a.isLt] at value
    simp [single] at value

  have fired {n : ℕ} (C : Circuit) (norm : AOB n C) (r : Fin C.size)
      (op : (gateAt C r.val).op=.or) (x : Fin n → Bool) (w : ℕ)
      (mem : w∈(gateAt C r.val).inputs) (value : wv n C x w=true) :
      wv n C x (n+r.val)=true := by
    rw [wv_rec _ _ _ norm _ r.isLt,op]
    change ((gateAt C r.val).inputs.map (wv n C x)).any id=true
    exact List.any_eq_true.mpr ⟨true,List.mem_map.mpr ⟨w,mem,value⟩,rfl⟩

  have decisiveLow (C : Circuit) (norm : AOB 9 C) (ok : circuitFun 9 C=edgeTarget)
      (a : Fin 9) (r : Fin C.size) (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (op : (gateAt C r.val).op=.or) (aMem : a.val∈(gateAt C r.val).inputs)
      (x : Fin 9 → Bool) (low : edgeTarget x=false) (high : edgeTarget (switched a x)=true) :
      ∀ b∈(gateAt C r.val).inputs, wv 9 C x b=false := by
    intro b hb
    apply partnerFalse C norm a r unique op aMem b hb (outputNotRaw C ok a) x (switched a x)
      (fun i hi => by simp [switched,hi]) (by simp [switched])
    change circuitFun 9 C x ≠ circuitFun 9 C (switched a x)
    rw [ok,low,high]
    decide

  have agreesOnBoundary (C : Circuit) (norm : AOB 9 C) (ok : circuitFun 9 C=edgeTarget)
      (a : Fin 9) (r : Fin C.size) (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (op : (gateAt C r.val).op=.or) (aMem : a.val∈(gateAt C r.val).inputs)
      (x : Fin 9 → Bool) (low : edgeTarget x=false) (decisive : x a=false → edgeTarget (switched a x)=true) :
      wv 9 C x (9+r.val)=x a := by
    cases hx : x a with
    | false =>
      have every := decisiveLow C norm ok a r unique op aMem x low (decisive hx)
      rw [wv_rec _ _ _ norm _ r.isLt,op]
      change ((gateAt C r.val).inputs.map (wv 9 C x)).any id=false
      simp only [List.any_map,List.any_eq_false,Function.comp_apply,id_eq]
      intro b hb
      simp [every b hb]
    | true =>
      exact fired C norm r op x a.val aMem (by rwa [wv_input _ _ _ _ a.isLt])

  have beforeReader {n : ℕ} (C : Circuit) (norm : AOB n C) (a : Fin n) (r : Fin C.size)
      (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (x y : Fin n → Bool) (agree : ∀i,i≠a → x i=y i) :
      ∀ w, w<n+r.val → w≠a.val → wv n C x w=wv n C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w prev =>
      intro before diff
      by_cases raw : w<n
      · rw [wv_input _ _ _ _ raw,wv_input _ _ _ _ raw]
        exact agree ⟨w,raw⟩ (fun eq => diff (congrArg Fin.val eq))
      let j : Fin C.size := ⟨w-n, by have := r.isLt;omega⟩
      have idx : n+j.val=w := by dsimp [j];omega
      rw [← idx,wv_rec _ _ _ norm _ j.isLt,wv_rec _ _ _ norm _ j.isLt]
      congr 1
      apply List.map_congr_left
      intro b hb
      have earlier : b<w := idx ▸ (norm j.val j.isLt).2 b hb
      apply prev b earlier (lt_trans earlier before)
      intro eq
      have same := congrArg Fin.val (unique j (eq ▸ hb))
      omega

  have noSingle (C : Circuit) (norm : AOB 9 C) (mono : Monotone2 C)
      (ok : circuitFun 9 C=edgeTarget) (a : Fin 9) (marked : a∈([4,6,7] : List (Fin 9)))
      (r : Fin C.size) (unique : ∀j : Fin C.size,a.val∈(gateAt C j.val).inputs → j=r)
      (op : (gateAt C r.val).op=.or) (aMem : a.val∈(gateAt C r.val).inputs)
      (b : ℕ) (hb : b∈(gateAt C r.val).inputs) (other : b≠a.val) :
      ∀v : Fin 9,wv 9 C (single v) b=false := by
    have rest (v : Fin 9) (neq : v≠a) : wv 9 C (single v) b=false := by
      obtain ⟨c,lo,hi⟩ := witnesses a marked v neq
      have off := decisiveLow C norm ok a r unique op aMem (pairRow v c) lo hi b hb
      cases val : wv 9 C (single v) b with
      | false => rfl
      | true =>
        have order (i : Fin 9) (on : single v i=true) : pairRow v c i=true := by
          simp [single] at on
          simp [pairRow,on]
        have yes := wireOrder 9 C mono (single v) (pairRow v c) order b val
        simp [off] at yes
    intro v
    by_cases eq : v=a
    · subst v
      have nz : (0:Fin 9)≠a := by simp at marked;omega
      have z := rest 0 nz
      have eqZero := beforeReader C norm a r unique (single a) (fun _ => false)
        (fun i hi => by simp [single,hi]) b ((norm r.val r.isLt).2 b hb) other
      rw [eqZero]
      cases val : wv 9 C (fun _ => false) b with
      | false => rfl
      | true =>
        have h := wireOrder 9 C mono (fun _ => false) (single 0) (by simp) b val
        simp [z] at h
    · exact rest v eq

  let mark : Fin 3 → Fin 9 := ![4,6,7]
  let core : Fin 6 → Fin 9 := ![0,1,2,3,5,8]

  have markMem : ∀ i,mark i ∈ ([4,6,7] : List (Fin 9)) := by decide +kernel
  have distinctMarks : Function.Injective mark := by intro i j;fin_cases i <;> fin_cases j <;> decide
  have partition : ∀ v : Fin 9, (∃ i, v=mark i) ∨ ∃ i, v=core i := by decide +kernel

  have mateInputs {l : List ℕ} (hlen : l.length=2) (nd : l.Nodup) (a : ℕ) (mem : a∈l) :
      ∃ b, b≠a ∧ b∈l ∧ (l=[a,b] ∨ l=[b,a]) := by
    obtain ⟨i,j,rfl⟩ := List.length_eq_two.mp hlen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    have ne : i≠j := by simpa using nd
    rcases mem with h|h
    · subst i; exact ⟨j,ne.symm,by simp,Or.inl rfl⟩
    · subst j; exact ⟨i,ne,by simp,Or.inr rfl⟩

  let Only (C : Circuit) (r : Fin 3 → Fin C.size) : Prop :=
    ∀ i, (∀j : Fin C.size,(mark i).val∈(gateAt C j.val).inputs ↔ j=r i) ∧ (gateAt C (r i).val).op=.or

  let WellFormed (C : Circuit) : Prop :=
    ∀j : Fin C.size,(gateAt C j.val).inputs.length=2 ∧ (gateAt C j.val).inputs.Nodup

  have parts (C : Circuit) (norm : AOB 9 C) (mono : Monotone2 C) (shape : WellFormed C)
      (ok : circuitFun 9 C=edgeTarget) (r : Fin 3 → Fin C.size) (only : Only C r) :
      Function.Injective r ∧ ∃m : Fin 3 → Fin C.size, ∀i,
        m i < r i ∧ (∀a,m i ≠ r a) ∧
        (∀x : Fin 9 → Bool,wv 9 C x (9+(r i).val) = (x (mark i) || wv 9 C x (9+(m i).val))) ∧
        (∀x : Fin 9 → Bool,edgeTarget x=false → edgeTarget (switched (mark i) x)=true →
            wv 9 C x (9+(m i).val)=false) := by
    classical
    have rd (i : Fin 3) := ((only i).1 (r i)).mpr rfl
    have uniq (i : Fin 3) : ∀j : Fin C.size,(mark i).val∈(gateAt C j.val).inputs → j=r i :=
      fun j => ((only i).1 j).mp
    have inj : Function.Injective r := by
      intro a i same
      by_contra neq
      have hval : (mark a).val≠(mark i).val := fun h => neq (distinctMarks (Fin.ext h))
      have mem : (mark a).val∈(gateAt C (r i).val).inputs := same ▸ rd a
      have late := freshMate C norm ok (mark i) (markMem i) (r i) (uniq i) (only i).2 (rd i) _ mem hval
      exact (Nat.not_le_of_lt (mark a).isLt) late
    refine ⟨inj,?_⟩
    have facts (i : Fin 3) : ∃ m : Fin C.size, m < r i ∧ (∀a,m ≠ r a) ∧
        (∀x : Fin 9 → Bool,wv 9 C x (9+(r i).val) = (x (mark i) || wv 9 C x (9+m.val))) ∧
        (∀x : Fin 9 → Bool,edgeTarget x=false → edgeTarget (switched (mark i) x)=true →
            wv 9 C x (9+m.val)=false) := by
      obtain ⟨b,ne,mem,form⟩ := mateInputs (shape (r i)).1 (shape (r i)).2 _ (rd i)
      have lo := freshMate C norm ok (mark i) (markMem i) (r i) (uniq i) (only i).2 (rd i) b mem ne
      have hi := (norm (r i).val (r i).isLt).2 b mem
      let m : Fin C.size := ⟨b-9, by have := (r i).isLt;omega⟩
      have idx : 9+m.val=b := by dsimp [m];omega
      refine ⟨m, by change m.val<(r i).val;omega,?_,?_,?_⟩
      · intro a eq
        let x := single (mark a)
        have off := noSingle C norm mono ok (mark i) (markMem i) (r i) (uniq i) (only i).2 (rd i) b mem ne (mark a)
        have on := fired C norm (r a) (only a).2 x (mark a).val (rd a) (by rw [wv_input _ _ _ _ (mark a).isLt];simp [x,single])
        rw [←idx,eq] at off
        exact Bool.noConfusion (off.symm.trans on)
      · intro x
        rw [wv_rec _ _ _ norm _ (r i).isLt,(only i).2,idx]
        rcases form with h|h <;> rw [h] <;>
          simp [evalAnd,evalOr,wv_input _ _ _ _ (mark i).isLt,Bool.or_comm]
      · intro x hx hx'
        rw [idx]
        exact decisiveLow C norm ok (mark i) (r i) (uniq i) (only i).2 (rd i) x hx hx' b mem
    choose m hm using facts
    exact ⟨m,hm⟩

  let testRows : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320,42,50,69,104,116,138,201,208,261,276,385,402]
  let rawWords : Fin 9 → (BitVec 24) := ![5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224]
  let coreWords : List (BitVec 24) := [5521449,8532035,3227782,430612,111904,15732224]
  let tagWords (a : Fin 3) : (BitVec 24) := ([11083800,903232,13500800] : List (BitVec 24)).getD a.val 0
  let sample (t : Fin 24) (i : Fin 9) := (testRows.getD t.val 0).testBit i.val
  let pack (f : Fin 24 → Bool) : (BitVec 24) := (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
  let sig (C : Circuit) (w : ℕ) : (BitVec 24) := pack fun t => wv 9 C (sample t) w
  let sourcePool (mate : Fin 3 → (BitVec 24)) (prev : List (BitVec 24)) : List (BitVec 24) :=
    coreWords ++ prev ++ (((List.finRange 3).filter fun a => mate a ∈ prev).map fun a => tagWords a ||| mate a)
  let Certificate (mate : Fin 3 → (BitVec 24)) (v : List (BitVec 24)) : Prop :=
    v.length≤12 ∧ (∀a,mate a∈v ∧ (mate a &&& (~~~ (4095 : (BitVec 24))) &&& (~~~ (tagWords a)))=0) ∧
    (∀j : Fin v.length, ∃ x∈sourcePool mate (v.take j.val), ∃y∈sourcePool mate (v.take j.val),
        v[j.val]=x &&& y ∨ v[j.val]=x ||| y) ∧ (4095 : (BitVec 24))∈v

  have packBit (f : Fin 24 → Bool) (t : Fin 24) : (pack f).getLsbD t.val=f t := by
    simp only [pack,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    simp [t.isLt]

  have wordBit {C : Circuit} (w : ℕ) (t : Fin 24) : (sig C w).getLsbD t.val=wv 9 C (sample t) w :=
    packBit _ _

  have data : (∀t : Fin 24, ∀i : Fin 9, (rawWords i).getLsbD t.val=sample t i) ∧
      (∀t : Fin 24,(4095 : (BitVec 24)).getLsbD t.val=edgeTarget (sample t)) ∧
      (∀t : Fin 24,∀a : Fin 3,edgeTarget (sample t)=false → sample t (mark a)=false →
          edgeTarget (switched (mark a) (sample t))=true) ∧
      (∀a : Fin 3,tagWords a=rawWords (mark a)) ∧ (∀i : Fin 6,rawWords (core i)∈coreWords) := by
    decide +kernel

  have sigRaw (C : Circuit) (i : Fin 9) : sig C i.val=rawWords i := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let t : Fin 24 := ⟨j,hj⟩
    exact (wordBit i.val t).trans ((wv_input _ _ _ _ i.isLt).trans (data.1 t i).symm)

  have sigOutput (C : Circuit) (ok : circuitFun 9 C=edgeTarget) : sig C C.output=4095 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let t : Fin 24 := ⟨j,hj⟩
    exact (wordBit C.output t).trans ((congrFun ok (sample t)).trans (data.2.1 t).symm)

  have sigGate (C : Circuit) (norm : AOB 9 C) (j : Fin C.size) (u v : ℕ)
      (pair : (gateAt C j.val).inputs=[u,v]) :
      sig C (9+j.val)=sig C u &&& sig C v ∨ sig C (9+j.val)=sig C u ||| sig C v := by
    have h (t : Fin 24) := wv_rec 9 C (sample t) norm j.val j.isLt
    rcases (norm _ j.isLt).1 with op|op
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro z hz
      let t : Fin 24 := ⟨z,hz⟩
      change (sig C (9+j.val)).getLsbD t.val=_
      rw [BitVec.getLsbD_and,wordBit _ t,wordBit _ t,wordBit _ t,h t,op,pair]
      simp [evalAnd,evalOr]
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro z hz
      let t : Fin 24 := ⟨z,hz⟩
      change (sig C (9+j.val)).getLsbD t.val=_
      rw [BitVec.getLsbD_or,wordBit _ t,wordBit _ t,wordBit _ t,h t,op,pair]
      simp [evalAnd,evalOr]

  have ofFnEarlier {α : Type} {n : ℕ} (values : Fin n → α) (i j : Fin n) (lt : i<j) :
      values i ∈ (List.ofFn values).take j.val := by
    have h : i.val<((List.ofFn values).take j.val).length := by
      simp only [List.length_take,List.length_ofFn]
      exact lt_min lt i.isLt
    have mem := List.getElem_mem (l:=(List.ofFn values).take j.val) h
    simpa only [List.getElem_take,List.getElem_ofFn] using mem

  have compress (C : Circuit) (norm : AOB 9 C) (mono : Monotone2 C) (shape : WellFormed C)
      (budget : C.size≤15) (ok : circuitFun 9 C=edgeTarget) (r : Fin 3 → Fin C.size) (only : Only C r) :
      ∃mate v,Certificate mate v := by
    classical
    obtain ⟨injective,m,props⟩ := parts C norm mono shape ok r only
    let U : Finset (Fin C.size) := (Finset.univ.image r)ᶜ
    let order := U.orderIsoOfFin rfl
    let ord (j : Fin U.card) : Fin C.size := (order j).val
    let value (j : Fin U.card) := sig C (9+(ord j).val)
    let v := List.ofFn value
    let mate := fun a => sig C (9+(m a).val)
    have ordinary (j : Fin C.size) : j∈U ↔ ∀a,j≠r a := by
      simp [U,eq_comm]
    have belongs (j : Fin U.card) : ord j ∈ U := (order j).property
    have inside (j : Fin C.size) (hj : j∈U) : sig C (9+j.val) ∈v := by
      let i := order.symm ⟨j,hj⟩
      have eq : ord i=j := congrArg Subtype.val (order.apply_symm_apply ⟨j,hj⟩)
      exact List.mem_ofFn.mpr ⟨i,by simp only [value,eq]⟩
    have earlier (j : Fin U.card) (k : Fin C.size) (hk : k∈U) (lt : k<ord j) :
        sig C (9+k.val)∈v.take j.val := by
      let i := order.symm ⟨k,hk⟩
      have eq : ord i=k := congrArg Subtype.val (order.apply_symm_apply ⟨k,hk⟩)
      have less : i<j := by
        apply order.lt_iff_lt.mp
        change ord i<ord j
        simpa [eq] using lt
      simpa only [value,eq] using ofFnEarlier value i j less
    have markWord (a : Fin 3) : sig C (9+(r a).val)=tagWords a ||| mate a := by
      apply BitVec.eq_of_getLsbD_eq
      intro z hz
      let t : Fin 24 := ⟨z,hz⟩
      change (sig C _).getLsbD t.val=_
      rw [BitVec.getLsbD_or,wordBit _ t,data.2.2.2.1 a,data.1 t (mark a)]
      exact ((props a).2.2.1 (sample t)).trans (by rw [show (mate a).getLsbD t.val=wv 9 C (sample t) (9+(m a).val) from wordBit _ t])
    have sz (a : Fin 3) : m a∈U := (ordinary _).mpr (props a).2.1
    refine ⟨mate,v,?_,?_,?_,?_⟩
    · have card := Finset.card_compl (Finset.univ.image r)
      have three : (Finset.univ.image r).card=3 := by simp [Finset.card_image_of_injective _ injective]
      change (List.ofFn value).length≤12
      rw [List.length_ofFn]
      change (Finset.univ.image r)ᶜ.card≤12
      rw [card,three,Fintype.card_fin]
      omega
    · intro a
      refine ⟨inside (m a) (sz a),?_⟩
      apply BitVec.eq_of_getLsbD_eq
      intro z hz
      let t : Fin 24 := ⟨z,hz⟩
      change (mate a &&& ~~~(4095 : (BitVec 24)) &&& ~~~(tagWords a)).getLsbD t.val=_
      simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_zero,t.isLt,decide_true,Bool.true_and]
      rw [data.2.1 t,data.2.2.2.1 a,data.1 t (mark a)]
      cases low : edgeTarget (sample t) <;> cases bit : sample t (mark a) <;> simp
      exact (wordBit (9+(m a).val) t).trans ((props a).2.2.2 _ low (data.2.2.1 t a low bit))
    · intro j
      let i : Fin U.card := ⟨j.val,by simpa [v] using j.isLt⟩
      let g := gateAt C (ord i).val
      obtain ⟨l,k,pair⟩ := List.length_eq_two.mp (shape (ord i)).1
      have pool (w : ℕ) (hw : w∈g.inputs) : sig C w∈sourcePool mate (v.take i.val) := by
        have bound := (norm _ (ord i).isLt).2 w hw
        by_cases raw : w<9
        · let u : Fin 9 := ⟨w,raw⟩
          rcases partition u with ⟨a,eq⟩|⟨a,eq⟩
          · have h := ((only a).1 (ord i)).mp (by rw [←eq];exact hw)
            exact ((ordinary _).mp (belongs i) a h).elim
          · have physical : sig C w=rawWords (core a) := (sigRaw C u).trans (congrArg rawWords eq)
            exact List.mem_append_left _ (List.mem_append_left _ (physical ▸ data.2.2.2.2 a))
        · let h : Fin C.size := ⟨w-9,by have := (ord i).isLt;omega⟩
          have idw : 9+h.val=w := by dsimp [h];omega
          have lt : h<ord i := by change h.val<(ord i).val;omega
          by_cases seen : h∈U
          · exact List.mem_append_left _ (List.mem_append_right _ (idw ▸ earlier i h seen lt))
          · have marked : ∃a,h=r a := by simpa [U,eq_comm] using seen
            obtain ⟨a,same⟩ := marked
            have lt' : m a<ord i := lt_trans (props a).1 (same ▸ lt)
            have before : mate a ∈v.take i.val := earlier i (m a) (sz a) lt'
            apply List.mem_append_right
            apply List.mem_map.mpr
            refine ⟨a,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using before⟩,?_⟩
            rw [←markWord,←idw,same]
      have hp : g.inputs=[l,k] := pair
      have get : v[j.val]=value i := List.getElem_ofFn j.isLt
      refine ⟨sig C l,pool l (by simp [hp]),sig C k,pool k (by simp [hp]),?_⟩
      rw [get]
      exact sigGate C norm (ord i) l k pair
    · have lo : 9≤C.output := by
        by_contra! raw
        exact outputNotRaw C ok ⟨C.output,raw⟩ rfl
      have hi : C.output<9+C.size := by
        by_contra! past
        have off := pastEnd C (pairRow 0 1) past
        have on := congrFun ok (pairRow 0 1)
        change wv 9 C (pairRow 0 1) C.output=edgeTarget (pairRow 0 1) at on
        rw [off] at on
        exact (by decide : false≠edgeTarget (pairRow 0 1)) on
      let j : Fin C.size := ⟨C.output-9,by omega⟩
      have idx : 9+j.val=C.output := by dsimp [j];omega
      have reg : j∈U := by
        apply (ordinary _).mpr
        intro a same
        have off : ∀a : Fin 9,edgeTarget (single a)=false := by decide +kernel
        have value' := (congrFun ok (single (mark a))).trans (off (mark a))
        change wv 9 C (single (mark a)) C.output=false at value'
        rw [←idx,same,(props a).2.2.1] at value'
        simp [single] at value'
      have ans := inside j reg
      rwa [idx,sigOutput C ok] at ans
  intro C minimal budget ok normalized readers _apart noNot
  have gateEq (j : Fin C.size) : gateAt C j.val=C.gates.get j := by
    change C.gates.getD j.val _ = C.gates[j.val]
    exact List.getD_eq_getElem _ _ j.isLt
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    let k : Fin C.size := ⟨j,hj⟩
    obtain ⟨ops,arity⟩ := minimal.1 _ (List.getElem_mem hj)
    refine ⟨?_,arity⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops ⊢
    rcases ops with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact ((noNot k) h).elim
  have norm : AOB 9 C := by
    intro j hj
    let k : Fin C.size := ⟨j,hj⟩
    change ((gateAt C k.val).op=.and ∨ (gateAt C k.val).op=.or) ∧ _
    rw [gateEq k]
    refine ⟨by simpa using (mono _ (List.get_mem _ k)).1,(normalized k).1⟩
  have shape : WellFormed C := by
    intro j
    rw [gateEq j]
    have ar := (normalized j).2.2
    exact ⟨ar.elim (fun e => ((noNot j) e.1).elim) And.right,(normalized j).2.1⟩
  choose read hread using fun i : Fin 3 => readers (mark i) (markMem i)
  have only : Only C read := by
    intro i
    refine ⟨fun j => ?_,?_⟩
    · rw [gateEq j]
      exact (hread i).1 j
    · rw [gateEq (read i)]
      exact (hread i).2
  obtain ⟨mate,v,cert⟩ := compress C norm mono shape budget ok read only
  exact exclude ⟨mate,v,cert⟩
