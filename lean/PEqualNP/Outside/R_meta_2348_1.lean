import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- For each representative pair a < b, the mask has bit 14 * a + b set.
-- The second hypothesis identifies the derivative recurrence with the library linear part.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2348_1
  (canonical : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .or →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (let a := opnd C 0 0
       let b := opnd C 0 1
       Nat.testBit 365118556550 (14 * min a b + max a b) = true) →
      ∃ s : Bool, PEqualNP.ReadK.lineSingle C 14 (fun i => i == (if s then 7 else 0)) 0 7 = true)
  (linear : ∀ C : Circuit, IsAO2 14 C →
    ∀ (s : Bool) (v : ℕ → Bool),
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) →
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) → v C.output = false → PEqualNP.ReadK.lineSingle C 14 (fun i => i == (if s then 7 else 0)) 0 7 = false) :
    ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .or →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      False := by
  intro C hsize hm distinct first hfun hreads
  have hget (C : Circuit) (j : ℕ) (hj : j < C.size) : C.gates[j]? = some (gateAt C j) := by
    change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem (show j < C.gates.length from hj),
      List.getD_eq_getElem _ _ (show j < C.gates.length from hj)]
  have hopnd (C : Circuit) (j a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) :
      opnd C j 0 = a ∧ opnd C j 1 = b := by
    change (gateAt C j).inputs.getD 0 0 = a ∧ (gateAt C j).inputs.getD 1 0 = b
    rw [hab]
    exact ⟨rfl, rfl⟩
  have hg (j : ℕ) (g : Gate) (he : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j := by
    have hj : j < C.size := by
      change j < C.gates.length
      exact List.getElem?_eq_some_iff.mp he |>.choose
    have mem := List.mem_of_getElem? he
    have len := hm.2.2 g mem
    obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := List.length_eq_two.mp len
    have eqg := Option.some.inj ((hget C j hj).symm.trans he)
    obtain ⟨ha,hb⟩ := hopnd C j a b (eqg ▸ hab)
    refine ⟨hm.1 g mem,a,b,hab,?_,?_,?_⟩
    · simpa [ha,hb] using distinct j hj
    · apply hm.2.1 j hj a
      change a ∈ (gateAt C j).inputs
      simp [eqg,hab]
    · apply hm.2.1 j hj b
      change b ∈ (gateAt C j).inputs
      simp [eqg,hab]
  have hgate (j : ℕ) (hj : j < C.size) :
      ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j :=
    (hg j (gateAt C j) (hget C j hj)).2
  have pos : 0 < C.size := by
    by_contra! hz
    obtain ⟨gs,o⟩ := C
    have hnil : gs = [] := List.length_eq_zero_iff.mp (by change gs.length ≤ 0 at hz; omega)
    subst gs
    let x : Fin 14 → Bool := fun i => decide (i.val = o)
    have h := hfun x
    by_cases ho : o < 14
    · have yes : (Circuit.mk [] o).eval (List.ofFn x) = true := by
        change (List.ofFn x).getD o false = true
        rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
        simp [ho,x]
      obtain ⟨u,t,_,hu,ht⟩ := h.mp yes
      simp [x] at hu ht
      omega
    · have h := (hfun (fun _ => true)).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩
      change (List.ofFn (fun _ : Fin 14 => true)).getD o false = true at h
      rw [List.getD_eq_default _ false (by simp; omega)] at h
      contradiction
  obtain ⟨a,b,hab,hn,ha,hb⟩ := hgate 0 pos
  let A : Fin 14 := ⟨a,by omega⟩
  let B : Fin 14 := ⟨b,by omega⟩
  let edge (i j : Fin 14) : Prop := ∃ p l : Fin 7,
    (p = l ∨ p = l+1 ∨ p = l+3) ∧
    ((i = Fin.castAdd 7 p ∧ j = Fin.natAdd 7 l) ∨
     (j = Fin.castAdd 7 p ∧ i = Fin.natAdd 7 l))
  -- The even rows fix both marked inputs and the odd rows interchange them.
  let maps : Fin 16 → Fin 14 → Fin 14 :=
    ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13],
      ![7,13,12,11,10,9,8,0,6,5,4,3,2,1],
      ![0,1,4,3,2,6,5,7,8,10,9,13,12,11],
      ![7,13,10,11,12,8,9,0,6,4,5,1,2,3],
      ![0,1,5,3,6,2,4,7,12,9,10,13,8,11],
      ![7,13,9,11,8,12,10,0,2,5,4,1,6,3],
      ![0,1,6,3,5,4,2,7,12,10,9,11,8,13],
      ![7,13,8,11,9,10,12,0,2,4,5,3,6,1],
      ![0,3,2,1,5,4,6,7,9,8,12,11,10,13],
      ![7,11,12,13,9,10,8,0,5,6,2,3,4,1],
      ![0,3,4,1,6,2,5,7,10,8,12,13,9,11],
      ![7,11,10,13,8,12,9,0,4,6,2,1,5,3],
      ![0,3,5,1,2,6,4,7,9,12,8,13,10,11],
      ![7,11,9,13,12,8,10,0,5,2,6,1,4,3],
      ![0,3,6,1,4,5,2,7,10,12,8,11,9,13],
      ![7,11,8,13,10,9,12,0,4,2,6,3,5,1]]
  let adjacent (i j : Fin 14) : Bool :=
    let p := min i.val j.val
    let l := max i.val j.val - 7
    decide (p < 7 ∧ 7 ≤ max i.val j.val ∧ (p = l ∨ p = (l+1)%7 ∨ p = (l+3)%7))
  have edgeTest : ∀ i j, edge i j ↔ adjacent i j = true := by
    dsimp only [edge, adjacent]
    decide +kernel
  have cert : (∀ k : Fin 16, let f := maps k; (∀ x y, f x = f y → x = y) ∧
      (∀ x y, adjacent (f x) (f y) = adjacent x y) ∧
      ((f 0 = 0 ∧ f 7 = 7) ∨ (f 0 = 7 ∧ f 7 = 0))) ∧
      ∀ i j : Fin 14, i ≠ j → ∃ k : Fin 16, let f := maps k
      Nat.testBit 365118556550 (14 * min (f i).val (f j).val + max (f i).val (f j).val) = true := by
    dsimp only [adjacent,maps]
    decide +kernel
  obtain ⟨k,rep⟩ := cert.2 A B (fun e => hn (congrArg Fin.val e))
  obtain ⟨hi,hAdj,flag⟩ := cert.1 k
  have preserve (i j : Fin 14) : edge (maps k i) (maps k j) ↔ edge i j := by
    rw [edgeTest, edgeTest, hAdj]
  let σ := Equiv.ofBijective (maps k) (Finite.injective_iff_bijective.mp hi)
  let τ := σ.symm
  -- Relabel input wires while preserving all gate wire numbers.
  let M (ρ : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
    if h : w < 14 then (ρ ⟨w, h⟩).val else w
  have hMlt (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ i < 14 ↔ i < 14 := by
    by_cases h : i < 14
    · simp only [M, dite_eq_left h, h, iff_true]
      exact (ρ ⟨i, h⟩).isLt
    · simp [M, h]
  have hMof (ρ : Equiv.Perm (Fin 14)) (i : Fin 14) : M ρ i.val = (ρ i).val := by
    simp [M, i.isLt]
  have hMinv (ρ : Equiv.Perm (Fin 14)) (i : ℕ) : M ρ.symm (M ρ i) = i := by
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change M ρ.symm (M ρ j.val) = j.val
      rw [hMof, hMof, ρ.symm_apply_apply]
    · simp [M, h]
  have hMbound (ρ : Equiv.Perm (Fin 14)) (i j : ℕ) (h : i < 14 + j) : M ρ i < 14 + j := by
    by_cases hi : i < 14
    · have := (hMlt ρ i).2 hi
      omega
    · simpa [M, hi] using h
  let mapGate (ρ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (M ρ)⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalRel (ρ : Equiv.Perm (Fin 14)) (gs : List Gate) :
      ∀ W W' : List Bool, 14 ≤ W.length → W'.length = W.length →
        (∀ w, W'.getD (M ρ w) false = W.getD w false) →
        ∀ w, ((gs.map (mapGate ρ)).foldl step W').getD (M ρ w) false =
          (gs.foldl step W).getD w false := by
    induction gs with
    | nil => intro W W' hW hlen hbase w; exact hbase w
    | cons g gs ih =>
      intro W W' hW hlen hbase w
      simp only [List.map_cons, List.foldl_cons]
      have hv : (mapGate ρ g).op.eval ((mapGate ρ g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hbase a
      apply ih (step W g) (step W' (mapGate ρ g)) (by simp [step]; omega)
        (by simp [step, hlen]) _ w
      intro u
      simp only [step, hv]
      rcases Nat.lt_trichotomy u W.length with hlt | heq | hgt
      · have hlt' : M ρ u < W'.length := by
          by_cases hsmall : u < 14
          · have := (hMlt ρ u).2 hsmall
            omega
          · simpa [M, hsmall, hlen] using hlt
        rw [List.getD_append _ _ _ _ hlt', List.getD_append _ _ _ _ hlt]
        exact hbase u
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge]]
        have last (w : List Bool) (x : Bool) (h : u = w.length) :
            (w ++ [x]).getD u false = x := by rw [h]; simp
        rw [last W' _ (by omega), last W _ heq]
      · have hlarge : ¬ u < 14 := by omega
        rw [show M ρ u = u by simp [M, hlarge],
          List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have hWires (ρ : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) :
      ((Circuit.mk (C.gates.map (mapGate ρ)) (M ρ C.output)).wires (List.ofFn x)).getD
        (M ρ w) false = (C.wires (List.ofFn (x ∘ ρ))).getD w false := by
    apply evalRel ρ C.gates _ _ (by simp) (by simp) _ w
    intro i
    by_cases h : i < 14
    · let j : Fin 14 := ⟨i, h⟩
      change (List.ofFn x).getD (M ρ j.val) false = (List.ofFn (x ∘ ρ)).getD j.val false
      rw [hMof]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (ρ j).isLt),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
          List.getElem_ofFn, List.getElem_ofFn]
      rfl
    · rw [show M ρ i = i by simp [M, h],
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  let D : Circuit := ⟨C.gates.map (mapGate σ), M σ C.output⟩
  have hDsize : D.size = C.size := List.length_map (mapGate σ)
  have hDget (j : ℕ) : D.gates[j]? = C.gates[j]?.map (mapGate σ) := List.getElem?_map
  have hDgate (j : ℕ) (hj : j < D.size) :
      gateAt D j = mapGate σ (gateAt C j) := by
    have hj' : j < C.size := hDsize ▸ hj
    have h := hDget j
    rw [hget D j hj, hget C j hj'] at h
    exact Option.some.inj h
  have hDinputs (j a b : ℕ) (hj : j < D.size) (hab : (gateAt C j).inputs = [a, b]) :
      (gateAt D j).inputs = [M σ a, M σ b] := by
    rw [hDgate j hj]
    change (gateAt C j).inputs.map (M σ) = _
    rw [hab]
    rfl
  have hDmono : IsAO2 14 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      exact (hg j g' hj).1
    · intro j hj i hi
      obtain ⟨a, b, hab, _, ha, hb⟩ := hgate j (hDsize ▸ hj)
      rw [hDinputs j a b hj hab] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hMbound σ a j ha
      · exact hMbound σ b j hb
    · intro g hmem
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg'
      obtain ⟨a, b, hab, _⟩ := (hg j g' hj).2
      change (g'.inputs.map (M σ)).length = 2
      simp [hab]
  have hDdistinct (j : ℕ) (hj : j < D.size) : opnd D j 0 ≠ opnd D j 1 := by
    obtain ⟨a, b, hab, hn, _⟩ := hgate j (hDsize ▸ hj)
    obtain ⟨ha, hb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
    rw [ha, hb]
    intro he
    exact hn (by simpa only [hMinv] using congrArg (M σ.symm) he)
  have hDfun (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    have alt (y : Fin 14 → Bool) : (∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
        y (Fin.castAdd 7 p) = true ∧ y (Fin.natAdd 7 l) = true) ↔
        ∃ i j, edge i j ∧ y i = true ∧ y j = true := by
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        exact ⟨_,_,⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
      · rintro ⟨i,j,⟨p,l,h,e⟩,hi',hj'⟩
        rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ⟨p,l,h,by assumption,by assumption⟩
    have he : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := hWires σ C x C.output
    rw [he,hfun,alt,alt]
    constructor
    · rintro ⟨i,j,h,hi',hj'⟩
      exact ⟨σ i,σ j,(preserve i j).2 h,hi',hj'⟩
    · rintro ⟨i,j,h,hi',hj'⟩
      obtain ⟨i,rfl⟩ := σ.surjective i
      obtain ⟨j,rfl⟩ := σ.surjective j
      exact ⟨i,j,(preserve i j).1 h,hi',hj'⟩
  have hdpos : 0 < D.size := hDsize ▸ pos
  have hfirst : (gateAt D 0).op = .or := by rw [hDgate 0 hdpos]; exact first
  obtain ⟨dfa,dfb⟩ := hopnd D 0 _ _ (hDinputs 0 a b hdpos hab)
  obtain ⟨s,hs⟩ := canonical D (by omega) hDmono hDdistinct hfirst hDfun (by
    dsimp only
    rw [dfa,dfb]
    change Nat.testBit _ (14 * min (M σ A.val) (M σ B.val) + max (M σ A.val) (M σ B.val)) = true
    rw [hMof,hMof]
    exact rep)
  obtain ⟨t,base,seed⟩ : ∃ t : Bool,
      σ (if t then 0 else 7) = (if s then 0 else 7) ∧
      σ (if t then 7 else 0) = (if s then 7 else 0) := by
    rcases flag with f | f
    · exact ⟨s,by cases s <;> first | exact f.1 | exact f.2,by cases s <;> first | exact f.1 | exact f.2⟩
    · exact ⟨!s,by cases s <;> first | exact f.1 | exact f.2,by cases s <;> first | exact f.1 | exact f.2⟩
  obtain ⟨z,hzinit,hzgate,hzout⟩ := hreads t
  let x : Fin 14 → Bool := fun i => decide (i = if s then 0 else 7)
  have hx : x ∘ σ = fun i : Fin 14 => decide (i = if t then 0 else 7) := by
    funext i
    apply Bool.decide_congr
    change σ i = _ ↔ _
    rw [← base, σ.injective.eq_iff]
  have hW (i : ℕ) : (D.wires (List.ofFn x)).getD (M σ i) false =
      (C.wires (List.ofFn (fun i : Fin 14 => decide (i = if t then 0 else 7)))).getD i false := by
    rw [← hx]
    exact hWires σ C x i
  have hseed : M σ (if t then 7 else 0) = if s then 7 else 0 := by
    have h := congrArg Fin.val seed
    cases s <;> cases t <;> simpa [M,σ] using h
  have neg := linear D hDmono s (fun i => z (M τ i))
  have hfalse : PEqualNP.ReadK.lineSingle D 14 (fun i => i == (if s then 7 else 0)) 0 7 = false := by
    apply neg
    · intro i hi
      change z (M τ i) = decide (i = if s then 7 else 0)
      rw [hzinit _ ((hMlt τ i).2 hi)]
      apply Bool.decide_congr
      constructor
      · intro he
        have he' := congrArg (M σ) he
        change M τ.symm (M τ i) = M σ _ at he'
        rwa [hMinv, hseed] at he'
      · intro he
        have he' := congrArg (M τ) (he.trans hseed.symm)
        change M τ i = M σ.symm (M σ _) at he'
        rwa [hMinv] at he'
    · intro j hj
      have hj' : j < C.size := hDsize ▸ hj
      obtain ⟨a, b, hab, _⟩ := hgate j hj'
      obtain ⟨ha, hb⟩ := hopnd C j a b hab
      obtain ⟨hda, hdb⟩ := hopnd D j (M σ a) (M σ b) (hDinputs j a b hj hab)
      have hOp : (gateAt D j).op = (gateAt C j).op := by rw [hDgate j hj]
      have hwire : M τ (14 + j) = 14 + j := by simp [M, show ¬ 14 + j < 14 by omega]
      have hma : M τ (M σ a) = a := hMinv σ a
      have hmb : M τ (M σ b) = b := hMinv σ b
      have hh := hzgate j hj'
      simp only [ha, hb] at hh
      change ((gateAt D j).op = GateOp.and → z (M τ (14 + j)) =
          (((D.wires (List.ofFn x)).getD (opnd D j 0) false && z (M τ (opnd D j 1))) ||
           (z (M τ (opnd D j 0)) && (D.wires (List.ofFn x)).getD (opnd D j 1) false))) ∧
        ((gateAt D j).op = GateOp.or → z (M τ (14 + j)) =
          (z (M τ (opnd D j 0)) || z (M τ (opnd D j 1))))
      simpa only [hOp, hda, hdb, hwire, hma, hmb, hW] using hh
    · change z (M σ.symm (M σ C.output)) = false
      rwa [hMinv]
  simp [hs] at hfalse
