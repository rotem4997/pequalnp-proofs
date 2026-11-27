import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The fifteen-gate form and the thirteen-binary-gate bound are L-meta-3602
-- and L-meta-3400 respectively. The ten permutations send the deleted vertex to nine.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_5150_43
  (shape : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    C.size ≤ 15 → C.size = 15 ∧ C.output = 23 ∧ ∀ j < 14, ∃ k : Fin C.gates.length, j < k.val ∧ 9 + j ∈ (C.gates.get k).inputs)
  (binary : ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
    13 ≤ C.size - PEqualNP.NotBracket.notCount C)
  (exclude : ∀ C : Circuit, FanInTwo C → C.size = 15 → C.output = 23 →
    PEqualNP.NotBracket.notCount C ≤ 2 → (∀ j < 14, ∃ k : Fin C.gates.length, j < k.val ∧ 9 + j ∈ (C.gates.get k).inputs) →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) :
∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  have transport : ∀ (n m : ℕ) (p : Fin n → Option (Fin m)) (C : Circuit) (b : Bool),
      FanInTwo C → ∃ D : Circuit, FanInTwo D ∧
        D.size ≤ C.size + (if b = true then 1 else 0) ∧
        ∀ x : Fin m → Bool,
          let y : Fin n → Bool := fun i => ((p i).map x).getD false
          circuitFun m D x = (if b = true then !C.eval (List.ofFn y) else C.eval (List.ofFn y)) := by
    intro n m p C b fan
    let redirect (i : ℕ) := if h : i < n then ((p ⟨i,h⟩).map Fin.val).getD (m+C.size)
      else m+(i-n)
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map redirect⟩
    let B : Circuit := ⟨C.gates.map gate,redirect C.output⟩
    have hSize : B.size = C.size := List.length_map _
    have hFan : FanInTwo B := by
      intro g hg
      change g ∈ C.gates.map gate at hg
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
      exact ⟨(fan u hu).1,by simpa only [gate, List.length_map] using (fan u hu).2⟩
    have early (i : ℕ) (h : i < n) :
        redirect i = ((p ⟨i,h⟩).map Fin.val).getD (m+C.size) := dite_eq_left h
    have late (i : ℕ) (h : n ≤ i) : redirect i = m+(i-n) := dite_eq_right (Nat.not_lt.mpr h)
    have eval (gs : List Gate) (k : ℕ) (ws zs : List Bool)
        (hcap : k + gs.length = C.size)
        (lenW : ws.length = n+k) (lenZ : zs.length = m+k)
        (same : ∀ i, zs.getD (redirect i) false = ws.getD i false) :
        ∀ i, ((⟨gs.map gate,0⟩ : Circuit).wires zs).getD (redirect i) false =
          ((⟨gs,0⟩ : Circuit).wires ws).getD i false := by
      induction gs generalizing k ws zs with
      | nil => exact same
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => ws.getD i false)
        have eq : (gate g).op.eval ((gate g).inputs.map fun i => zs.getD i false) = bit := by
          simp only [gate,List.map_map,Function.comp_def,same,bit]
        change ∀ i, ((⟨gs.map gate,0⟩ : Circuit).wires (zs ++ [_])).getD (redirect i) false =
          ((⟨gs,0⟩ : Circuit).wires (ws ++ [bit])).getD i false
        rw [eq]
        have k1 : k + 1 ≤ C.size := by simp only [List.length_cons] at hcap; omega
        apply ih (k+1) _ _ (by simp only [List.length_cons] at hcap; omega)
          (by simp only [List.length_append,List.length_singleton,lenW,Nat.add_assoc])
          (by simp only [List.length_append,List.length_singleton,lenZ,Nat.add_assoc])
        intro i
        by_cases first : i < n
        · have hs : i < ws.length := by omega
          rw [List.getD_append _ _ _ _ hs]
          rcases ep : p ⟨i,first⟩ with _ | v
          · have e : redirect i = m + C.size := by rw [early i first,ep]; rfl
            have val : ws.getD i false = false := by
              rw [← same, e, List.getD_eq_default _ _ (by omega)]
            have limit : (zs ++ [bit]).length ≤ m+C.size := by
              simp only [List.length_append, List.length_singleton, lenZ]
              omega
            rw [val, e, List.getD_eq_default _ _ limit]
          · have e : redirect i = v.val := by rw [early i first,ep]; rfl
            have hl : redirect i < zs.length := by rw [e,lenZ]; exact v.isLt.trans_le (Nat.le_add_right _ _)
            rw [List.getD_append _ _ _ _ hl]
            exact same i
        · have hN : n ≤ i := Nat.le_of_not_gt first
          have e := late i hN
          by_cases hi : i < ws.length
          · have hz : redirect i < zs.length := by rw [e,lenZ]; omega
            rw [List.getD_append _ _ _ _ hz,List.getD_append _ _ _ _ hi]
            exact same i
          · have hz : zs.length ≤ redirect i := by rw [e,lenZ]; omega
            rw [List.getD_append_right _ _ _ _ hz,
              List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
            have diff : redirect i - zs.length = i - ws.length := by rw [e,lenZ,lenW]; omega
            rw [diff]
    have transport (x : Fin m → Bool) :
        circuitFun m B x = C.eval (List.ofFn fun i => ((p i).map x).getD false) := by
      let y (i : Fin n) := ((p i).map x).getD false
      change B.eval (List.ofFn x) = C.eval (List.ofFn y)
      apply eval C.gates 0 _ _ (by rw [Nat.zero_add]; rfl) (by simp) (by simp) _ C.output
      intro i
      by_cases hi : i < n
      · have h : i < (List.ofFn y).length := by simpa only [List.length_ofFn] using hi
        rw [List.getD_eq_getElem _ _ h,List.getElem_ofFn]
        rcases ep : p ⟨i,hi⟩ with _ | v
        · have e : redirect i = m+C.size := by rw [early i hi,ep]; rfl
          have rhs : y ⟨i,hi⟩ = false := by simp [y,ep]
          rw [e,List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
          exact rhs.symm
        · have e : redirect i = v.val := by rw [early i hi,ep]; rfl
          have h : v.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using v.isLt
          have rhs : y ⟨i,hi⟩ = x v := by simp [y,ep]
          rw [e,List.getD_eq_getElem _ _ h,List.getElem_ofFn]
          exact rhs.symm
      · rw [late i (Nat.le_of_not_gt hi),
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
    cases b with
    | false => exact ⟨B,hFan,by simp [hSize],by simpa using transport⟩
    | true =>
      let E : Circuit := ⟨B.gates ++ [⟨.not,[B.output]⟩],m+B.size⟩
      have hE : FanInTwo E := by
        intro g hg
        change g ∈ B.gates ++ _ at hg
        rcases List.mem_append.mp hg with hn | hn
        · exact hFan g hn
        · obtain rfl := List.mem_singleton.mp hn
          exact ⟨by simp, by change 1 ≤ 2; decide⟩
      have eSize : E.size = B.size + 1 := by
        change (B.gates ++ [_]).length = _
        rw [List.length_append]
        rfl
      refine ⟨E,hE,by simp [eSize,hSize],?_⟩
      intro x
      let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      let W := B.wires (List.ofFn x)
      have foldLen (l : List Gate) (ws : List Bool) :
          (l.foldl step ws).length = ws.length + l.length := by
        induction l generalizing ws with
        | nil => simp
        | cons g l ih => rw [List.foldl_cons,ih]; simp [step]; omega
      have len : W.length = m + B.size := by
        change (B.gates.foldl step (List.ofFn x)).length = _
        rw [foldLen,List.length_ofFn]
        rfl
      change (((B.gates ++ [_]).foldl step (List.ofFn x)).getD (m+B.size) false) = _
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change (W ++ [!(circuitFun m B x)]).getD (m+B.size) false = _
      rw [List.getD_append_right _ _ _ _ len.le,len,Nat.sub_self,List.getD_cons_zero,transport]
      rfl
  intro v C flipped fan cap
  let permutations : List (List ℕ) := [[9,4,0,1,6,7,3,5,2,8],
    [4,9,6,1,0,3,7,8,2,5],
    [0,4,9,6,1,5,3,7,8,2],
    [0,1,6,9,4,5,2,8,7,3],
    [4,0,1,6,9,3,5,2,8,7],
    [4,0,1,2,3,9,5,6,7,8],
    [0,4,3,2,1,5,9,8,7,6],
    [0,1,6,8,5,4,2,9,3,7],
    [0,1,2,7,5,4,6,3,9,8],
    [0,1,2,3,4,5,6,7,8,9]]
  let σ (v i : Fin 10) : Fin 10 := Fin.ofNat 10 ((permutations.getD v.val []).getD i.val 0)
  let p (v i : Fin 10) : Option (Fin 9) :=
    if h : (σ v i).val < 9 then some ⟨(σ v i).val,h⟩ else none
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let F : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let lift (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) := ((p v i).map x).getD false
  have deleted : ∀ v : Fin 10, p v v = none := by decide +kernel
  let norm (a b : Fin 9) : Fin 9 × Fin 9 := (min a b, max a b)
  let mapEdge (v : Fin 10) (e : Fin 10 × Fin 10) : Option (Fin 9 × Fin 9) :=
    (p v e.1).bind fun a => (p v e.2).map (norm a)
  have perm : ∀ v : Fin 10,
      (E.map (mapEdge v)).Perm ((F.map fun e => some (norm e.1 e.2)) ++ [none,none,none]) := by
    decide +kernel
  have geom (v : Fin 10) (x : Fin 9 → Bool) :
      E.any (fun e => lift v x e.1 && lift v x e.2) = F.any (fun e => x e.1 && x e.2) := by
    let mark (e : Fin 9 × Fin 9) := x e.1 && x e.2
    let mark' (e : Option (Fin 9 × Fin 9)) := (e.map mark).getD false
    have commute (a b : Fin 9) : mark (norm a b) = (x a && x b) := by
      by_cases h : a ≤ b
      · simp only [mark, norm, min_eq_left h, max_eq_right h]
      · have hh : b ≤ a := le_of_not_ge h
        simp only [mark,norm,min_eq_right hh,max_eq_left hh,Bool.and_comm]
    have mapMarks (e : Fin 10 × Fin 10) :
        (lift v x e.1 && lift v x e.2) = mark' (mapEdge v e) := by
      rcases h₁ : p v e.1 with _ | a <;> rcases h₂ : p v e.2 with _ | b <;>
        simp [mapEdge,lift,mark',h₁,h₂,commute]
    have invariant {es es' : List (Option (Fin 9 × Fin 9))} (p : es.Perm es') :
        es.any mark' = es'.any mark' := by
      induction p with
      | nil => rfl
      | cons h _ ih => simp only [List.any_cons, ih]
      | swap a b tail => simp only [List.any_cons, Bool.or_left_comm]
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    simp only [mapMarks, ← Function.comp_def (f := mark') (g := mapEdge v), ← List.any_map]
    rw [invariant (perm v)]
    simp only [List.any_append,List.any_map,Function.comp_def,List.any_cons,List.any_nil,
      mark',Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,Bool.or_false,commute]
  obtain ⟨D,hD,size,ev⟩ := transport 10 9 (p v) C flipped fan
  have small : D.size ≤ 15 := size.trans cap
  by_contra misses
  have matching (x : Fin 9 → Bool) : circuitFun 9 D x = F.any (fun e => x e.1 && x e.2) := by
    let y := lift v x
    have pinned : y v = false := by simp [y,lift,deleted v]
    have agrees :
        (if flipped = true then !C.eval (List.ofFn y) else C.eval (List.ofFn y)) =
          E.any (fun e => y e.1 && y e.2) := by
      by_contra diff
      apply misses
      refine ⟨y,pinned,?_⟩
      simpa only [E,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using diff
    exact (ev x).trans (agrees.trans (geom v x))
  have eqFun : circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    simpa only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using matching x
  obtain ⟨exactSize,out,usedGates⟩ := shape D hD eqFun small
  have binaryBound := binary D hD matching
  have nots : PEqualNP.NotBracket.notCount D ≤ 2 := by omega
  obtain ⟨x,hx⟩ := exclude D hD exactSize out nots usedGates
  exact hx (matching x)
