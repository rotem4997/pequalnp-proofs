import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_5361_1
    (search : ∃ H : Circuit, Monotone2 H ∧ ReadsBack 21 H ∧ H.output < 21 + H.size ∧ H.size ≤ 33 ∧
  ∀ z : Fin 21 → Bool, H.eval (List.ofFn z) = ((List.range 7).flatMap fun i => ([14+i, 7+i, 7+(i+1)%7, 7+(i+5)%7] : List ℕ).map fun j => (Fin.ofNat 21 i, Fin.ofNat 21 j)).any (fun e => z e.1 && z e.2))
    (project : ∀ (n k m : ℕ) (pairs : Fin k → Fin n × Fin n) (ports : Fin m → Fin (n+k)) (H : Circuit),
  Monotone2 H → ReadsBack m H → H.output < m + H.size →
  ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.output < n+C.size ∧ C.size ≤ k+H.size ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = H.eval (List.ofFn fun i =>
      Fin.addCases x (fun a => x (pairs a).1 || x (pairs a).2) (ports i)))
    (attach : ∀ (n : ℕ) (C : Circuit) (B : List (Fin n × List (Fin n))),
  Monotone2 C → ReadsBack n C → C.output < n+C.size →
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
    D.size ≤ C.size + (B.map fun s => s.2.length+1).sum ∧
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      (C.eval (List.ofFn x) || B.any (fun s => x s.1 && s.2.any x)))
    : ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     (have x5 : List ℕ := if x1 = (1 : Fin (42 : ℕ)) then [(81788948 : ℕ), (0 : ℕ), (4398145077304 : ℕ), (0 : ℕ), (4398077984768 : ℕ), (4398059094016 : ℕ), (4398256226304 : ℕ), (4406653222912 : ℕ)] else if x1 = (21 : Fin (42 : ℕ)) then [(71303174 : ℕ), (4398126202900 : ℕ), (4398067482760 : ℕ)] else [(10485770 : ℕ), (4398258323484 : ℕ), (0 : ℕ), (4402383429648 : ℕ)];       (x5.getD (List.idxOf ↑x2 [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (21 : ℕ), (22 : ℕ), (23 : ℕ)]) (0 : ℕ)).testBit ↑x3 = Bool.true) ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧           x4.size ≤ (122 : ℕ) ∧             ∀ (x5 : Fin (42 : ℕ) → Bool),               have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;               x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  let ce : List (Fin 21 × Fin 21) := ((List.range 7).flatMap fun i => ([14+i, 7+i, 7+(i+1)%7, 7+(i+5)%7] : List ℕ).map fun j => (Fin.ofNat 21 i, Fin.ofNat 21 j))
  let pairs : Fin 7 → Fin 44 × Fin 44 := fun i =>
    (Fin.ofNat 44 (3*i.val+1), Fin.ofNat 44 ((3*i.val+15)%21))
  let ports : Fin 21 → Fin (44+7) := fun i =>
    Fin.ofNat 51 (if i.val < 7 then 22+3*i.val else if i.val < 14 then 2+3*(i.val-7) else 44+(i.val-14))
  let stars : List (Fin 44 × List (Fin 44)) :=
    ([0,2,3,5,6,8,9,11,12,14,15,17,18,20] : List ℕ).map fun l =>
      (Fin.ofNat 44 (21+l), if l = 0 then [42,43,16] else
        ([0,5,7,17,20] : List ℕ).map fun d => Fin.ofNat 44 ((l+21-d)%21))
  obtain ⟨H, hm, hr, ho, hs, he⟩ := search
  obtain ⟨C, cm, cr, co, cs, hc⟩ := project 44 7 21 pairs ports H hm hr ho
  obtain ⟨D, dm, dr, ds, hd⟩ := attach 44 C stars cm cr co
  have cost : (stars.map (fun s => s.2.length+1)).sum = 82 := by decide
  refine ⟨1,4,14,D, Or.inl rfl, by decide, dm, dr, by omega, ?_⟩
  let raw : Fin 44 → List (Fin 42) := fun i => if i.val = 43 then [4,14] else if i.val = 42 then [0,1] else [Fin.ofNat 42 i.val]
  let src : Fin (44+7) → List (Fin 42) := fun w => if w.val < 44 then raw (Fin.ofNat 44 w.val) else
    let j := Fin.ofNat 7 (w.val-44); raw (pairs j).1 ++ raw (pairs j).2
  let allEdges : List (Fin 42 × Fin 42) :=
    (ce.flatMap fun e => (src (ports e.1)).flatMap fun l => (src (ports e.2)).map fun p => (p,l)) ++
    (stars.flatMap fun s => (raw s.1).flatMap fun l => s.2.flatMap fun j => (raw j).map fun p => (p,l))
  let incident := fun (p l : Fin 42) => p.val < 21 ∧ 21 ≤ l.val ∧
    (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let offs : List ℕ := [0,5,7,17,20]
  let order : List (Fin 21) := [1,4,7,10,13,16,19,0,2,3,5,6,8,9,11,12,14,15,17,18,20]
  let shifts : Fin 21 → List ℕ := fun i =>
    if i.val % 3 = 1 then [0,7,20,17,5] else if i = 0 then [0,20,17,7,5] else offs
  let standard : List (Fin 42 × Fin 42) := order.flatMap fun i =>
    (shifts i).map fun d => (Fin.ofNat 42 ((i.val+21-d)%21), Fin.ofNat 42 (21+i.val))
  have same : allEdges = standard := by decide
  have inorder : ∀ i : Fin 21, i ∈ order := by decide
  have perm (i : Fin 21) (d : ℕ) : d ∈ shifts i ↔ d ∈ offs := by
    dsimp only [shifts]
    split
    · simp [offs, or_comm, or_left_comm, or_assoc]
    · split
      · simp [offs, or_comm, or_left_comm, or_assoc]
      · rfl
  have checkEdges (p l : Fin 42) : (p,l) ∈ allEdges ↔ incident p l := by
    rw [same]
    simp only [standard, List.mem_flatMap, inorder, true_and, List.mem_map, Prod.mk.injEq, perm]
    constructor
    · rintro ⟨i,d,hd,rfl,rfl⟩
      have h20 : d ≤ 20 := by
        simp [offs] at hd
        omega
      have ih := i.isLt
      change ((i.val + 21 - d) % 21) % 42 < 21 ∧ 21 ≤ (21+i.val)%42 ∧ _ ∈ offs
      refine ⟨by omega, by omega, ?_⟩
      change (((21+i.val)%42 + 21 - (((i.val+21-d)%21)%42))%21) ∈ offs
      convert hd using 1 <;> omega
    · rintro ⟨hp,hl,hd⟩
      let i : Fin 21 := ⟨l.val - 21, by have := l.isLt; omega⟩
      refine ⟨i,(l.val+21-p.val)%21,hd,Fin.ext ?_,Fin.ext ?_⟩
      · change ((l.val-21+21-(l.val+21-p.val)%21)%21)%42 = p.val
        omega
      · change (21+(l.val-21))%42 = l.val
        have := l.isLt
        omega
  intro x
  let a : Fin 43 → Bool := Fin.lastCases (x 0 || x 1) x
  let b : Fin 44 → Bool := Fin.lastCases (a 4 || a 14) a
  let y : Fin 21 → Bool := fun i => Fin.addCases b (fun j => b (pairs j).1 || b (pairs j).2) (ports i)
  have rb : ∀ i, b i = true ↔ ∃ j ∈ raw i, x j = true := by
    intro i
    have h4 : a 4 = x 4 := Fin.lastCases_castSucc (motive := fun _ => Bool) (last := x 0 || x 1) (cast := x) (4 : Fin 42)
    have h14 : a 14 = x 14 := Fin.lastCases_castSucc (motive := fun _ => Bool) (last := x 0 || x 1) (cast := x) (14 : Fin 42)
    refine Fin.lastCases (motive := fun j => b j = true ↔ ∃ t ∈ raw j, x t = true) ?_ (fun t => ?_) i
    · rw [show b (Fin.last 43) = (a 4 || a 14) from Fin.lastCases_last, h4, h14]
      change (x 4 || x 14) = true ↔ ∃ j ∈ ([4,14] : List (Fin 42)), x j = true
      simp [Bool.or_eq_true]
    · rw [show b t.castSucc = a t from Fin.lastCases_castSucc _]
      refine Fin.lastCases (motive := fun j => a j = true ↔ ∃ u ∈ raw j.castSucc, x u = true) ?_ (fun q => ?_) t
      · rw [show a (Fin.last 42) = (x 0 || x 1) from Fin.lastCases_last]
        change (x 0 || x 1) = true ↔ ∃ j ∈ ([0,1] : List (Fin 42)), x j = true
        simp [Bool.or_eq_true]
      · rw [show a q.castSucc = x q from Fin.lastCases_castSucc _]
        have h43 : q.val ≠ 43 := by omega
        have h42 : q.val ≠ 42 := by omega
        simp [raw, h43, h42]
  have ry (i) : y i = true ↔ ∃ j ∈ src (ports i), x j = true := by
    have h (w : Fin (44+7)) : Fin.addCases b (fun j => b (pairs j).1 || b (pairs j).2) w = true ↔
        ∃ j ∈ src w, x j = true := by
      refine Fin.addCases (motive := fun w => Fin.addCases b (fun j => b (pairs j).1 || b (pairs j).2) w = true ↔
        ∃ j ∈ src w, x j = true) (fun u => ?_) (fun v => ?_) w
      · simpa [src, Fin.addCases_left, u.isLt] using rb u
      · rw [Fin.addCases_right]
        have hsv : src (Fin.natAdd 44 v) = raw (pairs v).1 ++ raw (pairs v).2 := by
          simp [src, Fin.natAdd]
        rw [hsv]
        simp only [Bool.or_eq_true, rb, List.mem_append]
        constructor
        · rintro (⟨j,hj,hx⟩ | ⟨j,hj,hx⟩)
          · exact ⟨j,Or.inl hj,hx⟩
          · exact ⟨j,Or.inr hj,hx⟩
        · rintro ⟨j,h1|h2,hx⟩
          · exact Or.inl ⟨j,h1,hx⟩
          · exact Or.inr ⟨j,h2,hx⟩
    exact h (ports i)
  change D.eval (List.ofFn b) = true ↔ ∃ p l, incident p l ∧ x p = true ∧ x l = true
  rw [hd, hc, he]
  change ((ce.any (fun e => y e.1 && y e.2)) || stars.any (fun s => b s.1 && s.2.any b)) = true ↔ _
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, ry, rb]
  constructor
  · rintro (⟨e, he', ⟨l, hl, xl⟩, ⟨p, hp, xp⟩⟩ | ⟨s, hs', ⟨l, hl, xl⟩, j, hj, p, hp, xp⟩)
    · exact ⟨p,l,(checkEdges p l).mp (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨e,he',List.mem_flatMap.mpr ⟨l,hl,List.mem_map.mpr ⟨p,hp,rfl⟩⟩⟩)),xp,xl⟩
    · exact ⟨p,l,(checkEdges p l).mp (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨s,hs',List.mem_flatMap.mpr ⟨l,hl,List.mem_flatMap.mpr ⟨j,hj,List.mem_map.mpr ⟨p,hp,rfl⟩⟩⟩⟩)),xp,xl⟩
  · rintro ⟨p,l,had,xp,xl⟩
    have hh := (checkEdges p l).mpr had
    simp only [allEdges, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hh
    rcases hh with ⟨e,he',_,hl,_,hp,rfl,rfl⟩ | ⟨s,hs',_,hl,j,hj,_,hp,rfl,rfl⟩
    · exact Or.inl ⟨e,he',⟨_,hl,xl⟩,_,hp,xp⟩
    · exact Or.inr ⟨s,hs',⟨_,hl,xl⟩,j,hj,_,hp,xp⟩
