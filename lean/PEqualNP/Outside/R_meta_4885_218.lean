import PEqualNP.Defs

-- The finite search uses a row number for each boundary input. Lifting a set
-- of rows to its image preserves the union and intersection inclusions.
theorem PEqualNP.Outside.R_meta_4885_218
    (search :
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13,
        (p.val+l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x (p.castAdd 13) = true ∧
          x (Fin.natAdd 13 l) = true
      ∀ E : Fin 756 → Fin 26 → Bool,
      (∀ x, (Minimal F x ∨ Maximal (fun y => ¬F y) x) → ∃ j, E j=x) →
      ∃ b ∈ ([1,13,15] : List (Fin 26)), ∃ o : Bool,
      let init := ((List.ofFn fun i : Fin 26 => fun j : Fin 756 => E j i) ++
        [fun j => if o then E j 0 || E j b else E j 0 && E j b]).map
        (fun f q => {j | f j=q})
      ∃ (A : List (Bool → Set (Fin 756))) (r : Bool → Set (Fin 756)),
        A.length ≤ 62 ∧ r ∈ init ++ A ∧
        (∀ i : Fin A.length,
          let B := init ++ A.take i.val
          ∃ a ∈ B, ∃ b ∈ B, ∃ d : Bool, ∀ q : Bool,
            A.get i q ⊆ if q=d then a q ∪ b q else a q ∩ b q) ∧
        ∀ j, j ∈ r (decide (F (E j))))
    (cover :
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13,
        (p.val+l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ x (p.castAdd 13) = true ∧
          x (Fin.natAdd 13 l) = true
      ∃ E : Fin 756 → Fin 26 → Bool,
        ∀ x, (Minimal F x ∨ Maximal (fun y => ¬F y) x) → ∃ j, E j=x) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ x3 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ))],   ∃ (x4 : Bool),     have x5 : List ((Fin (26 : ℕ) → Bool) → Bool) := (List.ofFn fun (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (26 : ℕ) → Bool) => if x4 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x3 else x5 (0 : Fin (26 : ℕ)) && x5 x3];     have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x6 : (Fin (26 : ℕ) → Bool) → Bool) (x7 : Bool) => {x8 : Fin (26 : ℕ) → Bool | x6 x8 = x7}) x5;     ∃ (x7 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x8 : Bool → Set (Fin (26 : ℕ) → Bool)),       x7.length ≤ (62 : ℕ) ∧         x8 ∈ x6 ++ x7 ∧           (∀ (x9 : Fin x7.length),               have x10 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x6 ++ List.take (↑x9) x7;               ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool), ∀ (x14 : Bool), x7.get x9 x14 ⊆ if x14 = x13 then x11 x14 ∪ x12 x14 else x11 x14 ∩ x12 x14) ∧             ∀ (x9 : Fin (26 : ℕ) → Bool), (Minimal x2 x9 → x9 ∈ x8 Bool.true) ∧ (Maximal (fun (x10 : Fin (26 : ℕ) → Bool) => ¬x2 x10) x9 → x9 ∈ x8 Bool.false) := by
  classical
  dsimp only at search cover ⊢
  obtain ⟨E,onto⟩ := cover
  obtain ⟨b,hb,o,A,r,bound,output,valid,labels⟩ := search E onto
  let X := Fin 26 → Bool
  let raw := (List.ofFn fun (i : Fin 26) (x : X) => x i) ++
    [fun (x : X) => if o then x 0 || x b else x 0 && x b]
  let U : List (Bool → Set X) := raw.map fun f q => {x | f x=q}
  let cut (g : Bool → Set X) (q : Bool) : Set (Fin 756) := E ⁻¹' g q
  let lift (g : Bool → Set (Fin 756)) (q : Bool) : Set X := E '' g q
  have start : ((List.ofFn fun (i : Fin 26) (j : Fin 756) => E j i) ++
      [fun j => if o then E j 0 || E j b else E j 0 && E j b]).map
        (fun f q => {j | f j=q}) = U.map cut := by
    simp only [U,raw,cut,List.map_append,List.map_ofFn,List.map_map,
      List.map_cons,List.map_nil,Function.comp_def]
    rfl
  rw [start] at output valid
  have source {Z : List (Bool → Set (Fin 756))} {g} (h : g ∈ U.map cut ++ Z) :
      ∃ h' ∈ U ++ Z.map lift, ∀ q j, j ∈ g q → E j ∈ h' q := by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨g',hu,rfl⟩ := List.mem_map.mp h
      exact ⟨g',List.mem_append_left _ hu,fun _ _ yes => yes⟩
    · exact ⟨lift g,List.mem_append_right _ (List.mem_map.mpr ⟨g,h,rfl⟩),fun _ j yes =>
        ⟨j,yes,rfl⟩⟩
  obtain ⟨root,member,carries⟩ := source output
  refine ⟨b,hb,o,A.map lift,root,by simpa using bound,member,?_,?_⟩
  · intro i
    let j : Fin A.length := ⟨i.val,by simpa using i.isLt⟩
    obtain ⟨left,hl,right,hr,d,step⟩ := valid j
    obtain ⟨a,ha,mapA⟩ := source hl
    obtain ⟨b,hb,mapB⟩ := source hr
    refine ⟨a,by simpa only [List.map_take,j] using ha,
      b,by simpa only [List.map_take,j] using hb,d,?_⟩
    intro q x hx
    have lifted : x ∈ lift (A.get j) q := by
      simpa only [List.get_eq_getElem,List.getElem_map,j] using hx
    obtain ⟨t,ht,rfl⟩ := lifted
    have rule := step q ht
    by_cases eq : q=d
    · rw [if_pos eq] at rule ⊢
      exact rule.elim (fun h => Or.inl (mapA q t h)) (fun h => Or.inr (mapB q t h))
    · rw [if_neg eq] at rule ⊢
      exact ⟨mapA q t rule.1,mapB q t rule.2⟩
  · intro x
    constructor
    · intro pos
      obtain ⟨j,rfl⟩ := onto x (Or.inl pos)
      exact carries true j (by simpa only [decide_eq_true pos.1] using labels j)
    · intro neg
      obtain ⟨j,rfl⟩ := onto x (Or.inr neg)
      exact carries false j (by simpa only [decide_eq_false neg.1] using labels j)
