import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1988_627
    (compiler :
    ∀ (n : ℕ) (C : Circuit), Monotone2 C →
    let X := Fin n → Bool
    let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin n => {x | x i = true})
    ∃ F : Finset (Set X), F.card ≤ C.size ∧ (∀ z ∈ F, z ∉ B) ∧
      (∀ U : Set (Set X), B ⊆ U →
        (∀ a ∈ U, ∀ b ∈ U, ∀ z ∈ F, z = a ∩ b ∨ z = a ∪ b → z ∈ U) →
        ∀ z ∈ F, z ∈ U) ∧
      ∀ j : ℕ, {x : X | (C.wires (List.ofFn x)).getD j false = true} ∈ B ∪ (F : Set (Set X)))
    (barrier :
      let X := Fin 26 → Bool
      let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x | x i = true})
      let G : Set X := {x | ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true}
      ∀ F : Finset (Set X), F.card ≤ 62 → (∀ z ∈ F, z ∉ B) →
        ∃ U : Set (Set X), B ⊆ U ∧
          (∀ a ∈ U, ∀ b ∈ U, ∀ z ∈ F, z = a ∩ b ∨ z = a ∪ b → z ∈ U) ∧
          ∀ a ∈ U, ∀ b ∈ U, a ∩ b ≠ G) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C pins hm plen tests
  let X := Fin 26 → Bool
  let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x | x i = true})
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let pt (p : Fin 13) := p.castAdd 13
  let ln (l : Fin 13) := Fin.natAdd 13 l
  let G : Set X := {x | ∃ p l : Fin 13, near p l ∧ x (pt p) = true ∧ x (ln l) = true}
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, ¬near p l
  let wire (i : ℕ) : Set X := {x | (C.wires (List.ofFn x)).getD i false = true}
  let yes : Set X := {x | GateOp.and.eval (pins.map fun j => (C.wires (List.ofFn x)).getD j false) = true}
  obtain ⟨F, hc, fresh, ground, wires⟩ := compiler 26 C hm
  change ∀ i, wire i ∈ B ∪ (F : Set (Set X)) at wires
  have topB : (Set.univ : Set X) ∈ B := Or.inl (by simp)
  have eval_and (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have ends : ∃ a ∈ B ∪ (F : Set (Set X)), ∃ b ∈ B ∪ (F : Set (Set X)), yes = a ∩ b := by
    cases e : pins with
    | nil =>
      refine ⟨_, Or.inl topB, _, Or.inl topB, ?_⟩
      ext x
      simp [yes,e,eval_and]
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨_, wires i, _, Or.inl topB, ?_⟩
        ext x
        simp [yes,e,eval_and,wire]
      | cons j tail =>
        cases tail with
        | nil =>
          refine ⟨_, wires i, _, wires j, ?_⟩
          ext x
          simp [yes,e,eval_and,wire]
        | cons k tail => simp [e] at plen
  obtain ⟨a,ha,b,hb,meet⟩ := ends
  let up : Set (Set X) := {z | ∀ x ∈ z, ∀ y : X, (∀ i, x i = true → y i = true) → y ∈ z}
  have baseUp : B ⊆ up := by
    intro z hz x hx y h
    rcases hz with hz | ⟨i,rfl⟩
    · rcases (show z = ∅ ∨ z = Set.univ by simpa using hz) with rfl | rfl
      · exact hx.elim
      · trivial
    · exact h i hx
  have combine : ∀ c ∈ up, ∀ d ∈ up, ∀ z ∈ F, z = c ∩ d ∨ z = c ∪ d → z ∈ up := by
    intro c hc d hd z _ h
    rcases h with rfl | rfl
    · exact fun x hx y h => ⟨hc x hx.1 y h, hd x hx.2 y h⟩
    · exact fun x hx y h => hx.elim (fun h' => Or.inl (hc x h' y h)) (fun h' => Or.inr (hd x h' y h))
  have liftUp : B ∪ (F : Set (Set X)) ⊆ up := fun z hz => hz.elim (fun h => baseUp h) (ground up baseUp combine z)
  have yup : yes ∈ up := by
    rw [meet]
    exact fun x hx y h => ⟨liftUp ha x hx.1 y h,liftUp hb x hx.2 y h⟩
  have mono {s t u v : Finset (Fin 13)} (h : s ⊆ u) (k : t ⊆ v) (old : vec s t ∈ yes) : vec u v ∈ yes := by
    apply yup _ old
    intro i
    by_cases hi : i.val < 13
    · simpa [vec,hi] using h (x := Fin.ofNat 13 i.val)
    · simpa [vec,hi] using k (x := Fin.ofNat 13 i.val)
  have key : ∀ a b c d : Fin 13, a < b → b < c → c < d →
      (Finset.univ.filter fun l : Fin 13 =>
        ¬ ((a : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((b : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧
        ¬ ((c : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((d : ℕ) + l) % 13 ∈ [0, 1, 3, 9]).card ≤ 3 := by
    decide +kernel
  have geometry (X Y : Finset (Fin 13)) (h : ∀ p ∈ X, ∀ l ∈ Y, ¬ near p l) : X.card ≤ 3 ∨ Y.card ≤ 3 := by
    by_contra hc
    push Not at hc
    obtain ⟨X', hX', hc'⟩ := Finset.exists_subset_card_eq (s := X) (n := 4) (by omega)
    let f := X'.orderEmbOfFin hc'
    have hm : ∀ i, f i ∈ X := fun i => hX' (X'.orderEmbOfFin_mem hc' i)
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have h23 : f 2 < f 3 := f.strictMono (by decide)
    have hk := key _ _ _ _ h01 h12 h23
    have hsub : Y ⊆ Finset.univ.filter fun l : Fin 13 =>
        ¬ ((f 0 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((f 1 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧
        ¬ ((f 2 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] ∧ ¬ ((f 3 : ℕ) + l) % 13 ∈ [0, 1, 3, 9] := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h _ (hm 0) l hl, h _ (hm 1) l hl, h _ (hm 2) l hl, h _ (hm 3) l hl⟩
    have := Finset.card_le_card hsub
    omega
  have exactPG : yes = G := by
    ext x
    let s := Finset.univ.filter fun p : Fin 13 => x (pt p) = true
    let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
    have repr : vec s t = x := by
      funext i
      by_cases hi : i.val < 13
      · have hp : pt (Fin.ofNat 13 i.val) = i := Fin.ext (Nat.mod_eq_of_lt hi)
        simp only [vec,ite_eq_left hi,s,Finset.mem_filter,Finset.mem_univ,true_and,hp]
        simp
      · have hl : ln (Fin.ofNat 13 i.val) = i := by
          apply Fin.ext
          change 13+i.val % 13 = i.val
          omega
        simp only [vec,ite_eq_right hi,t,Finset.mem_filter,Finset.mem_univ,true_and,hl]
        simp
    have giff : x ∈ G ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
      change (∃ p l, near p l ∧ _ ∧ _) ↔ _
      simp only [s,t,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        exact ⟨p,hp,l,hl,h⟩
      · rintro ⟨p,hp,l,hl,h⟩
        exact ⟨p,l,h,hp,hl⟩
    rw [giff,←repr]
    constructor
    · intro accepted
      by_contra no
      have miss : ∀ p ∈ s, ∀ l ∈ t, ¬ near p l := fun p hp l hl e => no ⟨p,hp,l,hl,e⟩
      rcases geometry s t miss with sp | st
      · have sub : t ⊆ off s := fun l hl => Finset.mem_filter.mpr ⟨by simp,fun p hp => miss p hp l hl⟩
        have bad := mono (Finset.Subset.rfl : s ⊆ s) sub accepted
        exact Bool.noConfusion (((tests.2 s sp).1).symm.trans bad)
      · have sub : s ⊆ off t := by
          intro p hp
          refine Finset.mem_filter.mpr ⟨by simp,fun l hl => ?_⟩
          simpa only [near,Nat.add_comm l.val p.val] using miss p hp l hl
        have bad := mono sub (Finset.Subset.rfl : t ⊆ t) accepted
        exact Bool.noConfusion (((tests.2 t st).2).symm.trans bad)
    · rintro ⟨p,hp,l,hl,hpl⟩
      exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (tests.1 p l hpl)
  by_contra short
  obtain ⟨U,base,locked,blocked⟩ := barrier F (by omega) fresh
  have lift : B ∪ (F : Set (Set X)) ⊆ U := fun z hz => hz.elim (fun h => base h) (ground U base locked z)
  exact blocked a (lift ha) b (lift hb) (meet.symm.trans exactPG)
