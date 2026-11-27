import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire relabeling follows the upstream proof of R_meta_2736_91.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3632_606
    (at0 : ∀ (C : Circuit) (j : Fin 9), j ∈ ([1,2,3,6] : List (Fin 9)) →
      FanInTwo C → C.size = 13 →
      ¬∀ (x : Fin 9 → Bool), C.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x j]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun z => x z.1 && x z.2))
    (at4 : ∀ (C : Circuit) (j : Fin 9), j ∈ ([1,2,3,6] : List (Fin 9)) →
      FanInTwo C → C.size = 13 →
      ¬∀ (x : Fin 9 → Bool), C.eval (List.ofFn x ++ [x 0 || x 4, x 4 || x j]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun z => x z.1 && x z.2))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → ¬Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  let mapGate (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let rewired (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate σ),σ C.output⟩

  have fan {C : Circuit} (σ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (rewired σ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h a ha).1,by simpa [mapGate] using (h a ha).2⟩

  have run {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (gs : List Gate) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires y).getD (σ i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map (fun i => x.getD i false))
      have same : (mapGate σ g).op.eval ((mapGate σ g).inputs.map (fun i => y.getD i false)) = b := by
        simp only [b,mapGate,List.map_map,Function.comp_def,agree]
      change ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires (y++[_])).getD (σ i) false =
        ((Circuit.mk gs 0).wires (x++[b])).getD i false
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i<x.length
      · have hsi : σ i<y.length := by
          by_cases hr : i<cut
          · have := raw i hr; omega
          · rw [later i (by omega)]; omega
        rw [List.getD_append _ _ _ _ hsi, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [later i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]

  have evalMap {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (C : Circuit) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      (rewired σ C).eval y = C.eval x :=
    run σ raw later C.gates x y len lo agree C.output

  let rawMap (p : Fin 9 → Fin 9) (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i

  have permute (C : Circuit) (p : Fin 9 → Fin 9) (hc : FanInTwo C) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin 9 → Bool) (a b : Bool),
          D.eval (List.ofFn x ++ [a,b]) = C.eval (List.ofFn (x ∘ p) ++ [a,b]) := by
    let σ := rawMap p
    refine ⟨rewired σ C,fan σ hc,?_,?_⟩
    · change (C.gates.map (mapGate σ)).length = C.gates.length
      exact List.length_map (mapGate σ)
    · intro x a b
      have small (i : ℕ) (hi : i<9) : σ i < 9 := by simp [σ,rawMap,hi]
      have late (i : ℕ) (hi : 9 ≤ i) : σ i=i := by simp [σ,rawMap,Nat.not_lt.mpr hi]
      apply evalMap σ small late C _ _ (by simp) (by simp)
      intro i
      by_cases h : i<9
      · have h1 : σ i < (List.ofFn x).length := by simpa using small i h
        have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using h
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2]
        simp only [List.getElem_ofFn,Function.comp_apply]
        congr 1
        apply Fin.ext
        exact dite_eq_left h
      · have hn : 9 ≤ i := by omega
        rw [late i hn, List.getD_append_right _ _ _ _ (by simpa using hn),
          List.getD_append_right _ _ _ _ (by simpa using hn)]
        simp
  let p (j : Fin 9) := Fin.ofNat 9 (([0,5,8,3,4,1,7,6,2] : List Nat).getD j.val 0)
  let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun z => x z.1 && x z.2)
  have sym : ∀ x : Fin 9 → Bool, edge (x ∘ p) = edge x := by decide +kernel
  have invol : ∀ j : Fin 9, p (p j) = j := by decide +kernel
  have catalog : ∀ a b : Fin 9, a ≠ b → ({a,b} : Finset (Fin 9)) ≠ {0,4} →
      (a = 0 ∨ a = 4 ∨ b = 0 ∨ b = 4) →
      ∃ u : Fin 9, (u = 0 ∨ u = 4) ∧ ∃ j ∈ ([1,2,3,6] : List (Fin 9)),
        ({a,b} : Finset (Fin 9)) = {u,j} ∨ ({a,b} : Finset (Fin 9)) = {u,p j} := by decide +kernel
  intro C S basis card diff hit len correct
  obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp card
  have cover : a = 0 ∨ a = 4 ∨ b = 0 ∨ b = 4 := by
    obtain ⟨z,ha,hb⟩ := Finset.not_disjoint_iff.mp hit
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with h|h <;> simp [h]
  obtain ⟨u,which,j,member,orientation⟩ := catalog a b ab diff cover
  have val (w : Fin 9) (e : ({a,b} : Finset (Fin 9)) = {u,w}) (x : Fin 9 → Bool) :
      decide (∃ i ∈ ({a,b} : Finset (Fin 9)), x i = true) = (x u || x w) := by
    rw [e]
    apply Bool.eq_iff_iff.mpr
    simp
  have no (D : Circuit) (hd : FanInTwo D) (hs : D.size = 13) :
      ¬∀ x, D.eval (List.ofFn x ++ [x 0 || x 4,x u || x j]) = edge x := by
    rcases which with h|h
    · rw [h]
      exact at0 D j member hd hs
    · rw [h]
      exact at4 D j member hd hs
  rcases orientation with e|e
  · apply no C basis len
    intro x
    simpa only [val j e x] using correct x
  · obtain ⟨D,hd,hs,ev⟩ := permute C p basis
    apply no D hd (hs.trans len)
    intro x
    rw [ev]
    have same := (correct (x ∘ p)).trans (sym x)
    rw [val (p j) e] at same
    have pu : p u = u := by rcases which with h|h <;> rw [h] <;> rfl
    have p0 : p 0 = 0 := rfl
    have p4 : p 4 = 4 := rfl
    simpa only [Function.comp_apply,p0,p4,pu,invol] using same
