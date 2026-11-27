import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3551_1
    (prune : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (L : List (Option (Fin 7))), PEqualNP.MetaComplexity.FanInTwo D →
      let V := fun (y : Fin 7 → Bool) => L.map fun p => p.elim false y
      let active := fun (j : Fin D.gates.length) =>
        let g := D.gates.get j
        ∀ i ∈ g.inputs, (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∨ g.inputs[0]? = some i) →
          ∃ y z : Fin 7 → Bool, ((⟨D.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (V y)).getD i false ≠
                                ((⟨D.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (V z)).getD i false
      (∃ y z : Fin 7 → Bool, D.eval (V y) ≠ D.eval (V z)) →
      ∃ J : Finset (Fin D.gates.length), (∀ j ∈ J, active j) ∧ PEqualNP.MetaComplexity.HasCircuitSize 7 (fun y => D.eval (V y)) J.card)
    (theta : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 || x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1) s → 11 ≤ s)
    (sparse : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
      let read := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) => g.inputs[0]? = some v ∨ g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ v ∈ g.inputs
      (∀ v ∈ [4,6], ∃! i : Fin D.gates.length, read (D.gates.get i) v) →
      ∀ K : Finset (Fin D.gates.length), K.card + 11 ≤ D.size →
      (∀ j ∉ K, ∀ i ∈ [4,6,9], ¬ read (D.gates.get j) i) →
      (∀ j ∉ K, ∀ i ∈ (D.gates.get j).inputs, read (D.gates.get j) i →
        let S := fun (x : Fin 7 → Bool) => ((⟨D.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires [x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6,false]).getD i false
        ∃ y z, S y ≠ S z) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →     (∀ (x4 : Fin (9 : ℕ) → Bool), { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) x4) →       (∃ (x5 : Fin x1.length) (x6 : Fin x1.length),           x5 < x6 ∧             (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x5;               x7.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x7.inputs) ∧               (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x6;                 x7.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x7.inputs) ∧                 (∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x8.inputs) →                       x7 = x5) ∧                   ∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x8.inputs) →                       x7 = x6) →         (15 : ℕ) ≤ x1.length := by
  classical
  intro t o hfan heval huniq
  obtain ⟨a, b, -, ha4, hb6, hua, hub⟩ := huniq
  by_contra! small
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨t, o⟩
  let F : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have fd : PEqualNP.MetaComplexity.FanInTwo D := hfan
  have sd : D.size ≤ 14 := by
    change t.length ≤ 14
    omega
  have run (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = F x := by
    have h := heval x
    have same : (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) = F := by
      decide +kernel
    exact h.trans (congrFun same x)
  have readers' : ∀ v ∈ [(4 : ℕ), (6 : ℕ)], ∃! i : Fin D.gates.length,
      (D.gates.get i).inputs[0]? = Option.some v ∨ (D.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ v ∈ (D.gates.get i).inputs := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨a, ha4, fun i hi => hua i hi⟩
    · exact ⟨b, hb6, fun i hi => hub i hi⟩
  let L : List (Option (Fin 7)) := [some 4,some 3,some 0,some 5,none,some 1,none,some 2,some 6,none]
  let V (x : Fin 7 → Bool) := L.map fun p => p.elim false x
  let T : (Fin 7 → Bool) → Bool := fun x : Fin 7 → Bool => x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 || x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1
  have keep (tt : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      ((PEqualNP.CircuitLowerBounds.Circuit.mk tt 0).wires w).getD j false = w.getD j false := by
    induction tt generalizing w with
    | nil => rfl
    | cons z tt ih =>
      change ((PEqualNP.CircuitLowerBounds.Circuit.mk tt 0).wires (w ++ [_])).getD j false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hj
  have eval (x : Fin 7 → Bool) : D.eval (V x) = T x := by
    let z : Fin 9 → Bool := ![x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6]
    have h := run z
    change D.eval (V x) = F z at h
    have same : (fun x : Fin 7 → Bool => F ![x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6]) = T := by
      decide +kernel
    exact h.trans (congrFun same x)
  have nt : ∃ y z : Fin 7 → Bool, D.eval (V y) ≠ D.eval (V z) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [eval, eval]; decide
  obtain ⟨J, hJ, h⟩ := prune D L fd nt
  have hsmall : PEqualNP.MetaComplexity.HasCircuitSize 7 T J.card := by
    have eq : (fun y => D.eval (V y)) = T := funext eval
    rw [← eq]; exact h
  let K := Finset.univ \ J
  have restore (j : Fin D.gates.length) (hj : j ∉ K) : j ∈ J := by
    by_contra hjj
    exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjj⟩)
  have budget : K.card + 11 ≤ D.size := by
    have hsd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    have ht := theta _ hsmall
    change (Finset.univ \ J).card + 11 ≤ D.gates.length
    simpa only [Finset.card_univ, Fintype.card_fin] using (Nat.add_le_add_left ht (Finset.univ \ J).card).trans hsd.le
  have varies (j : Fin D.gates.length) (hj : j ∉ K) (i : ℕ) (hi : i ∈ (D.gates.get j).inputs)
      (hr : (D.gates.get j).inputs[0]? = some i ∨ (D.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ i ∈ (D.gates.get j).inputs) :=
    hJ j (restore j hj) i hi (hr.elim Or.inr (fun hh => Or.inl hh.1))
  obtain ⟨y, hy⟩ := sparse D fd sd readers' K budget (by
    intro j hj i hi hr
    have mem : i ∈ (D.gates.get j).inputs := hr.elim (fun hh => List.mem_of_getElem? hh) And.right
    obtain ⟨u, v, hne⟩ := varies j hj i mem hr
    have same (x : Fin 7 → Bool) : ((⟨D.gates.take j.val,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (V x)).getD i false = false := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rw [keep _ _ _ (by simp [V, L])] <;> rfl
    exact hne ((same u).trans (same v).symm)) (by
    intro j hj i hi hr; exact varies j hj i hi hr)
  exact hy (run y)
