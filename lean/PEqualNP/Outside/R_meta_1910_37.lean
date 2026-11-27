import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Restrict both marked inputs to false. The surviving seven-variable function is theta.
-- Its exact lower bound forces eleven tail gates whose effective operands all vary on that slice.
theorem PEqualNP.Outside.R_meta_1910_37
    (prune : ∀ (D : Circuit) (L : List (Option (Fin 7))), FanInTwo D →
      let V := fun (y : Fin 7 → Bool) => L.map fun p => p.elim false y
      let active := fun (j : Fin D.gates.length) =>
        let g := D.gates.get j
        ∀ i ∈ g.inputs, (g.op ≠ GateOp.not ∨ g.inputs[0]? = some i) →
          ∃ y z : Fin 7 → Bool, ((⟨D.gates.take j.val,0⟩ : Circuit).wires (V y)).getD i false ≠
                                ((⟨D.gates.take j.val,0⟩ : Circuit).wires (V z)).getD i false
      (∃ y z : Fin 7 → Bool, D.eval (V y) ≠ D.eval (V z)) →
      ∃ J : Finset (Fin D.gates.length), (∀ j ∈ J, active j) ∧ HasCircuitSize 7 (fun y => D.eval (V y)) J.card)
    (theta : ∀ s : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool => x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 || x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1) s → 11 ≤ s)
    (sparse : ∀ (D : Circuit), FanInTwo D → D.size ≤ 14 →
      let read := fun (g : Gate) (v : ℕ) => g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
      (∀ v ∈ [4,6], ∃! i : Fin D.gates.length, read (D.gates.get i) v) →
      ∀ K : Finset (Fin D.gates.length), K.card + 11 ≤ D.size →
      (∀ j ∉ K, ∀ i ∈ [4,6,9], ¬ read (D.gates.get j) i) →
      (∀ j ∉ K, ∀ i ∈ (D.gates.get j).inputs, read (D.gates.get j) i →
        let S := fun (x : Fin 7 → Bool) => ((⟨D.gates.take j.val,0⟩ : Circuit).wires [x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6,false]).getD i false
        ∃ y z, S y ≠ S z) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6]) ≠ (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) →       (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →         (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)],             ∃! x7 : Fin (List.drop (1 : ℕ) x1.gates).length,               have x8 : PEqualNP.CircuitLowerBounds.Gate := (List.drop (1 : ℕ) x1.gates).get x7;               x8.inputs[(0 : ℕ)]? = Option.some x5 ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x8.inputs) →           (16 : ℕ) ≤ x1.size := by
  classical
  intro C hfan first target readers
  by_contra! small
  cases C with | mk gs out =>
    cases gs with
    | nil =>
      obtain ⟨i,_⟩ := readers 4 (by simp)
      exact Fin.elim0 i
    | cons g tail =>
      let D : Circuit := ⟨tail,out⟩
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      have fd : FanInTwo D := fun z hz => hfan z (List.mem_cons_of_mem _ hz)
      have sd : D.size ≤ 14 := by change (g::tail).length < 16 at small; change tail.length ≤ 14; simp at small; omega
      have keep (t : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
          ((Circuit.mk t 0).wires w).getD j false = w.getD j false := by
        induction t generalizing w with
        | nil => rfl
        | cons z t ih =>
          change ((Circuit.mk t 0).wires (w ++ [_])).getD j false = _
          rw [ih _ (by simp; omega)]
          exact List.getD_append _ _ _ _ hj
      have run (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = F x := by
        let v := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
        have h := first x
        change ((Circuit.mk tail 0).wires (List.ofFn x ++ [v])).getD 9 false = _ at h
        rw [keep _ _ _ (by simp)] at h
        have hv : v = (x 4 || x 6) := by simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using h
        have hh := congrFun target x
        change D.eval (List.ofFn x ++ [v]) = _ at hh
        rw [hv] at hh
        have same : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = F := by decide +kernel
        exact hh.trans (congrFun same x)
      let L : List (Option (Fin 7)) := [some 4,some 3,some 0,some 5,none,some 1,none,some 2,some 6,none]
      let V (x : Fin 7 → Bool) := L.map fun p => p.elim false x
      let T := fun x : Fin 7 → Bool => x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 || x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1
      have eval (x : Fin 7 → Bool) : D.eval (V x) = T x := by
        let z : Fin 9 → Bool := ![x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6]
        have h := run z
        change D.eval (V x) = F z at h
        have same : (fun x : Fin 7 → Bool => F ![x 4,x 3,x 0,x 5,false,x 1,false,x 2,x 6]) = T := by decide +kernel
        exact h.trans (congrFun same x)
      have nt : ∃ y z : Fin 7 → Bool, D.eval (V y) ≠ D.eval (V z) := by
        refine ⟨fun _ => false,fun _ => true,?_⟩
        rw [eval,eval]; decide
      obtain ⟨J,hJ,h⟩ := prune D L fd nt
      have hsmall : HasCircuitSize 7 T J.card := by
        have eq : (fun y => D.eval (V y)) = T := funext eval
        rw [← eq]; exact h
      let K := Finset.univ \ J
      have restore (j : Fin D.gates.length) (hj : j ∉ K) : j ∈ J := by
        by_contra h; exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩)
      have budget : K.card + 11 ≤ D.size := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
        have ht := theta _ hsmall
        change (Finset.univ \ J).card + 11 ≤ D.gates.length
        simpa only [Finset.card_univ, Fintype.card_fin] using (Nat.add_le_add_left ht (Finset.univ \ J).card).trans h.le
      have varies (j : Fin D.gates.length) (hj : j ∉ K) (i : ℕ) (hi : i ∈ (D.gates.get j).inputs)
          (hr : (D.gates.get j).inputs[0]? = some i ∨ (D.gates.get j).op ≠ GateOp.not ∧ i ∈ (D.gates.get j).inputs) :=
        hJ j (restore j hj) i hi (hr.elim Or.inr (fun h => Or.inl h.1))
      obtain ⟨y,hy⟩ := sparse D fd sd readers K budget (by
        intro j hj i hi hr
        have mem : i ∈ (D.gates.get j).inputs := hr.elim (fun h => List.mem_of_getElem? h) And.right
        obtain ⟨u,v,hne⟩ := varies j hj i mem hr
        have same (x : Fin 7 → Bool) : ((⟨D.gates.take j.val,0⟩ : Circuit).wires (V x)).getD i false = false := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl <;> rw [keep _ _ _ (by simp [V,L])] <;> rfl
        exact hne ((same u).trans (same v).symm)) (by
        intro j hj i hi hr; exact varies j hj i hi hr)
      exact hy (run y)
