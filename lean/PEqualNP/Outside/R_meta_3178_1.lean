import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3178_1
    (renameInputs : ∀ (n : ℕ) (e : Equiv.Perm (Fin n)) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (tail : List Bool),
        D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (fun i => x (e i)) ++ tail))
    (case4 : ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ (x9 : Fin 9 → Bool),
        C.eval (List.ofFn x9 ++ [!x9 0, x9 0 || x9 4]) ≠
          (x9 0 && x9 1 || x9 1 && x9 2 || x9 2 && x9 3 || x9 3 && x9 4 || x9 4 && x9 0 ||
           x9 0 && x9 5 || x9 1 && x9 6 || x9 2 && x9 7 || x9 3 && x9 8 || x9 5 && x9 7 ||
           x9 6 && x9 8 || x9 8 && x9 5))
    (case16 : ∀ b : Fin 9, (b = 1 ∨ b = 6) → ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ (x9 : Fin 9 → Bool),
        C.eval (List.ofFn x9 ++ [!x9 0, x9 0 || x9 b]) ≠
          (x9 0 && x9 1 || x9 1 && x9 2 || x9 2 && x9 3 || x9 3 && x9 4 || x9 4 && x9 0 ||
           x9 0 && x9 5 || x9 1 && x9 6 || x9 2 && x9 7 || x9 3 && x9 8 || x9 5 && x9 7 ||
           x9 6 && x9 8 || x9 8 && x9 5))
    (case23 : ∀ b : Fin 9, (b = 2 ∨ b = 3) → ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ (x9 : Fin 9 → Bool),
        C.eval (List.ofFn x9 ++ [!x9 0, x9 0 || x9 b]) ≠
          (x9 0 && x9 1 || x9 1 && x9 2 || x9 2 && x9 3 || x9 3 && x9 4 || x9 4 && x9 0 ||
           x9 0 && x9 5 || x9 1 && x9 6 || x9 2 && x9 7 || x9 3 && x9 8 || x9 5 && x9 7 ||
           x9 6 && x9 8 || x9 8 && x9 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hlt _ hspec C hfan hsize
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have hget : ∀ (x : Fin 9 → Bool) (k : Fin 9),
      (List.ofFn x ++ [!x 0]).getD k.val false = x k := by
    intro x k
    fin_cases k <;> rfl
  have hget0 : ∀ (x : Fin 9 → Bool), (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := fun _ => rfl
  have hex : ∃ b : Fin 9, b ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (x 0 || x b) := by
    obtain ⟨hnotall, h0mem⟩ := hspec
    cases x1 with
    | nil => cases hlen
    | cons u rest =>
      cases rest with
      | nil => cases hlen
      | cons w rest2 =>
        cases rest2 with
        | cons _ _ => cases hlen
        | nil =>
          by_cases hu : u = 0
          · subst hu
            have hw0 : w ≠ 0 := fun hw => hnotall (by subst hw; simp)
            have hw9 : w ≠ 9 := fun hw => hnotall (by subst hw; simp)
            have hw10 : w < 10 := hlt w (by simp)
            have hwlt : w < 9 := by omega
            refine ⟨⟨w, hwlt⟩, fun h => hw0 (congrArg Fin.val h), fun x => ?_⟩
            change ((List.ofFn x ++ [!x 0]).getD 0 false ||
              ((List.ofFn x ++ [!x 0]).getD w false || false)) = (x 0 || x ⟨w, hwlt⟩)
            rw [Bool.or_false, hget0 x, hget x ⟨w, hwlt⟩]
          · have hw : w = 0 := by simp at h0mem; omega
            subst hw
            have hu9 : u ≠ 9 := fun hu9' => hnotall (by subst hu9'; simp)
            have hu10 : u < 10 := hlt u (by simp)
            have hult : u < 9 := by omega
            refine ⟨⟨u, hult⟩, fun h => hu (congrArg Fin.val h), fun x => ?_⟩
            change ((List.ofFn x ++ [!x 0]).getD u false ||
              ((List.ofFn x ++ [!x 0]).getD 0 false || false)) = (x 0 || x ⟨u, hult⟩)
            rw [Bool.or_false, hget x ⟨u, hult⟩, hget0 x, Bool.or_comm]
  obtain ⟨b, hb0, hpair⟩ := hex
  change ∃ x, C.eval ((List.ofFn x ++ [!x 0]) ++
    [GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) ≠ F x
  simp_rw [hpair, List.append_assoc, List.cons_append, List.nil_append]
  let v : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have inv : ∀ i, v (v i) = i := by decide
  let e : Equiv.Perm (Fin 9) := ⟨v, v, inv, inv⟩
  have symmF : ∀ (x : Fin 9 → Bool), F (fun i => x (v i)) = F x := by decide +kernel
  have transfer (k : Fin 9) (hk : v b = k)
      (hrep : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 0 || x k]) ≠ F x) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x b]) ≠ F x := by
    obtain ⟨D, hD, hsz, heval⟩ := renameInputs 9 e C hfan
    obtain ⟨x, hx⟩ := hrep D hD (hsz ▸ hsize)
    refine ⟨fun i => x (v i), ?_⟩
    rw [symmF x]
    dsimp only
    have hb_eq : x (v b) = x k := congrArg x hk
    have h0_eq : x (v 0) = x 0 := congrArg x (by decide : v 0 = 0)
    rw [h0_eq, hb_eq]
    rw [heval] at hx
    exact hx
  fin_cases b
  · exact absurd rfl hb0
  · exact case16 1 (Or.inl rfl) C hfan hsize
  · exact case23 2 (Or.inl rfl) C hfan hsize
  · exact case23 3 (Or.inr rfl) C hfan hsize
  · exact case4 C hfan hsize
  · exact transfer 1 (by decide) (case16 1 (Or.inl rfl))
  · exact case16 6 (Or.inr rfl) C hfan hsize
  · exact transfer 6 (by decide) (case16 6 (Or.inr rfl))
  · exact transfer 2 (by decide) (case23 2 (Or.inl rfl))
