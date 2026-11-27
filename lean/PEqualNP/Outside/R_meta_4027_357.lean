import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- A final layer of ANDs or ORs can be chosen by a set cover on the boundary rows.
-- The circuit starts with the required point pair already available as an input.
theorem PEqualNP.Outside.R_meta_4027_357
    (collector : ∀ (n : ℕ) (useOr : Bool) (a : Fin n) (s : List (Fin n)),
      s ≠ [] → (a :: s).Nodup →
      ∃ J : Circuit, J.size = s.length ∧ J.output = n + J.size - 1 ∧
        IsAO2 n J ∧ (∀ g ∈ J.gates, g.inputs.Nodup) ∧
        ∀ u : List Bool, u.length = n →
          J.eval u = (if useOr then (a :: s).any (fun i => u.getD i.val false)
                     else (a :: s).all (fun i => u.getD i.val false)))
    (cover :
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, l ≠ 1 ∧
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ (D : Circuit) (useOr : Bool) (a : Fin (27+D.size)) (s : List (Fin (27+D.size))),
        s ≠ [] ∧ (a :: s).Nodup ∧ D.size + s.length ≤ 58 ∧
        IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∀ x, Minimal F x ∨ Maximal (fun y => ¬ F y) x →
          let v := D.wires (List.ofFn x ++ [x 1 || x 2])
          (if useOr then (a :: s).any (fun i => v.getD i.val false)
           else (a :: s).all (fun i => v.getD i.val false)) = true ↔ F x) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true := by
  classical
  let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, l ≠ 1 ∧
    (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  obtain ⟨D, useOr, a, s, sne, distinct, cost, hD, dD, good⟩ := cover
  obtain ⟨J, js, jo, hJ, dJ, evalJ⟩ := collector _ useOr a s sne distinct
  let seed : Gate := ⟨.or, [1,2]⟩
  let C : Circuit := ⟨seed :: (D.gates ++ J.gates), J.output⟩
  let step := fun (u : List Bool) (g : Gate) =>
    u ++ [g.op.eval (g.inputs.map (fun i => u.getD i false))]
  have sizeC : C.size = 1 + D.size + J.size := by
    change (seed :: (D.gates ++ J.gates)).length = 1 + D.gates.length + J.gates.length
    simp; omega
  have jspos : 0 < J.size := by rw [js]; exact List.length_pos_iff.mpr sne
  have output : C.output = 27 + D.size + J.size - 1 := jo
  have spec (n : ℕ) (H : Circuit) (h : IsAO2 n H) (hd : ∀ g ∈ H.gates, g.inputs.Nodup)
      (i : ℕ) (g : Gate) (hi : H.gates[i]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+i ∧ b < n+i := by
    obtain ⟨hop,hback,hpair⟩ := h
    have hm := List.mem_of_getElem? hi
    obtain ⟨a,b,hab⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
      have len := hpair g hm
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp len
      exact ⟨a,b,hab⟩
    have hr : i < H.gates.length := by
      by_contra! hh
      rw [List.getElem?_eq_none hh] at hi
      contradiction
    have gate : PEqualNP.MetaComplexity.NestedCover.gateAt H i = g := by
      change H.gates.getD i _ = g
      simp only [List.getD_eq_getElem?_getD, hi, Option.getD_some]
    have hb := hback i hr
    rw [gate,hab] at hb
    exact ⟨hop g hm,a,b,hab,by simpa [hab] using hd g hm,hb a (by simp),hb b (by simp)⟩
  have legal (i : ℕ) (g : Gate) (hi : C.gates[i]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i := by
    cases i with
    | zero =>
      have he : seed = g := by simpa [C] using hi
      subst g
      exact ⟨Or.inr rfl,1,2,rfl,by decide,by decide,by decide⟩
    | succ i =>
      change (D.gates ++ J.gates)[i]? = some g at hi
      by_cases h : i < D.gates.length
      · rw [List.getElem?_append_left h] at hi
        obtain ⟨hop,a,b,hab,ne,ha,hb⟩ := spec 27 D hD dD i g hi
        exact ⟨hop,a,b,hab,ne,by omega,by omega⟩
      · rw [List.getElem?_append_right (by omega)] at hi
        obtain ⟨hop,a,b,hab,ne,ha,hb⟩ := spec (27+D.size) J hJ dJ _ g hi
        change a < 27+D.gates.length+_ at ha
        change b < 27+D.gates.length+_ at hb
        exact ⟨hop,a,b,hab,ne,by omega,by omega⟩
  have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (gs.foldl step u).getD i false = u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step u g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have len (gs : List Gate) (u : List Bool) :
      (gs.foldl step u).length = u.length + gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have wiring (x : Fin 26 → Bool) :
      C.wires (List.ofFn x) = J.wires (D.wires (List.ofFn x ++ [x 1 || x 2])) := by
    change ((seed :: (D.gates ++ J.gates)).foldl step (List.ofFn x)) = _
    rw [List.foldl_cons,List.foldl_append]
    have he : step (List.ofFn x) seed = List.ofFn x ++ [x 1 || x 2] := by
      change List.ofFn x ++ [x 1 || (x 2 || false)] = _
      simp
    rw [he]
    rfl
  have mono : Monotone (fun x : Fin 26 → Bool => C.eval (List.ofFn x)) := by
    intro x y hxy
    have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have aux (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (u v : List Bool) (hlen : u.length = v.length)
        (hle : ∀ i, u.getD i false ≤ v.getD i false) :
        ∀ i, (gs.foldl step u).getD i false ≤ (gs.foldl step v).getD i false := by
      induction gs generalizing u v with
      | nil => exact hle
      | cons g gs ih =>
        apply ih (fun g hg => ops g (List.mem_cons_of_mem _ hg)) (step u g) (step v g)
        · simp [step,hlen]
        · intro i
          by_cases hi : i < u.length
          · simpa only [step,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (hlen ▸ hi)] using hle i
          · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
                  List.getD_append_right _ _ _ _ (by omega : v.length ≤ i), ← hlen]
            by_cases he : i = u.length
            · simp only [he,Nat.sub_self,List.getD_cons_zero]
              rcases ops g (by simp) with ha | ho
              · simp only [ha,andEval,Bool.le_iff_imp,List.all_eq_true,List.mem_map,id_eq]
                intro h b hb
                obtain ⟨j,hj,rfl⟩ := hb
                exact (Bool.le_iff_imp.mp (hle j)) (h _ ⟨j,hj,rfl⟩)
              · simp only [ho,orEval,Bool.le_iff_imp,List.any_eq_true,List.mem_map,id_eq]
                rintro ⟨b,⟨j,hj,rfl⟩,hb⟩
                exact ⟨_,⟨j,hj,rfl⟩,Bool.le_iff_imp.mp (hle j) hb⟩
            · have hn : 1 ≤ i-u.length := by omega
              have hz (b : Bool) : [b].getD (i-u.length) false = false := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hn)]
                rfl
              simp only [hz, le_refl]
    apply aux C.gates (fun g hg => by
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      exact (legal j g hj).1) (List.ofFn x) (List.ofFn y) (by simp) _ C.output
    intro i
    by_cases hi : i < 26
    · simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some] using hxy (⟨i,hi⟩ : Fin 26)
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hi,Option.getD_none,le_refl]
  have rows (x : Fin 26 → Bool) (hx : Minimal F x ∨ Maximal (fun y => ¬ F y) x) :
      C.eval (List.ofFn x) = true ↔ F x := by
    let u := D.wires (List.ofFn x ++ [x 1 || x 2])
    have hu : u.length = 27 + D.size := by
      change (D.gates.foldl step _).length = _
      rw [len]
      change (List.ofFn x ++ [x 1 || x 2]).length + D.gates.length = 27 + D.gates.length
      simp
    change (C.wires _).getD J.output false = true ↔ _
    rw [wiring]
    change J.eval u = true ↔ _
    rw [evalJ u hu]
    exact good x hx
  refine ⟨C,26,by omega,by omega,by omega,le_rfl,by omega,legal,?_,?_⟩
  · intro x
    rw [wiring]
    let u := List.ofFn x ++ [x 1 || x 2]
    change (J.gates.foldl step (D.gates.foldl step u)).getD 26 false = _
    rw [keep _ _ _ (by rw [len]; simp [u]; omega),keep _ _ _ (by simp [u])]
    exact List.getD_append_right _ _ _ _ (by simp) |>.trans (by simp)
  · intro x
    change C.eval (List.ofFn x) = true ↔ F x
    constructor
    · intro hx
      by_contra hn
      obtain ⟨y,hy,hm⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ F z) x hn
      have h := mono hy
      change C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) at h
      rw [hx] at h
      exact hm.1 ((rows y (Or.inr hm)).1 (top_unique h))
    · intro hx
      obtain ⟨y,hy,hm⟩ := exists_minimal_le_of_wellFoundedLT F x hx
      have h := mono hy
      change C.eval (List.ofFn y) ≤ C.eval (List.ofFn x) at h
      rw [(rows y (Or.inl hm)).2 hm.1] at h
      exact top_unique h
