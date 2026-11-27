import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_8407_2
    (mon : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.getD x6 Bool.false = Bool.true → x4.getD x6 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true)
    (search :
      let adj : Fin 7 → Fin 14 → Bool := fun p l => decide
        (l.val = 7 + p.val ∨ l.val = p.val + (0 : ℕ) ∨ l.val = (p.val+1)%7 ∨ l.val = (p.val+5)%7)
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 21 C ∧ C.output < 21+C.size ∧ C.size ≤ 33 ∧
        (∀ p l, adj p l = true →
          C.eval (List.ofFn fun i : Fin 21 => decide (i = Fin.castAdd 14 p ∨ i = Fin.natAdd 7 l)) = true) ∧
        (∀ s : Fin 7 → Bool, C.eval (List.ofFn (Fin.append s
          (fun l : Fin 14 => decide (∀ p : Fin 7, s p = true → adj p l = false)))) = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧ x1.output < (21 : ℕ) + x1.size ∧ x1.size ≤ (33 : ℕ) ∧ ∀ (x2 : Fin (21 : ℕ) → Bool), x1.eval (List.ofFn x2) = (List.flatMap (fun (x3 : ℕ) => List.map (fun (x4 : ℕ) => (Fin.ofNat (21 : ℕ) x3, Fin.ofNat (21 : ℕ) x4)) [(14 : ℕ) + x3, (7 : ℕ) + x3, (7 : ℕ) + (x3 + (1 : ℕ)) % (7 : ℕ), (7 : ℕ) + (x3 + (5 : ℕ)) % (7 : ℕ)]) (List.range (7 : ℕ))).any fun (x3 : Fin (21 : ℕ) × Fin (21 : ℕ)) => x2 x3.1 && x2 x3.2 := by
  let adj : Fin 7 → Fin 14 → Bool := fun p l => decide
    (l.val = 7 + p.val ∨ l.val = p.val + (0 : ℕ) ∨ l.val = (p.val+1)%7 ∨ l.val = (p.val+5)%7)
  let es : List (Fin 21 × Fin 21) := (List.range 7).flatMap fun i =>
    ([14+i,7+i,7+(i+1)%7,7+(i+5)%7] : List ℕ).map fun j =>
      (Fin.ofNat 21 i, Fin.ofNat 21 j)
  have insert_edge : ∀ p l, adj p l = true → (Fin.castAdd 14 p, Fin.natAdd 7 l) ∈ es := by
    unfold es adj
    decide +kernel
  have split_edge : ∀ a b : Fin 21, (a,b) ∈ es → ∃ p : Fin 7, ∃ l : Fin 14,
      adj p l = true ∧ a = Fin.castAdd 14 p ∧ b = Fin.natAdd 7 l := by
    unfold es adj
    decide +kernel
  obtain ⟨C,hm,hb,ho,hs,hpos,hneg⟩ := search
  have ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm g hg).1
  have mono (a b : Fin 21 → Bool) (sub : ∀ i, a i = true → b i = true) :
      C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true := by
    apply mon C ops _ _ (by simp)
    intro i hi
    by_cases h : i < 21
    · have ha : i < (List.ofFn a).length := by simpa using h
      have hb' : i < (List.ofFn b).length := by simpa using h
      rw [List.getD_eq_getElem _ _ ha, List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ hb', List.getElem_ofFn]
      exact sub _ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)] at hi
      contradiction
  refine ⟨C,hm,hb,ho,hs,?_⟩
  intro x
  change C.eval (List.ofFn x) = es.any (fun e => x e.1 && x e.2)
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · intro acc
    by_contra bad
    let s : Fin 7 → Bool := fun p => x (Fin.castAdd 14 p)
    let t : Fin 14 → Bool := fun l => decide (∀ p : Fin 7, s p = true → adj p l = false)
    have sub : ∀ i, x i = true → Fin.append s t i = true := by
      intro i
      refine Fin.addCases (motive := fun j : Fin (7+14) => x j = true → Fin.append s t j = true)
        (fun p hp => ?_) (fun l hl => ?_) i
      · simpa only [Fin.append_left] using hp
      · rw [Fin.append_right]
        apply decide_eq_true
        intro p hp
        cases e : adj p l with
        | false => rfl
        | true =>
          exfalso
          apply bad
          exact ⟨(Fin.castAdd 14 p,Fin.natAdd 7 l),
            insert_edge p l e,hp,hl⟩
    have accepted := mono x (Fin.append s t) sub acc
    have rejected : C.eval (List.ofFn (Fin.append s t)) = false := hneg s
    exact Bool.noConfusion (rejected.symm.trans accepted)
  · rintro ⟨⟨a,b⟩,hab,ha,hb'⟩
    obtain ⟨p,l,had,rfl,rfl⟩ := split_edge a b hab
    apply mono _ x _ (hpos p l had)
    intro i hi
    rcases of_decide_eq_true hi with h | h
    · exact h ▸ ha
    · exact h ▸ hb'
