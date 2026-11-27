import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

set_option maxHeartbeats 6400000 in
theorem PEqualNP.Outside.R_meta_4147_234
    (relabel :
      let cut := fun (C : Circuit) i => {C with gates := C.gates.set i ⟨.or, []⟩}
      ∀ (C : Circuit) (P L : Equiv.Perm (Fin 13)), ∃ D : Circuit,
        D.size = C.size ∧ (Monotone2 C → Monotone2 D) ∧ (ReadsBack 26 C → ReadsBack 26 D) ∧
        (∀ i, (gateAt D i).op = (gateAt C i).op) ∧
        (∀ i j, InCone 26 D i j ↔ InCone 26 C i j) ∧
        ∀ X Y, let v := incidenceInput (X.map P.toEmbedding) (Y.map L.toEmbedding)
               let u := incidenceInput X Y
               D.eval v = C.eval u ∧
                 (∀ i, (D.wires v).getD (26 + i) false = (C.wires u).getD (26 + i) false) ∧
                 ∀ i, (cut D i).eval v = (cut C i).eval u)
    (fixedFrame :
      let S := singerLines3
      let row := fun Q => incidenceInput Q (missLines S Q)
      let inner := fun (C : Circuit) i => (gateAt C i).op = .and ∧
        ∃ j, (gateAt C j).op = .and ∧ InCone 26 C i j
      let hit := fun (C : Circuit) i Q => (C.wires (row Q)).getD (26+i) false = true
      ∀ C, Monotone2 C → ReadsBack 26 C → RightOnIncidentPairs S C →
        (∀ Q, IsQuadrangle S Q → C.eval (row Q) = false) →
        (∀ i, inner C i → (∃ Q, IsQuadrangle S Q ∧ hit C i Q) ∧
          2 ≤ ((incidences S).filter fun e =>
            ({C with gates := C.gates.set i ⟨.or, []⟩} : Circuit).eval
              (incidenceInput {e.1} {e.2}) = false).card) →
        (∃ i, inner C i ∧ hit C i {0, 1, 2, 5}) → 64 ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → List Bool := fun (x2 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines x1 x2); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x4 → x3.eval (x2 x4) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ (x6 : ℕ), x4 x5 x6) ∧ ∀ (x6 : ℕ), x4 x5 x6 → (∃ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x8 ∧ (x5.wires (x2 x8)).getD ((26 : ℕ) + x6) Bool.false = Bool.true) ∧ (2 : ℕ) ≤ {x8 ∈ PEqualNP.HeptadCover.incidences x1 | { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (PEqualNP.GenericRejection.incidenceInput {x8.1} {x8.2}) = Bool.false}.card; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → (64 : ℕ) ≤ x6.size := by
  have frames : ∀ Q, IsQuadrangle singerLines3 Q →
      ∃ P L : Equiv.Perm (Fin 13),
        (∀ p l, P p ∈ singerLines3 (L l) ↔ p ∈ singerLines3 l) ∧
        Q.map P.toEmbedding = {0, 1, 2, 5} := by
    let F : Finset (Fin 13) := {0, 1, 2, 5}
    let reaches := fun (Q : Finset (Fin 13)) =>
      ∃ P L : Equiv.Perm (Fin 13),
        (∀ p l, P p ∈ singerLines3 (L l) ↔ p ∈ singerLines3 l) ∧ F.map P.toEmbedding = Q
    let shift (t : Fin 13) : Equiv.Perm (Fin 13) :=
      ⟨(· + t), (· - t), fun x => add_sub_cancel_right x t, fun x => sub_add_cancel x t⟩
    -- The two involutions below act together on points and lines.
    let flipP := ((Equiv.swap (4 : Fin 13) 10).trans (Equiv.swap 5 11)).trans
      ((Equiv.swap 6 7).trans (Equiv.swap 8 12))
    let flipL := ((Equiv.swap (3 : Fin 13) 7).trans (Equiv.swap 4 10)).trans
      ((Equiv.swap 5 11).trans (Equiv.swap 8 9))
    have singer : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      decide +kernel
    have shiftOK (t p l : Fin 13) : shift t p ∈ singerLines3 (shift t l) ↔ p ∈ singerLines3 l := by
      rw [singer, singer]
      change p + t - (l + t) ∈ _ ↔ _
      rw [add_sub_add_right_eq_sub]
    have flipOK : ∀ p l, flipP p ∈ singerLines3 (flipL l) ↔ p ∈ singerLines3 l := by
      decide +kernel
    have move {Q : Finset (Fin 13)} (h : reaches Q) (U V : Equiv.Perm (Fin 13))
        (ok : ∀ p l, U p ∈ singerLines3 (V l) ↔ p ∈ singerLines3 l) :
        reaches (Q.map U.toEmbedding) := by
      obtain ⟨P, L, inc, rfl⟩ := h
      exact ⟨P.trans U, L.trans V, fun p l => (ok (P p) (L l)).trans (inc p l), by
        rw [Finset.map_map]; rfl⟩
    have step {Q R : Finset (Fin 13)} (a b : Fin 13) (h : reaches Q)
        (eq : (((Q.map (shift a).toEmbedding).map flipP.toEmbedding).map (shift b).toEmbedding) = R) :
        reaches R := eq ▸ move (move (move h _ _ (shiftOK a)) _ _ flipOK) _ _ (shiftOK b)
    -- Eighteen representatives suffice up to translation. Each step translates a
    -- previously reached representative, applies the involution, and translates back into the list.
    have rep0 : reaches F := ⟨Equiv.refl _, Equiv.refl _, fun _ _ => Iff.rfl, by simp⟩
    have rep1 : reaches {0, 1, 2, 11} := step 0 0 rep0 (by decide +kernel)
    have rep2 : reaches {0, 1, 2, 6} := step 1 12 rep0 (by decide +kernel)
    have rep3 : reaches {0, 1, 4, 8} := step 2 11 rep0 (by decide +kernel)
    have rep4 : reaches {0, 1, 5, 11} := step 5 7 rep0 (by decide +kernel)
    have rep5 : reaches {0, 1, 2, 7} := step 6 8 rep0 (by decide +kernel)
    have rep6 : reaches {0, 1, 4, 11} := step 7 5 rep0 (by decide +kernel)
    have rep7 : reaches {0, 1, 5, 10} := step 8 1 rep0 (by decide +kernel)
    have rep8 : reaches {0, 2, 5, 10} := step 11 10 rep0 (by decide +kernel)
    have rep9 : reaches {0, 1, 8, 10} := step 12 0 rep0 (by decide +kernel)
    have rep10 : reaches {0, 1, 8, 11} := step 2 11 rep1 (by decide +kernel)
    have rep11 : reaches {0, 1, 4, 6} := step 3 3 rep1 (by decide +kernel)
    have rep12 : reaches {0, 1, 7, 10} := step 4 3 rep2 (by decide +kernel)
    have rep13 : reaches {0, 2, 4, 6} := step 5 6 rep3 (by decide +kernel)
    have rep14 : reaches {0, 2, 7, 10} := step 12 7 rep3 (by decide +kernel)
    have rep15 : reaches {0, 1, 6, 7} := step 1 12 rep4 (by decide +kernel)
    have rep16 : reaches {0, 2, 5, 9} := step 12 5 rep4 (by decide +kernel)
    have rep17 : reaches {0, 2, 4, 9} := step 5 6 rep6 (by decide +kernel)
    let charts : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 1, 2, 11}, {0, 1, 2, 6}, {0, 1, 4, 8}, {0, 1, 5, 11}, {0, 1, 2, 7}, {0, 1, 4, 11}, {0, 1, 5, 10}, {0, 2, 5, 10}, {0, 1, 8, 10}, {0, 1, 8, 11}, {0, 1, 4, 6}, {0, 1, 7, 10}, {0, 2, 4, 6}, {0, 2, 7, 10}, {0, 1, 6, 7}, {0, 2, 5, 9}, {0, 2, 4, 9}]
    have chartOK : ∀ A ∈ charts, reaches A := by
      intro A h
      simp only [charts, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact rep0
      · exact rep1
      · exact rep2
      · exact rep3
      · exact rep4
      · exact rep5
      · exact rep6
      · exact rep7
      · exact rep8
      · exact rep9
      · exact rep10
      · exact rep11
      · exact rep12
      · exact rep13
      · exact rep14
      · exact rep15
      · exact rep16
      · exact rep17
    -- Translate one point to zero and order the other three by increasing value.
    -- The table indexes these triples in colexicographic order.
    -- An entry below 234 is thirteen times the representative index plus its translation.
    -- An entry at least 234 gives, after subtracting 234, a line containing three points.
    let table : List ℕ :=
      [234, 235, 234, 15, 0, 234, 236, 238, 238, 238, 26, 234, 80, 143, 169, 237,
        239, 122, 135, 238, 65, 234, 54, 238, 238, 238, 238, 238, 238, 238, 195, 240,
        162, 238, 238, 246, 234, 246, 39, 246, 94, 239, 246, 107, 238, 239, 246, 188,
        225, 239, 202, 246, 241, 238, 238, 71, 234, 234, 234, 234, 221, 234, 234, 208,
        234, 238, 234, 240, 234, 212, 44, 234, 240, 234, 238, 238, 240, 234, 246, 234,
        242, 99, 60, 33, 235, 234, 132, 235, 235, 159, 91, 104, 185, 238, 244, 244,
        244, 244, 244, 156, 182, 241, 238, 238, 244, 117, 246, 241, 216, 112, 244, 241,
        234, 152, 234, 48, 243, 244, 87, 8, 13, 234, 236, 78, 180, 120, 52, 236,
        236, 238, 244, 244, 244, 244, 244, 245, 232, 219, 238, 238, 244, 130, 246, 115,
        242, 193, 244, 150, 234, 178, 234, 242, 230, 244, 176, 242, 244, 244, 244, 244,
        244, 244, 244, 244, 244, 246, 234, 246, 12, 246, 237, 38, 246, 155, 238, 77,
        246, 237, 237, 207, 245, 246, 51, 238, 238, 201, 246, 246, 246, 246, 246, 246,
        246, 234, 246, 234, 103, 243, 168, 129, 246, 25, 246, 90, 64, 243, 244, 142,
        246, 243, 245, 246, 11, 37, 76, 244, 245, 246, 24, 244]
    let code := fun (a b c : Fin 13) => table.getD
      ((c.val - 1).choose 3 + (b.val - 1).choose 2 + (a.val - 1)) 247
    have cert : ∀ a b c : Fin 13, 0 < a → a < b → b < c →
        let w := code a b c
        let T : Finset (Fin 13) := {0, a, b, c}
        if w < 234 then
          (charts.getD (w / 13) F).map (shift (Fin.ofNat 13 w)).toEmbedding = T
        else 2 < (T ∩ singerLines3 (Fin.ofNat 13 (w - 234))).card := by decide +kernel
    intro Q hQ
    have qpos : 0 < Q.card := by rw [hQ.1]; decide
    obtain ⟨p, hp⟩ := Finset.card_pos.mp qpos
    let U := shift (-p)
    let B := Q.map U.toEmbedding
    have h0 : 0 ∈ B := Finset.mem_map.mpr ⟨p, hp, by simp [U, shift]⟩
    have hline (l : Fin 13) : (singerLines3 l).map U.toEmbedding = singerLines3 (U l) := by
      ext x
      obtain ⟨a, rfl⟩ := U.surjective x
      simpa using (shiftOK (-p) a l).symm
    have hb : IsQuadrangle singerLines3 B := by
      refine ⟨by simpa [B] using hQ.1, ?_⟩
      intro l
      obtain ⟨m, rfl⟩ := U.surjective l
      change (Q.map U.toEmbedding ∩ singerLines3 (U m)).card ≤ 2
      rw [← hline, ← Finset.map_inter, Finset.card_map]
      exact hQ.2 m
    let rem := B.erase 0
    have hrem : rem.card = 3 := by simp [rem, Finset.card_erase_of_mem h0, hb.1]
    let E := rem.orderEmbOfFin hrem
    have ha : 0 < E 0 := Fin.pos_iff_ne_zero.mpr
      (Finset.mem_erase.mp (rem.orderEmbOfFin_mem hrem 0)).1
    have ht : rem = {E 0, E 1, E 2} := by
      have three : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      have he : Finset.image E Finset.univ = rem := rem.image_orderEmbOfFin_univ hrem
      simpa [three] using he.symm
    have hset : B = {0, E 0, E 1, E 2} := by
      calc
        B = insert 0 rem := (Finset.insert_erase h0).symm
        _ = _ := by rw [ht]
    let w := code (E 0) (E 1) (E 2)
    have hcert := cert (E 0) (E 1) (E 2) ha (E.strictMono (by decide)) (E.strictMono (by decide))
    change (if w < 234 then
      (charts.getD (w / 13) F).map (shift (Fin.ofNat 13 w)).toEmbedding = {0, E 0, E 1, E 2}
      else 2 < (({0, E 0, E 1, E 2} : Finset (Fin 13)) ∩ singerLines3 (Fin.ofNat 13 (w - 234))).card) at hcert
    have reachB : reaches B := by
      by_cases small : w < 234
      · have hw : (charts.getD (w / 13) F).map (shift (Fin.ofNat 13 w)).toEmbedding = B := by
          rw [hset]
          simpa only [small, ↓reduceIte] using hcert
        have idx : w / 13 < charts.length := by
          have len : charts.length = 18 := rfl
          omega
        have mem : charts.getD (w / 13) F ∈ charts := by
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem idx, Option.getD_some] using
            (List.getElem_mem (l := charts) (h := idx))
        exact hw ▸ move (chartOK _ mem) _ _ (shiftOK _)
      · have bad : 2 < (B ∩ singerLines3 (Fin.ofNat 13 (w - 234))).card := by
          rw [hset]
          simpa only [small, ↓reduceIte] using hcert
        exact False.elim ((Nat.not_lt_of_ge (hb.2 _)) bad)
    obtain ⟨P, L, ok, hP⟩ := reachB
    refine ⟨U.trans P.symm, U.trans L.symm, fun a l => ?_, ?_⟩
    · have hi := (ok (P.symm (U a)) (L.symm (U l))).symm
      exact (by simpa using hi : P.symm (U a) ∈ singerLines3 (L.symm (U l)) ↔
        U a ∈ singerLines3 (U l)) |>.trans (shiftOK (-p) a l)
    · change Q.map (U.toEmbedding.trans P.symm.toEmbedding) = F
      rw [← Finset.map_map]
      change B.map P.symm.toEmbedding = F
      rw [← hP]
      simp [Finset.map_map]
  intro S row valid inner hard C hvalid hhard
  obtain ⟨hm, hb, hp, hn⟩ := hvalid
  obtain ⟨⟨k, hk⟩, hall⟩ := hhard
  obtain ⟨Q, hQ, hf⟩ := (hall k hk).1
  obtain ⟨P, L, hinc, hframe⟩ := frames Q hQ
  obtain ⟨D, hsize, hmD, hbD, hops, hcone, heval⟩ := relabel C P L
  have line (l : Fin 13) : (S l).map P.toEmbedding = S (L l) := by
    ext x
    obtain ⟨p, rfl⟩ := P.surjective x
    simpa using (hinc p l).symm
  have quad (A : Finset (Fin 13)) :
      IsQuadrangle S (A.map P.toEmbedding) ↔ IsQuadrangle S A := by
    have hcard (l : Fin 13) :
        (A.map P.toEmbedding ∩ S (L l)).card = (A ∩ S l).card := by
      rw [← line l, ← Finset.map_inter, Finset.card_map]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨by simpa using h, fun l => (hcard l) ▸ hh (L l)⟩
    · rintro ⟨h, hh⟩
      refine ⟨by simpa using h, ?_⟩
      intro l
      obtain ⟨m, rfl⟩ := L.surjective l
      simpa only [hcard] using hh m
  have miss (A : Finset (Fin 13)) :
      (missLines S A).map L.toEmbedding = missLines S (A.map P.toEmbedding) := by
    ext l
    obtain ⟨m, rfl⟩ := L.surjective l
    change L m ∈ (Finset.univ.filter fun l => Disjoint (S l) A).map L.toEmbedding ↔
      L m ∈ Finset.univ.filter fun l => Disjoint (S l) (A.map P.toEmbedding)
    simp [← line m, Finset.disjoint_left]
    exact ⟨fun h _ ha => h ha, fun h a ha => by simpa using @h (P a) (by simpa using ha)⟩
  have rowEq (A : Finset (Fin 13)) :
      D.eval (row (A.map P.toEmbedding)) = C.eval (row A) := by
    simpa only [row, ← miss] using (heval A (missLines S A)).1
  have wireEq (A : Finset (Fin 13)) (i : ℕ) :
      (D.wires (row (A.map P.toEmbedding))).getD (26+i) false =
        (C.wires (row A)).getD (26+i) false := by
    simpa only [row, ← miss] using (heval A (missLines S A)).2.1 i
  have inn (i : ℕ) : inner D i ↔ inner C i := by
    change ((gateAt D i).op = .and ∧ ∃ j, (gateAt D j).op = .and ∧ InCone 26 D i j) ↔ _
    simp only [hops, hcone]
    rfl
  have onto (A : Finset (Fin 13)) : ∃ B : Finset (Fin 13), B.map P.toEmbedding = A :=
    ⟨A.map P.symm.toEmbedding, by simp [Finset.map_map]⟩
  let loss := fun (E : Circuit) i => (incidences S).filter fun e =>
    ({E with gates := E.gates.set i ⟨.or, []⟩} : Circuit).eval (incidenceInput {e.1} {e.2}) = false
  -- Relabeling each lost incident pair injects it into the loss set of the new circuit.
  have loss_le (i : ℕ) : (loss C i).card ≤ (loss D i).card := by
    let e := P.prodCongr L
    rw [← Finset.card_map (s := loss C i) e.toEmbedding]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨⟨p, l⟩, hp, rfl⟩ := Finset.mem_map.mp hz
    change (P p, L l) ∈ loss D i
    dsimp only [loss] at hp ⊢
    unfold incidences at hp ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨(hinc p l).2 hp.1, ?_⟩
    have ha := (heval {p} {l}).2.2 i
    simpa only [Finset.map_singleton, Equiv.toEmbedding_apply] using ha.trans hp.2
  rw [← hsize]
  apply fixedFrame D (hmD hm) (hbD hb)
  · intro l p hpl
    obtain ⟨a, rfl⟩ := P.surjective p
    obtain ⟨b, rfl⟩ := L.surjective l
    simpa only [Finset.map_singleton, Equiv.toEmbedding_apply] using ((heval {a} {b}).1.trans (hp b a ((hinc a b).1 hpl)))
  · intro A hA
    obtain ⟨B, rfl⟩ := onto A
    exact (rowEq B).trans (hn B ((quad B).1 hA))
  · intro i hi
    obtain ⟨⟨A, hA, ha⟩, hnum⟩ := hall i ((inn i).1 hi)
    exact ⟨⟨_, (quad A).2 hA, (wireEq A i).trans ha⟩, hnum.trans (loss_le i)⟩
  · refine ⟨k, (inn k).2 hk, ?_⟩
    rw [← hframe]
    exact (wireEq Q k).trans hf
