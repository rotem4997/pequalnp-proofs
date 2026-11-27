import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4684_613
    (extendArcs :
      let I (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let misses (A : Finset (Fin 13)) := Finset.univ.filter (fun l => ∀ p ∈ A, ¬ I p l)
      ∀ X Y : Finset (Fin 13),
        (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
        (∀ l, (X.filter (fun p => I p l)).card ≤ 2) →
        (∀ p, (Y.filter (fun l => I p l)).card ≤ 2) →
        ∃ A : Finset (Fin 13), X ⊆ A ∧ Y ⊆ misses A ∧
          (∀ p ∉ A, ∃ l ∈ misses A, I p l) ∧
          (¬ ∃ l, ∀ p ∈ A, I p l) ∧ (¬ ∃ p, ∀ l ∈ misses A, I p l))
    (countIrredundant : ∀ D : AndCountCircuit 27, D.WellFormed →
      let I (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let mask (X Y : Finset (Fin 13)) := Finset.univ.filter (fun i : Fin 27 =>
        Fin.cases true (fun k : Fin 26 => !(decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
          ∃ l ∈ Y, k = Fin.natAdd 13 l))) i = true)
      D.outVars = ∅ → (∀ p l, I p l → D.eval (mask {p} {l}) = false) →
      (∀ X Y : Finset (Fin 13), (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
        (∀ l, (X.filter (fun p => I p l)).card ≤ 2) →
        (∀ p, (Y.filter (fun l => I p l)).card ≤ 2) → D.eval (mask X Y) = true) →
      (∀ (i : Fin D.size) (b : Bool), ∃ p l, I p l ∧
        let U := mask {p} {l}
        sideTrue U (D.leftVars i) (D.leftGates i) i (D.gateVal U) = b ∧
        sideTrue U (D.rightVars i) (D.rightGates i) i (D.gateVal U) = !b) → 51 ≤ D.size) :
    (∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x4, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ x7 ∈ x5, x6 = Fin.natAdd (13 : ℕ) x7);     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x5 x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x8 : Fin (26 : ℕ)) => !x4 x5 x6 x8) x7 = Bool.true};     have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x3 x8 x7};     (∀ (x7 x8 : Fin (13 : ℕ)), x3 x7 x8 → x1.eval (x5 {x7} {x8}) = Bool.false) → (∀ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ x11 ∈ x6 x8, x3 x9 x11) → (¬∃ (x10 : Fin (13 : ℕ)), ∀ x11 ∈ x8, x3 x11 x10) → (¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x6 x8, x3 x11 x12) → x1.eval (x5 x8 (x6 x8)) = Bool.true) → (51 : ℕ) ≤ x1.size) := by
  let testInput (X Y : Finset (Fin 13)) : Finset (Fin 27) :=
    Finset.univ.filter (fun i =>
      Fin.cases true (fun k : Fin 26 => !(decide
        ((∃ a ∈ X, k = Fin.castAdd 13 a) ∨ ∃ b ∈ Y, k = Fin.natAdd 13 b))) i = true)

  have testInput_antitone {X Y A B : Finset (Fin 13)} (xA : X ⊆ A) (yB : Y ⊆ B) :
      testInput A B ⊆ testInput X Y := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [testInput]
    · intro mem
      have noLarge : ¬ ((∃ p ∈ A, j = Fin.castAdd 13 p) ∨ ∃ l ∈ B, j = Fin.natAdd 13 l) := by
        simpa [testInput] using mem
      have noSmall : ¬ ((∃ p ∈ X, j = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, j = Fin.natAdd 13 l) := by
        rintro (⟨p, hp, same⟩ | ⟨l, hl, same⟩)
        · exact noLarge (Or.inl ⟨p, xA hp, same⟩)
        · exact noLarge (Or.inr ⟨l, yB hl, same⟩)
      simpa [testInput] using noSmall

  have adequateFuel {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
      (i : Fin C.size) (d e : ℕ) (hd : i.val < d) (he : i.val < e) :
      C.gateValFuel U d i = C.gateValFuel U e i := by
    suffices help : ∀ k (j : Fin C.size), j.val < k → ∀ a b,
        j.val < a → j.val < b → C.gateValFuel U a j = C.gateValFuel U b j by
      exact help (i.val + 1) i (by omega) d e hd he
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj a b ha hb
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      have sides (V : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U V F j (C.gateValFuel U a) = sideTrue U V F j (C.gateValFuel U b) := by
        change decide ((∃ z ∈ V, z ∈ U) ∨ ∃ t ∈ F, t < j ∧ C.gateValFuel U a t = true) =
          decide ((∃ z ∈ V, z ∈ U) ∨ ∃ t ∈ F, t < j ∧ C.gateValFuel U b t = true)
        rw [decide_eq_decide]
        refine or_congr_right (exists_congr fun t => and_congr_right fun _ => and_congr_right fun ht => ?_)
        have earlier : t.val < j.val := ht
        rw [ih t (by omega) a b (by omega) (by omega)]
      change (sideTrue U (C.leftVars j) (C.leftGates j) j (C.gateValFuel U a) &&
        sideTrue U (C.rightVars j) (C.rightGates j) j (C.gateValFuel U a)) =
        (sideTrue U (C.leftVars j) (C.leftGates j) j (C.gateValFuel U b) &&
          sideTrue U (C.rightVars j) (C.rightGates j) j (C.gateValFuel U b))
      rw [sides, sides]

  have gate_equation {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
      (i : Fin C.size) :
      C.gateVal U i =
        (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
          sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
    have eq : C.gateVal U i = C.gateValFuel U (C.size + 1) i :=
      adequateFuel C U i C.size (C.size + 1) i.isLt (by have := i.isLt; omega)
    rw [eq]
    rfl

  let Reads {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
      (v : Fin k → Bool) : Prop :=
    (∃ a ∈ B, a ∈ U) ∨ ∃ j ∈ F, v j = true

  have side_reads {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
      (i : Fin k) (v : Fin k → Bool) (earlier : ∀ j ∈ F, j < i) :
      sideTrue U B F i v = true ↔ Reads U B F v := by
    change decide ((∃ a ∈ B, a ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) = true ↔
      (∃ a ∈ B, a ∈ U) ∨ ∃ j ∈ F, v j = true
    rw [decide_eq_true_eq]
    exact or_congr_right (exists_congr fun j => and_congr_right fun hj => and_iff_right (earlier j hj))

  have gate_reads {n : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      (U : Finset (Fin n)) (i : Fin C.size) :
      C.gateVal U i = true ↔
        Reads U (C.leftVars i) (C.leftGates i) (C.gateVal U) ∧
        Reads U (C.rightVars i) (C.rightGates i) (C.gateVal U) := by
    rw [gate_equation C U i, Bool.and_eq_true]
    rw [side_reads _ _ _ _ _ (wf i).1, side_reads _ _ _ _ _ (wf i).2]

  have eval_reads {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
      C.eval U = true ↔ Reads U C.outVars C.outGates (C.gateVal U) := by
    change decide (Reads U C.outVars C.outGates (C.gateVal U)) = true ↔
      Reads U C.outVars C.outGates (C.gateVal U)
    rw [decide_eq_true_eq]

  have eval_mono {n : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      {U V : Finset (Fin n)} (sub : U ⊆ V) (on : C.eval U = true) : C.eval V = true := by
    have readMono (B : Finset (Fin n)) (F : Finset (Fin C.size))
        (gates : ∀ j ∈ F, C.gateVal U j = true → C.gateVal V j = true) :
        Reads U B F (C.gateVal U) → Reads V B F (C.gateVal V) := by
      rintro (⟨a, ha, hU⟩ | ⟨j, hj, hU⟩)
      · exact Or.inl ⟨a, ha, sub hU⟩
      · exact Or.inr ⟨j, hj, gates j hj hU⟩
    have all : ∀ t (i : Fin C.size), i.val = t → C.gateVal U i = true → C.gateVal V i = true := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro i eq good
        obtain ⟨left, right⟩ := (gate_reads C wf U i).mp good
        apply (gate_reads C wf V i).mpr
        exact ⟨readMono _ _ (fun j hj => ih j.val (eq ▸ (wf i).1 j hj) j rfl) left,
          readMono _ _ (fun j hj => ih j.val (eq ▸ (wf i).2 j hj) j rfl) right⟩
    apply (eval_reads C V).mpr
    exact readMono _ _ (fun j _ => all j.val j rfl) ((eval_reads C U).mp on)

  let splicedVars {n k : ℕ} (removed : Fin k) (inserted B : Finset (Fin n))
      (F : Finset (Fin k)) : Finset (Fin n) :=
    B ∪ if removed ∈ F then inserted else ∅

  let splicedGates {k m : ℕ} (lift : Fin m ↪o Fin k) (removed : Fin k)
      (inserted F : Finset (Fin k)) : Finset (Fin m) :=
    Finset.univ.filter (fun j => lift j ∈ F ∨ (removed ∈ F ∧ lift j ∈ inserted))

  let spliceGate {n m : ℕ} (C : AndCountCircuit n) (lift : Fin m ↪o Fin C.size)
      (removed : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size)) : AndCountCircuit n := {
    size := m
    leftVars i := splicedVars removed B (C.leftVars (lift i)) (C.leftGates (lift i))
    leftGates i := splicedGates lift removed F (C.leftGates (lift i))
    rightVars i := splicedVars removed B (C.rightVars (lift i)) (C.rightGates (lift i))
    rightGates i := splicedGates lift removed F (C.rightGates (lift i))
    outVars := splicedVars removed B C.outVars C.outGates
    outGates := splicedGates lift removed F C.outGates
    }

  have spliceGate_wellFormed {n m : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      (lift : Fin m ↪o Fin C.size) (removed : Fin C.size) (B : Finset (Fin n))
      (F : Finset (Fin C.size)) (earlier : ∀ j ∈ F, j < removed) :
      (spliceGate C lift removed B F).WellFormed := by
    intro i
    have readsBack (G : Finset (Fin C.size)) (prior : ∀ j ∈ G, j < lift i) :
        ∀ j ∈ splicedGates lift removed F G, j < i := by
      intro j mem
      apply lift.lt_iff_lt.mp
      rcases (Finset.mem_filter.mp mem).2 with direct | ⟨readsRemoved, readsEarlier⟩
      · exact prior _ direct
      · exact (earlier _ readsEarlier).trans (prior _ readsRemoved)
    exact ⟨readsBack _ (wf (lift i)).1, readsBack _ (wf (lift i)).2⟩

  have splice_reads_forward {n k m : ℕ} {lift : Fin m ↪o Fin k} {removed : Fin k}
      {U B kept : Finset (Fin n)} {F refs : Finset (Fin k)} {v : Fin k → Bool} {w : Fin m → Bool}
      (covers : ∀ i, i ≠ removed → ∃ j, lift j = i) (earlier : ∀ i ∈ refs, i < removed)
      (value : ∀ j ∈ splicedGates lift removed refs F, v (lift j) = true → w j = true)
      (pivot : v removed = true → Reads U kept refs v) :
      Reads U B F v → Reads U (splicedVars removed kept B F) (splicedGates lift removed refs F) w := by
    rintro (⟨a, ha, hU⟩ | ⟨i, hi, on⟩)
    · exact Or.inl ⟨a, Finset.mem_union_left _ ha, hU⟩
    · by_cases equal : i = removed
      · subst i
        rcases pivot on with ⟨a, ha, hU⟩ | ⟨r, hr, hrOn⟩
        · exact Or.inl ⟨a, Finset.mem_union_right _ (by simpa [hi] using ha), hU⟩
        · obtain ⟨j, rfl⟩ := covers r (ne_of_lt (earlier r hr))
          have mem : j ∈ splicedGates lift removed refs F :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hi, hr⟩⟩
          exact Or.inr ⟨j, mem, value j mem hrOn⟩
      · obtain ⟨j, rfl⟩ := covers i equal
        have mem : j ∈ splicedGates lift removed refs F :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi⟩
        exact Or.inr ⟨j, mem, value j mem on⟩

  have splice_reads_backward {n k m : ℕ} {lift : Fin m ↪o Fin k} {removed : Fin k}
      {U B kept : Finset (Fin n)} {F refs : Finset (Fin k)} {v : Fin k → Bool} {w : Fin m → Bool}
      (value : ∀ j ∈ splicedGates lift removed refs F, w j = true → v (lift j) = true)
      (pivot : Reads U kept refs v → v removed = true) :
      Reads U (splicedVars removed kept B F) (splicedGates lift removed refs F) w → Reads U B F v := by
    rintro (⟨a, ha, hU⟩ | ⟨j, hj, on⟩)
    · rcases Finset.mem_union.mp ha with bare | extra
      · exact Or.inl ⟨a, bare, hU⟩
      · by_cases used : removed ∈ F
        · exact Or.inr ⟨removed, used, pivot (Or.inl ⟨a, by simpa [used] using extra, hU⟩)⟩
        · simp [used] at extra
    · rcases (Finset.mem_filter.mp hj).2 with reads | ⟨used, inserted⟩
      · exact Or.inr ⟨lift j, reads, value j hj on⟩
      · exact Or.inr ⟨removed, used, pivot (Or.inr ⟨lift j, inserted, value j hj on⟩)⟩

  have splice_comparison {n m : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      (lift : Fin m ↪o Fin C.size) (removed : Fin C.size) (B : Finset (Fin n))
      (F : Finset (Fin C.size)) (earlier : ∀ j ∈ F, j < removed)
      (covers : ∀ i, i ≠ removed → ∃ j, lift j = i) (U : Finset (Fin n))
      (forward : C.gateVal U removed = true → Reads U B F (C.gateVal U)) :
      let D := spliceGate C lift removed B F
      (C.eval U = true → D.eval U = true) ∧
      ((Reads U B F (C.gateVal U) → C.gateVal U removed = true) → D.eval U = true → C.eval U = true) := by
    let D := spliceGate C lift removed B F
    have dwf := spliceGate_wellFormed C wf lift removed B F earlier
    let Upper := Reads U B F (C.gateVal U) → C.gateVal U removed = true
    have values : ∀ t (i : Fin m), i.val = t →
        (C.gateVal U (lift i) = true → D.gateVal U i = true) ∧
        (Upper → D.gateVal U i = true → C.gateVal U (lift i) = true) := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro i eq
        have earlierValues (j : Fin m) (hj : j < i) :
            (C.gateVal U (lift j) = true → D.gateVal U j = true) ∧
            (Upper → D.gateVal U j = true → C.gateVal U (lift j) = true) :=
          ih j.val (eq ▸ hj) j rfl
        constructor
        · intro on
          obtain ⟨left, right⟩ := (gate_reads C wf U (lift i)).mp on
          apply (gate_reads D dwf U i).mpr
          exact ⟨splice_reads_forward covers earlier
            (fun j mem => (earlierValues j ((dwf i).1 j mem)).1) forward left,
            splice_reads_forward covers earlier
            (fun j mem => (earlierValues j ((dwf i).2 j mem)).1) forward right⟩
        · intro upper on
          obtain ⟨left, right⟩ := (gate_reads D dwf U i).mp on
          apply (gate_reads C wf U (lift i)).mpr
          exact ⟨splice_reads_backward
            (fun j mem => (earlierValues j ((dwf i).1 j mem)).2 upper) upper left,
            splice_reads_backward
            (fun j mem => (earlierValues j ((dwf i).2 j mem)).2 upper) upper right⟩
    constructor
    · intro accept
      apply (eval_reads D U).mpr
      exact splice_reads_forward covers earlier (fun j _ => (values j.val j rfl).1)
        forward ((eval_reads C U).mp accept)
    · intro upper accept
      apply (eval_reads C U).mpr
      exact splice_reads_backward (fun j _ => (values j.val j rfl).2 upper)
        upper ((eval_reads D U).mp accept)

  have remove_with_side {n : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      (removed : Fin C.size) (B : Finset (Fin n)) (F : Finset (Fin C.size))
      (earlier : ∀ j ∈ F, j < removed)
      (gives : ∀ U, C.gateVal U removed = true → Reads U B F (C.gateVal U)) :
      ∃ D : AndCountCircuit n, D.WellFormed ∧ D.size < C.size ∧
        ∀ U : Finset (Fin n), (C.eval U = true → D.eval U = true) ∧
          ((Reads U B F (C.gateVal U) → C.gateVal U removed = true) →
            D.eval U = true → C.eval U = true) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by have := removed.isLt; omega : C.size ≠ 0)
    let p : Fin (m + 1) := Fin.cast hm removed
    let lift : Fin m ↪o Fin C.size :=
      (Fin.succAboveOrderEmb p).trans (Fin.castOrderIso hm.symm).toOrderEmbedding
    have covers (i : Fin C.size) (other : i ≠ removed) : ∃ j, lift j = i := by
      have unequal : Fin.cast hm i ≠ p := by
        intro equal
        have values : i.val = removed.val := congrArg (fun j : Fin (m + 1) => j.val) equal
        exact other (Fin.ext values)
      obtain ⟨j, eq⟩ := Fin.exists_succAbove_eq unequal
      refine ⟨j, ?_⟩
      change Fin.cast hm.symm (p.succAbove j) = i
      rw [eq]
      simp
    exact ⟨spliceGate C lift removed B F, spliceGate_wellFormed C wf lift removed B F earlier,
      by change m < C.size; omega,
      fun U => splice_comparison C wf lift removed B F earlier covers U (gives U)⟩

  have minimize_separator {n : ℕ} (C : AndCountCircuit n) (wf : C.WellFormed)
      (wanted unwanted : Finset (Fin n) → Prop)
      (accept : ∀ U, wanted U → C.eval U = true)
      (reject : ∀ U, unwanted U → C.eval U = false) :
      ∃ D : AndCountCircuit n, D.WellFormed ∧ D.size ≤ C.size ∧
        (∀ U, wanted U → D.eval U = true) ∧ (∀ U, unwanted U → D.eval U = false) ∧
        ∀ i : Fin D.size,
          (∃ U, unwanted U ∧ Reads U (D.leftVars i) (D.leftGates i) (D.gateVal U) ∧
            ¬ Reads U (D.rightVars i) (D.rightGates i) (D.gateVal U)) ∧
          (∃ U, unwanted U ∧ Reads U (D.rightVars i) (D.rightGates i) (D.gateVal U) ∧
            ¬ Reads U (D.leftVars i) (D.leftGates i) (D.gateVal U)) := by
    classical
    let feasible (s : ℕ) := ∃ D : AndCountCircuit n, D.size = s ∧ D.WellFormed ∧
      (∀ U, wanted U → D.eval U = true) ∧ (∀ U, unwanted U → D.eval U = false)
    have hasFeasible : ∃ s, feasible s := ⟨C.size, C, rfl, wf, accept, reject⟩
    obtain ⟨D, sized, dwf, dAccept, dReject⟩ := Nat.find_spec hasFeasible
    have minimum (E : AndCountCircuit n) (proof : feasible E.size) : D.size ≤ E.size := by
      rw [sized]
      exact Nat.find_min' hasFeasible proof
    have incomparable (i : Fin D.size)
        (B B' : Finset (Fin n)) (F F' : Finset (Fin D.size)) (earlier : ∀ j ∈ F, j < i)
        (equation : ∀ U, D.gateVal U i = true ↔ Reads U B F (D.gateVal U) ∧ Reads U B' F' (D.gateVal U)) :
        ∃ U, unwanted U ∧ Reads U B F (D.gateVal U) ∧ ¬ Reads U B' F' (D.gateVal U) := by
      by_contra absent
      obtain ⟨E, ewf, smaller, compare⟩ :=
        remove_with_side D dwf i B F earlier (fun U on => ((equation U).mp on).1)
      have eAccept (U : Finset (Fin n)) (requested : wanted U) : E.eval U = true :=
        (compare U).1 (dAccept U requested)
      have eReject (U : Finset (Fin n)) (off : unwanted U) : E.eval U = false := by
        cases actual : E.eval U with
        | false => rfl
        | true =>
          have backwards : Reads U B F (D.gateVal U) → D.gateVal U i = true := by
            intro holds
            apply (equation U).mpr
            refine ⟨holds, ?_⟩
            by_contra other
            exact absent ⟨U, off, holds, other⟩
          exact Bool.noConfusion ((dReject U off).symm.trans ((compare U).2 backwards actual))
      exact (Nat.not_lt_of_ge (minimum E ⟨E, rfl, ewf, eAccept, eReject⟩)) smaller
    refine ⟨D, dwf, minimum C ⟨C, rfl, wf, accept, reject⟩, dAccept, dReject, ?_⟩
    intro i
    exact ⟨incomparable i _ _ _ _ (dwf i).1 (fun U => gate_reads D dwf U i),
      incomparable i _ _ _ _ (dwf i).2 (fun U => (gate_reads D dwf U i).trans and_comm)⟩

  intro C wellFormed
  dsimp only
  intro negative positive
  let I (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let misses (A : Finset (Fin 13)) := Finset.univ.filter (fun l => ∀ p ∈ A, ¬ I p l)
  let unwanted (U : Finset (Fin 27)) := ∃ p l : Fin 13, I p l ∧ U = testInput {p} {l}
  have rejectsUnwanted (U : Finset (Fin 27)) (off : unwanted U) : C.eval U = false := by
    obtain ⟨p, l, near, rfl⟩ := off
    exact negative p l near
  obtain ⟨D, dWellFormed, dSize, dAccept, dReject, sides⟩ :=
    minimize_separator C wellFormed (fun U => C.eval U = true) unwanted
      (fun _ h => h) rejectsUnwanted
  have rejectsPair (p l : Fin 13) (inc : I p l) : D.eval (testInput {p} {l}) = false :=
    dReject _ ⟨p, l, inc, rfl⟩
  have acceptedArcs (X Y : Finset (Fin 13))
      (apart : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l)
      (pArc : ∀ l, (X.filter (fun p => I p l)).card ≤ 2)
      (lArc : ∀ p, (Y.filter (fun l => I p l)).card ≤ 2) : D.eval (testInput X Y) = true := by
    obtain ⟨A, xA, yMiss, outside, points, lines⟩ := extendArcs X Y apart pArc lArc
    have passed : C.eval (testInput A (misses A)) = true := positive A outside points lines
    exact eval_mono D dWellFormed (testInput_antitone xA yMiss) (dAccept _ passed)
  have noOutputVars : D.outVars = ∅ := by
    have covered : ∀ i : Fin 27, i ∈ testInput {0} {0} ∨ i ∈ testInput {1} {1} := by decide +kernel
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i mem
    have impossible (U : Finset (Fin 27)) (reject : D.eval U = false) (present : i ∈ U) : False := by
      have accept : D.eval U = true := (eval_reads D U).mpr (Or.inl ⟨i, mem, present⟩)
      exact Bool.noConfusion (reject.symm.trans accept)
    rcases covered i with present | present
    · exact impossible _ (rejectsPair 0 0 (Or.inl rfl)) present
    · exact impossible _ (rejectsPair 1 1 (Or.inl rfl)) present
  have singleSide (i : Fin D.size) (b : Bool) : ∃ p l : Fin 13, I p l ∧
      let U := testInput {p} {l}
      sideTrue U (D.leftVars i) (D.leftGates i) i (D.gateVal U) = b ∧
      sideTrue U (D.rightVars i) (D.rightGates i) i (D.gateVal U) = !b := by
    have leftRead (U : Finset (Fin 27)) :=
      side_reads U (D.leftVars i) (D.leftGates i) i (D.gateVal U) (dWellFormed i).1
    have rightRead (U : Finset (Fin 27)) :=
      side_reads U (D.rightVars i) (D.rightGates i) i (D.gateVal U) (dWellFormed i).2
    cases b with
    | false =>
      obtain ⟨U, ⟨p, l, near, rfl⟩, rightOn, leftOff⟩ := (sides i).2
      refine ⟨p, l, near, Bool.eq_false_iff.mpr (fun h => leftOff ((leftRead _).mp h)),
        (rightRead _).mpr rightOn⟩
    | true =>
      obtain ⟨U, ⟨p, l, near, rfl⟩, leftOn, rightOff⟩ := (sides i).1
      refine ⟨p, l, near, (leftRead _).mpr leftOn,
        Bool.eq_false_iff.mpr (fun h => rightOff ((rightRead _).mp h))⟩
  exact (countIrredundant D dWellFormed noOutputVars rejectsPair acceptedArcs singleSide).trans dSize
