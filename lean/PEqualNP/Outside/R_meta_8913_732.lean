import PEqualNP.Defs

set_option maxRecDepth 18000 in
set_option maxHeartbeats 11000000 in
theorem PEqualNP.Outside.R_meta_8913_732
    (packBit : ∀ (xs : List Bool) (i : ℕ), (xs.foldr Nat.bit 0).testBit i = xs.getD i false)
    (numerical :
      let positive := (List.range 13).flatMap fun l =>
        [0,1,3,9].map fun s => 2 ^ ((l+s)%13) + 2 ^ (13+l)
      let rotate := fun m i : ℕ => ((m <<< i) ||| (m >>> (13-i))) &&& 8191
      let negative := (List.range 13).flatMap fun i =>
        [61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].map fun m => rotate (m % 8192) i + 8192 * rotate (m / 8192) i
      let rows := (positive ++ negative).map (fun r => (r,positive.contains r))
      let pack := fun (f : ℕ × Bool → Bool) => (rows.map f).foldr Nat.bit 0
      let bank := [0, pack (fun _ => true)] ++ List.ofFn (fun v : Fin 26 => pack (fun r => r.1.testBit v.val))
      let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
        let a := b.getD g.2.1 0
        let c := b.getD g.2.2 0
        b ++ [if g.1 then a ||| c else a &&& c]
      ∀ gs : List (Bool × ℕ × ℕ), gs.length ≤ 63 → pack Prod.snd ∉ gs.foldl step bank) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∃ (x2 : ℕ) (x3 : Fin x2 → Finset (Fin (13 : ℕ))) (x4 : Fin x2 → Finset (Fin (13 : ℕ))) (x5 : Set (Fin x2)),   (∀ x6 ∈ x5, ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x3 x6 = {x8} ∧ x4 x6 = {x9}) ∧     (∀ x6 ∉ x5, (∀ x8 ∈ x3 x6, ∀ x10 ∈ x4 x6, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x3 x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x4 x6 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧       have x6 : Fin x2 → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x6 : Fin x2) (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x3 x6)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x4 x6)) x7;       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | x6 x8 x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         x8.length ≤ (63 : ℕ) →           (∀ (x10 : Fin x8.length),               have x11 : Set (Set (Fin x2)) := x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8};               x8.getD ↑x10 ∅ ∉ x11 ∧ ∃ x12 ∈ x11, ∃ x13 ∈ x11, x8.getD ↑x10 ∅ = x12 ∪ x13 ∨ x8.getD ↑x10 ∅ = x12 ∩ x13) →             x5 ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8} := by
  intro incidence
  let positive := (List.range 13).flatMap fun l =>
    [0,1,3,9].map fun s => 2 ^ ((l+s)%13) + 2 ^ (13+l)
  let rotate := fun m i : ℕ => ((m <<< i) ||| (m >>> (13-i))) &&& 8191
  let negative := (List.range 13).flatMap fun i =>
    [61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].map fun m => rotate (m % 8192) i + 8192 * rotate (m / 8192) i
  let rows := positive.map (fun r => (r,true)) ++ negative.map (fun r => (r,false))
  let pack := fun (f : ℕ × Bool → Bool) => (rows.map f).foldr Nat.bit 0
  let bank := [0, pack (fun _ => true)] ++ List.ofFn (fun v : Fin 26 => pack (fun r => r.1.testBit v.val))
  let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
    let a := b.getD g.2.1 0
    let c := b.getD g.2.2 0
    b ++ [if g.1 then a ||| c else a &&& c]

  have compile (data : List (ℕ × Bool)) :
      let col := fun v : Fin 26 => {i : Fin data.length | data[i.val].1.testBit v.val = true}
      let labels := {i : Fin data.length | data[i.val].2 = true}
      let seeds : Set (Set (Fin data.length)) := {∅,Set.univ} ∪ Set.range col
      let pack := fun (f : ℕ × Bool → Bool) => (data.map f).foldr Nat.bit 0
      let bank := [0, pack (fun _ => true)] ++ List.ofFn (fun v : Fin 26 => pack (fun r => r.1.testBit v.val))
      ∀ L : List (Set (Fin data.length)),
        (∀ i : Fin L.length,
          let previous := seeds ∪ {s | s ∈ L.take i.val}
          ∃ a ∈ previous, ∃ b ∈ previous, L.getD i.val ∅ = a ∪ b ∨ L.getD i.val ∅ = a ∩ b) →
        labels ∈ seeds ∪ {s | s ∈ L} →
        ∃ gs : List (Bool × ℕ × ℕ), gs.length = L.length ∧ pack Prod.snd ∈ gs.foldl step bank := by
    intro col labels seeds pack bank L legal hm
    let Row := Fin data.length
    let sample (i : Row) := data[i.val]
    classical
    let encode (s : Set Row) := (List.ofFn fun i : Row => decide (i ∈ s)).foldr Nat.bit 0
    have bit (s : Set Row) (k : ℕ) :
        (encode s).testBit k = if h : k < data.length then decide (⟨k,h⟩ ∈ s) else false := by
      rw [show (encode s).testBit k = (List.ofFn fun i : Row => decide (i ∈ s)).getD k false from packBit _ _]
      by_cases hk : k < data.length
      · rw [dite_eq_left hk,List.getD_eq_getElem _ _ (by simpa)]
        simp only [List.getElem_ofFn]
      · rw [dite_eq_right hk,List.getD_eq_default]
        simpa using Nat.le_of_not_lt hk
    have encEmpty : encode ∅ = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [bit]
      by_cases hk : k < data.length <;> simp [hk]
    have encInter (s t : Set Row) : encode (s ∩ t) = encode s &&& encode t := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and,bit,bit,bit]
      by_cases hk : k < data.length
      · simp only [dite_eq_left hk,Set.mem_inter_iff,Bool.decide_and]
      · simp [hk]
    have encUnion (s t : Set Row) : encode (s ∪ t) = encode s ||| encode t := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_or,bit,bit,bit]
      by_cases hk : k < data.length
      · simp only [dite_eq_left hk,Set.mem_union,Bool.decide_or]
      · simp [hk]
    have packPred (f : ℕ × Bool → Bool) :
        encode {i | f (sample i) = true} = pack f := by
      change (List.ofFn fun i : Row =>
        @decide (f (sample i) = true) (Classical.propDecidable _)).foldr Nat.bit 0 =
        (data.map f).foldr Nat.bit 0
      congr 1
      simp only [Bool.decide_eq_true]
      change List.ofFn (f ∘ sample) = data.map f
      rw [← List.map_ofFn]
      exact congrArg (List.map f) List.ofFn_getElem
    have encUniv : encode Set.univ = pack (fun _ => true) := by
      have allRows : ({_i : Row | true = true} : Set Row) = Set.univ := by
        ext i
        simp
      rw [← allRows]
      exact packPred (fun _ => true)
    have encLabel : encode labels = pack Prod.snd := packPred Prod.snd
    have encCol (v : Fin 26) : encode (col v) = pack (fun r => r.1.testBit v.val) :=
      packPred (fun r => r.1.testBit v.val)
    have seedMem (s : Set Row) (hs : s ∈ seeds) : encode s ∈ bank := by
      rcases hs with hs | hs
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · rw [encEmpty]
          exact List.mem_append_left _ (by simp)
        · rw [encUniv]
          exact List.mem_append_left _ (by simp)
      · obtain ⟨v, rfl⟩ := hs
        rw [encCol]
        apply List.mem_append_right
        exact List.mem_ofFn.mpr ⟨v,rfl⟩
    have source {j : ℕ} {s : Set Row} (hs : s ∈ seeds ∪ {t | t ∈ L.take j}) :
        ∃ w, (bank ++ (L.take j).map encode).getD w 0 = encode s := by
      have hm : encode s ∈ bank ++ (L.take j).map encode := by
        rcases hs with hs | hs
        · exact List.mem_append_left _ (seedMem s hs)
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨s,hs,rfl⟩)
      obtain ⟨k,hk,val⟩ := List.mem_iff_getElem.mp hm
      exact ⟨k,(List.getD_eq_getElem _ _ hk).trans val⟩
    have compute (j : ℕ) (hj : j ≤ L.length) :
        ∃ gs : List (Bool × ℕ × ℕ), gs.length = j ∧ gs.foldl step bank = bank ++ (L.take j).map encode := by
      induction j with
      | zero => exact ⟨[],rfl,by simp⟩
      | succ j ih =>
        have hj' : j < L.length := hj
        obtain ⟨gs,hlen,hrun⟩ := ih (Nat.le_of_lt hj')
        obtain ⟨a,ha,b,hb,result⟩ := legal ⟨j,hj'⟩
        obtain ⟨wa,hwa⟩ := source ha
        obtain ⟨wb,hwb⟩ := source hb
        obtain eq | eq := result
        · refine ⟨gs ++ [(true,wa,wb)],by simp [hlen],?_⟩
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil,hrun]
          change (bank ++ (L.take j).map encode) ++
            [((bank ++ (L.take j).map encode).getD wa 0 |||
              (bank ++ (L.take j).map encode).getD wb 0)] = _
          rw [hwa,hwb,← encUnion,← eq,List.getD_eq_getElem _ _ hj',
            List.take_succ_eq_append_getElem hj',List.map_append,List.map_singleton,List.append_assoc]
        · refine ⟨gs ++ [(false,wa,wb)],by simp [hlen],?_⟩
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil,hrun]
          change (bank ++ (L.take j).map encode) ++
            [((bank ++ (L.take j).map encode).getD wa 0 &&&
              (bank ++ (L.take j).map encode).getD wb 0)] = _
          rw [hwa,hwb,← encInter,← eq,List.getD_eq_getElem _ _ hj',
            List.take_succ_eq_append_getElem hj',List.map_append,List.map_singleton,List.append_assoc]
    obtain ⟨gs,hlen,hrun⟩ := compute L.length le_rfl
    refine ⟨gs,hlen,?_⟩
    rw [hrun,List.take_length,← encLabel]
    rcases hm with hm | hm
    · exact List.mem_append_left _ (seedMem labels hm)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨labels,hm,rfl⟩)

  let left (r : ℕ) : Finset (Fin 13) := Finset.univ.filter fun p => r.testBit p.val
  let right (r : ℕ) : Finset (Fin 13) := Finset.univ.filter fun l => r.testBit (13+l.val)
  let posOK (r : ℕ) := ∃ p l, incidence p l ∧ left r = {p} ∧ right r = {l}
  let negOK (r : ℕ) :=
    (∀ p ∈ left r, ∀ l ∈ right r, ¬incidence p l) ∧
    (∀ l, ((left r).filter fun p => incidence p l).card ≤ 2) ∧
    ∀ p, ((right r).filter fun l => incidence p l).card ≤ 2
  have posOKs : positive.all (fun r => decide (posOK r)) = true := by decide +kernel
  let rotatedRows (i : ℕ) := [61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].map fun m =>
    rotate (m % 8192) i + 8192 * rotate (m / 8192) i
  have rotatedOK (i : Fin 13) : (rotatedRows i.val).all (fun r => decide (negOK r)) = true := by
    fin_cases i <;> decide +kernel
  have negOKs : negative.all (fun r => decide (negOK r)) = true := by
    change ((List.range 13).flatMap rotatedRows).all (fun r => decide (negOK r)) = true
    rw [List.all_flatMap]
    exact List.all_eq_true.mpr fun i hi => rotatedOK ⟨i,List.mem_range.mp hi⟩
  let Row := Fin rows.length
  let sample (i : Row) := rows[i.val]
  let labels : Set Row := {i | (sample i).2 = true}
  let A (i : Row) := left (sample i).1
  let B (i : Row) := right (sample i).1
  have rowCases (i : Row) :
      ((sample i).1 ∈ positive ∧ (sample i).2 = true) ∨
        ((sample i).1 ∈ negative ∧ (sample i).2 = false) := by
    have h : sample i ∈ rows := List.getElem_mem i.isLt
    change sample i ∈ positive.map (fun r => (r,true)) ++ negative.map (fun r => (r,false)) at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r,hr,eq⟩ := List.mem_map.mp h
      exact .inl ⟨eq ▸ hr,eq ▸ rfl⟩
    · obtain ⟨r,hr,eq⟩ := List.mem_map.mp h
      exact .inr ⟨eq ▸ hr,eq ▸ rfl⟩
  refine ⟨rows.length,A,B,labels,?_,?_,?_⟩
  · intro i hi
    rcases rowCases i with h | h
    · exact of_decide_eq_true (List.all_eq_true.mp posOKs _ h.1)
    · exact (Bool.false_ne_true (h.2.symm.trans hi)).elim
  · intro i hi
    rcases rowCases i with h | h
    · exact (hi h.2).elim
    · exact of_decide_eq_true (List.all_eq_true.mp negOKs _ h.1)
  let col (v : Fin 26) : Set Row := {i | (sample i).1.testBit v.val = true}
  let seeds : Set (Set Row) := {∅,Set.univ} ∪ Set.range col
  have cols (v : Fin 26) :
      {i : Row | Fin.addCases (fun p => decide (p ∈ A i)) (fun l => decide (l ∈ B i)) v = true} =
        col v := by
    apply Fin.addCases (m := 13) (n := 13) (motive := fun v =>
      {i : Row | Fin.addCases (fun p => decide (p ∈ A i)) (fun l => decide (l ∈ B i)) v = true} =
        col v) _ _ v
    · intro p
      ext i
      simp [A,left,col,Fin.addCases_left]
    · intro l
      ext i
      change Fin.addCases (fun p => decide (p ∈ A i)) (fun k => decide (k ∈ B i))
        (Fin.natAdd 13 l) = true ↔ (sample i).1.testBit (13+l.val) = true
      rw [Fin.addCases_right]
      simp [B,right]
  have seedsEq : ({∅,Set.univ} ∪ Set.range (fun v : Fin 26 =>
      {i : Row | Fin.addCases (fun p => decide (p ∈ A i)) (fun l => decide (l ∈ B i)) v = true})) =
        seeds := by
    change ({∅,Set.univ} ∪ Set.range _) = {∅,Set.univ} ∪ Set.range col
    congr 2
    funext v
    exact cols v
  intro sampleBits originalSeeds L lengthL legal
  change originalSeeds = seeds at seedsEq
  change labels ∉ originalSeeds ∪ {s | s ∈ L}
  rw [seedsEq]
  have legal' (i : Fin L.length) :
      let previous := seeds ∪ {s | s ∈ L.take i.val}
      ∃ a ∈ previous, ∃ b ∈ previous, L.getD i.val ∅ = a ∪ b ∨ L.getD i.val ∅ = a ∩ b := by
    have h := (legal i).2
    change ∃ _ ∈ (originalSeeds ∪ {s | s ∈ L.take i.val}),
      ∃ _ ∈ (originalSeeds ∪ {s | s ∈ L.take i.val}), _ at h
    rw [seedsEq] at h
    exact h
  intro hm
  obtain ⟨gs,hlen,found⟩ := compile rows L legal' hm
  have labelsAgree : (positive ++ negative).map (fun r => (r,positive.contains r)) = rows := by
    decide +kernel
  have ruledOut := numerical gs (hlen ▸ lengthL)
  let listedRows := (positive ++ negative).map (fun r => (r,positive.contains r))
  let listPack (f : ℕ × Bool → Bool) := (listedRows.map f).foldr Nat.bit 0
  change listPack Prod.snd ∉ gs.foldl step
    ([0,listPack (fun _ => true)] ++ List.ofFn (fun v : Fin 26 => listPack (fun r => r.1.testBit v.val))) at ruledOut
  dsimp only [listPack,listedRows] at ruledOut
  rw [labelsAgree] at ruledOut
  exact ruledOut found
