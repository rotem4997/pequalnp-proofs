import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.HeptadCover BigOperators

-- Resolve AND gates to one predecessor and record the leaf sets of the resulting unions.
-- Small line sets force exact minimal vertex covers in this representation.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_5180_572
  (rectify : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (C : Circuit),
    let n := N+N
    let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
        let a := w.getD (g.inputs.getD 0 0) ∅
        let b := w.getD (g.inputs.getD 1 0) ∅
        w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
        ((List.finRange n).map fun i => {i})).getD C.output ∅
    let O := C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
    204 ≤ q → N=q^2+q+1 → (∀ l, (L l).card=q+1) →
    (∀ a b : Fin N, a ≠ b → (L a ∩ L b).card ≤ 1) → IsAO2 n C → ¬IsReadK n C 2 → C.output < n + C.size →
    2*q^2+1 ≤ O → 33*(q/4) ≤ C.size-O →
    (∀ s, ∀ l, ∀ p ∈ L l, Fin.castAdd N p ∈ M s ∨ Fin.natAdd N l ∈ M s) →
    (∀ B : Finset (Fin N), B.card ≤ q → ∃ s,
      M s = ((B.biUnion L).image (Fin.castAdd N) ∪ (Finset.univ \ B).image (Fin.natAdd N))) →
    ∃ F : Finset (Finset (Fin N) × Finset (Fin N)), F.biUnion (fun r => r.1 ×ˢ r.2) = incidences L ∧
      (∑ r ∈ F, (r.1.card + r.2.card - 1)) ≤ 100*C.size + N)
  (count : ∀ (N : ℕ) (L : Fin N → Finset (Fin N)),
    (∀ a b : Fin N, a ≠ b → (L a ∩ L b).card ≤ 1) →
    ∀ F : Finset (Finset (Fin N) × Finset (Fin N)), F.biUnion (fun r => r.1 ×ˢ r.2) = incidences L →
      (incidences L).card ≤ (∑ r ∈ F, (r.1.card + r.2.card - 1)))
  : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  have closeSmall5180 (q N O S : ℕ) (large : 200 ≤ q) (lastq : q ≤ 203)
      (order : N=q^2+q+1) (hOR : 2*q^2+1 ≤ O) (hAND : 33*(q/4) ≤ S-O)
      (included : O ≤ S) : N*q ≤ 100*S := by
    clear rectify count
    interval_cases q <;> norm_num at order hOR hAND ⊢ <;> omega

  have switchProgram5180 : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
          let a := w.getD (g.inputs.getD 0 0) ∅
          let b := w.getD (g.inputs.getD 1 0) ∅
          w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
          ((List.finRange n).map fun i => {i})).getD C.output ∅
      ∀ X : Finset (Fin n), circuitFun n C (setInput X) = false ↔ ∃ s, Disjoint (M s) X := by
    clear rectify count closeSmall5180
    classical
    intro n C ao M X
    let hit (P : Finset (Fin n)) := decide (¬ Disjoint P X)
    let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
    let read (l : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => l.getD i false)
    let run (l : List Bool) (g : Gate) := l ++ [read l g]
    let select (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b
    let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) := w ++ [select s w g]
    have emptyHit : hit ∅ = false := by simp [hit]
    have hitUnion (a b : Finset (Fin n)) : hit (a ∪ b) = (hit a || hit b) := by
      by_cases ha : Disjoint a X <;> by_cases hb : Disjoint b X <;>
        simp [hit,ha,hb]
    have readMap (w : List (Finset (Fin n))) (i : ℕ) :
        (w.map hit).getD i false = hit (w.getD i ∅) := by
      induction w generalizing i with
      | nil => cases i <;> exact emptyHit.symm
      | cons a w ih => cases i with
        | zero => rfl
        | succ i => exact ih i
    have snoc {α : Type} (l : List α) (d z : α) (i : ℕ) :
        (l ++ [d]).getD i z = if i = l.length then d else l.getD i z := by
      induction l generalizing i with
      | nil => cases i <;> rfl
      | cons x l ih => cases i with
        | zero => rfl
        | succ i => simpa using ih i
    let Shape (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ, g.inputs = [u,v]
    have gateShape (g : Gate) (hg : g ∈ C.gates) : Shape g := by
      have pair (l : List ℕ) (h : l.length = 2) : ∃ u v, l = [u,v] := by
        cases l with
        | nil => simp at h
        | cons u tl =>
          cases tl with
          | nil => simp at h
          | cons v tl =>
            have z : tl = [] := List.length_eq_zero_iff.mp (by simpa using h)
            exact ⟨u,v,by rw [z]⟩
      exact ⟨ao.1 g hg,pair g.inputs (ao.2.2 g hg)⟩
    have readAnd (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .and)
        (pins : g.inputs = [u,v]) : read l g = (l.getD u false && l.getD v false) := by
      simp only [read,kind,pins,List.map_cons,List.map_nil]
      cases l.getD u false <;> cases l.getD v false <;> rfl
    have readOr (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .or)
        (pins : g.inputs = [u,v]) : read l g = (l.getD u false || l.getD v false) := by
      simp only [read,kind,pins,List.map_cons,List.map_nil]
      cases l.getD u false <;> cases l.getD v false <;> rfl
    have selAnd (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
        (kind : g.op = .and) (pins : g.inputs = [u,v]) :
        select s w g = if s w.length then w.getD u ∅ else w.getD v ∅ := by
      simp only [select,kind,pins]
      rfl
    have selOr (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
        (kind : g.op = .or) (pins : g.inputs = [u,v]) :
        select s w g = w.getD u ∅ ∪ w.getD v ∅ := by
      simp only [select,kind,pins]
      rfl
    let Safe (l : List Bool) (w : List (Finset (Fin n))) :=
      ∀ i, hit (w.getD i ∅) = false → l.getD i false = false
    have sound (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (s : ℕ → Bool)
        (l : List Bool) (w : List (Finset (Fin n))) (len : l.length = w.length)
        (old : Safe l w) : Safe (gs.foldl run l) (gs.foldl (go s) w) := by
      induction gs generalizing l w with
      | nil => exact old
      | cons g gs ih =>
        obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
        have next : hit (select s w g) = false → read l g = false := by
          rcases kind with andG | orG
          · rw [readAnd l g u v andG pins,selAnd s w g u v andG pins]
            cases h : s w.length with
            | false =>
              intro off
              have f : hit (w.getD v ∅) = false := off
              rw [old v f,Bool.and_false]
            | true =>
              intro off
              have f : hit (w.getD u ∅) = false := off
              rw [old u f,Bool.false_and]
          · rw [readOr l g u v orG pins,selOr s w g u v orG pins,hitUnion]
            intro off
            have both : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by
              intro a b
              cases a <;> cases b <;> simp
            obtain ⟨fa,fb⟩ := both _ _ off
            rw [old u fa,old v fb]
            rfl
        apply ih (fun k hk => hg k (by simp [hk])) (run l g) (go s w g) (by simp [run,go,len])
        intro i
        change hit ((w ++ [select s w g]).getD i ∅) = false →
          (l ++ [read l g]).getD i false = false
        rw [snoc,snoc,len]
        by_cases atEnd : i = w.length
        · simpa only [ite_eq_left atEnd] using next
        · simpa only [ite_eq_right atEnd] using old i
    have future (gs : List Gate) (s t : ℕ → Bool) (w : List (Finset (Fin n)))
        (agree : ∀ j, w.length ≤ j → s j = t j) :
        gs.foldl (go s) w = gs.foldl (go t) w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        have now : go s w g = go t w g := by simp only [go,select,agree w.length (le_refl _)]
        simp only [List.foldl_cons,now]
        apply ih
        intro j hj
        have a : w.length + 1 ≤ j := by simpa [go] using hj
        exact agree j (by omega)
    have realize (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (w : List (Finset (Fin n))) :
        ∃ s : ℕ → Bool, gs.foldl run (w.map hit) = (gs.foldl (go s) w).map hit := by
      induction gs generalizing w with
      | nil => exact ⟨fun _ => false,rfl⟩
      | cons g gs ih =>
        obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
        let side := !(hit (w.getD u ∅))
        let now : ℕ → Bool := fun _ => side
        have one : run (w.map hit) g = (go now w g).map hit := by
          change w.map hit ++ [read (w.map hit) g] = (w ++ [select now w g]).map hit
          rw [List.map_append]
          congr 1
          change [read (w.map hit) g] = [hit (select now w g)]
          rcases kind with andG | orG
          · rw [readAnd _ g u v andG pins,selAnd _ _ g u v andG pins,readMap,readMap]
            change [(hit (w.getD u ∅) && hit (w.getD v ∅))] =
              [hit (if !(hit (w.getD u ∅)) then w.getD u ∅ else w.getD v ∅)]
            cases e : hit (w.getD u ∅) <;> simp only [Bool.not_true,Bool.not_false,
              Bool.false_eq_true,ite_true,ite_false,e,Bool.false_and,Bool.true_and]
          · rw [readOr _ g u v orG pins,selOr _ _ g u v orG pins,hitUnion,readMap,readMap]
        obtain ⟨t,rest⟩ := ih (fun k hk => hg k (by simp [hk])) (go now w g)
        let s : ℕ → Bool := fun j => if j = w.length then side else t j
        have first : go s w g = go now w g := by simp only [go,select,s,now,ite_true]
        have tail : gs.foldl (go s) (go now w g) = gs.foldl (go t) (go now w g) := by
          apply future
          intro j hj
          have a : w.length + 1 ≤ j := by simpa [go] using hj
          simp only [s,ite_eq_right (show j ≠ w.length by omega)]
        refine ⟨s,?_⟩
        simp only [List.foldl_cons,one,first,tail]
        exact rest
    have initial : List.ofFn (setInput X) = seed.map hit := by
      change List.ofFn (setInput X) = ((List.finRange n).map fun i => ({i} : Finset (Fin n))).map hit
      rw [List.map_map]
      have finRange : List.finRange n = List.ofFn id := rfl
      rw [finRange,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      change decide (i ∈ X) = hit {i}
      simp [hit]
    have hitZero (P : Finset (Fin n)) : hit P = false ↔ Disjoint P X := by
      simp [hit]
    change (C.gates.foldl run (List.ofFn (setInput X))).getD C.output false = false ↔
      ∃ s, Disjoint ((C.gates.foldl (go s) seed).getD C.output ∅) X
    rw [initial]
    constructor
    · intro rejected
      obtain ⟨s,eq⟩ := realize C.gates gateShape seed
      rw [eq,readMap] at rejected
      exact ⟨s,(hitZero _).mp rejected⟩
    · rintro ⟨s,h⟩
      have seedSafe : Safe (seed.map hit) seed := fun i => by rw [readMap]; exact id
      exact sound C.gates gateShape s (seed.map hit) seed (by simp) seedSafe C.output ((hitZero _).mpr h)

  have primeBelow5180 (n : ℕ) (C : Circuit) (T : Finset (Fin n))
      (on : circuitFun n C (setInput T) = true) :
      ∃ Z ⊆ T, IsPrimeImplicant n C Z := by
    clear rectify count closeSmall5180 switchProgram5180
    classical
    let F := T.powerset.filter fun Z => circuitFun n C (setInput Z) = true
    have mem : T ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun _ h => h),on⟩
    obtain ⟨Z,hZ,least⟩ := F.exists_min_image Finset.card ⟨T,mem⟩
    obtain ⟨zt,yes⟩ := Finset.mem_filter.mp hZ
    refine ⟨Z,Finset.mem_powerset.mp zt,yes,?_⟩
    intro Y hY
    apply Bool.eq_false_iff.mpr
    intro hon
    have ss := Finset.mem_ssubsets.mp hY
    have ym : Y ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (ss.le.trans (Finset.mem_powerset.mp zt)),hon⟩
    exact (Nat.not_lt_of_ge (least Y ym)) (Finset.card_lt_card ss)

  have lineBudget5180 (N : ℕ) (Z : Finset (Fin (N+N))) (B : Finset (Fin N))
      (contained : ∀ l : Fin N, Fin.natAdd N l ∈ Z → l ∈ B) :
      (List.finRange N).countP (fun l => decide (Fin.natAdd N l ∈ Z)) ≤ B.card := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180
    classical
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
    apply Finset.card_le_card
    intro l hl
    exact contained l (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hl)).2)

  have privatePoint5180 (q N : ℕ) (L : Fin N → Finset (Fin N))
      (rows : ∀ l, (L l).card = q+1)
      (thin : ∀ a b : Fin N, a ≠ b → (L a ∩ L b).card ≤ 1)
      (B : Finset (Fin N)) (budget : B.card ≤ q) (l : Fin N) (hl : l ∉ B) :
      ∃ p ∈ L l, p ∉ B.biUnion L := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180
    classical
    have eq := Finset.inter_biUnion (L l) B L
    have cap : (L l ∩ B.biUnion L).card ≤ B.card := calc
      _ = _ := congrArg Finset.card eq
      _ ≤ ∑ k ∈ B, (L l ∩ L k).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ B, 1 := Finset.sum_le_sum fun k hk => thin l k (fun e => hl (e ▸ hk))
      _ = B.card := by simp
    by_contra! inside
    have sub : L l ⊆ B.biUnion L := fun p hp => inside p hp
    rw [Finset.inter_eq_left.mpr sub,rows] at cap
    omega

  have planeIncidenceCard5180 (q N : ℕ) (L : Fin N → Finset (Fin N))
      (lines : ∀ l, (L l).card = q+1) : (incidences L).card = N*(q+1) := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180 privatePoint5180
    classical
    calc
      (incidences L).card = ∑ z : Fin N × Fin N, (if z.1 ∈ L z.2 then 1 else 0 : ℕ) := by
        exact Finset.card_filter _ _
      _ = ∑ p : Fin N, ∑ l : Fin N, (if p ∈ L l then 1 else 0 : ℕ) := Fintype.sum_prod_type _
      _ = ∑ l : Fin N, ∑ p : Fin N, (if p ∈ L l then 1 else 0 : ℕ) := Finset.sum_comm
      _ = N*(q+1) := by simp [lines]

  have switchWidth5180 (n : ℕ) (C : Circuit) :
      let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
          let a := w.getD (g.inputs.getD 0 0) ∅
          let b := w.getD (g.inputs.getD 1 0) ∅
          w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
          ((List.finRange n).map fun i => {i})).getD C.output ∅
      ∀ s, (M s).card ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) + 1 := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180 privatePoint5180 planeIncidenceCard5180
    classical
    intro M s
    let select (w : List (Finset (Fin n))) (g : Gate) :=
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b
    let go (w : List (Finset (Fin n))) (g : Gate) := w ++ [select w g]
    let count (gs : List Gate) := gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
    let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
    let Small (w : List (Finset (Fin n))) (E : Finset (Fin n)) := ∀ A ∈ w, (A \ E).card ≤ 1
    have readSmall (w : List (Finset (Fin n))) (E : Finset (Fin n)) (ok : Small w E) (i : ℕ) :
        (w.getD i ∅ \ E).card ≤ 1 := by
      by_cases h : i < w.length
      · rw [List.getD_eq_getElem _ _ h]
        exact ok _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]
        simp
    have widen (A E F : Finset (Fin n)) (h : E ⊆ F) :
        (A \ F).card ≤ (A \ E).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨a,nf⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨a,fun he => nf (h he)⟩
    have cap (E A : Finset (Fin n)) : (E ∪ A).card ≤ E.card + (A \ E).card := by
      have eq : E ∪ A = E ∪ (A \ E) := by
        ext i
        simp only [Finset.mem_union,Finset.mem_sdiff]
        tauto
      rw [eq]
      exact Finset.card_union_le _ _
    have one (w : List (Finset (Fin n))) (g : Gate) (E : Finset (Fin n)) (ok : Small w E) :
        ∃ F : Finset (Fin n), F.card ≤ E.card + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 1 else 0) ∧ Small (go w g) F := by
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      have ha : (a \ E).card ≤ 1 := readSmall w E ok _
      have hb : (b \ E).card ≤ 1 := readSmall w E ok _
      by_cases hg : PEqualNP.SharedBlockCost.isOrOp g.op = true
      · let F := E ∪ a
        have extE : E ⊆ F := Finset.subset_union_left
        have newSmall : ((a ∪ b) \ F).card ≤ 1 := by
          apply le_trans _ hb
          apply Finset.card_le_card
          intro x hx
          obtain ⟨mem,exclude⟩ := Finset.mem_sdiff.mp hx
          have na : x ∉ a := fun h => exclude (Finset.mem_union_right _ h)
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp mem).resolve_left na,fun h => exclude (extE h)⟩
        refine ⟨F,?_,?_⟩
        · rw [ite_eq_left hg]
          exact (cap E a).trans (Nat.add_le_add_left ha _)
        · intro A hm
          change A ∈ w ++ [select w g] at hm
          rcases List.mem_append.mp hm with old | fresh
          · exact (widen A E F extE).trans (ok A old)
          · have eq : A = a ∪ b := by simpa [select,hg,a,b] using fresh
            exact eq ▸ newSmall
      · have sel : select w g = if s w.length then a else b := by
          simp [select,hg,a,b]
        refine ⟨E,by simp [hg],?_⟩
        intro A hm
        change A ∈ w ++ [select w g] at hm
        rcases List.mem_append.mp hm with old | fresh
        · exact ok A old
        · have eq : A = select w g := List.mem_singleton.mp fresh
          rw [eq,sel]
          split <;> assumption
    have sweep (gs : List Gate) (w : List (Finset (Fin n))) (E : Finset (Fin n)) (ok : Small w E) :
        ∃ F : Finset (Fin n), F.card ≤ E.card + count gs ∧ Small (gs.foldl go w) F := by
      induction gs generalizing w E with
      | nil => exact ⟨E,by simp [count],ok⟩
      | cons g gs ih =>
        obtain ⟨mid,cost,hmid⟩ := one w g E ok
        obtain ⟨F,last,hF⟩ := ih (go w g) mid hmid
        refine ⟨F,?_,hF⟩
        have countEq : count (g::gs) = count gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 1 else 0) := by
          cases hg : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [count,hg]
        rw [countEq]
        omega
    have start : Small seed ∅ := by
      intro A h
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      simp
    obtain ⟨F,cost,ok⟩ := sweep C.gates seed ∅ start
    have cf : F.card ≤ count C.gates := by simpa using cost
    have last : (M s \ F).card ≤ 1 := readSmall (C.gates.foldl go seed) F ok C.output
    have span : (M s).card ≤ (F ∪ M s).card := Finset.card_le_card Finset.subset_union_right
    exact (span.trans (cap F (M s))).trans (Nat.add_le_add cf last)

  have switchCount5180 (n : ℕ) (C : Circuit) :
      let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
          let a := w.getD (g.inputs.getD 0 0) ∅
          let b := w.getD (g.inputs.getD 1 0) ∅
          w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
          ((List.finRange n).map fun i => {i})).getD C.output ∅
      ∃ F : Finset (Finset (Fin n)), (∀ s, M s ∈ F) ∧
        F.card ≤ 2 ^ (C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180 privatePoint5180 planeIncidenceCard5180 switchWidth5180
    classical
    intro M
    let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b]
    let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
    let fixed (gs : List Gate) := gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
    let free (gs : List Gate) := gs.countP (fun g => !(PEqualNP.SharedBlockCost.isOrOp g.op))
    have fixedCons (g : Gate) (gs : List Gate) :
        fixed (g::gs) = fixed gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 1 else 0) := by
      cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [fixed,eq]
    have freeCons (g : Gate) (gs : List Gate) :
        free (g::gs) = free gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 0 else 1) := by
      cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [free,eq]
    have total (gs : List Gate) : fixed gs + free gs = gs.length := by
      induction gs with
      | nil => rfl
      | cons g gs ih =>
        rw [fixedCons,freeCons,List.length_cons]
        cases hg : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [hg] <;> omega
    let yes : ℕ → Bool := fun _ => true
    let no : ℕ → Bool := fun _ => false
    have family (gs : List Gate) (w : List (Finset (Fin n))) :
        ∃ T : Finset (List (Finset (Fin n))), (∀ s, gs.foldl (go s) w ∈ T) ∧ T.card ≤ 2 ^ free gs := by
      induction gs generalizing w with
      | nil => exact ⟨{w},fun _ => Finset.mem_singleton_self _,by simp [free]⟩
      | cons g gs ih =>
        obtain ⟨Tno,hasNo,sizeNo⟩ := ih (go no w g)
        by_cases hg : PEqualNP.SharedBlockCost.isOrOp g.op = true
        · have same (s : ℕ → Bool) : go s w g = go no w g := by simp [go,hg]
          refine ⟨Tno,fun s => ?_,?_⟩
          · simpa only [List.foldl_cons,same s] using hasNo s
          · simpa only [freeCons,ite_eq_left hg,Nat.add_zero] using sizeNo
        · obtain ⟨Tyes,hasYes,sizeYes⟩ := ih (go yes w g)
          refine ⟨Tno ∪ Tyes,?_,?_⟩
          · intro s
            simp only [List.foldl_cons]
            cases hs : s w.length with
            | false =>
              have eq : go s w g = go no w g := by simp only [go,no,hs]
              rw [eq]
              exact Finset.mem_union_left _ (hasNo s)
            | true =>
              have eq : go s w g = go yes w g := by simp only [go,yes,hs]
              rw [eq]
              exact Finset.mem_union_right _ (hasYes s)
          · rw [freeCons,ite_eq_right hg,pow_succ]
            have limit := (Finset.card_union_le Tno Tyes).trans (Nat.add_le_add sizeNo sizeYes)
            omega
    obtain ⟨T,rep,bound⟩ := family C.gates seed
    let extract (w : List (Finset (Fin n))) := w.getD C.output ∅
    refine ⟨T.image extract,?_,?_⟩
    · intro s
      exact Finset.mem_image.mpr ⟨C.gates.foldl (go s) seed,rep s,rfl⟩
    · have eq : C.size - fixed C.gates = free C.gates := by
        have h := total C.gates
        change C.gates.length - fixed C.gates = free C.gates
        omega
      change (T.image extract).card ≤ 2 ^ (C.size - fixed C.gates)
      rw [eq]
      exact Finset.card_image_le.trans bound

  have pencilWitness5180 (q N : ℕ) (L : Fin N → Finset (Fin N))
      (hq : 1 ≤ q) (order : N = q^2+q+1) (rows : ∀ l, (L l).card = q+1)
      (plane : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ L l ∧ r ∈ L l) :
      ∃ B : Finset (Fin N), B.card = q ∧ (B.biUnion L).card = q*q+1 := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180 privatePoint5180 planeIncidenceCard5180 switchWidth5180 switchCount5180
    classical
    let o : Fin N := ⟨0,by omega⟩
    let P := Finset.univ.filter fun l : Fin N => o ∈ L l
    let arm (l : Fin N) := (L l).erase o
    have member (l : Fin N) : l ∈ P ↔ o ∈ L l := by simp [P]
    have apart : (↑P : Set (Fin N)).PairwiseDisjoint arm := by
      intro a ha b hb ne
      apply Finset.disjoint_left.mpr
      intro p hp hq'
      obtain ⟨po,pa⟩ := Finset.mem_erase.mp hp
      obtain ⟨_,pb⟩ := Finset.mem_erase.mp hq'
      obtain ⟨u,_,only⟩ := plane p o po
      exact ne ((only a ⟨pa,(member a).mp ha⟩).trans (only b ⟨pb,(member b).mp hb⟩).symm)
    have unionAll : P.biUnion arm = Finset.univ.erase o := by
      ext p
      constructor
      · intro h
        obtain ⟨l,_,pl⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp pl).1, Finset.mem_univ _⟩
      · intro h
        have po := (Finset.mem_erase.mp h).1
        obtain ⟨l,⟨pl,ol⟩,_⟩ := plane p o po
        exact Finset.mem_biUnion.mpr ⟨l,(member l).mpr ol,Finset.mem_erase.mpr ⟨po,pl⟩⟩
    have sumArms (S : Finset (Fin N)) (sub : S ⊆ P) :
        (S.biUnion arm).card = S.card*q := by
      have sep : (↑S : Set (Fin N)).PairwiseDisjoint arm := fun a ha b hb ne => apart (sub ha) (sub hb) ne
      rw [Finset.card_biUnion sep]
      calc
        _ = ∑ _l ∈ S, q := Finset.sum_congr rfl (fun l hl => by
          have h := Finset.card_erase_add_one ((member l).mp (sub hl))
          rw [rows] at h
          change ((L l).erase o).card = q
          omega)
        _ = _ := by simp
    have total := sumArms P (Finset.Subset.refl _)
    rw [unionAll] at total
    have pencilCard : P.card = q+1 := by
      apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < q)
      rw [← total, Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ, Fintype.card_fin,
        order,pow_two,Nat.add_mul,one_mul]
      omega
    obtain ⟨l,hl⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
    let B := P.erase l
    have sub : B ⊆ P := Finset.erase_subset _ _
    have bcard : B.card = q := by
      have h := Finset.card_erase_add_one hl
      change (P.erase l).card = q
      omega
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    have u : B.biUnion L = insert o (B.biUnion arm) := by
      ext p
      constructor
      · intro h
        obtain ⟨w,hw,pw⟩ := Finset.mem_biUnion.mp h
        by_cases po : p=o
        · exact Finset.mem_insert.mpr (Or.inl po)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_erase.mpr ⟨po,pw⟩⟩))
      · intro h
        rcases Finset.mem_insert.mp h with rfl | h
        · exact Finset.mem_biUnion.mpr ⟨k,hk,(member k).mp (sub hk)⟩
        · obtain ⟨w,hw,pw⟩ := Finset.mem_biUnion.mp h
          exact Finset.mem_biUnion.mpr ⟨w,hw,(Finset.mem_erase.mp pw).2⟩
    have no : o ∉ B.biUnion arm := by
      intro h
      obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_erase.mp hw).1 rfl
    refine ⟨B,bcard,?_⟩
    rw [u,Finset.card_insert_of_notMem no,sumArms B sub,bcard]

  have distinguish5180 (q N k : ℕ) (fits : 800*k ≤ N) (small : 4*k ≤ q)
      (F : Finset (Finset (Fin (N+N))))
      (realize : ∀ B : Finset (Fin N), B.card ≤ q → ∃ A ∈ F,
        ∀ l : Fin N, Fin.natAdd N l ∈ A ↔ l ∉ B) :
      2^(33*k) ≤ F.card := by
    clear rectify count closeSmall5180 switchProgram5180 primeBelow5180 lineBudget5180 privatePoint5180 planeIncidenceCard5180 switchWidth5180 switchCount5180 pencilWitness5180
    classical
    let Pick := ↥((Finset.univ : Finset (Fin 800)).powersetCard 4)
    let code (i : Fin k) (j : Fin 800) : Fin N := ⟨800*i.val+j.val,by omega⟩
    have faithful (i i' : Fin k) (j j' : Fin 800) (h : code i j = code i' j') : i=i' ∧ j=j' := by
      have v := congrArg Fin.val h
      change 800*i.val+j.val = 800*i'.val+j'.val at v
      constructor <;> apply Fin.ext <;> omega
    let pick (f : Fin k → Pick) :=
      Finset.univ.biUnion fun i => (f i).val.image (code i)
    have cap (f : Fin k → Pick) : (pick f).card ≤ q := by
      calc
        (pick f).card ≤ ∑ i : Fin k, ((f i).val.image (code i)).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, 4 := Finset.sum_le_sum (fun i _ =>
          Finset.card_image_le.trans (le_of_eq (Finset.mem_powersetCard.mp (f i).property).2))
        _ ≤ q := by simpa [Nat.mul_comm] using small
    have picked (f : Fin k → Pick) (i : Fin k) (j : Fin 800) :
        code i j ∈ pick f ↔ j ∈ (f i).val := by
      constructor
      · intro h
        obtain ⟨i',_,hh⟩ := Finset.mem_biUnion.mp h
        obtain ⟨j',hj,eq⟩ := Finset.mem_image.mp hh
        obtain ⟨rfl,rfl⟩ := faithful i' i j' j eq
        exact hj
      · intro h
        exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ h⟩
    choose val mem test using fun f : Fin k → Pick => realize (pick f) (cap f)
    let J (f : Fin k → Pick) : ↥F := ⟨val f,mem f⟩
    have inj : Function.Injective J := by
      intro f g h
      have eq : val f = val g := congrArg Subtype.val h
      funext i
      apply Subtype.ext
      ext j
      rw [← picked f,← picked g]
      by_contra! bad
      have ff := test f (code i j)
      have gg := test g (code i j)
      rw [eq] at ff
      tauto
    have countP : Fintype.card Pick = Nat.choose 800 4 := by
      simp [Pick]
    have enough : (2:ℕ)^33 ≤ Fintype.card Pick := by
      rw [countP,Nat.choose_eq_descFactorial_div_factorial]
      norm_num [Nat.descFactorial,Nat.factorial]
    calc
      2^(33*k) = ((2:ℕ)^33)^k := pow_mul _ _ _
      _ ≤ (Fintype.card Pick)^k := Nat.pow_le_pow_left enough _
      _ = Fintype.card (Fin k → Pick) := by simp
      _ ≤ Fintype.card ↥F := Fintype.card_le_of_injective J inj
      _ = F.card := Fintype.card_coe _

  classical
  intro q N L C large order rows plane ao nonread out sparse
  let n := N + N
  let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
          let a := w.getD (g.inputs.getD 0 0) ∅
          let b := w.getD (g.inputs.getD 1 0) ∅
          w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
          ((List.finRange n).map fun i => {i})).getD C.output ∅
  have switches (X : Finset (Fin n)) :
      circuitFun n C (setInput X) = false ↔ ∃ s, Disjoint (M s) X :=
    switchProgram5180 n C ao X
  have cross (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have ev := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at ev
    omega
  have thin (a b : Fin N) (ab : a ≠ b) : (L a ∩ L b).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp r hr
    by_contra ne
    obtain ⟨u,_,only⟩ := plane p r ne
    obtain ⟨pa,pb⟩ := Finset.mem_inter.mp hp
    obtain ⟨ra,rb⟩ := Finset.mem_inter.mp hr
    exact ab ((only a ⟨pa,ra⟩).trans (only b ⟨pb,rb⟩).symm)
  -- Every switch setting hits each accepted incident pair.
  have cover (s : ℕ → Bool) (l p : Fin N) (hp : p ∈ L l) :
      Fin.castAdd N p ∈ M s ∨ Fin.natAdd N l ∈ M s := by
    let E : Finset (Fin n) := {Fin.castAdd N p, Fin.natAdd N l}
    have lim : (List.finRange N).countP (fun k => decide (Fin.natAdd N k ∈ E)) ≤ q := by
      have h := lineBudget5180 N E {l} (by
        intro k hk
        rcases Finset.mem_insert.mp hk with h | h
        · exact (cross p k h.symm).elim
        · exact Finset.mem_singleton.mpr (Fin.natAdd_injective N N (Finset.mem_singleton.mp h)))
      simpa only [Finset.card_singleton] using h.trans (by simp; omega)
    have yes := ((sparse E lim).mpr ⟨p,l,hp,rfl⟩).1
    by_contra! miss
    have dis : Disjoint (M s) E := by
      apply Finset.disjoint_left.mpr
      intro i hi he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact miss.1 hi
      · exact miss.2 (Finset.mem_singleton.mp he ▸ hi)
    have no := (switches E).mpr ⟨s,dis⟩
    exact Bool.noConfusion (yes.symm.trans no)
  let Hmask (B : Finset (Fin N)) : Finset (Fin n) :=
    (B.biUnion L).image (Fin.castAdd N) ∪ (Finset.univ \ B).image (Fin.natAdd N)
  have ptsOf (B : Finset (Fin N)) (p : Fin N) : Fin.castAdd N p ∈ Hmask B ↔ p ∈ B.biUnion L := by
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨p',hu,eq⟩ := Finset.mem_image.mp h
        exact Fin.castAdd_injective N N eq ▸ hu
      · obtain ⟨l,_,eq⟩ := Finset.mem_image.mp h
        exact (cross p l eq.symm).elim
    · intro hp
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
  have linesOf (B : Finset (Fin N)) (l : Fin N) : Fin.natAdd N l ∈ Hmask B ↔ l ∉ B := by
    constructor
    · intro hl
      rcases Finset.mem_union.mp hl with h | h
      · obtain ⟨p,_,eq⟩ := Finset.mem_image.mp h
        exact (cross p l eq).elim
      · obtain ⟨l',hu,eq⟩ := Finset.mem_image.mp h
        exact Fin.natAdd_injective N N eq ▸ (Finset.mem_sdiff.mp hu).2
    · intro hl
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hl⟩))
  -- A set of at most q lines determines a unique minimal vertex cover beneath its mask.
  have masks (B : Finset (Fin N)) (small : B.card ≤ q) :
      ∃ s, M s = (B.biUnion L).image (Fin.castAdd N) ∪ (Finset.univ \ B).image (Fin.natAdd N) := by
    let U := B.biUnion L
    let H : Finset (Fin n) := U.image (Fin.castAdd N) ∪ (Finset.univ \ B).image (Fin.natAdd N)
    have pts := ptsOf B
    have lns := linesOf B
    have no : circuitFun n C (setInput Hᶜ) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨Z,zs,prime⟩ := primeBelow5180 n C Hᶜ on
      have bounded (l : Fin N) (hl : Fin.natAdd N l ∈ Z) : l ∈ B := by
        by_contra h
        exact Finset.mem_compl.mp (zs hl) ((lns l).mpr h)
      obtain ⟨p,l,pl,eq⟩ := (sparse Z ((lineBudget5180 N Z B bounded).trans small)).mp prime
      have lp : l ∈ B := bounded l (by simp [eq])
      have zp : Fin.castAdd N p ∈ Z := by simp [eq]
      exact Finset.mem_compl.mp (zs zp) ((pts p).mpr (Finset.mem_biUnion.mpr ⟨l,lp,pl⟩))
    obtain ⟨s,dis⟩ := (switches Hᶜ).mp no
    have sub : M s ⊆ H := by
      intro i hi
      by_contra h
      exact Finset.disjoint_left.mp dis hi (Finset.mem_compl.mpr h)
    refine ⟨s,Finset.Subset.antisymm sub ?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,hl,pl⟩ := Finset.mem_biUnion.mp hp
      exact (cover s l p pl).resolve_right fun hit => (lns l).mp (sub hit) hl
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      have absent :=  (Finset.mem_sdiff.mp hl).2
      obtain ⟨p,pl,pr⟩ := privatePoint5180 q N L rows thin B small l absent
      exact (cover s l p pl).resolve_left fun hit => pr ((pts p).mp (sub hit))
  -- A pencil supplies a wide mask. Four choices in each block of eight hundred lines
  -- give more than thirty-three binary choices per complete block of four selected lines.
  let O := C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
  have orBound : 2*q^2+1 ≤ O := by
    obtain ⟨B,bc,uc⟩ := pencilWitness5180 q N L (by omega) order rows plane
    obtain ⟨s,ms⟩ := masks B (by omega)
    have w : (M s).card ≤ O+1 := switchWidth5180 n C s
    have separate : Disjoint ((B.biUnion L).image (Fin.castAdd N))
        ((Finset.univ \ B).image (Fin.natAdd N)) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hj
      exact cross p l he.symm
    rw [ms,Finset.card_union_of_disjoint separate,
      Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
      Finset.card_image_of_injective _ (Fin.natAdd_injective N N),
      Finset.card_sdiff_of_subset (Finset.subset_univ B),
      Finset.card_univ,Fintype.card_fin,uc,bc,order,pow_two] at w
    rw [pow_two]
    omega
  have otherBound : 33*(q/4) ≤ C.size-O := by
    obtain ⟨F,allF,capF⟩ := switchCount5180 n C
    have four : 4*(q/4) ≤ q := by omega
    have fit : 800*(q/4) ≤ N := by
      have h := Nat.mul_le_mul_right q large
      rw [order,pow_two]
      omega
    have cert (B : Finset (Fin N)) (hb : B.card ≤ q) :
        ∃ A ∈ F, ∀ l : Fin N, Fin.natAdd N l ∈ A ↔ l ∉ B := by
      obtain ⟨s,ms⟩ := masks B hb
      exact ⟨M s,allF s,fun l => ms ▸ linesOf B l⟩
    have lim := (distinguish5180 q N (q/4) fit four F cert).trans capF
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp lim
  by_cases hi : 204 ≤ q
  · obtain ⟨F,hF,price⟩ := rectify q N L C hi order rows thin ao nonread out orBound otherBound cover masks
    have lower := count N L thin F hF
    rw [planeIncidenceCard5180 q N L rows, Nat.mul_add, Nat.mul_one] at lower
    omega
  · have c : O ≤ C.size := List.countP_le_length
    exact closeSmall5180 q N O C.size large (by omega) order orBound otherBound c
