import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 20000 in
theorem PEqualNP.Outside.R_meta_2091_47
  (sparse : let D : Finset ℕ := {0, 1, 3, 9}
    ∀ C : Circuit, Monotone2 C → ∀ a b : ℕ,
    (∀ u v : Fin 26,
      (let z := C.wires (List.ofFn fun k : Fin 26 => decide (k = u ∨ k = v))
       GateOp.or.eval [z.getD a false, z.getD b false] = true) ↔
      (SimpleGraph.fromRel (fun i j : Fin 26 => i.val < 13 ∧ 13 ≤ j.val ∧
        (i.val + 13 - (j.val - 13)) % 13 ∈ D)).Adj u v) → 37 ≤ C.size)
  (lower : let D : Finset (Fin 13) := {0, 1, 3, 9}
    let E := fun (p l : Fin 13) => ∃ d ∈ D, p = l + d
    ∀ (C : Circuit), Monotone2 C → 37 ≤ C.size → C.size ≤ 62 →
      ∀ (a b : Fin (26 + C.size)), a ≠ b →
      (∀ P L : Finset (Fin 13),
        ((∃ l, ∀ p ∈ P, E p l) ∨ ∃ p, ∀ l ∈ L, E p l) →
        let x := fun k : Fin 26 => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
          ∃ l ∈ L, k = Fin.natAdd 13 l)
        let ws := C.wires (List.ofFn x)
        (ws.getD a.val false || ws.getD b.val false) =
          decide (∃ p ∈ P, ∃ l ∈ L, E p l)) → False) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  have complete : let E := fun (p l : Fin 13) => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d
    let A := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ P, ¬ E p l
    ∀ P L : Finset (Fin 13), (∀ l ∈ L, A P l) →
      ((∃ l, ∀ p ∈ P, E p l) ∨ ∃ p, ∀ l ∈ L, E p l) →
      ∃ Q : Finset (Fin 13), P ⊆ Q ∧ (∀ l ∈ L, A Q l) ∧
        (∀ q ∉ Q, ∃ l, A Q l ∧ E q l) ∧
        ((∃ l, ∀ q ∈ Q, E q l) ∨ ∃ p, ∀ l, A Q l → E p l) := by
    let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let incident (p l : Fin 13) : Prop := ∃ d ∈ offsets, p = l + d
    let avoids (S : Finset (Fin 13)) (l : Fin 13) := ∀ p ∈ S, ¬incident p l
    have planePairLine : ∀ p q : Fin 13, ∃ l : Fin 13, incident p l ∧ incident q l := by
      dsimp only [incident, offsets]
      decide
    have planePairPoint : ∀ l m : Fin 13, ∃ p : Fin 13, incident p l ∧ incident p m := by
      dsimp only [incident, offsets]
      decide
    let AvoidRel (I : Fin 13 → Fin 13 → Prop) (S : Finset (Fin 13)) (l : Fin 13) :=
      ∀ p ∈ S, ¬I p l
    let SaturatedRel (I : Fin 13 → Fin 13 → Prop) (S : Finset (Fin 13)) :=
      ∀ p ∉ S, ∃ l, AvoidRel I S l ∧ I p l
    let LineRel (I : Fin 13 → Fin 13 → Prop) (S : Finset (Fin 13)) :=
      ∃ l, ∀ p ∈ S, I p l
    let DegenerateRel (I : Fin 13 → Fin 13 → Prop) (S : Finset (Fin 13)) :=
      LineRel I S ∨ ∃ p, ∀ l, AvoidRel I S l → I p l
    have completeLine (I : Fin 13 → Fin 13 → Prop)
        (meet : ∀ l k, ∃ p, I p l ∧ I p k)
        (crossing : ∀ l r q, I r l → (I q l → q = r) →
          ∃ k, I q k ∧ ∀ z, I z k → I z l → z = r)
        (P L : Finset (Fin 13)) (off : ∀ l ∈ L, AvoidRel I P l)
        (line : LineRel I P) :
        ∃ Q, P ⊆ Q ∧ (∀ l ∈ L, AvoidRel I Q l) ∧ SaturatedRel I Q ∧ DegenerateRel I Q := by
      classical
      obtain ⟨l, inside⟩ := line
      by_cases full : ∀ r, I r l → r ∈ P
      · refine ⟨Finset.univ, Finset.subset_univ _, ?_, ?_, Or.inr ⟨0, ?_⟩⟩
        · intro k hk
          obtain ⟨p, hl, hpk⟩ := meet l k
          exact False.elim (off k hk p (full p hl) hpk)
        · intro p hp
          exact False.elim (hp (Finset.mem_univ _))
        · intro k h
          obtain ⟨p, hpk, _⟩ := meet k k
          exact False.elim (h p (Finset.mem_univ _) hpk)
      · push Not at full
        obtain ⟨r, hr, absent⟩ := full
        refine ⟨P, Finset.Subset.rfl, off, ?_, Or.inl ⟨l, inside⟩⟩
        intro q hq
        by_cases h : I q l
        · obtain ⟨k, hqk, uniq⟩ := crossing l q q h (fun _ => rfl)
          exact ⟨k, fun z hz hzk => hq (uniq z hzk (inside z hz) ▸ hz), hqk⟩
        · obtain ⟨k, hqk, uniq⟩ := crossing l r q hr (False.elim ∘ h)
          exact ⟨k, fun z hz hzk => absent (uniq z hzk (inside z hz) ▸ hz), hqk⟩
    have swapInc (p l : Fin 13) : incident p l ↔ incident (-l) (-p) := by
      constructor <;> rintro ⟨d, hd, eq⟩ <;> refine ⟨d, hd, ?_⟩
      · rw [eq]
        abel
      · rw [show p = -(-p) from (neg_neg p).symm, show l = -(-l) from (neg_neg l).symm, eq]
        abel
    have shiftInc (p l t : Fin 13) : incident p l ↔ incident (p+t) (l+t) := by
      constructor <;> rintro ⟨d,hd,h⟩ <;> refine ⟨d,hd,?_⟩
      · rw [h]
        abel
      · exact add_right_cancel (b := t) (by simpa only [add_right_comm l d t] using h)
    have crossingZero : ∀ r q : Fin 13, incident r 0 → (incident q 0 → q = r) →
        ∃ k : Fin 13, incident q k ∧ ∀ z : Fin 13, incident z k → incident z 0 → z = r := by
      dsimp only [incident, offsets]
      decide
    have crossingLine (l r q : Fin 13) (hr : incident r l) (hq : incident q l → q = r) :
        ∃ k : Fin 13, incident q k ∧ ∀ z : Fin 13, incident z k → incident z l → z = r := by
      have atZero (x : Fin 13) : incident (x + -l) 0 ↔ incident x l := by
        simpa using (shiftInc x l (-l)).symm
      obtain ⟨k, hk, unique⟩ := crossingZero (r + -l) (q + -l) ((atZero r).mpr hr)
        (fun h => congrArg (· + -l) (hq ((atZero q).mp h)))
      refine ⟨k+l, by simpa using (shiftInc _ _ l).mp hk, ?_⟩
      intro z hzk hzl
      have z0 : incident (z + -l) k := by simpa using (shiftInc _ _ (-l)).mp hzk
      exact add_right_cancel (unique (z + -l) z0 ((atZero z).mpr hzl))
    have crossingPoint (l r q : Fin 13) (hr : incident l r) (hq : incident l q → q = r) :
        ∃ k : Fin 13, incident k q ∧ ∀ z : Fin 13, incident k z → incident l z → z = r := by
      obtain ⟨k, hk, hu⟩ := crossingLine (-l) (-r) (-q) ((swapInc _ _).mp hr)
        (fun h => congrArg Neg.neg (hq ((swapInc _ _).mpr h)))
      refine ⟨-k, by simpa using (swapInc _ _).mp hk, ?_⟩
      intro z hzk hzl
      have hzk' : incident (-z) k := by simpa using (swapInc _ _).mp hzk
      exact neg_injective (hu (-z) hzk' ((swapInc _ _).mp hzl))
    have geometryCompletion (P L : Finset (Fin 13)) (off : ∀ l ∈ L, avoids P l)
        (thin : (∃ l, ∀ p ∈ P, incident p l) ∨ (∃ p, ∀ l ∈ L, incident p l)) :
        ∃ Q, P ⊆ Q ∧ (∀ l ∈ L, avoids Q l) ∧ SaturatedRel incident Q ∧ DegenerateRel incident Q := by
      classical
      rcases thin with h | h
      · exact completeLine incident planePairPoint crossingLine P L off h
      · let J := fun l p : Fin 13 => incident p l
        have rev : ∀ p ∈ P, AvoidRel J L p := fun p hp l hl => off l hl p hp
        obtain ⟨B, hLB, hPB, hsat, hdeg⟩ :=
          completeLine J planePairLine crossingPoint L P rev h
        let Q := Finset.univ.filter fun p : Fin 13 => AvoidRel J B p
        have hQ (p : Fin 13) : p ∈ Q ↔ AvoidRel J B p := by simp [Q]
        have hB (l : Fin 13) : l ∈ B ↔ avoids Q l := by
          constructor
          · exact fun hl p hp => (hQ p).mp hp l hl
          · intro hAvoid
            by_contra hx
            obtain ⟨p, hp, inc⟩ := hsat l hx
            exact hAvoid p ((hQ p).mpr hp) inc
        refine ⟨Q, (fun p hp => (hQ p).mpr (hPB p hp)), (fun l hl => (hB l).mp (hLB hl)), ?_, ?_⟩
        · intro p hp
          have hnot : ¬∀ l ∈ B, ¬incident p l := fun e => hp ((hQ p).mpr e)
          push Not at hnot
          obtain ⟨l, hl, hit⟩ := hnot
          exact ⟨l, (hB l).mp hl, hit⟩
        · rcases hdeg with ⟨p, cover⟩ | ⟨l, cover⟩
          · exact Or.inr ⟨p, fun k hk => cover k ((hB k).mpr hk)⟩
          · exact Or.inl ⟨l, fun p hp => cover p ((hQ p).mp hp)⟩
    exact geometryCompletion
  classical
  let E := fun (p l : Fin 13) => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d
  let A := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ P, ¬ E p l
  let inputs := fun (P L : Finset (Fin 13)) (k : Fin 26) =>
    decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l ∈ L, k = Fin.natAdd 13 l)
  intro offsets rel avoid pair negInput wires C hm hs a b hab pos neg
  let out := fun (x : Fin 26 → Bool) =>
    (C.wires (List.ofFn x)).getD a.val false || (C.wires (List.ofFn x)).getD b.val false
  have mono (x y : Fin 26 → Bool) (le : ∀ k, x k = true → y k = true) : out x = true → out y = true := by
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have lift (gs : List Gate) (w z : List Bool) (hlen : w.length = z.length)
        (h : ∀ i, w.getD i false = true → z.getD i false = true)
        (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
        ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step z).getD i false = true := by
      induction gs generalizing w z with
      | nil => exact h
      | cons g gs ih =>
        have val : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
            g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
          rcases ops g (by simp) with he | he
          · rw [he]
            change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
            simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
            exact fun hw i hi => h i (hw i hi)
          · rw [he]
            change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
            simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            rintro ⟨i, hi, hv⟩
            exact ⟨i, hi, h i hv⟩
        apply ih (step w g) (step z g) (by simp [step, hlen]) _ (fun g' hg => ops g' (by simp [hg]))
        intro i
        dsimp only [step]
        by_cases hi : i < w.length
        · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hlen ▸ hi)]
          exact h i
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
          cases i - z.length with
          | zero => exact val
          | succ j => simp
    have lift' := lift C.gates (List.ofFn x) (List.ofFn y) (by simp) (by
      intro i
      by_cases hi : i < 26
      · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] using le ⟨i, hi⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_none, Bool.false_eq_true, imp_self]) (fun g hg => (hm g hg).1)
    intro hx
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hx).imp (lift' a.val) (lift' b.val))
  have slices (P L : Finset (Fin 13)) (hslice : (∃ l, ∀ p ∈ P, E p l) ∨ ∃ p, ∀ l ∈ L, E p l) :
      out (inputs P L) = decide (∃ p ∈ P, ∃ l ∈ L, E p l) := by
    by_cases hit : ∃ p ∈ P, ∃ l ∈ L, E p l
    · rw [decide_eq_true hit]
      obtain ⟨p, hp, l, hl, he⟩ := hit
      have start := pos p l he
      change (wires C a.val (pair p l) || (wires C b.val (pair p l) || false)) = true at start
      apply mono (pair p l) _ _ (show out (pair p l) = true from by simpa only [out, wires, Bool.or_false] using start)
      intro k hk
      simp only [pair, decide_eq_true_eq] at hk
      change decide _ = true
      apply decide_eq_true
      exact hk.elim (fun e => Or.inl ⟨p, hp, e⟩) (fun e => Or.inr ⟨l, hl, e⟩)
    · rw [decide_eq_false hit]
      obtain ⟨Q, hP, hL, hmax, hdeg⟩ := complete P L (fun l hl p hp he => hit ⟨p, hp, l, hl, he⟩) hslice
      have stop := neg Q hmax hdeg
      apply Bool.eq_false_iff.mpr
      intro hx
      have hup := mono (inputs P L) (fun k => decide ((∃ p ∈ Q, k = Fin.castAdd 13 p) ∨
        ∃ l, k = Fin.natAdd 13 l ∧ A Q l)) (by
        intro k hk
        simp only [inputs, decide_eq_true_eq] at hk ⊢
        rcases hk with ⟨p, hp, he⟩ | ⟨l, hl, he⟩
        · exact Or.inl ⟨p, hP hp, he⟩
        · exact Or.inr ⟨l, he, hL l hl⟩) hx
      change (wires C a.val (negInput Q) || (wires C b.val (negInput Q) || false)) = false at stop
      have hd : out (negInput Q) = false := by simpa only [out, wires, Bool.or_false] using stop
      exact Bool.noConfusion (hup.symm.trans hd)
  let lefts (u v : Fin 26) := Finset.univ.filter (fun p : Fin 13 => Fin.castAdd 13 p = u ∨ Fin.castAdd 13 p = v)
  let rights (u v : Fin 26) := Finset.univ.filter (fun l : Fin 13 => Fin.natAdd 13 l = u ∨ Fin.natAdd 13 l = v)
  let adj := (SimpleGraph.fromRel (fun i j : Fin 26 => i.val < 13 ∧ 13 ≤ j.val ∧
    (i.val + 13 - (j.val - 13)) % 13 ∈ ({0,1,3,9} : Finset ℕ))).Adj
  have collinear : ∀ u v, ∃ l, ∀ p ∈ lefts u v, E p l := by
    dsimp only [lefts, E]
    decide
  have edge : ∀ u v, (∃ p ∈ lefts u v, ∃ l ∈ rights u v, E p l) ↔ adj u v := by
    dsimp only [lefts, rights, E, adj]
    decide
  have bits (u v : Fin 26) : inputs (lefts u v) (rights u v) =
      (fun k => decide (k = u ∨ k = v)) := by
    funext k
    apply decide_eq_decide.mpr
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact (Finset.mem_filter.mp hp).2
      · exact (Finset.mem_filter.mp hl).2
    · intro hk
      induction k using Fin.addCases (m := 13) (n := 13) with
      | left p => exact Or.inl ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
      | right l => exact Or.inr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
  have lo := sparse C hm a.val b.val (by
    intro u v
    have h := slices (lefts u v) (rights u v) (Or.inl (collinear u v))
    rw [bits] at h
    change (( _ || (_ || false)) = true) ↔ adj u v
    rw [Bool.or_false]
    change (out (fun k => decide (k = u ∨ k = v)) = true) ↔ adj u v
    rw [h, decide_eq_true_eq, edge])
  exact lower C hm lo hs a b hab slices
