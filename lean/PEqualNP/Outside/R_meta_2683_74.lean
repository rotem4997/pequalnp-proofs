import Mathlib
import PEqualNP.Defs

-- Retain gates through the output and charge exactly the negative references they and the output use.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2683_74
  (low : ∀ (b : Nat) (op : Fin b → Bool) (l r : Fin b → Nat × Bool)
    (phase : Bool) (paid : Finset Nat) (w : (Fin 9 → Bool) → Nat → Bool),
    0 < b → paid.card ≤ 3 → b + paid.card ≤ 14 → paid.card ≤ 1 →
    (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
    (∀ i : Fin 9, ∃ j, (l j).1 = i.val ∨ (r j).1 = i.val) →
    (∀ i, i ∈ paid ↔ i ≠ 0 ∧ i ≠ 9 ∧
      ((phase = true ∧ i = 9 + b) ∨ ∃ j, l j = (i,true) ∨ r j = (i,true))) →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
      w x (10+j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
    ∃ x : Fin 9 → Bool, (w x (9+b) ^^ phase) ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  (high : ∀ (b : Nat) (op : Fin b → Bool) (l r : Fin b → Nat × Bool)
    (phase : Bool) (paid : Finset Nat) (w : (Fin 9 → Bool) → Nat → Bool),
    0 < b → paid.card ≤ 3 → b + paid.card ≤ 14 → 2 ≤ paid.card →
    (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
    (∀ i : Fin 9, ∃ j, (l j).1 = i.val ∨ (r j).1 = i.val) →
    (∀ i, i ∈ paid ↔ i ≠ 0 ∧ i ≠ 9 ∧
      ((phase = true ∧ i = 9 + b) ∨ ∃ j, l j = (i,true) ∨ r j = (i,true))) →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
      w x (10+j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
    ∃ x : Fin 9 → Bool, (w x (9+b) ^^ phase) ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x6;             x12 x5 ∧ ∀ (x13 : Fin x1), x12 (x3 x13) ∧ x12 (x4 x13)) →             (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x7 x13 ↑x14 = x13 x14) →               (∀ (x14 : Fin (9 : ℕ) → Bool), x7 x14 (9 : ℕ) = Bool.false) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin x1),                     have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x7 x15 x17.1 ^^ x17.2;                     x7 x15 ((10 : ℕ) + ↑x16) = if x2 x16 = Bool.true then x17 (x3 x16) && x17 (x4 x16) else x17 (x3 x16) || x17 (x4 x16)) →                   ∃ (x16 : Fin (9 : ℕ) → Bool), (x7 x16 x5.1 ^^ x5.2) ≠ (x16 (0 : Fin (9 : ℕ)) && x16 (1 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (2 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (3 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (4 : Fin (9 : ℕ)) || x16 (4 : Fin (9 : ℕ)) && x16 (0 : Fin (9 : ℕ)) || x16 (0 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ)) || x16 (1 : Fin (9 : ℕ)) && x16 (6 : Fin (9 : ℕ)) || x16 (2 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (5 : Fin (9 : ℕ)) && x16 (7 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ)) && x16 (8 : Fin (9 : ℕ)) || x16 (8 : Fin (9 : ℕ)) && x16 (5 : Fin (9 : ℕ))) := by
  intro n op l r out paid w hcard hcost hback hout hpaid raw zero step
  classical
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let packed := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have packed_eq : ∀ x, target x = packed x := by decide +kernel
  change ∃ x : Fin 9 → Bool, (w x out.1 ^^ out.2) ≠ target x
  by_contra impossible
  have correct (x : Fin 9 → Bool) : (w x out.1 ^^ out.2) = target x := by
    by_contra differ
    exact impossible ⟨x,differ⟩
  let sample (i : Fin 10) (phase : Bool) (j : Fin 9) : Bool :=
    if phase then false else if i.val = 9 then decide (j.val = 0 ∨ j.val = 1) else decide (j.val = i.val)
  have seedBad : ∀ (i : Fin 10) (phase : Bool),
      ((if h : i.val < 9 then sample i phase ⟨i.val,h⟩ else false) ^^ phase) ≠
        target (sample i phase) := by decide +kernel
  have late : 10 ≤ out.1 := by
    by_contra early
    let i : Fin 10 := ⟨out.1, by omega⟩
    have hs := seedBad i out.2
    have hw : w (sample i out.2) out.1 =
        if h : i.val < 9 then sample i out.2 ⟨i.val,h⟩ else false := by
      split_ifs with h
      · exact raw _ ⟨i.val,h⟩
      · have eq : out.1 = 9 := by change ¬out.1 < 9 at h; omega
        rw [eq]
        exact zero _
    exact hs (hw ▸ correct (sample i out.2))
  let b := out.1 - 9
  have hb : 0 < b := by dsimp [b]; omega
  have bn : b ≤ n := by dsimp [b]; omega
  have last : 9 + b = out.1 := by dsimp [b]; omega
  let embed : Fin b → Fin n := fun j => ⟨j.val, j.isLt.trans_le bn⟩
  let opc := fun j => op (embed j)
  let lc := fun j => l (embed j)
  let rc := fun j => r (embed j)
  have back (j : Fin b) : (lc j).1 < 10+j.val ∧ (rc j).1 < 10+j.val := hback (embed j)
  have calcWire (x : Fin 9 → Bool) (j : Fin b) :
      let val := fun p : Nat × Bool => w x p.1 ^^ p.2
      w x (10+j.val) = if opc j then val (lc j) && val (rc j) else val (lc j) || val (rc j) :=
    step x (embed j)
  let used := fun i : Nat => (out.2 = true ∧ i = 9+b) ∨ ∃ j, lc j = (i,true) ∨ rc j = (i,true)
  let charged := paid.filter (fun i => i ≠ 0 ∧ i ≠ 9 ∧ used i)
  have oldCharged (i : Nat) (ne0 : i ≠ 0) (ne9 : i ≠ 9) (q : used i) : i ∈ paid := by
    change (out.2 = true ∧ i = 9+b) ∨ ∃ j, lc j = (i,true) ∨ rc j = (i,true) at q
    change (out.2 = true → out.1 = 0 ∨ out.1 = 9 ∨ out.1 ∈ paid) ∧
      (∀ j, ((l j).2 = true → (l j).1 = 0 ∨ (l j).1 = 9 ∨ (l j).1 ∈ paid) ∧
        ((r j).2 = true → (r j).1 = 0 ∨ (r j).1 = 9 ∨ (r j).1 ∈ paid)) at hpaid
    rcases q with ⟨phase,eq⟩ | ⟨j,eq | eq⟩
    · rw [last] at eq
      subst i
      exact (hpaid.1 phase).resolve_left ne0 |>.resolve_left ne9
    · have q := (hpaid.2 (embed j)).1
      change (lc j).2 = true → (lc j).1 = 0 ∨ (lc j).1 = 9 ∨ (lc j).1 ∈ paid at q
      rw [eq] at q
      exact (q rfl).resolve_left ne0 |>.resolve_left ne9
    · have q := (hpaid.2 (embed j)).2
      change (rc j).2 = true → (rc j).1 = 0 ∨ (rc j).1 = 9 ∨ (rc j).1 ∈ paid at q
      rw [eq] at q
      exact (q rfl).resolve_left ne0 |>.resolve_left ne9
  have exactSet : ∀ i, i ∈ charged ↔ i ≠ 0 ∧ i ≠ 9 ∧
      ((out.2 = true ∧ i = 9+b) ∨ ∃ j, lc j = (i,true) ∨ rc j = (i,true)) := by
    intro i
    change i ∈ charged ↔ i ≠ 0 ∧ i ≠ 9 ∧ used i
    rw [show charged = paid.filter (fun i => i ≠ 0 ∧ i ≠ 9 ∧ used i) from rfl, Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨oldCharged i h.1 h.2.1 h.2.2,h⟩⟩
  have smallCharges : charged.card ≤ paid.card := Finset.card_le_card (Finset.filter_subset _ _)
  let neighbor : Fin 9 → Fin 9 := ![1,0,1,2,3,0,1,2,3]
  let off (i j : Fin 9) : Bool := decide (j = neighbor i)
  let on (i j : Fin 9) : Bool := decide (j = neighbor i ∨ j = i)
  have inputData : ∀ i, target (off i) = false ∧ target (on i) = true ∧
      ∀ j : Fin 9, j.val ≠ i.val → off i j = on i j := by decide +kernel
  have everyRaw : ∀ i : Fin 9, ∃ j : Fin b, (lc j).1 = i.val ∨ (rc j).1 = i.val := by
    intro i
    by_contra miss
    obtain ⟨lo,hi,agree⟩ := inputData i
    have prop (p : Nat) : p < 10+b → p ≠ i.val → w (off i) p = w (on i) p := by
      induction p using Nat.strong_induction_on with
      | ind p ih =>
        intro lim ne
        by_cases rawp : p < 9
        · have e := agree ⟨p,rawp⟩ ne
          exact (raw _ ⟨p,rawp⟩).trans (e.trans (raw _ ⟨p,rawp⟩).symm)
        · by_cases z : p = 9
          · subst p; rw [zero,zero]
          · let j : Fin b := ⟨p-10,by omega⟩
            have jp : p = 10+j.val := by dsimp [j]; omega
            have nl : (lc j).1 ≠ i.val := fun h => miss ⟨j,Or.inl h⟩
            have nr : (rc j).1 ≠ i.val := fun h => miss ⟨j,Or.inr h⟩
            have ltL : (lc j).1 < p := by rw [jp]; exact (back j).1
            have ltR : (rc j).1 < p := by rw [jp]; exact (back j).2
            have el := ih (lc j).1 ltL (ltL.trans lim) nl
            have er := ih (rc j).1 ltR (ltR.trans lim) nr
            rw [jp, calcWire (off i) j, calcWire (on i) j]
            simp only [el,er]
    have same := prop out.1 (by omega) (by omega)
    have a := correct (off i)
    have c := correct (on i)
    rw [same,lo] at a
    rw [a,hi] at c
    contradiction
  have finish : ∃ x : Fin 9 → Bool, (w x (9+b) ^^ out.2) ≠ packed x := by
    by_cases small : charged.card ≤ 1
    · exact low b opc lc rc out.2 charged w hb (by omega) (by omega) small back everyRaw exactSet raw zero calcWire
    · exact high b opc lc rc out.2 charged w hb (by omega) (by omega) (by omega) back everyRaw exactSet raw zero calcWire
  obtain ⟨x,neq⟩ := finish
  rw [last, ← packed_eq] at neq
  exact neq (correct x)
