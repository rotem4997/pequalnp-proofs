import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_713
    (and_end : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 D → pins.length ≤ 2 →
      (let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
       let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
       let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
       let read := fun s t => PEqualNP.CircuitLowerBounds.GateOp.and.eval
         (pins.map fun i => (D.wires (List.ofFn (vec s t))).getD i false)
       (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
          (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false)) → 63 ≤ D.size)
    (or_end : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (pins : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 D → pins.length ≤ 2 →
      (let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
       let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
       let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
       let read := fun s t => PEqualNP.CircuitLowerBounds.GateOp.or.eval
         (pins.map fun i => (D.wires (List.ofFn (vec s t))).getD i false)
       (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
          (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false)) → 63 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C mono computes
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let checks (f : (Fin 26 → Bool) → Bool) : Prop :=
    let read := fun s t => f (vec s t)
    (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
          (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false)
  let pt (p : Fin 13) : Fin 26 := ⟨p.val,by omega⟩
  let ln (l : Fin 13) : Fin 26 := ⟨13+l.val,by omega⟩
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ u v : Fin 26, (u.val,v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ near (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val) := by
    dsimp only [edges,near]
    decide +kernel
  have points : ∀ p : Fin 13, (Fin.ofNat 13 (pt p).val) = p := by
    intro p
    apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  have lines : ∀ l : Fin 13, (Fin.ofNat 13 (ln l).val) = l := by
    intro l
    apply Fin.ext
    change (13+l.val) % 13 = l.val
    omega
  have pointInv : ∀ i : Fin 26, i.val < 13 → pt (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  have lineInv : ∀ i : Fin 26, 13 ≤ i.val → ln (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    change 13+i.val % 13 = i.val
    omega
  have pv (s t : Finset (Fin 13)) (p : Fin 13) : vec s t (pt p) = true ↔ p ∈ s := by
    simp only [vec,ite_eq_left (show (pt p).val < 13 from p.isLt),points,decide_eq_true_eq]
  have lv (s t : Finset (Fin 13)) (l : Fin 13) : vec s t (ln l) = true ↔ l ∈ t := by
    have high : ¬(ln l).val < 13 := by dsimp [ln]; omega
    simp only [vec,ite_eq_right high,lines,decide_eq_true_eq]
  have value (s t : Finset (Fin 13)) :
      C.eval (List.ofFn (vec s t)) = true ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
    rw [computes]
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      obtain ⟨lo,hi,h⟩ := (table u v).mp he
      exact ⟨Fin.ofNat 13 u.val,(pv s t _).mp (by rwa [pointInv u lo]),
        Fin.ofNat 13 v.val,(lv s t _).mp (by rwa [lineInv v hi]),h⟩
    · rintro ⟨p,hp,l,hl,h⟩
      exact ⟨pt p,ln l,(table _ _).mpr ⟨p.isLt,by dsimp [ln]; omega,by simpa only [points,lines] using h⟩,
        (pv s t p).mpr hp,(lv s t l).mpr hl⟩
  have cert : checks (fun x => C.eval (List.ofFn x)) := by
    constructor
    · intro p l hp
      exact (value _ _).mpr ⟨p,Finset.mem_singleton_self _,l,Finset.mem_singleton_self _,hp⟩
    · intro s _
      constructor
      · apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p,hp,l,hl,inc⟩ := (value s (off s)).mp h
        exact (Finset.mem_filter.mp hl).2 p hp inc
      · apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p,hp,l,hl,inc⟩ := (value (off s) s).mp h
        exact (Finset.mem_filter.mp hp).2 l hl (by simpa only [near,Nat.add_comm l.val p.val] using inc)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp only [step,List.length_append,List.length_cons,List.length_nil]
      omega
  obtain ⟨gs,out⟩ := C
  induction gs using List.reverseRecOn with
  | nil =>
    let u : Fin 26 → Bool := fun i => decide (i.val = 0 ∨ i.val = 13)
    let v : Fin 26 → Bool := fun i => decide (i.val = 1 ∨ i.val = 15)
    have hu := (computes u).mpr ⟨0,13,by decide,rfl,rfl⟩
    have hv := (computes v).mpr ⟨1,15,by decide,rfl,rfl⟩
    change (List.ofFn u).getD out false = true at hu
    change (List.ofFn v).getD out false = true at hv
    by_cases h : out < 26
    · rw [List.getD_eq_getElem (List.ofFn u) false (by simpa only [List.length_ofFn] using h),List.getElem_ofFn] at hu
      rw [List.getD_eq_getElem (List.ofFn v) false (by simpa only [List.length_ofFn] using h),List.getElem_ofFn] at hv
      simp only [u,v,decide_eq_true_eq] at hu hv
      omega
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn];omega)] at hu
      exact Bool.noConfusion hu
  | append_singleton pre g ih =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre,out⟩
    have hd : PEqualNP.MetaComplexity.Monotone2 D := by
      intro k hk
      exact mono k (List.mem_append_left _ hk)
    have hg := mono g (List.mem_append_right pre (by simp))
    let packet (op : PEqualNP.CircuitLowerBounds.GateOp) (pins : List ℕ) (x : Fin 26 → Bool) :=
      op.eval (pins.map fun i => (D.wires (List.ofFn x)).getD i false)
    have run (x : Fin 26 → Bool) :
        (PEqualNP.CircuitLowerBounds.Circuit.mk (pre ++ [g]) out).eval (List.ofFn x) =
        ((D.wires (List.ofFn x)) ++ [packet g.op g.inputs x]).getD out false := by
      change ((pre ++ [g]).foldl step (List.ofFn x)).getD out false = _
      rw [List.foldl_append]
      rfl
    have len (x : Fin 26 → Bool) : (D.wires (List.ofFn x)).length = 26+pre.length := by
      change (pre.foldl step (List.ofFn x)).length = _
      rw [length,List.length_ofFn]
    have lo : 63 ≤ D.size := by
      by_cases last : out = 26+pre.length
      · have same : (fun x => (PEqualNP.CircuitLowerBounds.Circuit.mk (pre ++ [g]) out).eval (List.ofFn x)) = packet g.op g.inputs := by
          funext x
          rw [run, last, ← len x,List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self]
          rfl
        rw [same] at cert
        have typ : g.op = .and ∨ g.op = .or := by simpa using hg.1
        rcases typ with e | e
        · exact and_end D g.inputs hd hg.2 (by rw [e] at cert; exact cert)
        · exact or_end D g.inputs hd hg.2 (by rw [e] at cert; exact cert)
      · have same : (fun x => (PEqualNP.CircuitLowerBounds.Circuit.mk (pre ++ [g]) out).eval (List.ofFn x)) = packet .or [out] := by
          funext x
          rw [run]
          change (_ ++ [_]).getD out false = ((D.wires (List.ofFn x)).getD out false || false)
          rw [Bool.or_false]
          by_cases short : out < 26+pre.length
          · exact List.getD_append _ _ _ _ (by rw [len];exact short)
          · rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_cons,List.length_nil,len];omega),
                List.getD_eq_default _ _ (by rw [len];omega)]
        rw [same] at cert
        exact or_end D [out] hd (by change 1 ≤ 2; decide) cert
    change 63 ≤ pre.length at lo
    change 64 ≤ (pre ++ [g]).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
