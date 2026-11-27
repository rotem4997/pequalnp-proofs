import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxRecDepth 40000 in
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxSize 2048 in
theorem PEqualNP.Outside.R_meta_7692_672
    (table : ∃ (C : Circuit) (u v : ℕ),
      C.size ≤ 24 ∧ TopForm.IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ g ∈ C.gates, 2 ∉ g.inputs) ∧ u < 14+C.size ∧ v < 14+C.size ∧
      u ≠ 2 ∧ v ≠ 2 ∧ u ≠ v ∧
      let w := fun (m r : ℕ) => BlindGate.wireValue C 14 (fun i => m.testBit i.val) r
      (∀ m ∈ ([129,130,136,258,272,520,544,1032,1040,1088,2049,2064,2080,4098,4128,4160,8193,8256] : List ℕ), w m u = true) ∧
      (∀ m ∈ ([123,240,361,480,595,720,833,1059,1313,1539,2122,2376,2626,3008,4121,4361,4625,5889,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256] : List ℕ), w m u = false) ∧
      (∀ m ∈ ([256,512,8192] : List ℕ), w m v = true) ∧
      (∀ m ∈ ([123,240,1059,1184,2122,2240,3074,4121,4240,5121,6152,7296] : List ℕ), w m v = false))
    (transfer : ∀ (C : Circuit), TopForm.IsAO2 14 C →
      (∀ g ∈ C.gates, 2 ∉ g.inputs) → ∀ (r : ℕ), r ≠ 2 → ∀ (a b : Fin 14 → Bool),
      (∀ i, i ≠ 2 → a i = true → b i = true) →
      BlindGate.wireValue C 14 a r = true → BlindGate.wireValue C 14 b r = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),   x1.size ≤ (24 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧         x2 < (14 : ℕ) + x1.size ∧           x3 < (14 : ℕ) + x1.size ∧             x2 ≠ (2 : ℕ) ∧               x2 ≠ x3 ∧                 ∀ (x4 : Fin (14 : ℕ) → Bool),                   have x5 : ℕ → Bool := PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4;                   (x5 x2 || x5 (2 : ℕ) && x5 x3) = Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧ ∀ x6 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))], (x4 = fun (x8 : Fin (14 : ℕ)) => Decidable.decide (x8 = x6)) → x5 (2 : ℕ) = Bool.false ∧ x5 x3 = Bool.false := by
  let E := fun p l : Fin 7 => p = l ∨ p = l+1 ∨ p = l+3
  let P : List ℕ := [129,130,136,258,272,520,544,1032,1040,1088,2049,2064,2080,4098,4128,4160,8193,8256]
  let Z : List ℕ := [123,240,361,480,595,720,833,1059,1313,1539,2122,2376,2626,3008,4121,4361,4625,5889,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256]
  let B : List ℕ := [256,512,8192]
  let T : List ℕ := [123,240,1059,1184,2122,2240,3074,4121,4240,5121,6152,7296]
  let row := fun (m : ℕ) (i : Fin 14) => m.testBit i.val
  have edgeRows : ∀ p l : Fin 7, p ≠ 2 → E p l → ∃ m ∈ P,
      ∀ i, row m i = true → i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := by decide +kernel
  have lineRows : ∀ l : Fin 7, E 2 l → ∃ m ∈ B,
      ∀ i, row m i = true → i = Fin.natAdd 7 l := by decide +kernel
  have boxes : ∀ (t : Bool) (a : Fin 7 → Bool), ∃ m ∈ (if t then T else Z),
      (∀ p : Fin 7, p ≠ 2 → a p = true → row m (Fin.castAdd 7 p) = true) ∧
      (∀ l : Fin 7, (∀ p : Fin 7, p ≠ 2 → E p l → a p = false) →
        (t = true → ¬ E 2 l) → row m (Fin.natAdd 7 l) = true) := by
    intro t
    cases t <;> simp <;> decide +kernel
  have singles : ∀ i ∈ ([0,7] : List (Fin 14)), (2 : Fin 14) ≠ i ∧
      ∃ m ∈ T, row m i = true := by decide +kernel
  obtain ⟨C,u,v,hs,ao,nd,skip,hu,hv,hu2,hv2,huv,hP,hZ,hB,hT⟩ := table
  let w := BlindGate.wireValue C 14
  have keep (gs : List Gate) (z : List Bool) (hz : 2 < z.length) :
      ((Circuit.mk gs 0).wires z).getD 2 false = z.getD 2 false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      let zs := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
      change ((Circuit.mk gs 0).wires zs).getD 2 false = z.getD 2 false
      rw [ih zs (by simp [zs]; omega)]
      exact List.getD_append _ _ _ _ hz
  have raw (x : Fin 14 → Bool) : w x 2 = x 2 := by
    change ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD 2 false = x 2
    rw [keep _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have zero (t : Bool) (x : Fin 14 → Bool)
      (h0 : ∀ p l : Fin 7, p ≠ 2 → E p l → x (Fin.natAdd 7 l) = true → x (Fin.castAdd 7 p) = false)
      (h1 : t = true → ∀ l : Fin 7, E 2 l → x (Fin.natAdd 7 l) = false) :
      w x (if t then v else u) = false := by
    obtain ⟨m,hm,mp,ml⟩ := boxes t (fun p => x (Fin.castAdd 7 p))
    have le : ∀ i : Fin 14, i ≠ 2 → x i = true → row m i = true := by
      intro i hi hx
      by_cases hl : i.val < 7
      · let p : Fin 7 := ⟨i.val,hl⟩
        have eq : Fin.castAdd 7 p = i := Fin.ext rfl
        rw [←eq] at hi hx ⊢
        exact mp p (fun h => hi (by rw [h]; rfl)) hx
      · let l : Fin 7 := ⟨i.val-7,by omega⟩
        have eq : Fin.natAdd 7 l = i := Fin.ext (by simp [l]; omega)
        rw [←eq] at hx ⊢
        exact ml l (fun p hp he => h0 p l hp he hx)
          (fun ht he => Bool.noConfusion (hx.symm.trans (h1 ht l he)))
    have rn : (if t then v else u) ≠ 2 := by cases t <;> assumption
    have bad : w (row m) (if t then v else u) = false := by
      cases t
      · exact hZ m hm
      · exact hT m hm
    cases ev : w x (if t then v else u) with
    | false => rfl
    | true => exact Bool.noConfusion ((transfer C ao skip _ rn x (row m) le ev).symm.trans bad)
  refine ⟨C,u,v,hs,ao,nd,hu,hv,hu2,huv,?_⟩
  intro x
  change (w x u || w x 2 && w x v) =
    decide (∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ _
  constructor
  · by_cases he : ∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
    · rw [decide_eq_true he, Bool.or_eq_true]
      obtain ⟨p,l,ep,xp,xl⟩ := he
      by_cases eq : p = 2
      · subst p
        obtain ⟨m,hm,small⟩ := lineRows l ep
        apply Or.inr
        rw [Bool.and_eq_true,raw]
        refine ⟨xp,transfer C ao skip v hv2 (row m) x ?_ (hB m hm)⟩
        intro i _ hi
        simpa only [small i hi] using xl
      · obtain ⟨m,hm,small⟩ := edgeRows p l eq ep
        apply Or.inl
        apply transfer C ao skip u hu2 (row m) x _ (hP m hm)
        intro i _ hi
        rcases small i hi with rfl | rfl
        · exact xp
        · exact xl
    · rw [decide_eq_false he,raw]
      have noP (p l : Fin 7) (_ : p ≠ 2) (hp : E p l) (xl : x (Fin.natAdd 7 l) = true) :
          x (Fin.castAdd 7 p) = false := by
        cases xp : x (Fin.castAdd 7 p) with
        | false => rfl
        | true => exact False.elim (he ⟨p,l,hp,xp,xl⟩)
      have zu : w x u = false := zero false x noP (by simp)
      rw [zu]
      cases xp : x 2 with
      | false => rfl
      | true =>
        have zv : w x v = false := zero true x noP (by
          intro _ l hp
          cases xl : x (Fin.natAdd 7 l) with
          | false => rfl
          | true => exact False.elim (he ⟨2,l,hp,xp,xl⟩))
        rw [zv]
        rfl
  · intro i hi hx
    obtain ⟨hne,m,hm,on⟩ := singles i hi
    change w x 2 = false ∧ w x v = false
    refine ⟨by rw [raw,hx]; simpa using hne,?_⟩
    cases ev : w x v with
    | false => rfl
    | true =>
      have le : ∀ k : Fin 14, k ≠ 2 → x k = true → row m k = true := by
        intro k _ hk
        rw [hx] at hk
        obtain rfl : k = i := of_decide_eq_true hk
        exact on
      exact Bool.noConfusion ((transfer C ao skip v hv2 x (row m) le ev).symm.trans (hT m hm))
