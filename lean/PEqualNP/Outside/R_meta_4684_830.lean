import PEqualNP.Defs

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4684_830
    (uniform : ∀ (C : PEqualNP.AndCount.AndCountCircuit 27) (bad : Fin 52 → Finset (Fin 27)) (test : Fin 4 → Finset (Fin 27)),
      (∀ e, C.eval (bad e) = false) → (∀ t, C.eval (test t) = true) →
      (∀ e f, e ≠ f → ∃ t, test t ⊆ bad e ∪ bad f) →
      (∀ i t, C.gateVal (test t) i = true) → 52 ≤ C.size+1)
    (active : ∀ (C : PEqualNP.AndCount.AndCountCircuit 27) (U : Finset (Fin 27)) (bad : Fin 19 → Finset (Fin 27)) (G : Finset (Fin C.size)),
      (∀ i, i ∈ G ↔ C.gateVal U i = true) → (∀ e, C.eval (bad e) = false) → C.eval U = true →
      (∀ e f, e ≠ f → U ⊆ bad e ∪ bad f) →
      19 ≤ G.card + 1)
    (mixed : ∀ (C : PEqualNP.AndCount.AndCountCircuit 27), C.WellFormed → C.size ≤ 50 →
    let row := fun (m : ℕ) (k : Fin 13) => Finset.univ.filter
      (fun i : Fin 27 => i.val = 0 ∨ m.testBit (((i.val-1)%13 + 13 - k.val)%13 + 13*((i.val-1)/13)) = false)
    let bad := fun e : Fin 52 => row (([8193,8194,8200,8704] : List ℕ).getD (e.val/13) 0) (Fin.ofNat 13 e.val)
    let reps : List ℕ := [61888,92576,162112,177472,192832,208132,308368,339076,408580,470020,555296,570640,601376,616736,670976,686336,701696,732416,801808,832528,932864,1079392,1194052,1210432,1325076,1456132,1603616,1849360,2172068,2241604,2274368,2405504,2434180,2503684,3289156,4532356]
    let chosen : List ℕ := [7405575,59244600,33916544,162112]
    (∀ e, C.eval (bad e) = false) →
    (∀ (j : Fin 36) k, C.eval (row (reps.getD j.val 0) k) = true) →
    (∃ (t : Fin 4) (G : Finset (Fin C.size)),
      (∀ i, i ∈ G ↔ C.gateVal (row (chosen.getD t.val 0) 0) i = true) ∧
      18 ≤ G.card ∧ G.card < C.size) → False) :
    ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x4, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ x7 ∈ x5, x6 = Fin.natAdd (13 : ℕ) x7);     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x5 x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x8 : Fin (26 : ℕ)) => !x4 x5 x6 x8) x7 = Bool.true};     have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x3 x8 x7};     (∀ (x7 x8 : Fin (13 : ℕ)), x3 x7 x8 → x1.eval (x5 {x7} {x8}) = Bool.false) → (∀ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ x11 ∈ x6 x8, x3 x9 x11) → (¬∃ (x10 : Fin (13 : ℕ)), ∀ x11 ∈ x8, x3 x11 x10) → (¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x6 x8, x3 x11 x12) → x1.eval (x5 x8 (x6 x8)) = Bool.true) → (51 : ℕ) ≤ x1.size := by
  intro C wf
  dsimp only
  intro neg pos
  let I := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let raw := fun (X Y : Finset (Fin 13)) (k : Fin 26) =>
    decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, k = Fin.natAdd 13 l)
  let mask := fun X Y => Finset.univ.filter (fun i : Fin 27 => Fin.cases true (fun k => !(raw X Y k)) i = true)
  let row := fun (m : ℕ) (k : Fin 13) => Finset.univ.filter
      (fun i : Fin 27 => i.val = 0 ∨ m.testBit (((i.val-1)%13 + 13 - k.val)%13 + 13*((i.val-1)/13)) = false)
  let bad := fun e : Fin 52 => row (([8193,8194,8200,8704] : List ℕ).getD (e.val/13) 0) (Fin.ofNat 13 e.val)
  let reps : List ℕ := [61888,92576,162112,177472,192832,208132,308368,339076,408580,470020,555296,570640,601376,616736,670976,686336,701696,732416,801808,832528,932864,1079392,1194052,1210432,1325076,1456132,1603616,1849360,2172068,2241604,2274368,2405504,2434180,2503684,3289156,4532356]
  let chosen : List ℕ := [7405575,59244600,33916544,162112]
  let test := fun t : Fin 4 => row (chosen.getD t.val 0) 0
  let X := fun (m : ℕ) (k : Fin 13) => Finset.univ.filter (fun p : Fin 13 => m.testBit ((p.val+13-k.val)%13) = true)
  let Y := fun (m : ℕ) (k : Fin 13) => Finset.univ.filter (fun l : Fin 13 => m.testBit ((l.val+13-k.val)%13 + 13) = true)
  let valid := fun (m : ℕ) (k : Fin 13) =>
    (Y m k = Finset.univ.filter (fun l => ∀ p ∈ X m k, ¬ I p l)) ∧
    (∀ p ∉ X m k, ∃ l ∈ Y m k, I p l) ∧
    (¬∃ l, ∀ p ∈ X m k, I p l) ∧ (¬∃ p, ∀ l ∈ Y m k, I p l) ∧
    mask (X m k) (Y m k) = row m k
  have positiveRows : ∀ (j : Fin 36) (k : Fin 13), valid (reps.getD j.val 0) k := by
    intro j
    fin_cases j <;> decide +kernel
  let pnt := fun e : Fin 52 => ((Fin.ofNat 13 e.val) : Fin 13) +
      (([0,1,3,9] : List (Fin 13)).getD (e.val/13) 0)
  let lin := fun e : Fin 52 => ((Fin.ofNat 13 e.val) : Fin 13)
  have negatives : ∀ e : Fin 52, I (pnt e) (lin e) ∧ mask {pnt e} {lin e} = bad e := by decide +kernel
  have selected : ∀ t : Fin 4, valid (chosen.getD t.val 0) 0 := by decide +kernel
  have pair : ∀ e f : Fin 52, e ≠ f → ∃ t : Fin 4, test t ⊆ bad e ∪ bad f := by decide +kernel
  let ids : List (List ℕ) := [[3,16,48,29,7,8,9,22,34,35,0,1,2,43,44,45,36,37,25],[25,37,38,6,19,51,32,10,11,12,26,27,15,3,4,5,46,47,48],[25,44,2,3,16,5,18,31,41,12,39,40,30,19,7,21,9,10,50],[0,1,14,26,4,17,30,39,40,41,29,18,6,20,8,35,23,11,12]]
  let choose := fun (t : Fin 4) (j : Fin 19) => (⟨((ids.getD t.val []).getD j.val 0)%52,Nat.mod_lt _ (by decide)⟩ : Fin 52)
  have pivots : ∀ (t : Fin 4) (i j : Fin 19), i ≠ j → test t ⊆ bad (choose t i) ∪ bad (choose t j) := by decide +kernel
  have off (e : Fin 52) : C.eval (bad e) = false := by
    obtain ⟨inc,h⟩ := negatives e
    simpa only [← h] using neg (pnt e) (lin e) inc
  have good (m : ℕ) (k : Fin 13) (h : valid m k) : C.eval (row m k) = true := by
    obtain ⟨hm,hc,hl,hp,heq⟩ := h
    rw [← heq]
    rw [hm] at hc hp ⊢
    exact pos (X m k) hc hl hp
  have yes (t : Fin 4) : C.eval (test t) = true := good _ _ (selected t)
  by_contra lower
  have small : C.size ≤ 50 := by omega
  by_cases all : ∀ (i : Fin C.size) t, C.gateVal (test t) i = true
  · have bound := uniform C bad test off yes pair all
    omega
  · apply mixed C wf small off (fun j k => good _ _ (positiveRows j k))
    push Not at all
    obtain ⟨i,t,failed⟩ := all
    let G := Finset.univ.filter (fun j => C.gateVal (test t) j = true)
    have absent : i ∉ G := by simpa [G] using failed
    have sub : G ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun eq => absent (eq ▸ hj),Finset.mem_univ _⟩
    have strict : G.card < C.size := by
      have h := Finset.card_le_card sub
      have h' := Finset.card_erase_add_one (Finset.mem_univ i)
      simp only [Finset.card_univ,Fintype.card_fin] at h'
      omega
    have memG (j : Fin C.size) : j ∈ G ↔ C.gateVal (test t) j = true := by simp [G]
    have counted := active C (test t) (fun j => bad (choose t j)) G memG (fun j => off _) (yes t) (pivots t)
    refine ⟨t,G,memG,?_,strict⟩
    omega
