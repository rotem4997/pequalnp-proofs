import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2619_215
    (search :
      let P := fun x : Fin 26 → Bool =>
        let p := fun i : Fin 13 => x (Fin.castAdd 13 i)
        ∃ j : Fin 13, x (Fin.natAdd 13 j) = true ∧
          (p j || p (j+1) || p (j+3) || p (j+9)) = true
      ∃ (D : Circuit) (a b : ℕ), D.size ≤ 63 ∧ IsAO2 26 D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ a ≠ b ∧
        50 ≤ a ∧ a < 26+D.size ∧ b < 26+D.size ∧
        let read := fun (w : ℕ) (x : Fin 26 → Bool) => (D.wires (List.ofFn x)).getD w false
        let yes := fun x => read a x && read b x
        read a (fun i => decide (i.val = 2)) = true ∧
        read b (fun i => decide (i.val = 15)) = true ∧
        (∀ x, Minimal P x → yes x = true) ∧
        (∀ x, Maximal (fun y => ¬ P y) x → yes x = false))
    (extend : ∀ (n : ℕ) (D : Circuit) (a b : ℕ),
      IsAO2 n D → a < n+D.size → b < n+D.size →
      let C : Circuit := ⟨D.gates ++ [⟨.and,[a,b]⟩], n+D.size⟩
      IsAO2 n C ∧ ∀ x : Fin n → Bool,
        let W := D.wires (List.ofFn x)
        let V := C.wires (List.ofFn x)
        C.eval (List.ofFn x) = (W.getD a false && W.getD b false) ∧
        V.getD a false = W.getD a false ∧ V.getD b false = W.getD b false)
    (ordered : ∀ (n : ℕ) (D : Circuit), IsAO2 n D → ∀ w : ℕ,
      Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  let P := fun x : Fin 26 → Bool =>
    let p := fun i : Fin 13 => x (Fin.castAdd 13 i)
    ∃ j : Fin 13, x (Fin.natAdd 13 j) = true ∧
      (p j || p (j+1) || p (j+3) || p (j+9)) = true
  obtain ⟨D,a,b,hs,hm,hd,hab,_,ha,hb,hotA,hotB,pos,neg⟩ := search
  let rd := fun (w : ℕ) (x : Fin 26 → Bool) => (D.wires (List.ofFn x)).getD w false
  let yes := fun x => rd a x && rd b x
  change ∀ x, Minimal P x → yes x = true at pos
  change ∀ x, Maximal (fun y => ¬ P y) x → yes x = false at neg
  have up (w : ℕ) : Monotone (rd w) := ordered 26 D hm w
  have supYes {x y : Fin 26 → Bool} (le : x ≤ y) (h : yes x = true) : yes y = true := by
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr
      ⟨(Bool.le_iff_imp.mp (up a le)) h1,(Bool.le_iff_imp.mp (up b le)) h2⟩
  have correct (x : Fin 26 → Bool) : yes x = true ↔ P x := by
    constructor
    · intro hx
      by_contra h
      obtain ⟨z,hz,hn⟩ := Finite.exists_le_maximal (p := fun y => ¬ P y) h
      have hyes := supYes hz hx
      rw [neg z hn] at hyes
      contradiction
    · intro h
      obtain ⟨z,hz,hp⟩ := Finite.exists_le_minimal (p := P) h
      exact supYes hz (pos z hp)
  let atom := fun (j : ℕ) (i : Fin 26) => decide (i.val = j)
  let mark := fun s : Bool => atom (if s = true then 13 else 0)
  have bad : ∀ s : Bool, ¬ P (atom 2 ⊔ mark s) ∧ ¬ P (atom 15 ⊔ mark s) := by
    dsimp only [P,atom,mark]
    decide
  change rd a (atom 2) = true at hotA
  change rd b (atom 15) = true at hotB
  have cold (s : Bool) : rd a (mark s) = false ∧ rd b (mark s) = false := by
    constructor
    · apply Bool.eq_false_iff.mpr
      intro hot
      apply (bad s).2
      apply (correct _).mp
      exact Bool.and_eq_true_iff.mpr
        ⟨(Bool.le_iff_imp.mp (up a (le_sup_right : mark s ≤ atom 15 ⊔ mark s))) hot,
          (Bool.le_iff_imp.mp (up b (le_sup_left : atom 15 ≤ atom 15 ⊔ mark s))) hotB⟩
    · apply Bool.eq_false_iff.mpr
      intro hot
      apply (bad s).1
      apply (correct _).mp
      exact Bool.and_eq_true_iff.mpr
        ⟨(Bool.le_iff_imp.mp (up a (le_sup_left : atom 2 ≤ atom 2 ⊔ mark s))) hotA,
          (Bool.le_iff_imp.mp (up b (le_sup_right : mark s ≤ atom 2 ⊔ mark s))) hot⟩
  let C : Circuit := ⟨D.gates ++ [⟨.and,[a,b]⟩], 26+D.size⟩
  obtain ⟨hc,hval⟩ := extend 26 D a b hm ha hb
  refine ⟨C,?_,hc,?_,?_,?_⟩
  · have bound : D.gates.length + 1 ≤ 64 := by change D.gates.length ≤ 63 at hs; omega
    change (D.gates ++ [Gate.mk GateOp.and [a,b]]).length ≤ 64
    simpa only [List.length_append,List.length_cons,List.length_nil] using bound
  · intro g hg
    change g ∈ D.gates ++ [⟨.and,[a,b]⟩] at hg
    obtain h | h := List.mem_append.mp hg
    · exact hd _ h
    · obtain rfl := List.mem_singleton.mp h
      simpa using hab
  · intro p l
    let x : Fin (13+13) → Bool := fun i =>
      Fin.addCases (motive := fun _ => Bool) p l i
    change C.eval (List.ofFn x) = true ↔ _
    rw [(hval x).1]
    exact (correct x).trans (by simp only [P,x,Fin.addCases_left,Fin.addCases_right])
  · refine ⟨D.size,a,b,rfl,?_,?_⟩
    · change (D.gates ++ [Gate.mk GateOp.and [a,b]])[D.gates.length]? = _
      simp [List.getElem?_append]
    · intro s
      obtain ⟨_,ea,eb⟩ := hval (mark s)
      exact ⟨ea.trans (cold s).1,eb.trans (cold s).2⟩
