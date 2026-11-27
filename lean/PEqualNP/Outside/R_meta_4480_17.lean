import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Pin every input outside the surviving edges low and test the largest remaining input.
-- A gate reading a false wire there has a fixed operand throughout that restriction.
-- The cover construction also suffices whenever the original circuit costs at
-- least as much. The remaining least circuits beat every cover and expose few gates.
set_option maxHeartbeats 1400000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_4480_17
    (compress : ∀ (n : ℕ) (C : Circuit) (keep : Fin n → Bool),
      let off (x : Fin n → Bool) (i : Fin n) := keep i && x i
      let w := C.wires (List.ofFn keep)
      IsAO2 n C → (∃ x y, circuitFun n C (off x) ≠ circuitFun n C (off y)) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size +
        C.gates.countP (fun g => g.inputs.any fun i => !(w.getD i false)) ≤ C.size ∧
        ∀ x, circuitFun n D x = circuitFun n C (off x))
    (build : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e∈E, e.1∈A ∨ e.2∈B) → ∃ D : Circuit, IsAO2 (n+m) D ∧
        D.size≤E.card+A.card+B.card-1 ∧ ∀ x, circuitFun (n+m) D x =
          decide (∃ e∈E, x (e.1.castAdd m)=true ∧ x (Fin.natAdd n e.2)=true))
    (sparse : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      let touches (v : Fin (n+m)) (e : Fin n × Fin m) := e.1.castAdd m=v ∨ Fin.natAdd n e.2=v
      let degree (v : Fin (n+m)) := (E.filter (touches v)).card
      let fits (S : Finset (Fin n × Fin m)) (D : Circuit) := IsAO2 (n+m) D ∧
        ∀ x, circuitFun (n+m) D x = decide (∃ e∈S, x (e.1.castAdd m)=true ∧ x (Fin.natAdd n e.2)=true)
      (∀ a b c d, a≠b → c≠d → ¬((a,c)∈E ∧ (a,d)∈E ∧ (b,c)∈E ∧ (b,d)∈E)) →
      fits E C → (∀ D, fits E D → C.size≤D.size) → (∃ v, degree v=1) →
      (∀ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e∈E, e.1∈A ∨ e.2∈B) → C.size+1<E.card+A.card+B.card) →
      (∀ v, 0<degree v → degree v<E.card ∧
        let w := C.wires (List.ofFn fun i => decide (∃ e∈E, ¬touches v e ∧ touches i e))
        C.gates.countP (fun g => g.inputs.any fun i => !(w.getD i false)) ≤ degree v) →
      ∃ v, 0<degree v ∧ ∃ D, fits (E.filter fun e => ¬touches v e) D ∧
        D.size+degree v+1≤C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →     x6 x3 x4 →       (∃ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card = (1 : ℕ)) →         ∃ (x10 : Fin (x1 + x2)),           have x11 : Finset (Fin x1 × Fin x2) := {x11 ∈ x3 | ¬x5 x10 x11};           x11.card < x3.card ∧ (x11 = ∅ ∨ ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), x6 x11 x12 ∧ x12.size + (x3.card - x11.card) + (1 : ℕ) ≤ x4.size) := by
  classical
  intro n m E C
  let touches (v : Fin (n+m)) (e : Fin n × Fin m) := e.1.castAdd m=v ∨ Fin.natAdd n e.2=v
  let degree (v : Fin (n+m)) := (E.filter (touches v)).card
  let erase (v : Fin (n+m)) := E.filter fun e => ¬touches v e
  let value (S : Finset (Fin n × Fin m)) (x : Fin (n+m) → Bool) :=
    decide (∃ e∈S, x (e.1.castAdd m)=true ∧ x (Fin.natAdd n e.2)=true)
  let fits (S : Finset (Fin n × Fin m)) (D : Circuit) :=
    IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x=value S x
  change (∀ a b c d, a≠b → c≠d → ¬((a,c)∈E ∧ (a,d)∈E ∧ (b,c)∈E ∧ (b,d)∈E)) →
    fits E C → (∃ v, degree v=1) → ∃ v, (erase v).card<E.card ∧
    (erase v=∅ ∨ ∃ D, fits (erase v) D ∧ D.size+(E.card-(erase v).card)+1≤C.size)
  intro square original leaf
  have totals (v) : degree v + (erase v).card = E.card := E.card_filter_add_card_filter_not (touches v)
  let P (s : ℕ) := ∃ D, fits E D ∧ D.size=s
  have has : ∃ s, P s := ⟨C.size,C,original,rfl⟩
  obtain ⟨A,ao,sz⟩ := Nat.find_spec has
  have least (D : Circuit) (h : fits E D) : A.size≤D.size := by
    rw [sz]
    exact Nat.find_min' has ⟨D,h,rfl⟩
  have budget := least C original
  by_cases cheap : ∀ (S : Finset (Fin n)) (T : Finset (Fin m)),
      (∀ e∈E, e.1∈S ∨ e.2∈T) → A.size+1<E.card+S.card+T.card
  swap
  · push Not at cheap
    obtain ⟨S,T,cover,large⟩ := cheap
    obtain ⟨u,hu⟩ := leaf
    have total := totals u
    obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<E.card by omega)
    have remove (v : Fin (n+m)) (atv : touches v e) (S' : Finset (Fin n)) (T' : Finset (Fin m))
        (smaller : S'.card+T'.card+1=S.card+T.card)
        (remaining : ∀ q∈erase v, q.1∈S' ∨ q.2∈T') :
        (erase v).card<E.card ∧ (erase v=∅ ∨ ∃ D, fits (erase v) D ∧ D.size+(E.card-(erase v).card)+1≤C.size) := by
      have dpos : 0<degree v := Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,atv⟩⟩
      have sum := totals v
      refine ⟨by omega,?_⟩
      by_cases empty : erase v=∅
      · exact Or.inl empty
      have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      obtain ⟨D,allowed,size,eval⟩ := build _ _ (erase v) S' T' remaining
      exact Or.inr ⟨D,⟨allowed,eval⟩,by omega⟩
    rcases cover e he with left|right
    · refine ⟨_,remove (e.1.castAdd m) (Or.inl rfl) (S.erase e.1) T ?_ ?_⟩
      · have := Finset.card_pos.mpr ⟨e.1,left⟩
        rw [Finset.card_erase_of_mem left]; omega
      intro q hq
      obtain ⟨mem,disjoint⟩ := Finset.mem_filter.mp hq
      exact (cover q mem).imp_left fun a => Finset.mem_erase.mpr ⟨fun eq => disjoint (Or.inl (congrArg (Fin.castAdd m) eq)),a⟩
    · refine ⟨_,remove (Fin.natAdd n e.2) (Or.inr rfl) S (T.erase e.2) ?_ ?_⟩
      · have := Finset.card_pos.mpr ⟨e.2,right⟩
        rw [Finset.card_erase_of_mem right]; omega
      intro q hq
      obtain ⟨mem,disjoint⟩ := Finset.mem_filter.mp hq
      exact (cover q mem).imp_right fun b => Finset.mem_erase.mpr ⟨fun eq => disjoint (Or.inr (congrArg (Fin.natAdd n) eq)),b⟩
  let keep (v i : Fin (n+m)) := decide (∃ e∈E, ¬touches v e ∧ touches i e)
  let off (v : Fin (n+m)) (x : Fin (n+m) → Bool) (i : Fin (n+m)) := keep v i && x i
  let upper (v : Fin (n+m)) := A.wires (List.ofFn (keep v))
  let cost (v : Fin (n+m)) := A.gates.countP (fun g => g.inputs.any fun i => !((upper v).getD i false))
  have cof (v) (x) : value E (off v x)=value (erase v) x := by
    apply Bool.eq_iff_iff.mpr
    simp only [value,decide_eq_true_eq]
    constructor
    · rintro ⟨e,he,ha,hb⟩
      have zero : keep v v=false := by simp [keep]
      have a : e.1.castAdd m ≠ v := by rintro eq; simp [off,eq,zero] at ha
      have b : Fin.natAdd n e.2 ≠ v := by rintro eq; simp [off,eq,zero] at hb
      exact ⟨e,Finset.mem_filter.mpr ⟨he,not_or.mpr ⟨a,b⟩⟩,(Bool.and_eq_true_iff.mp ha).2,(Bool.and_eq_true_iff.mp hb).2⟩
    · rintro ⟨e,he,ha,hb⟩
      obtain ⟨mem,no⟩ := Finset.mem_filter.mp he
      have left : keep v (e.1.castAdd m)=true := decide_eq_true ⟨e,mem,no,Or.inl rfl⟩
      have right : keep v (Fin.natAdd n e.2)=true := decide_eq_true ⟨e,mem,no,Or.inr rfl⟩
      exact ⟨e,mem,by simp [off,left,ha],by simp [off,right,hb]⟩
  by_cases reg : ∀ v, 0<degree v → degree v<E.card ∧ cost v≤degree v
  · obtain ⟨v,positive,D,valid,small⟩ := sparse n m E A square ao least leaf cheap reg
    change 0<degree v at positive
    change D.size+degree v+1≤A.size at small
    have hd := totals v
    exact ⟨v,by omega,Or.inr ⟨D,valid,by omega⟩⟩
  · push Not at reg
    obtain ⟨v,positive,fails⟩ := reg
    have hd := totals v
    refine ⟨v,by omega,?_⟩
    by_cases void : erase v=∅
    · exact Or.inl void
    have nonempty := Finset.nonempty_iff_ne_empty.mpr void
    have count := Finset.card_pos.mpr nonempty
    have bound : degree v+1≤cost v := fails (by omega)
    obtain ⟨e,he⟩ := nonempty
    have nc : ∃ x y, circuitFun (n+m) A (off v x) ≠ circuitFun (n+m) A (off v y) := by
      refine ⟨fun _ => true,fun _ => false,?_⟩
      have yes : value (erase v) (fun _ => true)=true := decide_eq_true ⟨e,he,rfl,rfl⟩
      have zero : value (erase v) (fun _ => false)=false := by simp [value]
      have hi := ((ao.2 _).trans (cof v (fun _ => true))).trans yes
      have lo := ((ao.2 _).trans (cof v (fun _ => false))).trans zero
      intro eq
      rw [hi,lo] at eq
      contradiction
    obtain ⟨D,allowed,small,eq⟩ := compress (n+m) A (keep v) ao.1 nc
    change D.size+cost v≤A.size at small
    exact Or.inr ⟨D,⟨allowed,fun x => (eq x).trans ((ao.2 _).trans (cof v x))⟩,by omega⟩
