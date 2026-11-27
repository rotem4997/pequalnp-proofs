import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2602_415
    (hguard : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∀ b t : Fin n → Bool, (∀ i, b i=true → t i=true) →
      let v := fun (z : Fin n → Bool) (k : ℕ) => (C.wires (List.ofFn z)).getD k false
      (∀ i : Fin n, v t i.val=t i) ∧ ∀ j g i, C.gates[j]?=some g → i∈g.inputs → v t (n+j)=false →
        (g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ k∈g.inputs, k≠i → v b k=true) → v t i=false)
    (hface : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), 63≤C.size → C.size≤64 →
      PEqualNP.TopForm.IsAO2 26 C → (∀ g∈C.gates, g.inputs.Nodup) →
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z)=true ↔ ∃ p l : Fin 13,
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ z (Fin.castAdd 13 p)=true ∧ z (Fin.natAdd 13 l)=true) →
      let w := fun (m k : ℕ) => (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
      ∃ b∈([0,13] : List ℕ), let u := if b=0 then 25034751 else 67108341
      let x := if b=0 then 8191 else 67100672
      let y := if b=0 then 25018369 else 15860
      ∀ S : Set ℕ, C.output∈S → (∀ i : Fin 26, i.val∈S → u.testBit i.val=false) →
        ¬∀ j g, C.gates[j]?=some g → 26+j∈S →
          (g.op=PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i∈g.inputs,i∈S) ∧
          (g.op=PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i∈g.inputs,i∈S) ∨
            ((∀ i∈g.inputs, w (2^b) i=false) ∧ w x (26+j)=false ∧ w y (26+j)=false))) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  rintro ⟨C,lo,hi,wf,spec,dl,dp⟩
  have get (j : ℕ) (h : j<C.gates.length) := List.getElem?_eq_getElem (l:=C.gates) h
  have model : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg; obtain ⟨j,h,rfl⟩ := List.getElem_of_mem hg; exact (wf j _ (get j h)).1
    · intro j hj i mem; obtain ⟨a,b,ins,_,ha,hb⟩ := (wf j _ (get j hj)).2
      change i∈(C.gates.getD j ⟨.or,[]⟩).inputs at mem
      rw [List.getD_eq_getElem _ _ hj,ins] at mem; rcases List.mem_cons.mp mem with rfl|h; exact ha; exact (List.mem_singleton.mp h) ▸ hb
    · intro g hg; obtain ⟨j,h,rfl⟩ := List.getElem_of_mem hg; obtain ⟨a,b,ins,_⟩ := (wf j _ (get j h)).2; simp [ins]
  have nodup : ∀ g∈C.gates, g.inputs.Nodup := by
    intro g hg; obtain ⟨j,h,rfl⟩ := List.getElem_of_mem hg; obtain ⟨a,b,ins,ne,_⟩ := (wf j _ (get j h)).2; simp [ins,ne]
  obtain ⟨b,bb,test⟩ := hface C lo hi model nodup spec
  let u : ℕ := if b=0 then 25034751 else 67108341
  let x : ℕ := if b=0 then 8191 else 67100672
  let y : ℕ := if b=0 then 25018369 else 15860
  let row (m : ℕ) := fun i : Fin 26 => m.testBit i.val
  let w (m k : ℕ) := (C.wires (List.ofFn (row m))).getD k false
  have side : b=0 ∨ b=13 := by simpa using bb
  have seedbit : (fun i : Fin 26 => decide (i.val=b))=row (2^b) := by funext i; rcases side with rfl|rfl <;> revert i <;> decide
  have geom : (∀ i : Fin 26, (2^b : ℕ).testBit i.val=true → x.testBit i.val=true ∧ y.testBit i.val=true) ∧
      (∀ i : Fin 26, x.testBit i.val=false → y.testBit i.val=false → i.val≠13-b → u.testBit i.val=false) ∧
      ∀ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) →
        ¬(row x (Fin.castAdd 13 p)=true ∧ row x (Fin.natAdd 13 l)=true) ∧ ¬(row y (Fin.castAdd 13 p)=true ∧ row y (Fin.natAdd 13 l)=true) := by
    rcases side with rfl|rfl <;> decide
  have gx := hguard 26 C model (row (2^b)) (row x) (fun i h => (geom.1 i h).1)
  have gy := hguard 26 C model (row (2^b)) (row y) (fun i h => (geom.1 i h).2)
  have dead : w x C.output=false ∧ w y C.output=false := by
    constructor <;> apply Bool.eq_false_iff.mpr
    · intro h; obtain ⟨p,l,e,a,c⟩ := (spec _).1 h; exact (geom.2.2 p l e).1 ⟨a,c⟩
    · intro h; obtain ⟨p,l,e,a,c⟩ := (spec _).1 h; exact (geom.2.2 p l e).2 ⟨a,c⟩
  have tr : ∃ d : ℕ → Bool, (∀ i<26,d i=decide (i=13-b)) ∧ (∀ j (g : PEqualNP.CircuitLowerBounds.Gate) a c, C.gates[j]?=some g → g.inputs=[a,c] →
      (g.op=PEqualNP.CircuitLowerBounds.GateOp.and → d (26+j)=(w (2^b) a && d c || d a && w (2^b) c)) ∧
      (g.op=PEqualNP.CircuitLowerBounds.GateOp.or → d (26+j)=(d a || d c))) ∧ d C.output=false := by
    dsimp only [w]; rw [←seedbit]; rcases side with rfl|rfl; exact dl; exact dp
  obtain ⟨d,init,step,final⟩ := tr
  let S : Set ℕ := {i | w x i=false ∧ w y i=false ∧ d i=false}
  apply test S ⟨dead.1,dead.2,final⟩
  · intro i h; obtain ⟨a,c,e⟩ := h; apply geom.2.1 i
    · exact (gx.1 i).symm.trans a
    · exact (gy.1 i).symm.trans c
    · rw [init i.val i.isLt] at e; exact of_decide_eq_false e
  · intro j g hit out; obtain ⟨hx,hy,hd⟩ := out; obtain ⟨a,c,ins,ne,_,_⟩ := (wf j g hit).2; have st := step j g a c hit ins
    have ac : a∈g.inputs := by simp [ins]
    have cc : c∈g.inputs := by simp [ins]
    have go (i) (mem : i∈g.inputs) (edge : g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ k∈g.inputs,k≠i → w (2^b) k=true) (dz : d i=false) : i∈S := ⟨gx.2 j g i hit mem hx edge,gy.2 j g i hit mem hy edge,dz⟩
    constructor
    · intro tag i mem; rw [st.2 tag] at hd; have z := Bool.or_eq_false_iff.mp hd; rw [ins] at mem; rcases List.mem_cons.mp mem with rfl|h
      · exact go _ ac (Or.inl tag) z.1
      · have e := List.mem_singleton.mp h; exact e ▸ go _ cc (Or.inl tag) z.2
    · intro tag; rw [st.1 tag] at hd
      by_cases pa : w (2^b) a=true
      · left; refine ⟨c,cc,go c cc (Or.inr ?_) ?_⟩
        · intro k h nc; rw [ins] at h; rcases List.mem_cons.mp h with rfl|h; exact pa; exact (nc (List.mem_singleton.mp h)).elim
        · cases z : d c; rfl; simp only [pa,z,Bool.true_and,Bool.true_or,Bool.true_eq_false] at hd
      by_cases pc : w (2^b) c=true
      · left; refine ⟨a,ac,go a ac (Or.inr ?_) ?_⟩
        · intro k h nc; rw [ins] at h; rcases List.mem_cons.mp h with rfl|h; exact (nc rfl).elim; exact (List.mem_singleton.mp h) ▸ pc
        · cases z : d a; rfl; simp only [pc,z,Bool.true_and,Bool.and_true,Bool.or_true,Bool.true_eq_false] at hd
      · right; refine ⟨?_,hx,hy⟩; intro k h; rw [ins] at h; rcases List.mem_cons.mp h with rfl|h; exact Bool.eq_false_iff.mpr pa; exact (List.mem_singleton.mp h) ▸ Bool.eq_false_iff.mpr pc
