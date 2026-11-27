import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- Child one asks for two outputs of a single circuit. Child two constructs
-- directional traces at a dark AND gate for any normalized circuit.
theorem PEqualNP.Outside.R_meta_1479_824 :
(∃ C : Circuit, C.size≤24 ∧ (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) ∧
    ∃ h n : Nat, h<14+C.size ∧ n<14+C.size ∧ ∀ x : Fin 14 → Bool,
      ((C.wires (List.ofFn x)).getD h false = true ↔ ∃ u t : Fin 7,
        u≠0 ∧ (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u)=true ∧ x (Fin.natAdd 7 t)=true) ∧
      ((C.wires (List.ofFn x)).getD n false = true ↔ ∃ t : Fin 7,
        (0=t ∨ 0=t+1 ∨ 0=t+3) ∧ x (Fin.natAdd 7 t)=true)) →
(∀ C : Circuit, (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) →
    ∀ (x seed : Fin 14 → Bool) (k a b : Nat), C.gates[k]?=some ⟨.and,[a,b]⟩ →
      (C.wires (List.ofFn x)).getD a false=false → (C.wires (List.ofFn x)).getD b false=false →
      ∃ v : Nat → Bool, (∀ i : Fin 14, v i.val=seed i) ∧
        (∀ k (g : Gate) a b, C.gates[k]?=some g → g.inputs=[a,b] →
        (g.op=.and → v (14+k) = (((C.wires (List.ofFn x)).getD a false && v b) ||
          (v a && (C.wires (List.ofFn x)).getD b false))) ∧
        (g.op=.or → v (14+k) = (v a || v b))) ∧ v (14+k)=false) →
∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  intro common darkGate
  obtain ⟨C,size,normal,h,n,validH,validN,computed⟩ := common
  have size_eq (E : Circuit) : E.size=E.gates.length := rfl
  have eval_eq (E : Circuit) (x : List Bool) : E.eval x=(E.wires x).getD E.output false := rfl
  have eval_and (u v : Bool) : GateOp.and.eval [u,v]=(u && v) := by cases u <;> cases v <;> rfl
  have eval_or (u v : Bool) : GateOp.or.eval [u,v]=(u || v) := by cases u <;> cases v <;> rfl
  let Normal (C : Circuit) := ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j

  let Spec (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u t : Fin 7, (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true
  let single (s : Fin 14) (i : Fin 14) := decide (i=s)

  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have eval_extends (gs : List Gate) (w : List Bool) :
      ∃ u : List Bool, gs.foldl step w = w++u ∧ u.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih =>
      obtain ⟨u,hu,lu⟩ := ih (step w g)
      exact ⟨_::u,by simpa [step,List.append_assoc] using hu,by simp [lu]⟩

  have length_wires (C : Circuit) (x : Fin 14 → Bool) :
      (C.wires (List.ofFn x)).length = 14+C.size := by
    obtain ⟨u,e,l⟩ := eval_extends C.gates (List.ofFn x)
    change (C.gates.foldl step _).length = _
    rw [e,List.length_append,List.length_ofFn,l]
    rfl

  have earlier {w u : List Bool} {i : Nat} (h : i < w.length) :
      (w++u).getD i false = w.getD i false := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

  have raw (C : Circuit) (x : Fin 14 → Bool) :
      (C.wires (List.ofFn x)).getD 0 false = x 0 := by
    obtain ⟨u,e,_⟩ := eval_extends C.gates (List.ofFn x)
    change ((C.gates.foldl step _).getD 0 false) = _
    rw [e,earlier (by simp)]
    simp [List.getD_eq_getElem?_getD]
  let H (x : (Fin 14 → Bool)) : Bool := decide (∃ u t : Fin 7, u≠0 ∧
    (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u)=true ∧ x (Fin.natAdd 7 t)=true)

  let N (x : (Fin 14 → Bool)) : Bool := decide (∃ t : Fin 7, (0=t ∨ 0=t+1 ∨ 0=t+3) ∧ x (Fin.natAdd 7 t)=true)

  have factor (x : (Fin 14 → Bool)) : ((H x || x 0) && (H x || N x)) = true ↔
      ∃ u t : Fin 7, (u=t ∨ u=t+1 ∨ u=t+3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    simp only [Bool.and_eq_true_iff,Bool.or_eq_true_iff,H,N,decide_eq_true_eq]
    constructor
    · rintro ⟨left,right⟩
      rcases left with ⟨u,t,_,e,a,b⟩ | on
      · exact ⟨u,t,e,a,b⟩
      rcases right with ⟨u,t,_,e,a,b⟩ | ⟨t,e,b⟩
      · exact ⟨u,t,e,a,b⟩
      · exact ⟨0,t,e,on,b⟩
    · rintro ⟨u,t,e,a,b⟩
      by_cases zero : u=0
      · subst u; exact ⟨Or.inr a,Or.inr ⟨t,e,b⟩⟩
      · exact ⟨Or.inl ⟨u,t,zero,e,a,b⟩,Or.inl ⟨u,t,zero,e,a,b⟩⟩

  let suffix (C : Circuit) (h n : Nat) : List Gate :=
    [⟨.or,[h,0]⟩,⟨.or,[h,n]⟩,⟨.and,[14+C.size,14+C.size+1]⟩]

  let extend (C : Circuit) (h n : Nat) : Circuit := ⟨C.gates++suffix C h n,14+C.size+2⟩
  have normalized (C : Circuit) (normal : Normal C) {h n : Nat} (hb : h<14+C.size) (nb : n<14+C.size)
      (hz : h≠0) (hn : h≠n) : Normal (extend C h n) := by
    intro j g atGate
    change (C.gates++suffix C h n)[j]? = some g at atGate
    by_cases old : j<C.gates.length
    · rw [List.getElem?_append_left old] at atGate; exact normal j g atGate
    have member : j < (C.gates++suffix C h n).length := by
      by_contra! large
      rw [List.getElem?_eq_none large] at atGate
      contradiction
    have upper : j<C.size+3 := by simpa [suffix,size_eq] using member
    have lower : C.size ≤ j := Nat.le_of_not_gt old
    have cases : j=C.size ∨ j=C.size+1 ∨ j=C.size+2 := by omega
    rcases cases with rfl | rfl | rfl
    · have ident : (⟨.or,[h,0]⟩ : Gate) = g := by simpa [size_eq,suffix] using atGate
      subst g; exact ⟨Or.inr rfl,h,0,rfl,hz,hb,by omega⟩
    · have ident : (⟨.or,[h,n]⟩ : Gate) = g := by simpa [size_eq,suffix] using atGate
      subst g; exact ⟨Or.inr rfl,h,n,rfl,hn,by omega,by omega⟩
    · have ident : (⟨.and,[14+C.size,14+C.size+1]⟩ : Gate) = g := by simpa [size_eq,suffix] using atGate
      subst g; exact ⟨Or.inl rfl,_,_,rfl,by omega,by omega,by omega⟩
  have computesH (x : Fin 14 → Bool) : (C.wires (List.ofFn x)).getD h false = H x := by
    rw [Bool.eq_iff_iff]
    simpa only [H,decide_eq_true_eq] using (computed x).1
  have computesN (x : Fin 14 → Bool) : (C.wires (List.ofFn x)).getD n false = N x := by
    rw [Bool.eq_iff_iff]
    simpa only [N,decide_eq_true_eq] using (computed x).2
  let D := extend C h n
  have hz : h≠0 := by
    intro eq
    have a := computesH (single 0)
    rw [eq] at a
    change (C.wires (List.ofFn (single 0))).getD 0 false = _ at a
    rw [raw] at a
    have off : H (single 0)=false := by dsimp [H,single]; decide
    rw [off] at a
    contradiction
  have hn : h≠n := by
    intro eq
    let test := single (Fin.natAdd 7 (0 : Fin 7))
    have a := computesH test
    rw [eq,computesN] at a
    have different : N test ≠ H test := by dsimp [N,H,test,single]; decide
    exact different a
  have norm : Normal D := normalized C normal validH validN hz hn
  have last : D.gates[C.size+2]?=some ⟨.and,[14+C.size,14+C.size+1]⟩ := by
    simp [D,extend,suffix,size_eq]
  have tables (x : Fin 14 → Bool) : D.wires (List.ofFn x) = C.wires (List.ofFn x) ++
      [H x || x 0, H x || N x, (H x || x 0) && (H x || N x)] := by
    let w := C.wires (List.ofFn x)
    have len : w.length=14+C.size := length_wires C x
    have hlt : h<w.length := len ▸ validH
    have nlt : n<w.length := len ▸ validN
    have hval : w.getD h false=H x := computesH x
    have nval : w.getD n false=N x := computesN x
    have zval : w.getD 0 false=x 0 := raw C x
    change (C.gates++suffix C h n).foldl step (List.ofFn x)=_
    rw [List.foldl_append]
    change (suffix C h n).foldl step w=w++_
    simp only [suffix,List.foldl_cons,List.foldl_nil,step,List.map_cons,List.map_nil,
      eval_and,eval_or,earlier hlt,earlier nlt,hval,nval,zval,←len]
    simp [List.append_assoc,List.getD_eq_getElem?_getD]
  have spec : Spec D := by
    intro x
    rw [eval_eq,tables]
    change (_++[_,_,_]).getD (14+C.size+2) false = true ↔ _
    rw [← length_wires C x]
    simpa [List.getD_eq_getElem?_getD] using factor x
  have trace (s t : Fin 14) (darkH : H (single s)=false) (darkN : N (single s)=false)
      (dark0 : single s 0=false) :
      ∃ v : Nat → Bool, (∀ i : Fin 14, v i.val=decide (i=t)) ∧
        (∀ k (g : Gate) a b, D.gates[k]?=some g → g.inputs=[a,b] →
          (g.op=.and → v (14+k) = (((D.wires (List.ofFn (single s))).getD a false && v b) ||
            (v a && (D.wires (List.ofFn (single s))).getD b false))) ∧
          (g.op=.or → v (14+k) = (v a || v b))) ∧ v D.output=false := by
    have eq : D.output=14+(C.size+2) := by dsimp [D,extend]; omega
    rw [eq]
    apply darkGate D norm (single s) (fun i => decide (i=t)) _ _ _ last
    · rw [tables,← length_wires C (single s),darkH,dark0]
      simp [List.getD_eq_getElem?_getD]
    · rw [tables,← length_wires C (single s),darkH,darkN]
      simp [List.getD_eq_getElem?_getD]
  let p : Fin 7 := 1
  let l : Fin 7 := 1
  obtain ⟨v,vin,vr,vout⟩ := trace (Fin.castAdd 7 p) (Fin.natAdd 7 l)
    (by dsimp [H,single,p]; decide) (by dsimp [N,single,p]; decide) (by decide)
  obtain ⟨w,win,wr,wout⟩ := trace (Fin.natAdd 7 l) (Fin.castAdd 7 p)
    (by dsimp [H,single,l]; decide) (by dsimp [N,single,l]; decide) (by decide)
  have bound : D.size≤27 := by simpa [D,extend,suffix,size_eq] using Nat.add_le_add_right size 3
  refine ⟨D,bound,norm,spec,p,l,Or.inl rfl,⟨v,?_,vr,vout⟩,w,?_,wr,wout⟩
  · intro m
    refine ⟨?_,?_⟩
    · have h := vin (Fin.castAdd 7 m)
      simpa [Fin.ext_iff,show m.val ≠ l.val+7 by omega] using h
    · have h := vin (Fin.natAdd 7 m)
      simpa [Fin.ext_iff,Nat.add_comm 7] using h
  · intro m
    refine ⟨?_,?_⟩
    · have h := win (Fin.castAdd 7 m)
      simpa [Fin.ext_iff] using h
    · have h := win (Fin.natAdd 7 m)
      simpa [Fin.ext_iff,Nat.add_comm 7,show m.val+7 ≠ p.val by omega] using h
