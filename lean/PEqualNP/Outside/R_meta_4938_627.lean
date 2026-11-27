import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Put the earlier tap at the output of the shorter circuit and remove the later tap's gate.
-- An extra operand index represents the false default for an out-of-range read.
-- A final NOT can cover a positive row only if another NOT already occurs earlier.
-- The monotonicity argument follows project reduction R_meta_4027_357 (Apache-2.0).
theorem PEqualNP.Outside.R_meta_4938_627
    (andCase : let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)));
      ∀ (C : Circuit) (u v : Fin (11+C.size)), FanInTwo C → C.size ≤ 16 →
      10 ≤ C.output → C.output < 10+C.size → let W := fun (i : ℕ) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD i false;
      let A := W C.output; let B := fun x => W u.val x && W v.val x;
      (∀ x, (A x || B x) = F x) → A ≤ B ∨ B ≤ A)
    (orCase : let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)));
      ∀ (C : Circuit) (u v : Fin (11+C.size)), FanInTwo C → C.size ≤ 16 →
      10 ≤ C.output → C.output < 10+C.size → let W := fun (i : ℕ) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD i false;
      let A := W C.output; let B := fun x => W u.val x || W v.val x;
      (∀ x, (A x || B x) = F x) → A ≤ B ∨ B ≤ A)
    (notCase : let F := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)));
      ∀ (C : Circuit) (u : Fin (11+C.size)), FanInTwo C → C.size ≤ 16 →
      10 ≤ C.output → C.output < 10+C.size → (∃ g ∈ C.gates, g.op = GateOp.not) →
      let W := fun (i : ℕ) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD i false;
      let A := W C.output; let B := fun x => !(W u.val x);
      (∀ x, (A x || B x) = F x) → A ≤ B ∨ B ≤ A) :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false) := by
  classical
  intro g D a b gOk dOk budget
  dsimp only
  intro aOnly bOnly safe
  by_contra uncovered
  let P := fun x : Fin 10 → Bool => (List.finRange 5).any fun i =>
        (x (Fin.castAdd 5 i) && (x (Fin.castAdd 5 (i+1)) || x (Fin.natAdd 5 i))) ||
        (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2)))
  let explicit := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let step := fun (w : List Bool) (h : Gate) => w++[h.op.eval (h.inputs.map fun i => w.getD i false)]
  let gs := g::D.gates
  let V := fun (i : ℕ) (x : Fin 10 → Bool) => (gs.foldl step (List.ofFn x)).getD i false
  change (∃ x, V a x=true ∧ V b x=false) at aOnly
  change (∃ x, V a x=false ∧ V b x=true) at bOnly
  change ∀ x, explicit x=false → V a x=false ∧ V b x=false at safe
  change ¬ ∃ x, explicit x=true ∧ V a x=false ∧ V b x=false at uncovered
  have same : explicit=P := by
    funext x
    exact (show ∀ y : Fin 10 → Bool,explicit y=P y from by dsimp only [explicit,P]; decide +kernel) x
  rw [same] at safe uncovered
  have atZero : P (fun _ => false)=false := by decide +kernel
  have notSingle : ∀ i : Fin 10, P (fun j => decide (j=i))=false := by dsimp only [P]; decide +kernel
  have joint (x : Fin 10 → Bool) : (V a x || V b x)=P x := by
    cases pval : P x with
    | false => obtain ⟨za,zb⟩ := safe x pval; simp [za,zb]
    | true =>
      cases va : V a x with
      | true => rfl
      | false => cases vb : V b x with
                 | true => rfl
                 | false => exact (uncovered ⟨x,pval,va,vb⟩).elim
  have noncomp {A B : (Fin 10 → Bool) → Bool} (ha : ∃ x,A x=true ∧ B x=false)
      (hb : ∃ x,A x=false ∧ B x=true) : ¬(A ≤ B ∨ B ≤ A) := by
    rintro (le | le)
    · obtain ⟨x,za,zb⟩ := ha; have q := le x; rw [za,zb] at q; exact (by decide : ¬(true ≤ false)) q
    · obtain ⟨x,za,zb⟩ := hb; have q := le x; rw [za,zb] at q; exact (by decide : ¬(true ≤ false)) q
  have len (L : List Gate) (w : List Bool) : (L.foldl step w).length=w.length+L.length := by
    induction L generalizing w with
    | nil => simp
    | cons h hs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have keep (L : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) : (L.foldl step w).getD i false=w.getD i false := by
    induction L generalizing w with
    | nil => rfl
    | cons h hs ih =>
      rw [List.foldl_cons,ih (step w h) (by simp [step];omega)]
      exact List.getD_append _ _ _ _ hi
  have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have aux (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (u v : List Bool) (hlen : u.length = v.length)
      (hle : ∀ i, u.getD i false ≤ v.getD i false) :
      ∀ i, (gs.foldl step u).getD i false ≤ (gs.foldl step v).getD i false := by
    induction gs generalizing u v with
    | nil => exact hle
    | cons g gs ih =>
      apply ih (fun g hg => ops g (List.mem_cons_of_mem _ hg)) (step u g) (step v g)
      · simp [step,hlen]
      · intro i
        by_cases hi : i < u.length
        · simpa only [step,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (hlen ▸ hi)] using hle i
        · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
                List.getD_append_right _ _ _ _ (by omega : v.length ≤ i), ← hlen]
          by_cases he : i = u.length
          · simp only [he,Nat.sub_self,List.getD_cons_zero]
            rcases ops g (by simp) with ha | ho
            · simp only [ha,andEval,Bool.le_iff_imp,List.all_eq_true,List.mem_map,id_eq]
              intro h b hb
              obtain ⟨j,hj,rfl⟩ := hb
              exact (Bool.le_iff_imp.mp (hle j)) (h _ ⟨j,hj,rfl⟩)
            · simp only [ho,orEval,Bool.le_iff_imp,List.any_eq_true,List.mem_map,id_eq]
              rintro ⟨b,⟨j,hj,rfl⟩,hb⟩
              exact ⟨_,⟨j,hj,rfl⟩,Bool.le_iff_imp.mp (hle j) hb⟩
          · have hn : 1 ≤ i-u.length := by omega
            have hz (b : Bool) : [b].getD (i-u.length) false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hn)]
              rfl
            simp only [hz, le_refl]
  have cap : gs.length ≤ 17 := by change D.gates.length+1 ≤ 17; change D.gates.length ≤ 16 at budget; omega
  have basis (h : Gate) (mem : h∈gs) :
      (h.op=.and ∨ h.op=.or ∨ h.op=.not) ∧ h.inputs.length≤2 := by
    rcases List.mem_cons.mp mem with rfl | hD
    · exact gOk _ (by simp)
    · exact dOk _ hD
  have lo {i : ℕ} (zero : ∀ x,P x=false → V i x=false) : 10 ≤ i := by
    by_contra! small
    let j : Fin 10 := ⟨i,small⟩
    let x : Fin 10 → Bool := fun k => decide (k=j)
    have bad := zero x (notSingle j)
    change (gs.foldl step (List.ofFn x)).getD i false=false at bad
    rw [keep _ _ _ (by simpa only [List.length_ofFn] using small)] at bad
    have read : (List.ofFn x).getD j.val false=x j := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
      simp only [List.getElem_ofFn]
    change (List.ofFn x).getD j.val false=false at bad
    rw [read] at bad; simp [x] at bad
  have hi {i : ℕ} (on : ∃ x,V i x=true) : i<10+gs.length := by
    obtain ⟨x,hx⟩ := on
    by_contra! large
    change (gs.foldl step (List.ofFn x)).getD i false=true at hx
    rw [List.getD_eq_default _ _ (by simpa only [len,List.length_ofFn] using large)] at hx
    contradiction
  have lowA := lo (i:=a) (fun x hx => (safe x hx).1)
  have lowB := lo (i:=b) (fun x hx => (safe x hx).2)
  have different : a≠b := by
    rintro rfl
    obtain ⟨x,yes,no⟩ := aOnly
    rw [yes] at no; contradiction
  have ordered (early late : ℕ) (before : early<late) (start : 10 ≤ early)
      (left : ∃ x,V early x=true ∧ V late x=false)
      (right : ∃ x,V early x=false ∧ V late x=true)
      (covers : ∀ x,(V early x || V late x)=P x) : False := by
    obtain ⟨xPos,off,on⟩ := right
    have top := hi (i:=late) ⟨xPos,on⟩
    let j := late-10
    have hj : j<gs.length := by dsimp [j];omega
    let h := gs[j]
    let pre := gs.take j
    let post := gs.drop (j+1)
    have preLen : pre.length=j := List.length_take_of_le hj.le
    have split : gs=pre++h::post := by
      have eq := List.take_append_drop j gs
      rw [List.drop_eq_getElem_cons hj] at eq
      exact eq.symm
    let C : Circuit := ⟨pre,early⟩
    let W := fun (i : ℕ) (x : Fin 10 → Bool) => (C.wires (List.ofFn x)).getD i false
    have legalC : FanInTwo C := by
      intro v hv
      exact basis v (List.mem_of_mem_take hv)
    have lim : C.size ≤ 16 := by change pre.length ≤ 16; omega
    have outHi : C.output<10+C.size := by change early<10+pre.length;dsimp [j] at preLen;omega
    have wlen (x : Fin 10 → Bool) : (pre.foldl step (List.ofFn x)).length=10+j := by simp [len,preLen]
    have prior (x : Fin 10 → Bool) : V early x=W early x := by
      change (gs.foldl step (List.ofFn x)).getD early false = (pre.foldl step (List.ofFn x)).getD early false
      rw [split,List.foldl_append,keep _ _ _ (by rw [wlen];dsimp [j];omega)]
    have terminal (x : Fin 10 → Bool) : V late x=h.op.eval (h.inputs.map fun i => W i x) := by
      let bank := pre.foldl step (List.ofFn x)
      have place : late=bank.length := by rw [show bank.length=10+j from wlen x];dsimp [j];omega
      change (gs.foldl step (List.ofFn x)).getD late false = h.op.eval (h.inputs.map fun i => bank.getD i false)
      rw [split,List.foldl_append,List.foldl_cons]
      change (post.foldl step (step bank h)).getD late false = _
      rw [keep post _ _ (by simp [step,place]),place]
      simp [step]
    have hGate := basis h (List.getElem_mem hj)
    have nonempty : h.inputs≠[] := by
      intro empty
      obtain ⟨y,_,no⟩ := left
      have eq : V late y=V late xPos := by simp only [terminal,empty,List.map_nil]
      rw [no,on] at eq; contradiction
    have pair : ∃ u v : ℕ, h.inputs=[u] ∧ v=u ∨ h.inputs=[u,v] := by
      cases ins : h.inputs with
      | nil => exact (nonempty ins).elim
      | cons u rest =>
        cases rest with
        | nil => exact ⟨u,u,Or.inl ⟨rfl,rfl⟩⟩
        | cons v tail => cases tail with
                         | nil => exact ⟨u,v,Or.inr rfl⟩
                         | cons z zs => have k := hGate.2; simp [ins] at k
    obtain ⟨u,v,hpair⟩ := pair
    let capWire (w : ℕ) : Fin (11+C.size) := ⟨min w (10+C.size),by omega⟩
    have capped (w : ℕ) (x : Fin 10 → Bool) : W (capWire w).val x=W w x := by
      by_cases real : w≤10+C.size
      · simp [capWire,real]
      · have length : (C.wires (List.ofFn x)).length=10+C.size := by
          change (pre.foldl step (List.ofFn x)).length=10+pre.length
          rw [wlen,preLen]
        have a : W (10+C.size) x=false := List.getD_eq_default _ _ (by omega)
        have b : W w x=false := List.getD_eq_default _ _ (by omega)
        simp only [capWire,min_eq_right (by omega : 10+C.size≤w),a,b]
    have eqAB {B : (Fin 10 → Bool) → Bool} (lateEq : ∀ x,V late x=B x) :
        (∀ x,(W C.output x || B x)=P x) ∧ ¬(W C.output ≤ B ∨ B ≤ W C.output) := by
      have e : V early=W C.output := funext prior
      have l : V late=B := funext lateEq
      rw [← e,← l]; exact ⟨covers,noncomp left ⟨xPos,off,on⟩⟩
    rcases hGate.1 with hand | hor | hnot
    · have eq (x : Fin 10 → Bool) : V late x=(W (capWire u).val x && W (capWire v).val x) := by
        rw [capped,capped,terminal,hand]
        rcases hpair with ⟨pins,rfl⟩ | pins <;> simp [pins,andEval]
      obtain ⟨complete,impossible⟩ := eqAB eq
      exact impossible (andCase C (capWire u) (capWire v) legalC lim start outHi complete)
    · have eq (x : Fin 10 → Bool) : V late x=(W (capWire u).val x || W (capWire v).val x) := by
        rw [capped,capped,terminal,hor]
        rcases hpair with ⟨pins,rfl⟩ | pins <;> simp [pins,orEval]
      obtain ⟨complete,impossible⟩ := eqAB eq
      exact impossible (orCase C (capWire u) (capWire v) legalC lim start outHi complete)
    · have eq (x : Fin 10 → Bool) : V late x=!(W (capWire u).val x) := by
        rw [capped,terminal,hnot]
        rcases hpair with ⟨pins,_⟩ | pins <;> simp [pins,notEval]
      obtain ⟨complete,impossible⟩ := eqAB eq
      have signed : ∃ k∈C.gates,k.op=.not := by
        by_contra missing
        have ops (k : Gate) (hk : k∈pre) : k.op=.and ∨ k.op=.or := by
          have allowed := (basis k (List.mem_of_mem_take hk)).1
          exact allowed.imp_right (fun h => h.resolve_right (fun nn => missing ⟨k,hk,nn⟩))
        let zero : Fin 10 → Bool := fun _ => false
        have offAll := complete zero
        rw [atZero] at offAll
        have one : W (capWire u).val zero=true := by simpa using (Bool.or_eq_false_iff.mp offAll).2
        have grow : W (capWire u).val zero ≤ W (capWire u).val xPos := by
          apply aux pre ops (List.ofFn zero) (List.ofFn xPos) (by simp) _ (capWire u).val
          intro i
          by_cases inside : i<10
          · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left inside,Option.getD_some,zero,Bool.false_le]
          · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right inside,Option.getD_none,le_refl]
        have yes := Bool.eq_true_of_true_le (one ▸ grow)
        have bad := eq xPos
        rw [yes,on] at bad
        contradiction
      exact impossible (notCase C (capWire u) legalC lim start outHi signed complete)
  rcases lt_or_gt_of_ne different with lt | gt
  · exact ordered a b lt lowA aOnly bOnly joint
  · exact ordered b a gt lowB (by simpa only [and_comm] using bOnly) (by simpa only [and_comm] using aOnly)
      (fun x => (Bool.or_comm _ _).trans (joint x))
