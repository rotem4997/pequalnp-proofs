import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18938

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def op : Bool → GateOp | true => .and | false => .or
def mix (t a b : Bool) : Bool := if t then a && b else a || b

def evalBit (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
def ws (gs : List Gate) (x : List Bool) := gs.foldl (fun w g => w ++ [evalBit w g]) x
def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) := (ws gs (List.ofFn x)).getD i false

theorem len_ws (gs : List Gate) (x : List Bool) : (ws gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [ws]
  | cons g gs ih =>
    change (ws gs (x ++ [evalBit x g])).length = _
    rw [ih]; simp; omega

theorem ws_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    ws (gs ++ [g]) x = ws gs x ++ [evalBit (ws gs x) g] := by simp [ws, List.foldl_append]

theorem val_snoc_lt {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ)
    (h : i < n + gs.length) : val (gs ++ [g]) x i = val gs x i := by
  unfold val
  rw [ws_snoc, List.getD_append _ _ _ _ (by simpa [len_ws] using h)]

theorem val_snoc_last {n : ℕ} (gs : List Gate) (t : Bool) (a b : ℕ) (x : Fin n → Bool) :
    val (gs ++ [⟨op t,[a,b]⟩]) x (n + gs.length) = mix t (val gs x a) (val gs x b) := by
  have h : (ws gs (List.ofFn x)).length = n + gs.length := by simp [len_ws]
  unfold val
  rw [ws_snoc, List.getD_append_right _ _ _ _ (by omega),h,Nat.sub_self]
  cases t <;> simp [evalBit, op, mix, GateOp.eval]

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : Fin n) : val [] x i.val = x i := by
  simp [val,ws,List.getD_eq_getElem?_getD,i.isLt]

def Good (m : ℕ) (hs : List Gate) : Prop := ∀ j g, hs[j]? = some g →
  ∃ (t : Bool) (a b : ℕ), g = ⟨op t,[a,b]⟩ ∧ a < m+j ∧ b < m+j

theorem good_of {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) : Good n C.gates := by
  intro j g hj
  have hh := (List.getElem?_eq_some_iff.mp hj).1
  have hg : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j,hj⟩
  obtain ⟨a,b,hi⟩ := List.length_eq_two.mp (h.2.2 g hg)
  have he : gateAt C j = g := by simp [gateAt,List.getD_eq_getElem?_getD,hj]
  have ha := h.2.1 j hh a (by simp [he,hi])
  have hb := h.2.1 j hh b (by simp [he,hi])
  rcases h.1 g hg with hand | hor
  · exact ⟨true,a,b,by cases g; simp_all [op],ha,hb⟩
  · exact ⟨false,a,b,by cases g; simp_all [op],ha,hb⟩

theorem ao_of {n : ℕ} {hs : List Gate} (h : Good n hs) (o : ℕ) : TopForm.IsAO2 n ⟨hs,o⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨t,a,b,rfl,_,_⟩ := h j g hj
    cases t <;> simp [op]
  · intro j hj i hi
    change j < hs.length at hj
    obtain ⟨t,a,b,hg,ha,hb⟩ := h j hs[j] (List.getElem?_eq_getElem hj)
    change i ∈ (hs.getD j _).inputs at hi
    rw [List.getD_eq_getElem _ _ hj,hg] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨t,a,b,rfl,_,_⟩ := h j g hj
    rfl

theorem good_nil (m : ℕ) : Good m [] := by simp [Good]

theorem good_snoc {m : ℕ} {hs : List Gate} (h : Good m hs) (t : Bool) {a b : ℕ}
    (ha : a < m+hs.length) (hb : b < m+hs.length) : Good m (hs ++ [⟨op t,[a,b]⟩]) := by
  intro j g hj
  by_cases lt : j < hs.length
  · rw [List.getElem?_append_left lt] at hj
    exact h j g hj
  · obtain ⟨nlen,_⟩ := List.getElem?_eq_some_iff.mp hj
    have eq : j = hs.length := by simp at nlen; omega
    subst j
    simp at hj
    exact ⟨t,a,b,hj.symm,ha,hb⟩

def push (hs : List Gate) (t : Bool) (a b : Option ℕ) : List Gate :=
  match a,b with
  | some i, some j => hs ++ [⟨op t,[i,j]⟩]
  | _, _ => hs

def dest (next : ℕ) (t : Bool) (a b : Option ℕ) : Option ℕ :=
  match a,b with
  | some _, some _ => some next
  | none,o => if t then none else o
  | o,none => if t then none else o

def RefOK {m : ℕ} (hs : List Gate) (r : Option ℕ) (f : (Fin m → Bool) → Bool) : Prop :=
  (∀ z, r = some z → z < m+hs.length) ∧ f (fun _ => true) = r.isSome ∧
    ∀ x, f x = r.elim false (val hs x)

theorem ref_old {m : ℕ} {hs : List Gate} {r : Option ℕ} {f : (Fin m → Bool) → Bool}
    (hr : RefOK hs r f) (t : Bool) (a b : Option ℕ) : RefOK (push hs t a b) r f := by
  cases a with
  | none => exact hr
  | some i =>
    cases b with
    | none => exact hr
    | some j =>
      refine ⟨fun z h => by have := hr.1 z h; simp [push]; omega,hr.2.1,?_⟩
      intro x
      rw [hr.2.2 x]
      cases ho : r with
      | none => rfl
      | some z => exact (val_snoc_lt hs _ x z (hr.1 z ho)).symm

theorem ref_new {m : ℕ} {hs : List Gate} {a b : Option ℕ} {f g : (Fin m → Bool) → Bool}
    (hf : RefOK hs a f) (hg : RefOK hs b g) (t : Bool) :
    RefOK (push hs t a b) (dest (m+hs.length) t a b) (fun x => mix t (f x) (g x)) := by
  cases a with
  | none => cases t <;> cases b <;> simp_all [RefOK, mix, dest, push]
  | some i =>
    cases b with
    | none => cases t <;> simp_all [RefOK, mix, dest, push]
    | some j =>
      refine ⟨?_,?_,?_⟩
      · intro z hz
        simp [dest] at hz
        subst z
        simp [push]
      · change mix t (f _) (g _) = _
        rw [hf.2.1,hg.2.1]; cases t <;> rfl
      · intro x
        change mix t (f x) (g x) = _
        rw [hf.2.2 x,hg.2.2 x]
        exact (val_snoc_last hs t i j x).symm

theorem push_good {m : ℕ} {hs : List Gate} (hh : Good m hs) {a b : Option ℕ}
    {f g : (Fin m → Bool) → Bool} (hf : RefOK hs a f) (hg : RefOK hs b g) (t : Bool) :
    Good m (push hs t a b) := by
  cases a with
  | none => exact hh
  | some i =>
    cases b with
    | none => exact hh
    | some j => exact good_snoc hh t (hf.1 i rfl) (hg.1 j rfl)

theorem push_len (hs : List Gate) (t : Bool) (a b : Option ℕ) :
    (push hs t a b).length = hs.length + (if a.isSome && b.isSome then 1 else 0) := by
  cases a <;> cases b <;> simp [push]

theorem val_before {n : ℕ} (hs tail : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n+hs.length) :
    val (hs++tail) x i = val hs x i := by
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton rest g ih =>
    rw [← List.append_assoc, val_snoc_lt _ _ _ _ (by simp; omega), ih]

theorem val_primary {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) : val gs x i = x i := by
  calc val gs x i = val ([]++gs) x i := rfl
       _ = val [] x i := val_before [] gs x i.val (by simp)
       _ = x i := val_nil x i

theorem val_at {n : ℕ} {gs : List Gate} {j a b : ℕ} {t : Bool} (hj : j < gs.length)
    (he : gs[j] = ⟨op t,[a,b]⟩) (ha : a < n+j) (hb : b < n+j) (x : Fin n → Bool) :
    val gs x (n+j) = mix t (val gs x a) (val gs x b) := by
  let pre := gs.take j
  let g : Gate := ⟨op t,[a,b]⟩
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hshape : pre ++ [g] ++ gs.drop (j+1) = gs := by
    change gs.take j ++ [⟨op t,[a,b]⟩] ++ _ = _
    rw [← he,← List.take_succ_eq_append_getElem hj,List.take_append_drop]
  have old (w : ℕ) (hw : w < n+j) : val gs x w = val pre x w := by
    conv_lhs => rw [← hshape, List.append_assoc]
    exact val_before _ _ _ _ (by omega)
  rw [old a ha, old b hb]
  conv_lhs => rw [← hshape]
  rw [val_before _ _ _ _ (by simp [hpre]), ← hpre]
  exact val_snoc_last pre t a b x


theorem mono {n : ℕ} {C : Circuit} (ao : TopForm.IsAO2 n C) {x y : Fin n → Bool}
    (xy : ∀ i, x i = true → y i = true) (w : ℕ) : val C.gates x w = true → val C.gates y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases small : w < n
    · simpa only [val_primary C.gates x ⟨w,small⟩,val_primary C.gates y ⟨w,small⟩] using xy ⟨w,small⟩
    by_cases big : n+C.size ≤ w
    · have off : val C.gates x w = false := by
        apply List.getD_eq_default
        simpa [len_ws,Circuit.size] using big
      simp [off]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by change ¬ n+C.gates.length ≤ n+j at big; omega
    obtain ⟨t,a,b,hg,ha,hb⟩ := good_of ao j C.gates[j] (List.getElem?_eq_getElem hj)
    rw [val_at hj hg ha hb x,val_at hj hg ha hb y]
    cases t <;> simp only [mix, Bool.false_eq_true, ite_false, ite_true, Bool.or_eq_true, Bool.and_eq_true]
    · exact Or.imp (ih a ha) (ih b hb)
    · exact And.imp (ih a ha) (ih b hb)

theorem masked_projection (n : ℕ) (C : Circuit) (s : Fin n) (U : ℕ → Bool) (ao : TopForm.IsAO2 n C) :
    let T := ReadTwo.wval C (fun i : Fin n => decide (i ≠ s))
    U C.output = true →
    (∀ j < C.size, U (n+j) = true → T (n+j) = true →
      ∀ i ∈ (gateAt C j).inputs, T i = true → U i = true) →
    ∃ D : Circuit, TopForm.IsAO2 n D ∧
      D.size ≤ ((List.range C.size).filter (fun j => U (n+j) && (gateAt C j).inputs.all T)).length ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn fun i => if i=s then false else x i) := by
  intro T out closed
  let V (x : Fin n → Bool) := val C.gates (fun i => if i=s then false else x i)
  let K (j : ℕ) := U (n+j) && (gateAt C j).inputs.all T
  let G (w : ℕ) (x : Fin n → Bool) := U w && V x w
  have top (w : ℕ) : V (fun _ => true) w = T w := by
    have eq : (fun i : Fin n => if i=s then false else true) = (fun i => decide (i ≠ s)) := by
      funext i; by_cases h : i=s <;> simp [h]
    unfold V
    rw [eq]; rfl
  have dom (x : Fin n → Bool) (w : ℕ) (h : V x w = true) : T w = true := by
    apply mono ao (x := fun i => if i=s then false else x i) _ w h
    intro i hi
    by_cases eq : i=s <;> simp_all
  have noneOK (hs : List Gate) {w : ℕ} (h : U w = false ∨ T w = false) : RefOK hs none (G w) := by
    have alloff (x : Fin n → Bool) : G w x = false := by
      rcases h with cold | cold
      · simp [G,cold]
      · have z : V x w = false := Bool.eq_false_iff.mpr (fun v => Bool.noConfusion ((dom x w v).symm.trans cold))
        simp [G,z]
    exact ⟨by simp,alloff _,fun x => alloff x⟩
  have build (j : ℕ) (hj : j ≤ C.size) : ∃ (hs : List Gate) (r : ℕ → Option ℕ),
      Good n hs ∧ hs.length ≤ ((List.range j).filter K).length ∧
      ∀ w < n+j, RefOK hs (r w) (G w) := by
    induction j with
    | zero =>
      let r (w : ℕ) : Option ℕ := if U w = true ∧ w ≠ s.val then some w else none
      refine ⟨[],r,good_nil _,by simp,?_⟩
      intro w hw
      have lt : w < n := by omega
      let i : Fin n := ⟨w,lt⟩
      have v (x : Fin n → Bool) : V x w = if i = s then false else x i := val_primary C.gates _ i
      by_cases u : U w = true
      · by_cases eq : i=s
        · have ew : w=s.val := congrArg Fin.val eq
          rw [show r w = none by simp [r,ew]]
          apply noneOK [] (Or.inr ?_)
          rw [← top,v,ite_eq_left eq]
        · have ew : w ≠ s.val := fun a => eq (Fin.ext a)
          rw [show r w = some w by simp [r,u,ew]]
          exact ⟨fun z hz => by cases hz; exact lt, by simp [G,u,v,eq],fun x => by
            change (U w && V x w) = val [] x i.val
            simp [u,v,eq,val_nil]⟩
      · rw [show r w = none by simp [r,u]]
        exact noneOK [] (Or.inl (Bool.eq_false_iff.mpr u))
    | succ j ih =>
      have hj' : j < C.gates.length := hj
      obtain ⟨hs,r,good,sz,refs⟩ := ih (by omega)
      have extend (o : Option ℕ) (h : RefOK hs o (G (n+j))) :
          ∃ (H : List Gate) (R : ℕ → Option ℕ), Good n H ∧ H.length ≤ ((List.range (j+1)).filter K).length ∧
          ∀ w < n+(j+1), RefOK H (R w) (G w) := by
        let R := fun w => if w=n+j then o else r w
        refine ⟨hs,R,good,?_,?_⟩
        · rw [List.range_succ,List.filter_append,List.length_append]; omega
        · intro w hw
          by_cases eq : w=n+j
          · subst w; simpa [R] using h
          · simpa [R,eq] using refs w (by omega)
      by_cases u : U (n+j) = true
      · by_cases hot : T (n+j) = true
        · obtain ⟨t,a,b,hg,ha,hb⟩ := good_of ao j C.gates[j] (List.getElem?_eq_getElem hj')
          have gate : gateAt C j = ⟨op t,[a,b]⟩ := by
            rwa [gateAt,List.getD_eq_getElem _ _ hj']
          have operand (i : ℕ) (hi : i=a ∨ i=b) (x : Fin n → Bool) : G i x = V x i := by
            by_cases ui : U i = true
            · simp [G,ui]
            · have off : V x i = false := by
                apply Bool.eq_false_iff.mpr
                intro h
                exact ui (closed j hj' u hot i (by simpa [gate] using hi) (dom x i h))
              simp [G,off]
          have ra := refs a ha
          have rb := refs b hb
          let H := push hs t (r a) (r b)
          let o := dest (n+hs.length) t (r a) (r b)
          let R (w : ℕ) := if w=n+j then o else r w
          have kc : K j = ((r a).isSome && (r b).isSome) := by
            have ea := ra.2.1
            have eb := rb.2.1
            rw [operand a (Or.inl rfl),top] at ea
            rw [operand b (Or.inr rfl),top] at eb
            simp [K,u,gate,ea,eb]
          refine ⟨H,R,push_good good ra rb t,?_,?_⟩
          · rw [List.range_succ,List.filter_append,List.length_append]
            unfold H
            rw [push_len,← kc]
            apply Nat.add_le_add sz
            cases e : K j <;> simp [e]
          · intro w hw
            by_cases eq : w=n+j
            · subst w
              rw [show R (n+j) = o from ite_eq_left rfl]
              have ev : G (n+j) = fun x => mix t (G a x) (G b x) := by
                funext x
                simp only [G,u,Bool.true_and] at ⊢
                change V x (n+j) = mix t (G a x) (G b x)
                rw [operand a (Or.inl rfl),operand b (Or.inr rfl)]
                exact val_at hj' hg ha hb _
              rw [ev]
              exact ref_new ra rb t
            · rw [show R w = r w from ite_eq_right eq]
              exact ref_old (refs w (by omega)) t (r a) (r b)
        · exact extend none (noneOK hs (Or.inr (Bool.eq_false_iff.mpr hot)))
      · exact extend none (noneOK hs (Or.inl (Bool.eq_false_iff.mpr u)))
  obtain ⟨hs,r,good,sz,refs⟩ := build C.size le_rfl
  let endIdx := n+hs.length
  have beyond (x : Fin n → Bool) : val hs x endIdx = false := by
    apply List.getD_eq_default; simp [len_ws,endIdx]
  by_cases inside : C.output < n+C.size
  · refine ⟨⟨hs,(r C.output).getD endIdx⟩,ao_of good _,sz,?_⟩
    intro x
    change val hs x ((r C.output).getD endIdx) = V x C.output
    have hv := (refs _ inside).2.2 x
    rw [show G C.output x = V x C.output by simp [G,out]] at hv
    cases e : r C.output with
    | none => simpa [e,beyond] using hv.symm
    | some i => simpa [e] using hv.symm
  · refine ⟨⟨hs,endIdx⟩,ao_of good _,sz,?_⟩
    intro x
    change val hs x endIdx = V x C.output
    rw [beyond]; symm
    apply List.getD_eq_default
    simpa [len_ws,Circuit.size] using Nat.le_of_not_gt inside

end PEqualNP.Outside.L_meta_18938

theorem PEqualNP.Outside.L_meta_18938 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : ℕ → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     have x6 : ℕ → Bool := PEqualNP.ReadTwo.wval x2 fun (x6 : Fin x1) => Decidable.decide (x6 ≠ x3);     x4 x2.output = Bool.true → (∀ x8 < x2.size, x4 (x1 + x8) = Bool.true → x6 (x1 + x8) = Bool.true → ∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, x6 x12 = Bool.true → x4 x12 = Bool.true) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x9 ∧ x9.size ≤ (List.filter (fun (x10 : ℕ) => x4 (x1 + x10) && (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs.all x6) (List.range x2.size)).length ∧ ∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x2.eval (List.ofFn fun (x11 : Fin x1) => if x11 = x3 then Bool.false else x10 x11)) :=
  PEqualNP.Outside.L_meta_18938.masked_projection
