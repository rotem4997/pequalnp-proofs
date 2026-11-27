import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_3803_42
    (linear : ∀ C : Circuit, Monotone2 C → RightOnIncidentPairs singerLines3 C →
      (∀ Q, IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
      HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64 ≤ C.size)
    (unions : ∀ (C : Circuit) (s k : List ℕ) (c : Bool), s ∈ ([[],[0],[13],[0,1],[13,14],[0,13],[0,14]] : List (List ℕ)) →
      let g : Gate := if c then ⟨.and, []⟩ else ⟨.or, k⟩
      let A : Circuit := ⟨⟨.or,s⟩ :: g :: C.gates, C.output⟩
      Monotone2 A → ReadsBack 26 A → RightOnIncidentPairs singerLines3 A →
      (∀ Q, IsQuadrangle singerLines3 Q → A.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) A 1 → 62 ≤ C.size)
    (oneFlag : ∀ (C : Circuit) (s : List ℕ) (p₀ l₀ : Fin 13), s ∈ ([[],[0],[13],[0,1],[13,14],[0,13],[0,14]] : List (List ℕ)) → p₀ ∈ singerLines3 l₀ →
      let v := fun (X Y : Finset (Fin 13)) (b : Bool) =>
        let x := incidenceInput X Y
        C.eval ((x ++ [s.any fun j => x.getD j false]) ++ [b])
      Monotone2 C → ReadsBack 28 C →
      (∀ p l : Fin 13, p ∈ singerLines3 l → v {p} {l} (decide (p = p₀ ∧ l = l₀)) = true) →
      (∀ Q, IsQuadrangle singerLines3 Q → v Q (missLines singerLines3 Q) false = false) → 62 ≤ C.size)
    (twoFlags : ∀ (C : Circuit) (s : List ℕ), s = [0,1] ∨ s = [13,14] →
      let v := fun (X Y : Finset (Fin 13)) (b : Bool) =>
        let x := incidenceInput X Y
        C.eval ((x ++ [s.any fun j => x.getD j false]) ++ [b])
      Monotone2 C → ReadsBack 28 C →
      (∀ p l : Fin 13, p ∈ singerLines3 l →
        v {p} {l} (if s = [0,1] then decide (l = 0 ∧ (p = 0 ∨ p = 1))
                   else decide (p = 1 ∧ (l = 0 ∨ l = 1))) = true) →
      (∀ Q, IsQuadrangle singerLines3 Q → v Q (missLines singerLines3 Q) false = false) → 62 ≤ C.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → (63 : ℕ) ≤ x6.size := by
  intro D P N good spec C s hs mono read fit
  let ext (x : List Bool) := x ++ [s.any fun j => x.getD j false]
  let step (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  have orEval (x : List Bool) : GateOp.or.eval x = x.any id := rfl
  have andEval (x : List Bool) : GateOp.and.eval x = x.all id := rfl
  have gateDef (A : Circuit) (i : ℕ) : gateAt A i = A.gates.getD i ⟨.or,[]⟩ := rfl
  have sizeDef (A : Circuit) : A.size = A.gates.length := rfl
  have incDef (X Y : Finset (Fin 13)) : incidenceInput X Y =
      (List.ofFn fun p : Fin 13 => decide (p∈X)) ++ List.ofFn (fun l : Fin 13 => decide (l∈Y)) := rfl
  have missDef (Q : Finset (Fin 13)) : missLines singerLines3 Q =
      Finset.univ.filter (fun l => Disjoint (singerLines3 l) Q) := rfl
  have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ D := by decide
  have pin (p l : Fin 13) : incidenceInput {p} {l} = P p l := by
    simp [incDef, P]
  have qok (Q : Finset (Fin 13)) (h : IsQuadrangle singerLines3 Q) : good Q := by
    refine ⟨h.1, fun l => ?_⟩
    have eq : Q.filter (fun p => p-l ∈ D) = Q ∩ singerLines3 l := by
      ext p
      simp [geom]
    rw [eq]
    exact h.2 l
  have negrow (Q : Finset (Fin 13)) : incidenceInput Q (missLines singerLines3 Q) = N Q := by
    change _ ++ _ = _ ++ _
    congr 1
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    simp [missDef, Finset.disjoint_right, geom]
  have pos (p l : Fin 13) (h : p ∈ singerLines3 l) : C.eval (ext (P p l)) = true :=
    fit.1 p l ((geom p l).mp h)
  have neg (Q : Finset (Fin 13)) (h : IsQuadrangle singerLines3 Q) : C.eval (ext (N Q)) = false :=
    fit.2 Q (qok Q h)
  have base (i : ℕ) (p l : Fin 13) : (P p l).getD i false = decide (i = p.val ∨ i = 13+l.val) := by
    by_cases ht : i < 26
    · have h : ∀ j : Fin 26, ∀ p l : Fin 13, (P p l).getD j.val false = decide (j.val=p.val ∨ j.val=13+l.val) := by decide +kernel
      exact h ⟨i,ht⟩ p l
    · rw [List.getD_eq_default _ _ (by simp [P];omega)]
      have hp := p.isLt
      have hl := l.isLt
      simp [show i≠p.val by omega,show i≠13+l.val by omega]
  have readExt (w : List Bool) (hw : w.length=26) (u : Fin 26) :
      (ext w).getD u.val false = w.getD u.val false := by
    simp [ext,List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw [hw]; exact u.isLt : u.val < w.length)]
  have hint (w : List Bool) (hw : w.length=26) :
      (ext w).getD 26 false = s.any (fun i => w.getD i false) := by
    simp [ext,List.getD_eq_getElem?_getD,hw]
  have plen (p l : Fin 13) : (P p l).length=26 := by simp [P]
  have nlen (Q : Finset (Fin 13)) : (N Q).length=26 := by simp [N]
  have sLen : s.length ≤ 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have sRead : ∀ j ∈ s, j < 26 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have t (p : Fin 13) (h : p ∈ singerLines3 p) : (ext (P p p)).getD out false = true := pos p p h
    have t2 := t 2 (by decide)
    have t3 := t 3 (by decide)
    by_cases h : out < 27
    · have z : ∀ j ∈ ([[],[0],[13],[0,1],[13,14],[0,13],[0,14]] : List (List ℕ)), ∀ i : Fin 27,
          (((P 2 2 ++ [j.any fun k => (P 2 2).getD k false]).getD i false) &&
           ((P 3 3 ++ [j.any fun k => (P 3 3).getD k false]).getD i false)) = false := by decide
      have hz := z s hs ⟨out,h⟩
      change ((ext (P 2 2)).getD out false && (ext (P 3 3)).getD out false) = false at hz
      rw [t2,t3] at hz
      exact False.elim (Bool.noConfusion hz)
    · rw [List.getD_eq_default _ _ (by simp [ext,plen]; omega)] at t2
      exact False.elim (Bool.noConfusion t2)
  | cons g gs =>
    let T : Circuit := ⟨gs,out⟩
    let E (w : List Bool) (b : Bool) := T.eval (ext w ++ [b])
    have tailMono : Monotone2 T := fun a ha => mono a (List.mem_cons_of_mem _ ha)
    have tailBack : ∀ (j : Fin gs.length) (i : ℕ), i ∈ (gs.get j).inputs → i < 28 + j.val := by
      intro j i hi
      have hh := read (⟨j.val+1,by simp⟩ : Fin (g::gs).length) i hi
      change i < 27 + (j.val + 1) at hh
      omega
    have rbT : ReadsBack 28 T := by
      intro j hj i hi
      exact tailBack ⟨j,hj⟩ i (by simpa [gateDef,T,List.getD_eq_getElem?_getD,hj] using hi)
    have gRead (i : ℕ) (hi : i ∈ g.inputs) : i < 27 := read ⟨0,by simp⟩ i hi
    have gm := mono g List.mem_cons_self
    have ep (p l : Fin 13) (hp : p ∈ singerLines3 l) : E (P p l) (step g (ext (P p l))) = true := pos p l hp
    have en (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) : E (N Q) (step g (ext (N Q))) = false := neg Q hq
    have finish (h : 62 ≤ T.size) : 63 ≤ (⟨g::gs,out⟩ : Circuit).size := by
      simpa [T,sizeDef] using Nat.succ_le_succ h
    apply finish
    have byUnion (k : List ℕ) (c : Bool) (hk : k.length ≤ 2) (hr : ∀ j ∈ k, j < 27)
        (eq : ∀ w, w.length=26 → step g (ext w) = (if c then true else k.any (fun j => (ext w).getD j false))) : 62 ≤ T.size := by
      let h : Gate := if c then ⟨.and, []⟩ else ⟨.or,k⟩
      let A : Circuit := ⟨⟨.or,s⟩ :: h :: gs, out⟩
      have hh : h.op ∈ ({GateOp.and,.or} : Set GateOp) ∧ h.inputs.length ≤ 2 := by cases c <;> simp [h,hk]
      have hm : Monotone2 A := by
        intro a ha
        change a ∈ _ :: _ :: gs at ha
        rcases List.mem_cons.mp ha with rfl|ha
        · exact ⟨Or.inr rfl,sLen⟩
        rcases List.mem_cons.mp ha with rfl|ha
        · exact hh
        · exact tailMono a ha
      have hb : ReadsBack 26 A := by
        intro j hj i hi
        cases j with
        | zero => exact sRead i (by simpa [gateDef,A,List.getD_eq_getElem?_getD] using hi)
        | succ j =>
          cases j with
          | zero =>
            have hi' : i ∈ h.inputs := by simpa [gateDef,A,List.getD_eq_getElem?_getD] using hi
            cases c
            · exact hr i (by simpa [h] using hi')
            · simp [h] at hi'
          | succ j =>
            have hj' : j < gs.length := by simpa [A] using hj
            have h' := tailBack ⟨j,hj'⟩ i (by simpa [gateDef,A,List.getD_eq_getElem?_getD,hj'] using hi)
            change i < 28 + j at h'
            omega
      have sim (w : List Bool) (hw : w.length=26) : A.eval w = E w (step g (ext w)) := by
        rw [eq w hw]
        have hh' : step h (ext w) = (if c then true else k.any (fun j => (ext w).getD j false)) := by
          cases c <;> simp [h,step,orEval,andEval,List.any_map]
        rw [← hh']
        have pre : step ⟨.or,s⟩ w = s.any (fun j => w.getD j false) := by simp [step,orEval,List.any_map]
        change T.eval ((w++[step ⟨.or,s⟩ w])++[step h (w++[step ⟨.or,s⟩ w])]) = _
        rw [pre]
      have pa : RightOnIncidentPairs singerLines3 A := by
        intro l p hp
        rw [pin,sim _ (plen p l)]
        exact ep p l hp
      have na (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) :
          A.eval (incidenceInput Q (missLines singerLines3 Q)) = false := by
        rw [negrow,sim _ (nlen Q)]
        exact en Q hq
      by_cases hl : HasLineDegree 26 (Finset.Ico 13 26) A 1
      · have bound := linear A hm pa na hl
        simpa [A,T,sizeDef] using bound
      · exact unions T s k c hs hm hb pa na hl
    let run (ks : List Gate) (w : List Bool) := ks.foldl (fun ws g => ws ++ [step g ws]) w
    have pushMono (x y : List Bool) (a b : Bool) (sz : x.length=y.length)
        (m : ∀ i, x.getD i false=true → y.getD i false=true) (ab : a=true → b=true) :
        ∀ i, (x++[a]).getD i false=true → (y++[b]).getD i false=true := by
      intro i hi
      by_cases lt : i < x.length
      · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left lt] at hi
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : i < y.length)]
        exact m i hi
      · by_cases eq : i = x.length
        · subst i
          simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right,sz] using
            ab (by simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right] using hi)
        · rw [List.getD_eq_default _ _ (by simp;omega)] at hi
          exact False.elim (Bool.noConfusion hi)
    have runMono (ks : List Gate) (hm : ∀ g ∈ ks, g.op ∈ ({GateOp.and,.or} : Set GateOp)) :
        ∀ x y : List Bool, x.length=y.length → (∀ i, x.getD i false=true → y.getD i false=true) →
          ∀ i, (run ks x).getD i false=true → (run ks y).getD i false=true := by
      induction ks with
      | nil => exact fun _ _ _ m => m
      | cons a rest ih =>
        intro x y len m
        apply ih (fun g hg => hm g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
        apply pushMono x y _ _ len m
        rcases hm a List.mem_cons_self with op|op
        · simp only [step,op,andEval,List.all_map,List.all_eq_true,Function.comp,id]
          intro ok j hj
          exact m j (ok j hj)
        · change a.op = GateOp.or at op
          simp only [step,op,orEval,List.any_map,List.any_eq_true,Function.comp,id]
          rintro ⟨j,hj,on⟩
          exact ⟨j,hj,m j on⟩
    have vary (w : List Bool) (a b : Bool) (ab : a=true → b=true) : E w a=true → E w b=true :=
      runMono gs (fun k hk => (tailMono k hk).1) _ _ (by simp)
        (pushMono (ext w) (ext w) a b rfl (fun _ h => h) ab) out
    have off (Q : Finset (Fin 13)) (hq : IsQuadrangle singerLines3 Q) : E (N Q) false=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have bad := vary (N Q) false (step g (ext (N Q))) (by simp) h
      rw [en Q hq] at bad
      exact False.elim (Bool.noConfusion bad)
    have singleton (p₀ l₀ : Fin 13) (he : p₀ ∈ singerLines3 l₀)
        (cover : ∀ p l : Fin 13, p ∈ singerLines3 l → step g (ext (P p l))=true → p=p₀ ∧ l=l₀) :
        62 ≤ T.size := by
      apply oneFlag T s p₀ l₀ hs he tailMono rbT
      · intro p l hp
        change E (incidenceInput {p} {l}) _ = true
        rw [pin]
        exact vary (P p l) _ _ (fun h => decide_eq_true (cover p l hp h)) (ep p l hp)
      · intro Q hq
        change E (incidenceInput Q (missLines singerLines3 Q)) false = false
        rw [negrow]
        exact off Q hq
    have double (sok : s=[0,1] ∨ s=[13,14])
        (cover : ∀ p l : Fin 13, p ∈ singerLines3 l → step g (ext (P p l))=true →
          (if s=[0,1] then decide (l=0 ∧ (p=0 ∨ p=1)) else decide (p=1 ∧ (l=0 ∨ l=1)))=true) :
        62 ≤ T.size := by
      apply twoFlags T s sok tailMono rbT
      · intro p l hp
        change E (incidenceInput {p} {l}) _ = true
        rw [pin]
        exact vary (P p l) _ _ (cover p l hp) (ep p l hp)
      · intro Q hq
        change E (incidenceInput Q (missLines singerLines3 Q)) false = false
        rw [negrow]
        exact off Q hq
    rcases gm.1 with hop|hop
    swap
    · change g.op=GateOp.or at hop
      apply byUnion g.inputs false gm.2 gRead
      intro w _
      simp [step,hop,orEval,List.any_map]
    change g.op=GateOp.and at hop
    rcases hin : g.inputs with _|⟨a,rest⟩
    · exact byUnion [] true (by decide) (by simp) (by simp [step,hop,hin,andEval])
    rcases rest with _|⟨b,rest⟩
    · exact byUnion [a] false (by simp) (by simpa [hin] using gRead)
        (by simp [step,hop,hin,andEval])
    have nilrest : rest=[] := by
      have len := gm.2
      simp [hin] at len
      exact len
    subst rest
    have ha := gRead a (by simp [hin])
    have hb := gRead b (by simp [hin])
    have andVal (w : List Bool) :
        step g (ext w) = ((ext w).getD a false && (ext w).getD b false) := by
      simp [step,hop,hin,andEval]
    have proj (i : ℕ) (hi : i < 27)
        (hh : ∀ w, w.length = 26 → step g (ext w) = (ext w).getD i false) : 62 ≤ T.size := by
      apply byUnion [i] false (by simp) (by simpa)
      simpa using hh
    by_cases eq : a=b
    · exact proj a ha (by simp [andVal,eq])
    let lit (u : ℕ) (p l : Fin 13) : Bool := decide (u=p.val ∨ u=13+l.val)
    have lone (u : Fin 26) (w : List Bool) (hw : w.length=26) (hm : u.val ∈ s) :
        ((ext w).getD u false && (ext w).getD 26 false) = (ext w).getD u false := by
      rw [hint _ hw,readExt _ hw u]
      cases e : w.getD u.val false with
      | false => rfl
      | true =>
        have h : s.any (fun j => w.getD j false) = true := List.any_eq_true.mpr ⟨u.val,hm,e⟩
        rw [h]
        rfl
    have mixed (u : Fin 26)
        (uv : ∀ w, step g (ext w) = ((ext w).getD u false && (ext w).getD 26 false)) :
        62 ≤ T.size := by
      by_cases mem : u.val ∈ s
      · exact proj u.val (by omega) (fun w hw => (uv w).trans (lone u w hw mem))
      have mask (p l : Fin 13) : step g (ext (P p l)) = (lit u p l && s.any (fun j => lit j p l)) := by
        rw [uv,readExt _ (plen p l) u,hint _ (plen p l),base]
        simp only [lit,base]
      by_cases sp : (s=[0,1] ∧ u.val=13) ∨ (s=[13,14] ∧ u.val=1)
      · apply double (sp.imp And.left And.left)
        intro p l hp on
        rw [mask] at on
        rcases sp with ⟨hs',hu⟩|⟨hs',hu⟩ <;> simp [hs',hu,lit] at on ⊢ <;> omega
      let edge (u j : ℕ) : Fin 13 × Fin 13 := (Fin.ofNat 13 (min u j), Fin.ofNat 13 (max u j - 13))
      let pick (t : List ℕ) (v : Fin 26) : Fin 13 × Fin 13 :=
        let cand := t.find? (fun j =>
          (decide (min v.val j < 13 ∧ 13 ≤ max v.val j) &&
            decide ((edge v.val j).1 - (edge v.val j).2 ∈ D)))
        cand.elim (0,0) (edge v.val)
      have table : ∀ t ∈ ([[],[0],[13],[0,1],[13,14],[0,13],[0,14]] : List (List ℕ)), ∀ v : Fin 26, v.val ∉ t →
          ¬ ((t=[0,1] ∧ v.val=13) ∨ (t=[13,14] ∧ v.val=1)) →
          (pick t v).1 - (pick t v).2 ∈ D ∧
          ∀ p l : Fin 13, lit v p l && t.any (fun j => lit j p l) = true →
            p-l ∈ D → p=(pick t v).1 ∧ l=(pick t v).2 := by decide +kernel
      obtain ⟨ok,cov⟩ := table s hs u mem sp
      apply singleton _ _ ((geom _ _).mpr ok)
      intro p l hp on
      exact cov p l ((mask p l).symm ▸ on) ((geom p l).mp hp)
    by_cases a26 : a=26
    · have hb' : b < 26 := by omega
      exact mixed ⟨b,hb'⟩ (by simp [andVal,a26,Bool.and_comm])
    by_cases b26 : b=26
    · exact mixed ⟨a,by omega⟩ (by simp [andVal,b26])
    have raw (p l : Fin 13) (on : step g (ext (P p l))=true) :
        (a=p.val ∨ a=13+l.val) ∧ (b=p.val ∨ b=13+l.val) := by
      rw [andVal,readExt _ (plen p l) ⟨a,by omega⟩,readExt _ (plen p l) ⟨b,by omega⟩,base,base] at on
      simpa using on
    by_cases existsOn : ∃ p l : Fin 13, p ∈ singerLines3 l ∧ step g (ext (P p l))=true
    · obtain ⟨p₀,l₀,inc,on⟩ := existsOn
      apply singleton p₀ l₀ inc
      intro p l _ h
      have r := raw p l h
      have s₀ := raw p₀ l₀ on
      constructor <;> apply Fin.ext <;> omega
    · exact singleton 0 0 (by decide) (fun p l hp h => (existsOn ⟨p,l,hp,h⟩).elim)
