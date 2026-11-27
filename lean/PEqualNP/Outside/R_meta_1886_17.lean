import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pin the extra AND to false or the extra OR to true on a three-state promise.
-- An active reader then folds to a constant or one earlier wire. The remaining circuit
-- has at most seventeen gates and takes the original ten bits in their ordinary order.
-- If the extra signal is unread, remove it and use the ordinary eighteen-gate bound.
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_1886_17
    (ordinary : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 18)
    (noAnd : ∀ D : Circuit, FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      (x 0 && x 1) = false ∧ D.eval (List.ofFn x) ≠ (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (noOr : ∀ D : Circuit, FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
      (x 0 || x 1) = true ∧ D.eval (List.ofFn x) ≠ (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  classical
  let step (xs : List Bool) (g : Gate) :=
    xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

  let run (gs : List Gate) (xs : List Bool) := gs.foldl step xs

  let index (n m : ℕ) (f : ℕ → ℕ) (j : ℕ) :=
    if j < n then f j else m + (j-n)

  let rename (r : ℕ → ℕ) (gs : List Gate) : List Gate :=
    gs.map fun g => ⟨g.op, g.inputs.map r⟩

  let legal (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have rename_legal (r : ℕ → ℕ) (gs : List Gate) (h : ∀ g ∈ gs, legal g) :
      ∀ g ∈ rename r gs, legal g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simpa [legal] using h a ha

  have run_len (gs : List Gate) (xs : List Bool) : (run gs xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp [run]
    | cons g gs ih => change (run gs (step xs g)).length = _; rw [ih]; simp [step]; omega

  have keep (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (run gs xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step xs g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

  have rebase (n m : ℕ) (f : ℕ → ℕ) (hf : ∀ j < n, f j < m)
      (gs : List Gate) (xs ys : List Bool) (hx : xs.length = n) (hy : ys.length = m)
      (agree : ∀ j < n, xs.getD j false = ys.getD (f j) false) (j : ℕ) :
      (run gs xs).getD j false = (run (rename (index n m f) gs) ys).getD (index n m f j) false := by
    let r := index n m f
    have advance (k : ℕ) : r (n+k) = m+k := by simp [r,index]
    have bounds (k i : ℕ) : r i < m+k ↔ i < n+k := by
      by_cases h : i < n
      · have hh := hf i h; simp [r,index,h]; omega
      · simp [r,index,h]; omega
    have lift (k : ℕ) (A B : List Bool) (a : Bool) (ha : A.length=n+k) (hb : B.length=m+k)
        (eq : ∀ i, A.getD i false = B.getD (r i) false) :
        ∀ i, (A++[a]).getD i false = (B++[a]).getD (r i) false := by
      intro i
      rcases lt_trichotomy i (n+k) with h|h|h
      · rw [List.getD_append _ _ _ _ (by omega),
            List.getD_append _ _ _ _ (hb ▸ (bounds k i).mpr h),eq]
      · subst i; rw [advance,←ha,←hb]; simp
      · have ge : m+(k+1) ≤ r i := Nat.le_of_not_gt (fun e => by have := (bounds (k+1) i).mp e; omega)
        rw [List.getD_eq_default _ _ (by simp [ha]; omega),
            List.getD_eq_default _ _ (by simp [hb]; omega)]
    have aux (ls : List Gate) (k : ℕ) (A B : List Bool) (ha : A.length=n+k) (hb : B.length=m+k)
        (eq : ∀ i, A.getD i false = B.getD (r i) false) :
        ∀ i, (run ls A).getD i false = (run (rename r ls) B).getD (r i) false := by
      induction ls generalizing k A B with
      | nil => exact eq
      | cons g gs ih =>
        let a := g.op.eval (g.inputs.map fun i => A.getD i false)
        have v : a = g.op.eval ((g.inputs.map r).map fun i => B.getD i false) := by
          dsimp only [a]
          apply congrArg g.op.eval
          simp only [List.map_map,Function.comp_def]
          exact List.map_congr_left (fun i _ => eq i)
        change ∀ i, (run gs (A++[a])).getD i false =
          (run (rename r gs) (B++[g.op.eval ((g.inputs.map r).map fun i => B.getD i false)])).getD (r i) false
        rw [←v]
        exact ih (k+1) _ _ (by simp [ha]; omega) (by simp [hb]; omega) (lift k A B a ha hb eq)
    apply aux gs 0 xs ys (by omega) (by omega) _ j
    intro i
    by_cases h : i < n
    · simpa [r,index,h] using agree i h
    · have hr : m ≤ r i := by simp [r,index,h]
      rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

  let active (g : Gate) (i : ℕ) : Prop := by
    classical
    exact i ∈ (if g.op = .not then g.inputs.take 1 else g.inputs)

  have invisible (gs : List Gate) (i : ℕ) (hn : ∀ g ∈ gs, ¬active g i)
      (xs ys : List Bool) (hl : xs.length=ys.length) (before : i < xs.length)
      (h : ∀ j, j ≠ i → xs.getD j false = ys.getD j false) :
      ∀ j, j ≠ i → (run gs xs).getD j false = (run gs ys).getD j false := by
    induction gs generalizing xs ys with
    | nil => exact h
    | cons g gs ih =>
      have ng := hn g List.mem_cons_self
      have rest : ∀ g ∈ gs, ¬active g i := fun g hg => hn g (List.mem_cons_of_mem _ hg)
      have ev : g.op.eval (g.inputs.map fun j => xs.getD j false) =
          g.op.eval (g.inputs.map fun j => ys.getD j false) := by
        by_cases hop : g.op = .not
        · rw [hop]; cases he : g.inputs with
          | nil => rfl
          | cons a bs =>
            have hai : a ≠ i := by intro e; apply ng; simp [active,hop,he,e]
            exact congrArg Bool.not (h a hai)
        · have miss : i ∉ g.inputs := by simpa [active,hop] using ng
          congr 1
          exact List.map_congr_left (fun a ha => h a (fun e => miss (e ▸ ha)))
      change ∀ j, j ≠ i → (run gs (step xs g)).getD j false = (run gs (step ys g)).getD j false
      apply ih rest _ _ (by simp [step,hl]) (by simp [step]; omega)
      intro j hj
      unfold step
      rw [ev]
      by_cases old : j < xs.length
      · rw [List.getD_append _ _ _ _ old,List.getD_append _ _ _ _ (hl ▸ old),h j hj]
      · rw [List.getD_append_right _ _ _ j (by omega),List.getD_append_right _ _ _ j (by omega),hl]

  have frozenValue {X : Type} (g : Gate) (ok : legal g) (uses : active g 10)
      (A : ℕ → X → Bool) (c : Bool) (pin : ∀ x, A 10 x = c) :
      (∃ b : Bool, ∀ x, g.op.eval (g.inputs.map fun i => A i x) = b) ∨
      ∃ j : ℕ, ∀ x, g.op.eval (g.inputs.map fun i => A i x) = A j x := by
    have hand (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have hor (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    have hnot (a b : Bool) : GateOp.not.eval [a,b] = (!a) := rfl
    obtain ⟨op,len⟩ := ok
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases he : g.inputs with _ | ⟨u,us⟩
    · simp [active,he] at uses
    rcases hu : us with _ | ⟨v,vs⟩
    · have e : u=10 := by
        by_cases hop : g.op = .not <;> simpa [active,he,hu,hop,eq_comm] using uses
      subst u
      left; exact ⟨g.op.eval [c],by simp [pin]⟩
    have vsnil : vs = [] := by simpa [he,hu] using len
    subst vs
    rcases op with op | op | op
    · have h : 10=u ∨ 10=v := by simpa [active,op,he,hu] using uses
      rcases h with rfl|rfl <;> cases hc : c
      · left; exact ⟨false,by simp [op,hand,pin,hc]⟩
      · right; exact ⟨v,by simp [op,hand,pin,hc]⟩
      · left; exact ⟨false,by simp [op,hand,pin,hc]⟩
      · right; exact ⟨u,by simp [op,hand,pin,hc]⟩
    · have h : 10=u ∨ 10=v := by simpa [active,op,he,hu] using uses
      rcases h with rfl|rfl <;> cases hc : c
      · right; exact ⟨v,by simp [op,hor,pin,hc]⟩
      · left; exact ⟨true,by simp [op,hor,pin,hc]⟩
      · right; exact ⟨u,by simp [op,hor,pin,hc]⟩
      · left; exact ⟨true,by simp [op,hor,pin,hc]⟩
    · have h : 10=u := by simpa [active,op,he,hu] using uses
      subst u
      left; exact ⟨!c,by simp [op,hnot,pin]⟩

  have specialize (pre post : List Gate) (g : Gate) (out : ℕ)
      (legalAll : ∀ a ∈ pre ++ g :: post, legal a) (hit : active g 10)
      (p : Fin 10 → Fin 10) (c : Bool) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = pre.length+post.length ∧
        ∀ x : Fin 10 → Bool, D.eval ([false,true] ++ List.ofFn x) =
          (Circuit.mk (pre ++ g::post) out).eval (List.ofFn (x ∘ p) ++ [c]) := by
    classical
    let inp (x : Fin 10 → Bool) := List.ofFn (x ∘ p) ++ [c]
    let bank (x : Fin 10 → Bool) := [false,true] ++ List.ofFn x
    let code (b : Bool) : ℕ := if b then 1 else 0
    let f (j : ℕ) : ℕ := if h : j < 10 then 2+(p ⟨j,h⟩).val else code c
    have bound (j : ℕ) (_ : j<11) : f j < 12 := by
      unfold f; split_ifs with h
      · have := (p ⟨j,h⟩).isLt; omega
      · cases c <;> decide
    have start (x : Fin 10 → Bool) (j : ℕ) (hj : j < 11) :
        (inp x).getD j false = (bank x).getD (f j) false := by
      by_cases lo : j<10
      · rw [show f j=2+(p ⟨j,lo⟩).val by simp [f,lo]]
        change (List.ofFn (x ∘ p) ++ [c]).getD j false =
          ([false,true] ++ List.ofFn x).getD (2+_) false
        rw [List.getD_append _ _ _ _ (by simpa using lo),
            List.getD_append_right _ _ _ _ (by simp)]
        have diff : 2+(p ⟨j,lo⟩).val - [false,true].length = (p ⟨j,lo⟩).val := by simp
        rw [diff,List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using lo),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (p ⟨j,lo⟩).isLt)]
        simp only [List.getElem_ofFn,Function.comp_apply]
      · have ej : j=10 := by omega
        subst j
        cases c <;> simp [inp,bank,code,f,List.getD_append_right]
    let P := rename (index 11 12 f) pre
    let A (x : Fin 10 → Bool) := run pre (inp x)
    let B (x : Fin 10 → Bool) := run P (bank x)
    let n := 11+pre.length
    let m := 12+pre.length
    have la x : (A x).length = n := by simp [A,run_len,inp,n]
    have lb x : (B x).length = m := by simp [B,run_len,P,rename,bank,m]
    have init (x : Fin 10 → Bool) (j : ℕ) :
        (A x).getD j false = (B x).getD (index 11 12 f j) false := by
      exact rebase 11 12 f bound pre _ _ (by simp [inp]) (by simp [bank]) (start x) j
    have kcode (b : Bool) : code b < m := by cases b <;> simp [code,m] <;> omega
    have value (b : Bool) (x : Fin 10 → Bool) : (B x).getD (code b) false = b := by
      rw [show B x = run P (bank x) from rfl,keep P _ _ (by cases b <;> simp [code,bank])]
      cases b <;> rfl
    let rep (j : ℕ) := if j<n then index 11 12 f j else 0
    have rb (j : ℕ) : rep j < m := by
      unfold rep index; split_ifs with h l
      · have := bound j (by omega); dsimp [m]; omega
      · dsimp [n] at h; dsimp [m]; omega
      · simp [m]
    have rr (x : Fin 10 → Bool) (j : ℕ) : (A x).getD j false = (B x).getD (rep j) false := by
      by_cases h : j<n
      · simpa [rep,h] using init x j
      · rw [List.getD_eq_default _ _ (by rw [la]; omega)]
        simpa [rep,h,code] using (value false x).symm
    have fixed (x : Fin 10 → Bool) : (A x).getD 10 false = c := by
      rw [show A x = run pre (inp x) from rfl,keep _ _ _ (by simp [inp])]
      simp [inp,List.getD_append_right]
    have gok := legalAll g (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨q,hq,qv⟩ : ∃ q < m, ∀ x, g.op.eval (g.inputs.map fun i => (A x).getD i false) =
        (B x).getD q false := by
      rcases frozenValue g gok hit (fun i x => (A x).getD i false) c fixed with ⟨b,hb⟩|⟨j,hj⟩
      · exact ⟨code b,kcode b, fun x => (hb x).trans (value b x).symm⟩
      · exact ⟨rep j,rb j,fun x => (hj x).trans (rr x j)⟩
    let after (j : ℕ) := if j<n then rep j else q
    have ab (j : ℕ) (_ : j<n+1) : after j < m := by dsimp [after]; split <;> first | apply rb | exact hq
    have av (x : Fin 10 → Bool) (j : ℕ) (hj : j<n+1) :
        (step (A x) g).getD j false = (B x).getD (after j) false := by
      by_cases h : j<n
      · unfold step
        rw [List.getD_append _ _ _ _ (by rw [la]; exact h)]
        simpa only [after,if_pos h] using rr x j
      · have e : j=n := by omega
        subst j; simp only [after,lt_irrefl,↓reduceIte]
        unfold step
        rw [←la x]; simpa using qv x
    let s := index (n+1) m after
    let D := Circuit.mk (P ++ rename s post) (s out)
    refine ⟨D,?_,?_,?_⟩
    · intro u hu
      change u ∈ P ++ rename s post at hu
      rcases List.mem_append.mp hu with hu|hu
      · exact rename_legal _ _ (fun a ha => legalAll a (List.mem_append_left _ ha)) u hu
      · exact rename_legal _ _ (fun a ha => legalAll a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))) u hu
    · change (P ++ rename s post).length = _
      simp [P,rename]
    · intro x
      have eq := rebase (n+1) m after ab post (step (A x) g) (B x)
        (by simp [step,la]) (lb x) (av x) out
      change (run (P ++ rename s post) (bank x)).getD (s out) false =
        (run (pre ++ g::post) (inp x)).getD out false
      simp only [run,List.foldl_append,List.foldl_cons]
      exact eq.symm

  have plain (C : Circuit) (p : Fin 10 → Fin 10) (bit : (Fin 10 → Bool) → Bool)
      (ok : FanInTwo C) (noRead : ∀ g ∈ C.gates, ¬active g 10) (notOut : C.output ≠ 10) :
      ∃ D : Circuit, FanInTwo D ∧ D.size=C.size ∧
        ∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p) ++ [bit x]) := by
    let f (j : ℕ) := if h : j < 10 then (p ⟨j,h⟩).val else 0
    let r := index 11 10 f
    let D := Circuit.mk (rename r C.gates) (r C.output)
    have bound (j : ℕ) (_ : j<11) : f j < 10 := by
      dsimp [f]; split_ifs with h
      · exact (p ⟨j,h⟩).isLt
      · decide
    refine ⟨D,rename_legal r C.gates ok,?_,?_⟩
    · change (rename r C.gates).length = C.gates.length
      simp [rename]
    intro x
    let A := List.ofFn (x ∘ p) ++ [x 0]
    let B := List.ofFn (x ∘ p) ++ [bit x]
    have source (j : ℕ) (hj : j<11) : A.getD j false = (List.ofFn x).getD (f j) false := by
      by_cases h : j<10
      · change (List.ofFn (x ∘ p) ++ [x 0]).getD j false = _
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using h),
          show f j=(p ⟨j,h⟩).val by simp [f,h],
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (p ⟨j,h⟩).isLt)]
        simp only [List.getElem_ofFn,Function.comp_apply]
      · have e : j=10 := by omega
        subst j; simp [A,f,List.getD_append_right]
    have same (j : ℕ) (hj : j≠10) : A.getD j false = B.getD j false := by
      by_cases h : j<10
      · unfold A B; rw [List.getD_append _ _ _ _ (by simpa using h),List.getD_append _ _ _ _ (by simpa using h)]
      · rw [List.getD_eq_default _ _ (by simp [A]; omega),List.getD_eq_default _ _ (by simp [B]; omega)]
    have h1 := rebase 11 10 f bound C.gates A (List.ofFn x) (by simp [A]) (by simp) source C.output
    have h2 := invisible C.gates 10 noRead A B (by simp [A,B]) (by simp [A]) same C.output notOut
    exact h1.symm.trans h2

  have discardConstants (C : Circuit) (ok : FanInTwo C) (small : C.size ≤ 17) :
      ∃ E : Circuit, FanInTwo E ∧ E.size ≤ 17 ∧
        ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = C.eval ([false,true] ++ List.ofFn x) := by
    let raw (l : List ℕ) := (l.filter fun i => decide (2 ≤ i)).map fun i => i-2
    have ar (l : List ℕ) : (raw l).length ≤ l.length := by simp [raw,List.length_filter_le]
    have allVal (l : List ℕ) (w : List Bool) :
        (l.map (fun j => ([false,true]++w).getD j false)).all id =
        ((!decide (0 ∈ l)) && ((raw l).map fun j => w.getD j false).all id) := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp [raw] at ih
        rcases a with _|⟨_|a⟩ <;> simp [raw,List.filter_cons,ih,Bool.and_left_comm,Bool.and_assoc]
    have anyVal (l : List ℕ) (w : List Bool) :
        (l.map (fun j => ([false,true]++w).getD j false)).any id =
        (decide (1 ∈ l) || ((raw l).map fun j => w.getD j false).any id) := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp [raw] at ih
        rcases a with _|⟨_|a⟩ <;> simp [raw,List.filter_cons,ih,Bool.or_left_comm,Bool.or_assoc]
    have oneGate (g : Gate) (hg : legal g) : ∃ t : Gate, legal t ∧
        ∀ w : List Bool, t.op.eval (t.inputs.map fun j => w.getD j false) =
        g.op.eval (g.inputs.map fun j => ([false,true]++w).getD j false) := by
      obtain ⟨hop,len⟩ := hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
      rcases hop with e|e|e
      · by_cases z : 0 ∈ g.inputs
        · refine ⟨⟨.or,[]⟩,by simp [legal],?_⟩
          intro w; rw [e]; exact (by simpa [z] using (allVal g.inputs w).symm :
            false = (g.inputs.map fun j => ([false,true]++w).getD j false).all id)
        · refine ⟨⟨.and,raw g.inputs⟩,⟨by simp,(ar _).trans len⟩,?_⟩
          intro w; rw [e]
          change ((raw g.inputs).map fun j => w.getD j false).all id =
            (g.inputs.map fun j => ([false,true]++w).getD j false).all id
          simpa only [decide_eq_false z,Bool.not_false,Bool.true_and] using (allVal g.inputs w).symm
      · by_cases z : 1 ∈ g.inputs
        · refine ⟨⟨.and,[]⟩,by simp [legal],?_⟩
          intro w; rw [e]; exact (by simpa [z] using (anyVal g.inputs w).symm :
            true = (g.inputs.map fun j => ([false,true]++w).getD j false).any id)
        · refine ⟨⟨.or,raw g.inputs⟩,⟨by simp,(ar _).trans len⟩,?_⟩
          intro w; rw [e]
          change ((raw g.inputs).map fun j => w.getD j false).any id =
            (g.inputs.map fun j => ([false,true]++w).getD j false).any id
          simpa only [decide_eq_false z,Bool.false_or] using (anyVal g.inputs w).symm
      · cases l : g.inputs with
        | nil => exact ⟨⟨.and,[]⟩,by simp [legal],fun w => by rw [e]; rfl⟩
        | cons a l' =>
          rcases a with _|⟨_|a⟩
          · exact ⟨⟨.and,[]⟩,by simp [legal],fun w => by rw [e]; rfl⟩
          · exact ⟨⟨.or,[]⟩,by simp [legal],fun w => by rw [e]; rfl⟩
          · exact ⟨⟨.not,[a]⟩,by simp [legal],fun w => by rw [e]; rfl⟩
    have simulate (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
        ∃ ts : List Gate, (∀ t ∈ ts, legal t) ∧ ts.length=gs.length ∧
        ∀ w : List Bool, run gs ([false,true]++w) = [false,true]++run ts w := by
      induction gs with
      | nil => exact ⟨[],by simp,rfl,fun _ => rfl⟩
      | cons g gs ih =>
        obtain ⟨t,ht,he⟩ := oneGate g (hg g List.mem_cons_self)
        obtain ⟨ts,hts,hsize,runEq⟩ := ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
        refine ⟨t::ts,?_,by simp [hsize],?_⟩
        · intro a ha; rcases List.mem_cons.mp ha with rfl|ha; exact ht; exact hts a ha
        · intro w
          change run gs (step ([false,true]++w) g) = [false,true] ++ run ts (step w t)
          have s : step ([false,true]++w) g = [false,true]++step w t := by
            unfold step; rw [he, List.append_assoc]
          rw [s,runEq]
    obtain ⟨ts,ht,sz,sim⟩ := simulate C.gates ok
    cases ho : C.output with
    | zero =>
      refine ⟨⟨[⟨.or,[]⟩],10⟩,?_,by decide,?_⟩
      · intro g hg; simp at hg; subst g; simp
      · intro x
        change (List.ofFn x ++ [false]).getD 10 false =
          (run C.gates ([false,true]++List.ofFn x)).getD C.output false
        rw [sim,ho]; simp
    | succ k =>
      cases k with
      | zero =>
        refine ⟨⟨[⟨.and,[]⟩],10⟩,?_,by decide,?_⟩
        · intro g hg; simp at hg; subst g; simp
        · intro x
          change (List.ofFn x ++ [true]).getD 10 false =
            (run C.gates ([false,true]++List.ofFn x)).getD C.output false
          rw [sim,ho]; simp
      | succ j =>
        refine ⟨⟨ts,j⟩,ht,?_,?_⟩
        · change ts.length ≤ 17; rw [sz]; exact small
        · intro x
          change (run ts (List.ofFn x)).getD j false = (run C.gates ([false,true]++List.ofFn x)).getD C.output false
          rw [sim,ho]; rfl

  intro C p b ok small
  let F := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let bit (x : Fin 10 → Bool) := if b = true then x 0 && x 1 else x 0 || x 1
  by_contra! computes
  change ∀ x, C.eval (List.ofFn (x ∘ p) ++ [bit x]) = F x at computes
  have notOut : C.output ≠ 10 := by
    intro e
    let x : Fin 10 → Bool := ![false,false,true,true,false,false,false,false,false,false]
    have fx : F x = true := rfl
    have bx : bit x = false := by cases b <;> rfl
    have obs := computes x
    change (run C.gates (List.ofFn (x ∘ p) ++ [bit x])).getD C.output false = F x at obs
    rw [e,keep _ _ _ (by simp),fx,bx] at obs
    simpa [List.getD_append_right] using obs
  by_cases used : ∃ g ∈ C.gates, active g 10
  · obtain ⟨g,hg,hit⟩ := used
    obtain ⟨pre,post,he⟩ := List.append_of_mem hg
    have lg : ∀ a ∈ pre ++ g::post, legal a := by rw [←he]; exact ok
    have budget : pre.length + post.length ≤ 17 := by
      change C.gates.length ≤ 18 at small; rw [he,List.length_append,List.length_cons] at small; omega
    have runC : Circuit.mk (pre ++ g::post) C.output = C := by rw [←he]
    cases hb : b
    · obtain ⟨D,hl,hs,hd⟩ := specialize pre post g C.output lg hit p true
      obtain ⟨E,et,es,ee⟩ := discardConstants D hl (hs ▸ budget)
      obtain ⟨x,hx,hbad⟩ := noOr E et es
      apply hbad
      have t : bit x = true := by simpa [bit,hb] using hx
      exact (ee x).trans ((hd x).trans (by rw [runC,←t]; exact computes x))
    · obtain ⟨D,hl,hs,hd⟩ := specialize pre post g C.output lg hit p false
      obtain ⟨E,et,es,ee⟩ := discardConstants D hl (hs ▸ budget)
      obtain ⟨x,hx,hbad⟩ := noAnd E et es
      apply hbad
      have t : bit x = false := by simpa [bit,hb] using hx
      exact (ee x).trans ((hd x).trans (by rw [runC,←t]; exact computes x))
  · push Not at used
    obtain ⟨D,hl,hs,hd⟩ := plain C p bit ok used notOut
    exact ordinary ⟨D,hl,hs ▸ small,fun x => (hd x).trans (computes x)⟩
