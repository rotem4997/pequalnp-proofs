import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Eliminate every unary inverter by recording the polarity at each binary gate input.
-- The first input already has both polarities. Other complemented sources can be shared.
-- Wire nine in the signed program is false, including when a forward read was absent.
theorem PEqualNP.Outside.R_meta_1665_41 :
  (∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
    (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool), b ≤ 10 →
    (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
      w x (10 + j.val) = if op j then (val (left j) && val (right j))
        else (val (left j) || val (right j))) →
    ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (b : ℕ) (op : Fin b → Bool) (left right : Fin b → ℕ × Bool)
    (out : ℕ × Bool) (paid : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
    paid.card ≤ 3 → b + paid.card ≤ 14 →
    (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + b →
    (let ok := fun p : ℕ × Bool => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid
     ok out ∧ ∀ j, ok (left j) ∧ ok (right j)) →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let val := fun p : ℕ × Bool => Bool.xor (w x p.1) p.2
      w x (10 + j.val) = if op j then (val (left j) && val (right j))
        else (val (left j) || val (right j))) →
    ∃ x : Fin 9 → Bool, Bool.xor (w x out.1) out.2 ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  ∀ C : Circuit, FanInTwo C →
    (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
    circuitFun 9 C = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro unrestricted few C fan first correct
  classical
  by_contra insufficient
  have small : C.size ≤ 15 := by omega
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let Pin := ℕ × Bool
  let Node := Bool × Pin × Pin
  let neg := fun (p : Pin) => (p.1,!p.2)
  let c0 : Pin := (9,false)
  let takePin := fun (w : List Bool) (p : Pin) => Bool.xor (w.getD p.1 false) p.2
  let bindGate := fun (w : List Bool) (g : Node) =>
    w ++ [if g.1 then (takePin w g.2.1 && takePin w g.2.2)
          else (takePin w g.2.1 || takePin w g.2.2)]
  let run := fun (P : List Node) (x : Fin 9 → Bool) => P.foldl bindGate (List.ofFn x ++ [false])
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0)]
  let old := fun (gs : List Gate) (x : Fin 9 → Bool) => gs.foldl step (seed x)
  let allowed := fun (S : Finset ℕ) (p : Pin) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ S
  let ordered := fun (P : List Node) => ∀ j : Fin P.length,
    (P.get j).2.1.1 < 10 + j.val ∧ (P.get j).2.2.1 < 10 + j.val
  let state := fun (gs : List Gate) (P : List Node) (S : Finset ℕ) (M : List Pin) =>
    P.length + S.card ≤ gs.length ∧ ordered P ∧
    (∀ g ∈ P, allowed S g.2.1 ∧ allowed S g.2.2) ∧
    (∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) ∧
    ∀ x, old gs x = M.map (takePin (run P x))
  have more {α : Type} (op : List Bool → α → Bool) (gs : List α) (w : List Bool) :
      ∃ t, gs.foldl (fun v g => v ++ [op v g]) w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨t,he,hl⟩ := ih (w ++ [op w g])
      exact ⟨op w g :: t, by simp only [List.foldl_cons, he, List.append_assoc,
        List.cons_append, List.nil_append], by simp [hl]⟩
  have shape (P : List Node) (x : Fin 9 → Bool) :
      ∃ t, run P x = (List.ofFn x ++ [false]) ++ t ∧ t.length = P.length := by
    exact more (fun w (g : Node) => if g.1 then (takePin w g.2.1 && takePin w g.2.2)
      else (takePin w g.2.1 || takePin w g.2.2)) P _
  have width (P : List Node) (x : Fin 9 → Bool) : (run P x).length = 10 + P.length := by
    obtain ⟨t,he,hl⟩ := shape P x
    simp [he,hl]
    omega
  have constZero (P : List Node) (x : Fin 9 → Bool) : (run P x).getD 9 false = false := by
    obtain ⟨t,he,_⟩ := shape P x
    rw [he, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp
  have falsePin (P : List Node) (x : Fin 9 → Bool) : takePin (run P x) c0 = false := by
    change ((run P x).getD 9 false ^^ false) = false
    rw [constZero]
    rfl
  have complemented (w : List Bool) (p : Pin) : takePin w (neg p) = !(takePin w p) := by
    simp only [takePin,neg]
    cases w.getD p.1 false <;> cases p.2 <;> rfl
  have keepAllowed {S T : Finset ℕ} (h : S ⊆ T) {p : Pin} (a : allowed S p) : allowed T p := by
    intro on
    obtain z | k | mem := a on
    · exact Or.inl z
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr (h mem))
  have getOK (P : List Node) (S : Finset ℕ) (M : List Pin)
      (hm : ∀ p ∈ M, p.1 < 10 + P.length ∧ allowed S p) (i : ℕ) :
      (M.getD i c0).1 < 10 + P.length ∧ allowed S (M.getD i c0) := by
    by_cases hi : i < M.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hm _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨by simp [c0]; omega, by simp [allowed,c0]⟩
  have longer {P : List Node} (hP : ordered P) (g : Node)
      (ha : g.2.1.1 < 10 + P.length) (hb : g.2.2.1 < 10 + P.length) :
      ordered (P ++ [g]) := by
    intro j
    change (P ++ [g])[j.val].2.1.1 < 10 + j.val ∧ (P ++ [g])[j.val].2.2.1 < 10 + j.val
    by_cases hi : j.val < P.length
    · rw [List.getElem_append_left hi]
      exact hP ⟨j.val,hi⟩
    · have eq : j.val = P.length := by have hj := j.isLt; simp at hj; omega
      simp only [eq]
      rw [List.getElem_append_right (Nat.le_refl P.length)]
      simp only [Nat.sub_self,List.getElem_cons_zero]
      exact ⟨ha,hb⟩
  have compile (gs : List Gate)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
      ∃ P S M, state gs P S M := by
    induction gs using List.reverseRecOn with
    | nil =>
      let m : List Pin := [(0,false),(1,false),(2,false),(3,false),(4,false),
        (5,false),(6,false),(7,false),(8,false),(0,true)]
      refine ⟨[],∅,m,by simp,fun j => Fin.elim0 j,by simp,?_,?_⟩
      · simp [m,allowed]
      · intro x
        simp [old,seed,m,takePin,run,List.getD]
    | append_singleton gs gate ih =>
      obtain ⟨P,S,M,budget,order,paid,aliases,sem⟩ := ih (fun g hg => ok g (by simp [hg]))
      obtain ⟨hop,short⟩ := ok gate (by simp)
      let source := fun i => M.getD i c0
      have sourceOK := getOK P S M aliases
      have reads (x : Fin 9 → Bool) (i : ℕ) :
          (old gs x).getD i false = takePin (run P x) (source i) := by
        rw [sem x, ← falsePin P x]
        exact List.getD_map M c0 (takePin (run P x))
      let v := fun x => gate.op.eval (gate.inputs.map fun i => (old gs x).getD i false)
      have appendOld (x : Fin 9 → Bool) : old (gs ++ [gate]) x = old gs x ++ [v x] := by
        simp only [old, List.foldl_append, List.foldl_cons, List.foldl_nil, step, v]
      have wire (p : Pin) (T : Finset ℕ) (subset : S ⊆ T) (cost : T.card ≤ S.card + 1)
          (hp : p.1 < 10 + P.length) (legal : allowed T p)
          (value : ∀ x, v x = takePin (run P x) p) :
          ∃ P S M, state (gs ++ [gate]) P S M := by
        refine ⟨P,T,M ++ [p],?_,order,?_,?_,?_⟩
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro g hg
          exact ⟨keepAllowed subset (paid g hg).1, keepAllowed subset (paid g hg).2⟩
        · intro a ha
          obtain oldmem | last := List.mem_append.mp ha
          · exact ⟨(aliases a oldmem).1,keepAllowed subset (aliases a oldmem).2⟩
          · simpa only [List.mem_singleton.mp last] using And.intro hp legal
        · intro x
          rw [appendOld,sem,value]
          simp
      have binary (b : Bool) (i j : ℕ)
          (value : ∀ x, v x =
            if b then (takePin (run P x) (source i) && takePin (run P x) (source j))
            else (takePin (run P x) (source i) || takePin (run P x) (source j))) :
          ∃ P S M, state (gs ++ [gate]) P S M := by
        let g : Node := (b,source i,source j)
        let nextPin : Pin := (10 + P.length,false)
        have appendVals (x) : run (P ++ [g]) x = run P x ++ [v x] := by
          simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil,bindGate,g]
          rw [value]
        refine ⟨P ++ [g],S,M ++ [nextPin],?_,longer order g (sourceOK i).1 (sourceOK j).1,?_,?_,?_⟩
        · simp only [List.length_append,List.length_singleton]
          omega
        · intro k hk
          obtain h | h := List.mem_append.mp hk
          · exact paid k h
          · have e : k = g := List.mem_singleton.mp h
            exact e ▸ ⟨(sourceOK i).2,(sourceOK j).2⟩
        · intro a ha
          obtain h | h := List.mem_append.mp ha
          · exact ⟨by have z := (aliases a h).1; simp; omega, (aliases a h).2⟩
          · have e : a = nextPin := List.mem_singleton.mp h
            subst a
            exact ⟨by simp [nextPin],by simp [allowed,nextPin]⟩
        · intro x
          rw [appendOld,sem,List.map_append]
          have kept : M.map (takePin (run P x)) = M.map (takePin (run (P ++ [g]) x)) := by
            apply List.map_congr_left
            intro a ha
            have lt := (aliases a ha).1
            rw [appendVals]
            have bound : a.1 < (run P x).length := by rw [width]; exact lt
            exact congrArg (fun z => Bool.xor z a.2)
              (List.getD_append (run P x) [v x] false a.1 bound).symm
          rw [kept]
          have tip : takePin (run (P ++ [g]) x) nextPin = v x := by
            rw [appendVals]
            simp only [nextPin,takePin,Bool.xor_false]
            rw [List.getD_append_right _ _ _ _ (by rw [width])]
            simp [width]
          simp [tip]
      have cBound : c0.1 < 10 + P.length := by dsimp [c0]; omega
      rcases hop with ha | ho | hn
      · cases he : gate.inputs with
        | nil =>
          apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
          intro x
          change gate.op.eval _ = _
          rw [ha,he,complemented,falsePin]
          rfl
        | cons i is =>
          cases is with
          | nil =>
            apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
            intro x
            change gate.op.eval _ = _
            rw [ha,he]
            have unary (u : Bool) : GateOp.and.eval [u] = u := by cases u <;> rfl
            simpa only [List.map_cons,List.map_nil,unary] using reads x i
          | cons j rest =>
            have none : rest = [] := by simpa [he] using short
            subst rest
            apply binary true i j
            intro x
            have pair (u w : Bool) : GateOp.and.eval [u,w] = (u && w) := by cases u <;> cases w <;> rfl
            simp only [v,ha,he,List.map_cons,List.map_nil,pair,reads,ite_true]
      · cases he : gate.inputs with
        | nil =>
          apply wire c0 S (fun _ h => h) (by omega) cBound (by simp [allowed,c0])
          intro x
          change gate.op.eval _ = _
          rw [ho,he,falsePin]
          rfl
        | cons i is =>
          cases is with
          | nil =>
            apply wire (source i) S (fun _ h => h) (by omega) (sourceOK i).1 (sourceOK i).2
            intro x
            have unary (u : Bool) : GateOp.or.eval [u] = u := by cases u <;> rfl
            simpa only [v,ho,he,List.map_cons,List.map_nil,unary] using reads x i
          | cons j rest =>
            have none : rest = [] := by simpa [he] using short
            subst rest
            apply binary false i j
            intro x
            have pair (u w : Bool) : GateOp.or.eval [u,w] = (u || w) := by cases u <;> cases w <;> rfl
            simp only [v,ho,he,List.map_cons,List.map_nil,pair,reads,Bool.false_eq_true,ite_false]
      · cases he : gate.inputs with
        | nil =>
          apply wire (neg c0) S (fun _ h => h) (by omega) cBound (by simp [allowed,neg,c0])
          intro x
          change gate.op.eval _ = _
          rw [hn,he,complemented,falsePin]
          rfl
        | cons i is =>
          let a := source i
          apply wire (neg a) (insert a.1 S) (Finset.subset_insert _ _) (Finset.card_insert_le _ _)
            (sourceOK i).1 (by intro _; exact Or.inr (Or.inr (Finset.mem_insert_self _ _)))
          intro x
          have flip (u : Bool) (xs : List Bool) : GateOp.not.eval (u::xs) = !u := rfl
          simp only [v,hn,he,List.map_cons,flip,reads,complemented,a]
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    have impossible := first (fun _ => false)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at impossible
    rw [List.getD_eq_default _ false (by simp)] at impossible
    contradiction
  | cons g tail =>
    have firstValue (x : Fin 9 → Bool) : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = !(x 0) := by
      let ws := List.ofFn x
      let v := g.op.eval (g.inputs.map fun i => ws.getD i false)
      obtain ⟨t,h,_⟩ := more (fun w (a : Gate) => a.op.eval (a.inputs.map fun i => w.getD i false))
        tail (ws ++ [v])
      have hx := first x
      change (tail.foldl step (ws ++ [v])).getD 9 false = _ at hx
      rw [h,List.getD_append _ _ _ _ (by simp [ws]),List.getD_append_right _ _ _ _ (by simp [ws])] at hx
      simpa [ws,v] using hx
    have final (x) : (old tail x).getD o false = target x := by
      have hx := congrFun correct x
      change (tail.foldl step (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = _ at hx
      rw [firstValue] at hx
      exact hx
    have ok : ∀ a ∈ tail, (a.op = .and ∨ a.op = .or ∨ a.op = .not) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      have h := fan a (by simp [ha])
      exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h.1,h.2⟩
    obtain ⟨P,S,M,budget,back,pins,aliases,sem⟩ := compile tail ok
    let out := M.getD o c0
    have outOK := getOK P S M aliases o
    have agrees (x) : takePin (run P x) out = target x := by
      have hx := final x
      rw [sem,← falsePin P x] at hx
      exact (List.getD_map M c0 (takePin (run P x))).symm.trans hx
    have cap : P.length + S.card ≤ 14 := by
      change (g :: tail).length ≤ 15 at small
      simp only [List.length_cons] at small
      omega
    let left := fun j : Fin P.length => (P.get j).2.1
    let right := fun j : Fin P.length => (P.get j).2.2
    let op := fun j : Fin P.length => (P.get j).1
    let table := fun (x : Fin 9 → Bool) (i : ℕ) => (run P x).getD i false
    have inputBits (x : Fin 9 → Bool) (i : Fin 9) : table x i.val = x i := by
      obtain ⟨t,h,_⟩ := shape P x
      change (run P x).getD i.val false = _
      rw [h, List.getD_append _ _ false _ (by simp; omega),
        List.getD_append _ _ false _ (by simp),
        List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have gateTable (x : Fin 9 → Bool) (j : Fin P.length) :
        table x (10 + j.val) =
          if op j then (takePin (run P x) (left j) && takePin (run P x) (right j))
          else (takePin (run P x) (left j) || takePin (run P x) (right j)) := by
      let before := run (P.take j.val) x
      let g := P.get j
      let v := if g.1 then (takePin before g.2.1 && takePin before g.2.2)
               else (takePin before g.2.1 || takePin before g.2.2)
      have preLength : before.length = 10 + j.val := by
        rw [show before = run (P.take j.val) x from rfl, width, List.length_take, Nat.min_eq_left j.isLt.le]
      have decomposition : P = P.take j.val ++ g :: P.drop (j.val + 1) := by
        simpa only [g, List.get_eq_getElem, List.drop_eq_getElem_cons j.isLt]
          using (List.take_append_drop j.val P).symm
      obtain ⟨extra,he,_⟩ := more (fun a (k : Node) =>
        if k.1 then (takePin a k.2.1 && takePin a k.2.2) else (takePin a k.2.1 || takePin a k.2.2))
        (P.drop (j.val + 1)) (before ++ [v])
      have full : run P x = (before ++ [v]) ++ extra := by
        calc
          run P x = run (P.take j.val ++ g :: P.drop (j.val + 1)) x := congrArg (fun t => run t x) decomposition
          _ = (before ++ [v]) ++ extra := by
            simp only [run,List.foldl_append,List.foldl_cons]
            exact he
      have early (p : Pin) (lt : p.1 < 10 + j.val) : takePin (run P x) p = takePin before p := by
        have lb : p.1 < before.length := by omega
        have lb' : p.1 < (before ++ [v]).length := by simp; omega
        rw [full]
        simp only [takePin,List.getD_append _ _ false _ lb',List.getD_append _ _ false _ lb]
      change (run P x).getD (10 + j.val) false =
        if g.1 then (takePin (run P x) g.2.1 && takePin (run P x) g.2.2)
        else (takePin (run P x) g.2.1 || takePin (run P x) g.2.2)
      rw [early _ (back j).1,early _ (back j).2,full,
        List.getD_append _ _ false _ (by simp [preLength]),
        List.getD_append_right _ _ false _ (by rw [preLength])]
      simp only [preLength,Nat.sub_self,List.getD_cons_zero,v,g]
    have sizeLB : 11 ≤ P.length := by
      by_contra! below
      obtain ⟨x,hx⟩ := unrestricted P.length op left right out table (by omega) back outOK.1
        inputBits (constZero P) gateTable
      exact hx (agrees x)
    have permissions : allowed S out ∧ ∀ j : Fin P.length, allowed S (left j) ∧ allowed S (right j) :=
      ⟨outOK.2, fun j => pins (P.get j) (List.get_mem P j)⟩
    obtain ⟨x,hx⟩ := few P.length op left right out S table (by omega) cap back outOK.1
      permissions inputBits (constZero P) gateTable
    exact hx (agrees x)
