import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing input zero to false removes both readers. The residual search has
-- twelve ordinary gates interleaved with the two designated reader gates.
theorem PEqualNP.Outside.R_meta_2311_214
    (lower : ∀ D : Circuit, FanInTwo D →
      (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
      (D.gates.filter (fun g => [0,9].any fun i => g.inputs.contains i)).length = 2 →
      (∀ y : Fin 8 → Bool, D.eval (false :: List.ofFn y ++ [true]) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8)))) →
      14 ≤ D.size)
    (threePins : ∀ D : Circuit, FanInTwo D →
      (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
      (∀ y : Fin 8 → Bool, y 3 = false → D.eval (false :: List.ofFn y ++ [true]) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8)))) →
      11 + (D.gates.filter (fun g => [0,4,9].any fun i => g.inputs.contains i)).length ≤ D.size)
    (extension : ∀ (P Q R : List Gate) (a b : Gate) (out : ℕ),
      let D : Circuit := ⟨P ++ a :: (Q ++ b :: R),out⟩
      FanInTwo D → P.length + Q.length + R.length = 12 →
      out < 24 → (∀ g ∈ D.gates, (g.op = .not → g.inputs.length ≤ 1) ∧ ∀ i ∈ g.inputs, i ≤ 24) →
      (∀ g ∈ P ++ Q ++ R, 0 ∉ g.inputs ∧ 9 ∉ g.inputs) →
      ((P ++ Q ++ R).filter (fun g => g.inputs.contains 4)).length ≤ 1 →
      (∀ g ∈ [a,b], 0 ∈ g.inputs ∨ 9 ∈ g.inputs) →
      (∀ y : Fin 8 → Bool, D.eval (false :: List.ofFn y ++ [true]) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8)))) →
      ∃ y : Fin 8 → Bool, D.eval (true :: List.ofFn y ++ [false]) ≠ (y 0 || y 3 || y 4 || (y 1 && y 2) || (y 1 && y 6) || (y 2 && y 7) || (y 5 && y 7))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   have x6 : Prop := ∃ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x3 = x6 ++ x7 :: x8 ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x7.inputs ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x7.inputs) ∧ ∃ x9 ∈ x8, x4 x9 = Bool.false ∧ (10 : ℕ) + x6.length ∈ x9.inputs;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x8 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD (9 : ℕ) Bool.false = !x8 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 = (2 : ℕ) → ¬x6 → False := by
  dsimp only
  intro C fan head target size readers _
  let norm (g : Gate) : Gate := ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩
  let read (g : Gate) := [0,9].any (fun i => g.inputs.contains i)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have normalized (g : Gate) (hg : g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (norm g).op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ (norm g).inputs.length ≤ 2 ∧
      ((norm g).op = .not → (norm g).inputs.length ≤ 1) ∧ ∀ w, step w (norm g) = step w g := by
    obtain ⟨op,ins⟩ := g
    rcases hg with ⟨ops,len⟩
    change op = .and ∨ op = .or ∨ op = .not at ops
    change ins.length ≤ 2 at len
    rcases ops with rfl | rfl | rfl
    · simp [norm,show GateOp.and.eval [false] = false from rfl,step,len]
    · simp [norm,show GateOp.or.eval [false] = false from rfl,step,len]
    · cases ins with
      | nil => simp [norm,show GateOp.not.eval [false] = true from rfl,step]
      | cons i tail =>
        simp [norm,show GateOp.not.eval [false] = true from rfl,step]
        intro w
        rfl
  have stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  cases cs : C.gates with
  | nil =>
    have r := readers
    simp [cs] at r
  | cons h gs =>
    let D : Circuit := ⟨gs.map norm, C.output⟩
    have ok (g) (mem : g ∈ gs) := normalized g (fan g (cs ▸ List.mem_cons_of_mem h mem))
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨g,m,rfl⟩ := List.mem_map.mp hg
      exact ⟨(ok g m).1,(ok g m).2.1⟩
    have notD : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := by
      intro g hg
      obtain ⟨g,m,rfl⟩ := List.mem_map.mp hg
      exact (ok g m).2.2.1
    have agree (t : Bool) (y : Fin 8 → Bool) :
        D.eval (t :: List.ofFn y ++ [!t]) = circuitFun 9 C (Fin.cons t y) := by
      let x : Fin 9 → Bool := Fin.cons t y
      let w := List.ofFn x
      have len : w.length = 9 := List.length_ofFn
      have bit := head x
      change (C.gates.foldl step w).getD 9 false = !x 0 at bit
      rw [cs,List.foldl_cons,stable gs (step w h) 9 (by simp [step,len])] at bit
      have atEnd (v : Bool) : (w ++ [v]).getD 9 false = v := by rw [←len]; simp
      change (w ++ [_]).getD 9 false = !x 0 at bit
      rw [atEnd] at bit
      have appended : step w h = t :: List.ofFn y ++ [!t] := by
        change w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)] = _
        rw [bit]
        simp [w,x,List.ofFn_succ]
      have mapped (ls : List Gate) (hls : ∀ g∈ls, g ∈ gs) (z : List Bool) :
          (ls.map norm).foldl step z = ls.foldl step z := by
        induction ls generalizing z with
        | nil => rfl
        | cons g tail ih =>
          simp only [List.map_cons,List.foldl_cons,(ok g (hls g List.mem_cons_self)).2.2.2]
          exact ih (fun u m => hls u (List.mem_cons_of_mem g m)) _
      change ((gs.map norm).foldl step _).getD C.output false = (C.gates.foldl step w).getD C.output false
      rw [cs,List.foldl_cons,appended,mapped gs (fun _ m => m)]
    have rr : (D.gates.filter read).length = 2 := by simpa only [D,cs,List.drop_succ_cons,List.drop_zero,norm,read] using readers
    let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have eq0 : ∀ y : Fin 8 → Bool, F (Fin.cons false y) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))) := by
      intro y
      have truth : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, ((false && (v0)) || ((v0) && (v1)) || ((v1) && (v2)) || ((v2) && (v3)) || ((v3) && false) || (false && (v4)) || ((v0) && (v5)) || ((v1) && (v6)) || ((v2) && (v7)) || ((v4) && (v6)) || ((v5) && (v7)) || ((v7) && (v4))) = ((v0 && v1) || ((v1 && v2) || ((v2 && v3) || ((v0 && v5) || ((v1 && v6) || ((v2 && v7) || ((v4 && v6) || ((v5 && v7) || ((v7 && v4) || false))))))))) := by
        decide +kernel
      exact truth (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    have eq1 : ∀ y : Fin 8 → Bool, F (Fin.cons true y) = (y 0 || y 3 || y 4 || (y 1 && y 2) || (y 1 && y 6) || (y 2 && y 7) || (y 5 && y 7)) := by
      intro y
      have truth : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, ((true && (v0)) || ((v0) && (v1)) || ((v1) && (v2)) || ((v2) && (v3)) || ((v3) && true) || (true && (v4)) || ((v0) && (v5)) || ((v1) && (v6)) || ((v2) && (v7)) || ((v4) && (v6)) || ((v5) && (v7)) || ((v7) && (v4))) = (v0 || v3 || v4 || (v1 && v2) || (v1 && v6) || (v2 && v7) || (v5 && v7)) := by
        decide +kernel
      exact truth (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    have at0 (y : Fin 8 → Bool) : D.eval (false :: List.ofFn y ++ [true]) = ([1,10,19,5,14,23,38,47,60] : List ℕ).any (fun e =>
          y (Fin.ofNat 8 (e / 8)) && y (Fin.ofNat 8 (e % 8))) :=
      (agree false y).trans ((congrFun target _).trans (eq0 y))
    have at1 (y : Fin 8 → Bool) : D.eval (true :: List.ofFn y ++ [false]) = (y 0 || y 3 || y 4 || (y 1 && y 2) || (y 1 && y 6) || (y 2 && y 7) || (y 5 && y 7)) :=
      (agree true y).trans ((congrFun target _).trans (eq1 y))
    have low := lower D fanD notD rr at0
    have sz : D.size = 14 := by
      change (gs.map norm).length = 14
      change (gs.map norm).length ≥ 14 at low
      change C.gates.length ≤ 15 at size
      rw [cs] at size
      simp only [List.length_map,List.length_cons] at *
      omega
    have one (g : Gate) (ls : List Gate) (eq : ls.filter read = [g]) :
        ∃ P R, ls = P ++ g :: R ∧ ∀ u∈P++R, read u = false := by
      induction ls with
      | nil => simp at eq
      | cons x xs ih =>
        by_cases hit : read x = true
        · simp [hit] at eq
          exact ⟨[],xs,by simp [eq.1],by simpa using eq.2⟩
        · have hx : read x = false := Bool.eq_false_iff.mpr hit
          simp [hx] at eq
          obtain ⟨P,R,e,hR⟩ := ih eq
          exact ⟨x::P,R,by simp [e],by simpa [hx] using hR⟩
    have two (a b : Gate) (ls : List Gate) (eq : ls.filter read = [a,b]) :
        ∃ P Q R, ls = P ++ a :: (Q ++ b :: R) ∧ ∀ u∈P++Q++R, read u = false := by
      induction ls with
      | nil => simp at eq
      | cons x xs ih =>
        by_cases hit : read x = true
        · simp [hit] at eq
          obtain ⟨Q,R,e,clean⟩ := one b xs eq.2
          exact ⟨[],Q,R,by simp [e,eq.1],by simpa using clean⟩
        · have hx : read x = false := Bool.eq_false_iff.mpr hit
          simp [hx] at eq
          obtain ⟨P,Q,R,e,clean⟩ := ih eq
          exact ⟨x::P,Q,R,by simp [e],by simpa [hx] using clean⟩
    obtain ⟨a,b,t⟩ := List.length_eq_two.mp rr
    obtain ⟨P,Q,R,decomp,clean⟩ := two a b D.gates t
    have hit (g : Gate) (h : g ∈ [a,b]) : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by
      have h' := List.mem_filter.mp (t ▸ h : g ∈ D.gates.filter read)
      simpa [read] using h'.2
    have c' (g) (h : g∈P++Q++R) : 0 ∉ g.inputs ∧ 9 ∉ g.inputs := by
      simpa [read] using clean g h
    have cd : (⟨P ++ a :: (Q ++ b :: R),D.output⟩ : Circuit) = D := by rw [←decomp]
    have length : P.length + Q.length + R.length = 12 := by
      change D.gates.length = 14 at sz
      rw [decomp] at sz
      simp only [List.length_append,List.length_cons] at sz
      omega
    let clip := fun g : Gate => Gate.mk g.op (g.inputs.map (min 24))
    let E : Circuit := ⟨D.gates.map clip,D.output⟩
    have gates : E.gates = P.map clip ++ clip a :: (Q.map clip ++ clip b :: R.map clip) := by
      simp only [E,decomp,List.map_append,List.map_cons]
    have eFan : FanInTwo E := by
      intro g hg
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
      simpa [clip] using fanD u hu
    have bounds : ∀ g ∈ E.gates, (g.op = .not → g.inputs.length ≤ 1) ∧ ∀ i∈g.inputs, i ≤ 24 := by
      intro g hg
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
      refine ⟨by simpa [clip] using notD u hu, ?_⟩
      intro i mem
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp mem
      exact min_le_left _ _
    have pins (w : List Bool) (h : w.length ≤ 24) (i : ℕ) :
        w.getD (min 24 i) false = w.getD i false := by
      by_cases hi : i ≤ 24
      · rw [min_eq_right hi]
      · rw [min_eq_left (by omega),List.getD_eq_default _ _ h,List.getD_eq_default _ _ (by omega)]
    have same_step (w : List Bool) (h : w.length ≤ 24) (g : Gate) :
        step w (clip g) = step w g := by
      simp only [clip,step,List.map_map,Function.comp_def,pins w h]
    have same (ls : List Gate) (w : List Bool) (h : w.length + ls.length ≤ 24) :
        (ls.map clip).foldl step w = ls.foldl step w := by
      induction ls generalizing w with
      | nil => rfl
      | cons g ls ih =>
        simp only [List.map_cons,List.foldl_cons,same_step w (by omega : w.length ≤ 24)]
        apply ih
        simp [step] at *
        omega
    have eqEval (t : Bool) (y : Fin 8 → Bool) : E.eval (t :: List.ofFn y ++ [!t]) = D.eval (t :: List.ofFn y ++ [!t]) := by
      have lenD : D.gates.length = 14 := sz
      exact congrArg (fun w : List Bool => w.getD D.output false)
        (same D.gates _ (by simp [lenD]))
    have flen (ls : List Gate) (w : List Bool) : (ls.foldl step w).length = w.length + ls.length := by
      induction ls generalizing w with
      | nil => simp
      | cons g ls ih =>
        rw [List.foldl_cons,ih]
        simp [step]
        omega
    have out : D.output < 24 := by
      by_contra! high
      have yes := at1 (fun _ => true)
      change (D.gates.foldl step (true :: List.ofFn (fun _ : Fin 8 => true) ++ [false])).getD D.output false = true at yes
      have lenD : D.gates.length = 14 := sz
      rw [List.getD_eq_default _ _ (by simp [flen,lenD]; exact high)] at yes
      contradiction
    have normal : (⟨P.map clip ++ clip a :: (Q.map clip ++ clip b :: R.map clip),D.output⟩ : Circuit) = E := by rw [←gates]
    have clearPins (g : Gate) (hg : g ∈ P.map clip ++ Q.map clip ++ R.map clip) : 0 ∉ g.inputs ∧ 9 ∉ g.inputs := by
      rw [←List.map_append,←List.map_append] at hg
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
      have low := c' u hu
      constructor <;> intro bad <;> obtain ⟨i,hi,e⟩ := List.mem_map.mp bad
      · exact low.1 (by rwa [show i = 0 by omega] at hi)
      · exact low.2 (by rwa [show i = 9 by omega] at hi)
    have used (g : Gate) (hg : g ∈ [clip a,clip b]) : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by
      have image : [clip a,clip b] = [a,b].map clip := rfl
      rw [image] at hg
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
      rcases hit u hu with hl | hr
      · exact Or.inl (List.mem_map.mpr ⟨0,hl,rfl⟩)
      · exact Or.inr (List.mem_map.mpr ⟨9,hr,rfl⟩)
    let marked (g : Gate) := [0,4,9].any fun i => g.inputs.contains i
    have m (g) (hg : g ∈ [clip a,clip b]) : marked g = true := by
      rcases used g hg with ha | hb
      · simp [marked,ha]
      · simp [marked,hb]
    have ea : marked (clip a) = true := m _ (by simp)
    have eb : marked (clip b) = true := m _ (by simp)
    have narrow : ((P.map clip ++ Q.map clip ++ R.map clip).filter (fun g => g.inputs.contains 4)).length ≤ 1 := by
      have total := threePins E eFan (fun g h => (bounds g h).1) (fun y _ => (eqEval false y).trans (at0 y))
      have lenE : E.size = 14 := by
        change (D.gates.map clip).length = 14
        rw [List.length_map]
        exact sz
      change 11 + (E.gates.filter marked).length ≤ E.size at total
      rw [lenE,gates] at total
      simp only [List.filter_append,List.filter_cons_of_pos ea,List.filter_cons_of_pos eb,List.length_append,List.length_cons] at total
      have sub (g : Gate) (h : g.inputs.contains 4 = true) : marked g = true := by
        have m : 4 ∈ g.inputs := by simpa using h
        simp [marked,m]
      have cmp (ls : List Gate) : (ls.filter (fun g => g.inputs.contains 4)).length ≤ (ls.filter marked).length := by
        induction ls with
        | nil => rfl
        | cons g ls ih =>
          cases h : g.inputs.contains 4 with
          | true =>
            rw [List.filter_cons_of_pos (p := fun u : Gate => u.inputs.contains 4) h,List.filter_cons_of_pos (sub g h)]
            exact Nat.succ_le_succ ih
          | false =>
            rw [List.filter_cons_of_neg (p := fun u : Gate => u.inputs.contains 4) (a := g) (by simp only [h,Bool.false_eq_true,not_false_eq_true])]
            cases hm : marked g with
            | false => simpa only [List.filter_cons,hm,Bool.false_eq_true,ite_false] using ih
            | true => simpa only [List.filter_cons,hm,ite_true,List.length_cons] using Nat.le_succ_of_le ih
      have le := cmp (P.map clip ++ Q.map clip ++ R.map clip)
      simp only [List.filter_append,List.length_append] at le ⊢
      omega
    have bad := extension (P.map clip) (Q.map clip) (R.map clip) (clip a) (clip b) D.output
      (normal ▸ eFan) (by simpa only [List.length_map] using length) out (normal ▸ bounds) clearPins narrow used
      (normal ▸ (fun y => (eqEval false y).trans (at0 y)))
    obtain ⟨y,hy⟩ := bad
    rw [normal] at hy
    exact hy ((eqEval true y).trans (at1 y))
