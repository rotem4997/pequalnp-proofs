import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Singleton supports of the two final operands form a complete bipartite subgraph.
-- In the punctured plane one operand is silent on singletons or the supports form a star.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_18816_1
  (silent :
    let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
    let one := fun a i : Fin 25 => decide (i = a)
    ∀ (D : Circuit) (p q : ℕ), Monotone2 D →
      (∀ x, (W D p x && W D q x) = true ↔ target x) →
      (∀ i, W D p (one i) = false) → 57 ≤ D.size)
  (star :
    let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
    let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
    let one := fun a i : Fin 25 => decide (i = a)
    ∀ (D : Circuit) (p q : ℕ) (a : Fin 25), Monotone2 D →
      (∀ x, (W D p x && W D q x) = true ↔ target x) →
      (∀ i, W D p (one i) = true ↔ i = a) →
      (∃ i, W D q (one i) = true) →
      (∀ i, W D q (one i) = true → target (fun z => decide (z=a ∨ z=i))) → 57 ≤ D.size) :
  let I := fun (i : Fin 12) (j : Fin 13) =>
    i.succ = j ∨ i.succ = j+1 ∨ i.succ = j+3 ∨ i.succ = j+9
  let pair := fun (i : Fin 12) (j : Fin 13) (v : Fin 25) =>
    decide (v = Fin.castAdd 13 i ∨ v = Fin.natAdd 12 j)
  let neg := fun (S : Finset (Fin 12)) (v : Fin 25) =>
    Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ S)) (fun j => decide (∀ i ∈ S, ¬I i j)) v
  ∀ (D : Circuit) (ws : List ℕ), Monotone2 D → D.size ≤ 56 → ws.length ≤ 2 →
    let reads := fun (x : Fin 25 → Bool) => (ws.map fun w => (D.wires (List.ofFn x)).getD w false).all id
    (∀ i j, I i j → reads (pair i j) = true) → ∃ S, (∀ i ∉ S, ∃ j, I i j ∧ ∀ k ∈ S, ¬I k j) ∧ reads (neg S) = true := by
  let incident := fun (p : Fin 12) (l : Fin 13) => p.succ = l ∨ p.succ = l+1 ∨ p.succ = l+3 ∨ p.succ = l+9
  let target := fun x : Fin 25 → Bool => ∃ p l, incident p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
  let W := fun (D : Circuit) (w : ℕ) (x : Fin 25 → Bool) => (D.wires (List.ofFn x)).getD w false
  let one := fun a i : Fin 25 => decide (i = a)
  let P : Fin 12 → Fin 25 := Fin.castAdd 13
  let L : Fin 13 → Fin 25 := Fin.natAdd 12
  let pair := fun a b i : Fin 25 => decide (i=a ∨ i=b)
  let freeLines (S : Finset (Fin 12)) := Finset.univ.filter fun l : Fin 13 => ∀ i ∈ S, ¬incident i l
  let maximalInput (S : Finset (Fin 12)) (z : Fin 25) :=
    Fin.addCases (motive := fun _ => Bool) (fun i => decide (i ∈ S)) (fun l => decide (l ∈ freeLines S)) z
  let closedPoints (S : Finset (Fin 12)) := ∀ i ∉ S, ∃ l ∈ freeLines S, incident i l
  have fullFromBoundary (F : (Fin 25 → Bool) → Bool)
      (mono : ∀ x y, (∀ z, x z = true → y z = true) → F x = true → F y = true)
      (pos : ∀ p l, incident p l → F (pair (P p) (L l)) = true)
      (neg : ∀ S, closedPoints S → F (maximalInput S) ≠ true) :
      ∀ x, F x = true ↔ target x := by
    intro x
    constructor
    · intro hx
      by_contra miss
      let A := Finset.univ.filter fun p => x (P p) = true
      let M := freeLines A
      let S := Finset.univ.filter fun i => ∀ j ∈ M, ¬incident i j
      have inc : A ⊆ S := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j hj => (Finset.mem_filter.mp hj).2 i hi⟩
      have lines : freeLines S = M := by
        ext j
        simp only [freeLines,M,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨fun hj i hi => hj i (inc hi),fun hj i hi => (Finset.mem_filter.mp hi).2 j (by simpa [M,freeLines] using hj)⟩
      have closed : closedPoints S := by
        intro i hi
        simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at hi
        push Not at hi
        rwa [lines]
      apply neg S closed (mono x (maximalInput S) ?_ hx)
      intro z
      induction z using Fin.addCases (m := 12) (n := 13) with
      | left i =>
        intro hi
        simpa [maximalInput] using inc (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      | right j =>
        intro hj
        have hj' : j ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp e =>
          miss ⟨p,j,e,(Finset.mem_filter.mp hp).2,hj⟩⟩
        simpa [maximalInput,lines] using hj'
    · rintro ⟨p,l,e,hp,hl⟩
      apply mono _ _ _ (pos p l e)
      intro z on
      rcases of_decide_eq_true on with rfl | rfl
      · exact hp
      · exact hl
  -- Wire monotonicity follows the accepted proof of L-meta-18880.
  let wireDominates (xs ys : List Bool) : Prop :=
    xs.length = ys.length ∧ ∀ i, xs.getD i false = true → ys.getD i false = true

  have getD_snoc (ws : List Bool) (b : Bool) (i : ℕ) :
      (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
    by_cases hi : i < ws.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right (ne_of_lt hi)]
    by_cases he : i = ws.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
         List.getD_eq_default _ _ (by omega)]

  have snoc_extends {xs ys : List Bool} {a b : Bool}
      (h : wireDominates xs ys) (hab : a = true → b = true) :
      wireDominates (xs ++ [a]) (ys ++ [b]) := by
    refine ⟨by simp [h.1], ?_⟩
    intro i hi
    rw [getD_snoc, ← h.1]
    rw [getD_snoc] at hi
    split_ifs at hi ⊢
    · exact hab hi
    · exact h.2 i hi

  have gate_extends {g : Gate} (hop : g.op = .and ∨ g.op = .or)
      {xs ys : List Bool} (h : wireDominates xs ys) :
      g.op.eval (g.inputs.map (fun i => xs.getD i false)) = true →
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) = true := by
    rcases hop with e | e
    · rw [e]
      change (g.inputs.map (fun i => xs.getD i false)).all id = true → (g.inputs.map (fun i => ys.getD i false)).all id = true
      simp only [List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
      exact fun ha i hi => h.2 i (ha i hi)
    · rw [e]
      change (g.inputs.map (fun i => xs.getD i false)).any id = true → (g.inputs.map (fun i => ys.getD i false)).any id = true
      simp only [List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
      rintro ⟨i, hi, ha⟩
      exact ⟨i, hi, h.2 i ha⟩

  have fold_extends (gs : List Gate) {xs ys : List Bool}
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (h : wireDominates xs ys) :
      wireDominates (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) xs)
        (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) ys) := by
    induction gs generalizing xs ys with
    | nil => exact h
    | cons g gs ih =>
      exact ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
        (snoc_extends h (gate_extends (ops g (by simp)) h))

  intro _ _ _ D ws mono budget fan
  let F := fun x : Fin 25 → Bool => (ws.map fun w => W D w x).all id
  change (∀ p l, incident p l → F (pair (P p) (L l)) = true) → _
  intro pos
  by_contra! no
  have neg (S) (hs : closedPoints S) : F (maximalInput S) ≠ true := by
    have off := no S (fun i hi => by
      obtain ⟨l,hl,e⟩ := hs i hi
      exact ⟨l,e,(Finset.mem_filter.mp hl).2⟩)
    have bits : maximalInput S = Fin.addCases (motive := fun _ => Bool)
        (fun i => decide (i ∈ S)) (fun l => decide (∀ i ∈ S, ¬incident i l)) := by
      funext i
      induction i using Fin.addCases (m := 12) (n := 13) with
      | left i => simp [maximalInput]
      | right l => simp [maximalInput,freeLines]
    rw [bits]
    simpa only [F,W,Bool.not_eq_true] using off
  have up (w : ℕ) (x y : Fin 25 → Bool) (le : ∀ i, x i = true → y i = true) :
      W D w x = true → W D w y = true := by
    apply (fold_extends D.gates (fun g m => (mono g m).1) (xs := List.ofFn x) (ys := List.ofFn y) ?_).2 w
    refine ⟨by simp,fun i on => ?_⟩
    by_cases h : i < 25
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left h,Option.getD_some] at on ⊢
      exact le _ on
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right h,Option.getD_none,Bool.false_eq_true] at on
  have full : ∀ x, F x = true ↔ target x := by
    apply fullFromBoundary F _ pos neg
    intro x y le
    simp only [F,List.all_map,Function.comp_apply,id_eq,List.all_eq_true]
    exact fun h w mem => up w x y le (h w mem)
  let dir (a b : Fin 25) := a.val < 12 ∧ 12 ≤ b.val ∧ (a.val+14-(b.val-12)) % 13 ∈ ([0,1,3,9] : List ℕ)
  let adj (a b : Fin 25) := dir a b ∨ dir b a
  have edgeTest : ∀ a b, target (pair a b) ↔ adj a b := by
    dsimp only [target,pair,incident,adj,dir]
    decide +kernel
  have thin : ∀ a b : Fin 25, a ≠ b →
      (Finset.univ.filter fun i : Fin 25 => decide (adj a i ∧ adj b i)).card ≤ 1 := by
    dsimp only [adj,dir]
    decide +kernel
  have lower (p q : ℕ) (rep : ∀ x, (W D p x && W D q x) = true ↔ target x) : 57 ≤ D.size := by
    let live (w : ℕ) (a : Fin 25) := W D w (one a) = true
    have rev (x) : (W D q x && W D p x) = true ↔ target x := by rw [Bool.and_comm]; exact rep x
    have cross (u v) (hu : live p u) (hv : live q v) : target (pair u v) := by
      apply (rep _).mp
      apply Bool.and_eq_true_iff.mpr
      constructor
      · exact up p (one u) (pair u v) (fun i h => by obtain rfl := of_decide_eq_true h; simp [pair]) hu
      · exact up q (one v) (pair u v) (fun i h => by obtain rfl := of_decide_eq_true h; simp [pair]) hv
    by_cases lp : ∃ a, live p a
    · obtain ⟨a,ha⟩ := lp
      by_cases lq : ∃ b, live q b
      · obtain ⟨b,hb⟩ := lq
        by_cases single : ∀ i, live p i → i=a
        · exact star D p q a mono rep (fun i => ⟨single i,fun e => e ▸ ha⟩) ⟨b,hb⟩ (fun i h => cross a i ha h)
        · push Not at single
          obtain ⟨a',ha',ne⟩ := single
          have included (i) (hi : live q i) :
              i ∈ Finset.univ.filter fun t => decide (adj a' t ∧ adj a t) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (And.intro ((edgeTest _ _).mp (cross _ _ ha' hi)) ((edgeTest _ _).mp (cross _ _ ha hi)))⟩
          have uniq (i) (h : live q i) : i=b :=
            Finset.card_le_one.mp (thin a' a ne) i (included i h) b (included b hb)
          exact star D q p b mono rev (fun i => ⟨uniq i,fun e => e ▸ hb⟩) ⟨a,ha⟩
            (fun i h => by simpa only [pair,or_comm] using cross i b h hb)
      · exact silent D q p mono rev (fun i => Bool.eq_false_iff.mpr (fun h => lq ⟨i,h⟩))
    · exact silent D p q mono rep (fun i => Bool.eq_false_iff.mpr (fun h => lp ⟨i,h⟩))
  have noZero : ¬target (fun _ => false) := by simp [target]
  have contradiction : 57 ≤ D.size := by
    cases ws with
    | nil => exact False.elim (noZero ((full (fun _ => false)).mp rfl))
    | cons p tail =>
      cases tail with
      | nil => exact lower p p (by simpa [F] using full)
      | cons q rest =>
        have empty : rest = [] := by simpa using fan
        subst rest
        exact lower p q (by simpa [F] using full)
  omega
