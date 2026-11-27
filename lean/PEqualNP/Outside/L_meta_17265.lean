import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17265_aux

namespace ThetaAnd3241

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadK

theorem switchProgram5180 : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
    let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
        let a := w.getD (g.inputs.getD 0 0) ∅
        let b := w.getD (g.inputs.getD 1 0) ∅
        w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
        ((List.finRange n).map fun i => {i})).getD C.output ∅
    ∀ X : Finset (Fin n), circuitFun n C (setInput X) = false ↔ ∃ s, Disjoint (M s) X := by
  classical
  intro n C ao M X
  let hit (P : Finset (Fin n)) := decide (¬ Disjoint P X)
  let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
  let read (l : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => l.getD i false)
  let run (l : List Bool) (g : Gate) := l ++ [read l g]
  let select (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
    let a := w.getD (g.inputs.getD 0 0) ∅
    let b := w.getD (g.inputs.getD 1 0) ∅
    if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b
  let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) := w ++ [select s w g]
  have emptyHit : hit ∅ = false := by simp [hit]
  have hitUnion (a b : Finset (Fin n)) : hit (a ∪ b) = (hit a || hit b) := by
    by_cases ha : Disjoint a X <;> by_cases hb : Disjoint b X <;>
      simp [hit,ha,hb]
  have readMap (w : List (Finset (Fin n))) (i : ℕ) :
      (w.map hit).getD i false = hit (w.getD i ∅) := by
    induction w generalizing i with
    | nil => cases i <;> exact emptyHit.symm
    | cons a w ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  have snoc {α : Type} (l : List α) (d z : α) (i : ℕ) :
      (l ++ [d]).getD i z = if i = l.length then d else l.getD i z := by
    induction l generalizing i with
    | nil => cases i <;> rfl
    | cons x l ih => cases i with
      | zero => rfl
      | succ i => simpa using ih i
  let Shape (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ ∃ u v : ℕ, g.inputs = [u,v]
  have gateShape (g : Gate) (hg : g ∈ C.gates) : Shape g := by
    have pair (l : List ℕ) (h : l.length = 2) : ∃ u v, l = [u,v] := by
      cases l with
      | nil => simp at h
      | cons u tl =>
        cases tl with
        | nil => simp at h
        | cons v tl =>
          have z : tl = [] := List.length_eq_zero_iff.mp (by simpa using h)
          exact ⟨u,v,by rw [z]⟩
    exact ⟨ao.1 g hg,pair g.inputs (ao.2.2 g hg)⟩
  have readAnd (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .and)
      (pins : g.inputs = [u,v]) : read l g = (l.getD u false && l.getD v false) := by
    simp only [read,kind,pins,List.map_cons,List.map_nil]
    cases l.getD u false <;> cases l.getD v false <;> rfl
  have readOr (l : List Bool) (g : Gate) (u v : ℕ) (kind : g.op = .or)
      (pins : g.inputs = [u,v]) : read l g = (l.getD u false || l.getD v false) := by
    simp only [read,kind,pins,List.map_cons,List.map_nil]
    cases l.getD u false <;> cases l.getD v false <;> rfl
  have selAnd (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
      (kind : g.op = .and) (pins : g.inputs = [u,v]) :
      select s w g = if s w.length then w.getD u ∅ else w.getD v ∅ := by
    simp only [select,kind,pins]
    rfl
  have selOr (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) (u v : ℕ)
      (kind : g.op = .or) (pins : g.inputs = [u,v]) :
      select s w g = w.getD u ∅ ∪ w.getD v ∅ := by
    simp only [select,kind,pins]
    rfl
  let Safe (l : List Bool) (w : List (Finset (Fin n))) :=
    ∀ i, hit (w.getD i ∅) = false → l.getD i false = false
  have sound (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (s : ℕ → Bool)
      (l : List Bool) (w : List (Finset (Fin n))) (len : l.length = w.length)
      (old : Safe l w) : Safe (gs.foldl run l) (gs.foldl (go s) w) := by
    induction gs generalizing l w with
    | nil => exact old
    | cons g gs ih =>
      obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
      have next : hit (select s w g) = false → read l g = false := by
        rcases kind with andG | orG
        · rw [readAnd l g u v andG pins,selAnd s w g u v andG pins]
          cases h : s w.length with
          | false =>
            intro off
            have f : hit (w.getD v ∅) = false := off
            rw [old v f,Bool.and_false]
          | true =>
            intro off
            have f : hit (w.getD u ∅) = false := off
            rw [old u f,Bool.false_and]
        · rw [readOr l g u v orG pins,selOr s w g u v orG pins,hitUnion]
          intro off
          have both : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by
            intro a b
            cases a <;> cases b <;> simp
          obtain ⟨fa,fb⟩ := both _ _ off
          rw [old u fa,old v fb]
          rfl
      apply ih (fun k hk => hg k (by simp [hk])) (run l g) (go s w g) (by simp [run,go,len])
      intro i
      change hit ((w ++ [select s w g]).getD i ∅) = false →
        (l ++ [read l g]).getD i false = false
      rw [snoc,snoc,len]
      by_cases atEnd : i = w.length
      · simpa only [ite_eq_left atEnd] using next
      · simpa only [ite_eq_right atEnd] using old i
  have future (gs : List Gate) (s t : ℕ → Bool) (w : List (Finset (Fin n)))
      (agree : ∀ j, w.length ≤ j → s j = t j) :
      gs.foldl (go s) w = gs.foldl (go t) w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have now : go s w g = go t w g := by simp only [go,select,agree w.length (le_refl _)]
      simp only [List.foldl_cons,now]
      apply ih
      intro j hj
      have a : w.length + 1 ≤ j := by simpa [go] using hj
      exact agree j (by omega)
  have realize (gs : List Gate) (hg : ∀ g ∈ gs, Shape g) (w : List (Finset (Fin n))) :
      ∃ s : ℕ → Bool, gs.foldl run (w.map hit) = (gs.foldl (go s) w).map hit := by
    induction gs generalizing w with
    | nil => exact ⟨fun _ => false,rfl⟩
    | cons g gs ih =>
      obtain ⟨kind,u,v,pins⟩ := hg g (by simp)
      let side := !(hit (w.getD u ∅))
      let now : ℕ → Bool := fun _ => side
      have one : run (w.map hit) g = (go now w g).map hit := by
        change w.map hit ++ [read (w.map hit) g] = (w ++ [select now w g]).map hit
        rw [List.map_append]
        congr 1
        change [read (w.map hit) g] = [hit (select now w g)]
        rcases kind with andG | orG
        · rw [readAnd _ g u v andG pins,selAnd _ _ g u v andG pins,readMap,readMap]
          change [(hit (w.getD u ∅) && hit (w.getD v ∅))] =
            [hit (if !(hit (w.getD u ∅)) then w.getD u ∅ else w.getD v ∅)]
          cases e : hit (w.getD u ∅) <;> simp only [Bool.not_true,Bool.not_false,
            Bool.false_eq_true,ite_true,ite_false,e,Bool.false_and,Bool.true_and]
        · rw [readOr _ g u v orG pins,selOr _ _ g u v orG pins,hitUnion,readMap,readMap]
      obtain ⟨t,rest⟩ := ih (fun k hk => hg k (by simp [hk])) (go now w g)
      let s : ℕ → Bool := fun j => if j = w.length then side else t j
      have first : go s w g = go now w g := by simp only [go,select,s,now,ite_true]
      have tail : gs.foldl (go s) (go now w g) = gs.foldl (go t) (go now w g) := by
        apply future
        intro j hj
        have a : w.length + 1 ≤ j := by simpa [go] using hj
        simp only [s,ite_eq_right (show j ≠ w.length by omega)]
      refine ⟨s,?_⟩
      simp only [List.foldl_cons,one,first,tail]
      exact rest
  have initial : List.ofFn (setInput X) = seed.map hit := by
    change List.ofFn (setInput X) = ((List.finRange n).map fun i => ({i} : Finset (Fin n))).map hit
    rw [List.map_map]
    have finRange : List.finRange n = List.ofFn id := rfl
    rw [finRange,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change decide (i ∈ X) = hit {i}
    simp [hit]
  have hitZero (P : Finset (Fin n)) : hit P = false ↔ Disjoint P X := by
    simp [hit]
  change (C.gates.foldl run (List.ofFn (setInput X))).getD C.output false = false ↔
    ∃ s, Disjoint ((C.gates.foldl (go s) seed).getD C.output ∅) X
  rw [initial]
  constructor
  · intro rejected
    obtain ⟨s,eq⟩ := realize C.gates gateShape seed
    rw [eq,readMap] at rejected
    exact ⟨s,(hitZero _).mp rejected⟩
  · rintro ⟨s,h⟩
    have seedSafe : Safe (seed.map hit) seed := fun i => by rw [readMap]; exact id
    exact sound C.gates gateShape s (seed.map hit) seed (by simp) seedSafe C.output ((hitZero _).mpr h)

theorem switchCount5180 (n : ℕ) (C : Circuit) :
    let M (s : ℕ → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
        let a := w.getD (g.inputs.getD 0 0) ∅
        let b := w.getD (g.inputs.getD 1 0) ∅
        w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
        ((List.finRange n).map fun i => {i})).getD C.output ∅
    ∃ F : Finset (Finset (Fin n)), (∀ s, M s ∈ F) ∧
      F.card ≤ 2 ^ (C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) := by
  classical
  intro M
  let go (s : ℕ → Bool) (w : List (Finset (Fin n))) (g : Gate) :=
    let a := w.getD (g.inputs.getD 0 0) ∅
    let b := w.getD (g.inputs.getD 1 0) ∅
    w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b]
  let seed := (List.finRange n).map fun i => ({i} : Finset (Fin n))
  let fixed (gs : List Gate) := gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)
  let free (gs : List Gate) := gs.countP (fun g => !(PEqualNP.SharedBlockCost.isOrOp g.op))
  have fixedCons (g : Gate) (gs : List Gate) :
      fixed (g::gs) = fixed gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 1 else 0) := by
    cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [fixed,eq]
  have freeCons (g : Gate) (gs : List Gate) :
      free (g::gs) = free gs + (if PEqualNP.SharedBlockCost.isOrOp g.op = true then 0 else 1) := by
    cases eq : PEqualNP.SharedBlockCost.isOrOp g.op <;> simp [free,eq]
  have total (gs : List Gate) : fixed gs + free gs = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rw [fixedCons,freeCons,List.length_cons]
      cases PEqualNP.SharedBlockCost.isOrOp g.op <;> simp <;> omega
  let yes : ℕ → Bool := fun _ => true
  let no : ℕ → Bool := fun _ => false
  have family (gs : List Gate) (w : List (Finset (Fin n))) :
      ∃ T : Finset (List (Finset (Fin n))), (∀ s, gs.foldl (go s) w ∈ T) ∧ T.card ≤ 2 ^ free gs := by
    induction gs generalizing w with
    | nil => exact ⟨{w},fun _ => Finset.mem_singleton_self _,by simp [free]⟩
    | cons g gs ih =>
      obtain ⟨Tno,hasNo,sizeNo⟩ := ih (go no w g)
      by_cases hg : PEqualNP.SharedBlockCost.isOrOp g.op = true
      · have same (s : ℕ → Bool) : go s w g = go no w g := by simp [go,hg]
        refine ⟨Tno,fun s => ?_,?_⟩
        · simpa only [List.foldl_cons,same s] using hasNo s
        · simpa only [freeCons,ite_eq_left hg,Nat.add_zero] using sizeNo
      · obtain ⟨Tyes,hasYes,sizeYes⟩ := ih (go yes w g)
        refine ⟨Tno ∪ Tyes,?_,?_⟩
        · intro s
          simp only [List.foldl_cons]
          cases hs : s w.length with
          | false =>
            have eq : go s w g = go no w g := by simp only [go,no,hs]
            rw [eq]
            exact Finset.mem_union_left _ (hasNo s)
          | true =>
            have eq : go s w g = go yes w g := by simp only [go,yes,hs]
            rw [eq]
            exact Finset.mem_union_right _ (hasYes s)
        · rw [freeCons,ite_eq_right hg,pow_succ]
          have limit := (Finset.card_union_le Tno Tyes).trans (Nat.add_le_add sizeNo sizeYes)
          omega
  obtain ⟨T,rep,bound⟩ := family C.gates seed
  let extract (w : List (Finset (Fin n))) := w.getD C.output ∅
  refine ⟨T.image extract,?_,?_⟩
  · intro s
    exact Finset.mem_image.mpr ⟨C.gates.foldl (go s) seed,rep s,rfl⟩
  · have eq : C.size - fixed C.gates = free C.gates := by
      have h := total C.gates
      change C.gates.length - fixed C.gates = free C.gates
      omega
    change (T.image extract).card ≤ 2 ^ (C.size - fixed C.gates)
    rw [eq]
    exact Finset.card_image_le.trans bound

theorem false_family_bound {n k : Nat} (C : Circuit) (ao : IsAO2 n C)
    (X : Fin k → Finset (Fin n))
    (no : ∀ i, circuitFun n C (setInput (X i)) = false)
    (cross : ∀ i j, i ≠ j → circuitFun n C (setInput (X i ∪ X j)) = true) :
    k ≤ 2 ^ (C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) := by
  classical
  let M (s : Nat → Bool) := (C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
      let a := w.getD (g.inputs.getD 0 0) ∅
      let b := w.getD (g.inputs.getD 1 0) ∅
      w ++ [if PEqualNP.SharedBlockCost.isOrOp g.op then a ∪ b else if s w.length then a else b])
      ((List.finRange n).map fun i => {i})).getD C.output ∅
  obtain ⟨F, mem, size⟩ := switchCount5180 n C
  have exists_code (i : Fin k) : ∃ s, Disjoint (M s) (X i) :=
    (switchProgram5180 n C ao (X i)).mp (no i)
  choose sel avoids using exists_code
  let code (i : Fin k) : F := ⟨M (sel i), mem (sel i)⟩
  have inj : Function.Injective code := by
    intro i j h
    by_contra ne
    have same : M (sel i) = M (sel j) := congrArg Subtype.val h
    have other : Disjoint (M (sel i)) (X j) := same ▸ avoids j
    have together : Disjoint (M (sel i)) (X i ∪ X j) :=
      Finset.disjoint_union_right.mpr ⟨avoids i,other⟩
    have reject := (switchProgram5180 n C ao (X i ∪ X j)).mpr ⟨sel i,together⟩
    simp [cross i j ne] at reject
  have card : k ≤ F.card := by simpa using Fintype.card_le_of_injective code inj
  exact card.trans size

def thetaAdj (i j : Fin 4) : Bool := (13726 : Nat).testBit (4*i.val+j.val)

def theta (x : Fin 8 → Bool) : Bool :=
  decide (∃ i j : Fin 4, thetaAdj i j = true ∧
    x (Fin.castAdd 4 i) = true ∧ x (Fin.natAdd 4 j) = true)

def nine : Fin 9 → Finset (Fin 8) :=
  ![{0,1,2,3}, {0,4}, {1,2,5}, {1,3,6}, {1,5,6}, {2,3,7}, {2,5,7}, {3,6,7}, {4,5,6,7}]

theorem theta_and_count (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x) :
    4 ≤ C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) := by
  have no : ∀ i, theta (setInput (nine i)) = false := by decide +kernel
  have yes : ∀ i j, i ≠ j → theta (setInput (nine i ∪ nine j)) = true := by decide +kernel
  have bound := false_family_bound C ao nine (fun i => (correct _).trans (no i))
    (fun i j h => (correct _).trans (yes i j h))
  by_contra low
  have h : C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) ≤ 3 := by omega
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) h
  omega

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

theorem subtract_or_eq_and {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) =
      C.gates.countP andGate := by
  have total (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      gs.countP andGate + gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have tail := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      rcases ok g List.mem_cons_self with h | h
      · have a : andGate g = true := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = false := by rw [h]; rfl
        simp [a,o]
        omega
      · have a : andGate g = false := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = true := by rw [h]; rfl
        simp [a,o]
        omega
  have count := total C.gates ao.1
  unfold Circuit.size
  omega

theorem theta_four_and (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x) : 4 ≤ C.gates.countP andGate := by
  rw [← subtract_or_eq_and C ao]
  exact theta_and_count C ao correct

theorem theta_twelve_of_eight_or (C : Circuit) (ao : IsAO2 8 C)
    (correct : ∀ x, circuitFun 8 C x = theta x)
    (or_lb : 8 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op)) :
    12 ≤ C.size := by
  have and_lb := theta_and_count C ao correct
  omega

end ThetaAnd3241

namespace ThetaPin3241

abbrev Signal (α : Type) := α → Bool
abbrev Gate (α : Type) := Signal α × Signal α

def join {α : Type} (a b : Signal α) : Signal α := fun x => a x || b x
def meet {α : Type} (a b : Signal α) : Signal α := fun x => a x && b x

def Free {α : Type} (B : Set (Signal α)) (a : Signal α) : Prop :=
  ∀ S : Set (Signal α), B ⊆ S → (fun _ => false) ∈ S → (fun _ => true) ∈ S →
    (∀ u ∈ S, ∀ v ∈ S, meet u v ∈ S) → a ∈ S

theorem atom {α : Type} {B : Set (Signal α)} {a : Signal α} (ha : a ∈ B) : Free B a :=
  fun _ h _ _ _ => h ha

theorem free_zero {α : Type} {B : Set (Signal α)} : Free B (fun _ => false) :=
  fun _ _ h _ _ => h

theorem free_one {α : Type} {B : Set (Signal α)} : Free B (fun _ => true) :=
  fun _ _ _ h _ => h

theorem free_meet {α : Type} {B : Set (Signal α)} {u v : Signal α} (hu : Free B u)
    (hv : Free B v) : Free B (meet u v) :=
  fun S incl h0 h1 hc => hc _ (hu S incl h0 h1 hc) _ (hv S incl h0 h1 hc)

theorem widen {α : Type} {B D : Set (Signal α)} {a : Signal α}
    (incl : B ⊆ D) (h : Free B a) : Free D a :=
  fun S incl' => h S (incl.trans incl')

theorem transport {α β : Type} (p : β → α) {B : Set (Signal α)} {D : Set (Signal β)}
    (base : ∀ a ∈ B, Free D (a ∘ p)) {a : Signal α} (ha : Free B a) : Free D (a ∘ p) := by
  apply ha {a | Free D (a ∘ p)}
  · exact base
  · exact free_zero
  · exact free_one
  · intro u hu v hv
    exact free_meet hu hv

theorem factors {α : Type} {B : Set (Signal α)} {f : Signal α} (ok : Free B f) :
    f = (fun _ => false) ∨ ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧
      f = (fun x => xs.all (fun a => a x)) := by
  let S : Set (Signal α) := {f | f = (fun _ => false) ∨
    ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧ f = (fun x => xs.all (fun a => a x))}
  apply ok S
  · intro a ha
    exact Or.inr ⟨[a],by simpa using ha,funext (fun x => by simp)⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨[],by simp,rfl⟩
  · intro a ha b hb
    rcases ha with rfl | ⟨xs,hh,rfl⟩
    · exact Or.inl rfl
    rcases hb with rfl | ⟨ys,ii,rfl⟩
    · exact Or.inl (funext (fun x => by simp [meet]))
    · refine Or.inr ⟨xs++ys,?_,?_⟩
      · intro u hu
        exact (List.mem_append.mp hu).elim (hh u) (ii u)
      · exact funext (fun x => by simp [meet])

theorem separating_factor {α : Type} {B : Set (Signal α)} {f : Signal α}
    (ok : Free B f) (P : Set α) (nonempty : P.Nonempty) (z : α)
    (yes : ∀ x ∈ P, f x = true) (no : f z = false) :
    ∃ a ∈ B, (∀ x ∈ P, a x = true) ∧ a z = false := by
  rcases factors ok with rfl | ⟨xs,inside,rfl⟩
  · obtain ⟨x,hx⟩ := nonempty
    exact False.elim (Bool.noConfusion (yes x hx))
  · obtain ⟨a,ha,bad⟩ := List.all_eq_false.mp no
    exact ⟨a,inside _ ha,fun x hx => List.all_eq_true.mp (yes x hx) a ha,by simpa using bad⟩

def Valid {α : Type} (B : Set (Signal α)) (gs : List (Gate α)) (f : Signal α) : Prop :=
  match gs with
  | [] => Free B f
  | g :: rest => Free B g.1 ∧ Free B g.2 ∧ Valid (insert (join g.1 g.2) B) rest f

def Pass {α : Type} (t e z : α) (f : Signal α) : Prop :=
  f t = true → f e = true → f z = true

theorem free_pass {α : Type} {B : Set (Signal α)} {t e z : α} {f : Signal α}
    (base : ∀ a ∈ B, Pass t e z a) (ok : Free B f) : Pass t e z f := by
  apply ok {a | Pass t e z a}
  · exact base
  · intro h; contradiction
  · intro _ _; rfl
  · intro u hu v hv ht he
    have ⟨tu,tv⟩ : u t = true ∧ v t = true := by simpa [meet] using ht
    have ⟨eu,ev⟩ : u e = true ∧ v e = true := by simpa [meet] using he
    simp [meet,hu tu eu,hv tv ev]

theorem critical_gate {α : Type} (gs : List (Gate α)) (B : Set (Signal α)) (f : Signal α)
    (t e z : α) (base : ∀ a ∈ B, Pass t e z a) (ok : Valid B gs f)
    (ft : f t = true) (fe : f e = true) (fz : f z = false) :
    ∃ g ∈ gs, (g.1 t = false ∨ g.2 t = false) ∧
      join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  classical
  induction gs generalizing B with
  | nil =>
    have impossible := free_pass base ok ft fe
    simp [fz] at impossible
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    by_cases passes : Pass t e z (join g.1 g.2)
    · have next : ∀ a ∈ insert (join g.1 g.2) B, Pass t e z a := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact passes
        · exact base _ h
      obtain ⟨m,hm,p⟩ := ih _ next tail
      exact ⟨m,List.mem_cons_of_mem _ hm,p⟩
    · have hp : join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧
          join g.1 g.2 z = false := by simpa [Pass] using passes
      refine ⟨g,List.mem_cons_self,?_,hp⟩
      by_contra no
      have both : g.1 t = true ∧ g.2 t = true := by simpa using no
      have either : g.1 e = true ∨ g.2 e = true := by simpa [join] using hp.2.1
      rcases either with h | h
      · have yes := free_pass base ha both.1 h
        have nz := hp.2.2
        simp [join,yes] at nz
      · have yes := free_pass base hb both.2 h
        have nz := hp.2.2
        simp [join,yes] at nz

def Killed {α β : Type} (p : β → α) (g : Gate α) : Prop :=
  (∀ x, g.1 (p x) = false) ∨ (∀ x, g.2 (p x) = false)

def deadAt {α : Type} (t : α) (g : Gate α) : Bool := !(g.1 t && g.2 t)

theorem count_one_unique {α : Type} (gs : List α) (p : α → Bool) (a b : α)
    (ha : a ∈ gs) (hb : b ∈ gs) (pa : p a = true) (pb : p b = true)
    (one : gs.countP p ≤ 1) : a = b := by
  rw [List.countP_eq_length_filter] at one
  have a' := List.mem_filter.mpr ⟨ha,pa⟩
  have b' := List.mem_filter.mpr ⟨hb,pb⟩
  cases h : gs.filter p with
  | nil => simp [h] at a'
  | cons c rest =>
    have numeric : rest.length+1 ≤ 1 := by simpa only [h,List.length_cons] using one
    have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h,nil] at a' b'
    exact a'.trans b'.symm

theorem single_charge_passes {α : Type} {B : Set (Signal α)} {gs : List (Gate α)}
    {f : Signal α} (ok : Valid B gs f) (g : Gate α) (hg : g ∈ gs) (t e z : α)
    (base : ∀ a ∈ B, Pass t e z a) (ft : f t = true) (fe : f e = true)
    (fz : f z = false) (dg : deadAt t g = true) (one : gs.countP (deadAt t) ≤ 1) :
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  obtain ⟨j,hj,charge,h⟩ := critical_gate gs B f t e z base ok ft fe fz
  have dj : deadAt t j = true := by simpa [deadAt] using charge
  exact (count_one_unique gs (deadAt t) j g hj hg dj dg one) ▸ h

theorem propagate_property {α : Type} (B S : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (incl : B ⊆ S) (ok : Valid B gs f)
    (stable : ∀ g ∈ gs, Free S g.1 → Free S g.2 → join g.1 g.2 ∈ S) :
    Free S f := by
  induction gs generalizing B with
  | nil => exact widen incl ok
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have mem := stable g List.mem_cons_self (widen incl ha) (widen incl hb)
    exact ih (insert (join g.1 g.2) B) (Set.insert_subset mem incl) tail
      (fun a h => stable a (List.mem_cons_of_mem _ h))

noncomputable def killedBit {α β : Type} (p : β → α) (g : Gate α) : Bool :=
  @decide (Killed p g) (Classical.propDecidable _)

theorem restrict_transfer {α β : Type} (p : β → α) (gs : List (Gate α))
    (B : Set (Signal α)) (D : Set (Signal β)) (f : Signal α)
    (base : ∀ a ∈ B, Free D (a ∘ p)) (ok : Valid B gs f) :
    ∃ out : List (Gate β), Valid D out (f ∘ p) ∧
      out.length + gs.countP (killedBit p) = gs.length := by
  classical
  induction gs generalizing B D with
  | nil => exact ⟨[], transport p base ok, rfl⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have left := transport p base ha
    have right := transport p base hb
    by_cases dead : Killed p g
    · have combined : Free D (join g.1 g.2 ∘ p) := by
        rcases dead with l | r
        · have e : join g.1 g.2 ∘ p = g.2 ∘ p := funext (fun x => by simp [join,l])
          exact e ▸ right
        · have e : join g.1 g.2 ∘ p = g.1 ∘ p := funext (fun x => by simp [join,r])
          exact e ▸ left
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free D (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact combined
        · exact base _ h
      obtain ⟨out,sem,cost⟩ := ih _ D next tail
      refine ⟨out,sem,?_⟩
      have k : killedBit p g = true := by simp [killedBit,dead]
      simp [k]
      omega
    · let new := join (g.1 ∘ p) (g.2 ∘ p)
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free (insert new D) (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact atom (Set.mem_insert _ _)
        · exact widen (Set.subset_insert _ _) (base _ h)
      obtain ⟨out,sem,cost⟩ := ih _ (insert new D) next tail
      refine ⟨(g.1 ∘ p,g.2 ∘ p)::out,⟨left,right,sem⟩,?_⟩
      have k : killedBit p g = false := by simp [killedBit,dead]
      simp [k]
      omega

abbrev PhysicalGate := PEqualNP.CircuitLowerBounds.Gate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wire {α : Type} (w : List (Signal α)) (i : Nat) : Signal α := w.getD i (fun _ => false)

def step {α : Type} (w : List (Signal α)) (g : PhysicalGate) : List (Signal α) :=
  w ++ [fun x => g.op.eval (g.inputs.map fun i => wire w i x)]

def pairShape (g : PhysicalGate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b]

theorem free_wire {α : Type} {B : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ a ∈ w, Free B a) (i : Nat) : Free B (wire w i) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_zero
  | cons a w ih =>
    cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

def isOr (g : PhysicalGate) : Bool := PEqualNP.SharedBlockCost.isOrOp g.op

theorem compress {α : Type} (gs : List PhysicalGate) (output : Nat) (w : List (Signal α))
    (B : Set (Signal α)) (hw : ∀ a ∈ w, Free B a) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (Gate α), Valid B ops (wire (gs.foldl step w) output) ∧
      ops.length = gs.countP isOr := by
  induction gs generalizing w B with
  | nil => exact ⟨[],free_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    rcases hop with kind | kind
    · have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have ext : ∀ a ∈ step w g, Free B a := by
        intro a ha
        rw [eq,List.mem_append,List.mem_singleton] at ha
        rcases ha with old | rfl
        · exact hw a old
        · exact free_meet (free_wire hw i) (free_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : isOr g = false := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simpa [no] using cost
    · let a := wire w i
      let b := wire w j
      let D := insert (join a b) B
      have eq : step w g = w ++ [join a b] := by
        simp [step,pins,kind,GateOp.eval,a,b]
        rfl
      have ext : ∀ v ∈ step w g, Free D v := by
        intro v hv
        rw [eq,List.mem_append,List.mem_singleton] at hv
        rcases hv with old | rfl
        · exact widen (Set.subset_insert _ _) (hw v old)
        · exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨free_wire hw i,free_wire hw j,sem⟩,?_⟩
      have yes : isOr g = true := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simp [cost,yes]

theorem wire_point {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = wire w i x := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons f fs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem run_point {α : Type} (gs : List PhysicalGate) (w : List (Signal α)) (x : α) :
    (gs.foldl step w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    simp only [step,List.map_append,List.map_cons,List.map_nil,wire_point]

def inputs (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (fun (i : Fin n) x => x i)

def topMiss {n : Nat} (v : Fin n) (i : Fin n) : Bool := decide (i ≠ v)

theorem pass_inputs {n : Nat} (t e z : Fin n → Bool)
    (h : ∀ i, t i = true → e i = true → z i = true) : ∀ a ∈ inputs n, Pass t e z a := by
  rintro a ⟨i,rfl⟩
  exact h i

theorem one_charge {n : Nat} {gs f} (ok : Valid (inputs n) gs f)
    (v : Fin n) (e z : Fin n → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false) :
    1 ≤ gs.countP (deadAt (topMiss v)) := by
  obtain ⟨j,hj,hk,_⟩ := critical_gate gs (inputs n) f (topMiss v) e z
    (pass_inputs _ _ _ h) ok ft fe fz
  exact List.countP_pos_iff.mpr ⟨j,hj,by simpa [deadAt] using hk⟩

def Admissible {α : Type} (B : Set (Signal α)) (f : Signal α) (t : α) (g : Gate α) : Prop :=
  ∀ e z, (∀ a ∈ B, Pass t e z a) → f t = true → f e = true → f z = false →
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false

theorem double_from_classifier {n : Nat} (low : Set (Fin n)) (f : Signal (Fin n → Bool))
    (S : Set (Signal (Fin n → Bool))) (inc : inputs n ⊆ S) (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S)
    (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ v ∈ low, 2 ≤ gs.countP (deadAt (topMiss v)) := by
  classical
  by_contra no
  apply nonfree
  apply propagate_property (inputs n) S gs f inc ok
  intro g hg ha hb
  apply classify g ha hb
  intro v hv dg e z raw ft fe fz
  have small : gs.countP (deadAt (topMiss v)) ≤ 1 := by
    by_contra h
    exact no ⟨v,hv,by omega⟩
  exact single_charge_passes ok g hg (topMiss v) e z raw ft fe fz dg small

def Increasing {n : Nat} (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem free_increasing {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {a} (ha : Free B a) : Increasing a := by
  apply ha {v | Increasing v}
  · exact base
  · intro _ _ _ h; contradiction
  · intro _ _ _ _; rfl
  · intro u hu v hv x y le hx
    obtain ⟨lu,lv⟩ : u x = true ∧ v x = true := by simpa [meet] using hx
    simp [meet,hu x y le lu,hv x y le lv]

theorem active_monotone {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) :
    ∀ g ∈ gs, Increasing g.1 ∧ Increasing g.2 := by
  induction gs generalizing B with
  | nil => simp
  | cons h gs ih =>
    obtain ⟨left,right,tail⟩ := ok
    have l := free_increasing base left
    have r := free_increasing base right
    have next : ∀ a ∈ insert (join h.1 h.2) B, Increasing a := by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · intro x y le hx
        have one : h.1 x = true ∨ h.2 x = true := by simpa [join] using hx
        rcases one with p | p
        · simp [join,l x y le p]
        · simp [join,r x y le p]
      · exact base _ old
    intro g hg
    rcases List.mem_cons.mp hg with rfl | later
    · exact ⟨l,r⟩
    · exact ih next tail _ later

def pin {n : Nat} (v : Fin (n+1)) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  v.insertNth false x

theorem pin_raw {n : Nat} (v : Fin (n+1)) :
    ∀ a ∈ inputs (n+1), Free (inputs n) (a ∘ pin v) := by
  rintro a ⟨i,rfl⟩
  refine v.succAboveCases ?_ (fun j => ?_) i
  · have eq : (fun t : Fin (n+1) → Bool => t v) ∘ pin v = (fun _ => false) :=
      funext (fun x => by simp [pin])
    exact eq ▸ free_zero
  · have eq : (fun t : Fin (n+1) → Bool => t (v.succAbove j)) ∘ pin v = (fun x => x j) :=
      funext (fun x => by simp [pin])
    exact eq ▸ atom ⟨j,rfl⟩

theorem delete_charge {n : Nat} {gs f} (ok : Valid (inputs (n+1)) gs f) (v : Fin (n+1)) :
    ∃ out, Valid (inputs n) out (f ∘ pin v) ∧
      out.length + gs.countP (deadAt (topMiss v)) ≤ gs.length := by
  obtain ⟨out,sem,cost⟩ := restrict_transfer (pin v) gs _ _ f (pin_raw v) ok
  refine ⟨out,sem,?_⟩
  have base : ∀ a ∈ inputs (n+1), Increasing a := by
    rintro a ⟨i,rfl⟩ x y le hx
    exact le i hx
  have zero {a : Signal (Fin (n+1) → Bool)} (inc : Increasing a) (ha : a (topMiss v) = false) :
      ∀ x, a (pin v x) = false := by
    intro x
    cases h : a (pin v x) with
    | false => rfl
    | true =>
      have le : ∀ i, pin v x i = true → topMiss v i = true := by
        intro i
        by_cases hi : i = v
        · subst i; simp [pin]
        · simp [topMiss,hi]
      simp [inc _ _ le h] at ha
  have keep (g) (hg : g ∈ gs) (h : deadAt (topMiss v) g = true) : killedBit (pin v) g = true := by
    obtain ⟨l,r⟩ := active_monotone base ok _ hg
    have either : g.1 (topMiss v) = false ∨ g.2 (topMiss v) = false := by simpa [deadAt] using h
    have killed : Killed (pin v) g := either.imp (zero l) (zero r)
    simp [killedBit,killed]
  have count : gs.countP (deadAt (topMiss v)) ≤ gs.countP (killedBit (pin v)) :=
    List.countP_mono_left keep
  omega

theorem of_circuit {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∃ ops : List (Gate (Fin n → Bool)), Valid (inputs n) ops (circuitFun n C) ∧
      ops.length = C.gates.countP isOr := by
  let w : List (Signal (Fin n → Bool)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) a := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact atom ⟨i,rfl⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := compress C.gates C.output w (inputs n) ok shapes
  refine ⟨ops,?_,cost⟩
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  exact eq ▸ sem

def Lower {n : Nat} (f : Signal (Fin n → Bool)) (k : Nat) : Prop :=
  ∀ ops, Valid (inputs n) ops f → k ≤ ops.length

theorem lower_zero {n : Nat} (f : Signal (Fin n → Bool)) : Lower f 0 :=
  fun _ _ => Nat.zero_le _

theorem lower_one_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (v : Fin (n+1)) (e z : Fin (n+1) → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false)
    (rec : Lower (f ∘ pin v) k) : Lower f (k+1) := by
  intro gs ok
  have saved := one_charge ok v e z h ft fe fz
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec out sem
  omega

theorem lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool)) (low : Set (Fin (n+1)))
    (S : Set (Signal (Fin (n+1) → Bool))) (inc : inputs (n+1) ⊆ S)
    (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  intro gs ok
  obtain ⟨v,mem,saved⟩ := double_from_classifier low f S inc nonfree classify gs ok
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec v mem out sem
  omega

theorem lower_circuit {n k : Nat} {f : Signal (Fin n → Bool)} (lb : Lower f k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP isOr := by
  obtain ⟨ops,sem,cost⟩ := of_circuit C ao
  exact cost ▸ lb ops (correct ▸ sem)

theorem lower_transport {m n k : Nat} {f : Signal (Fin n → Bool)}
    (p : (Fin m → Bool) → (Fin n → Bool))
    (raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (sub : Lower (f ∘ p) k) : Lower f k := by
  intro gs ok
  obtain ⟨out,sem,budget⟩ := restrict_transfer p gs (inputs n) (inputs m) f raw ok
  have bound := sub out sem
  omega

theorem lower_rename {m n k : Nat} {f : Signal (Fin n → Bool)} (r : Fin n → Fin m)
    (sub : Lower (fun x => f (x ∘ r)) k) : Lower f k := by
  apply lower_transport (fun x => x ∘ r) _ sub
  rintro a ⟨i,rfl⟩
  exact atom ⟨r i,rfl⟩

end ThetaPin3241

namespace ThetaCores3241
open ThetaPin3241

def row {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val
def path2 (x : Fin 2 → Bool) : Bool := (x 0 && x 1)
def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def path5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
def cycle6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def pendant7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6)

def low : Set (Fin 8) := {v | v ≠ 0 ∧ v ≠ 4}

theorem path2_lower : Lower path2 0 := lower_zero path2

theorem path3_from_core (rec : Lower path2 0) : Lower path3 1 := by
  have eq : path3 ∘ pin (2 : Fin 3) = path2 := by
    funext x
    exact (by decide +kernel : ∀ y, path3 (pin (2 : Fin 3) y) = path2 y) x
  apply lower_one_step path3 2 (row 6) (row 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path4_from_core (rec : Lower path3 1) : Lower path4 2 := by
  have eq : path4 ∘ pin (3 : Fin 4) = path3 := by
    funext x
    exact (by decide +kernel : ∀ y, path4 (pin (3 : Fin 4) y) = path3 y) x
  apply lower_one_step path4 3 (row 12) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_from_core (rec : Lower path4 2) : Lower path5 3 := by
  have eq : path5 ∘ pin (4 : Fin 5) = path4 := by
    funext x
    exact (by decide +kernel : ∀ y, path5 (pin (4 : Fin 5) y) = path4 y) x
  apply lower_one_step path5 4 (row 24) (row 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_lower : Lower path5 3 := path5_from_core (path4_from_core (path3_from_core path2_lower))

theorem pendant7_from_core (rec : Lower cycle6 5) : Lower pendant7 6 := by
  have eq : pendant7 ∘ pin (6 : Fin 7) = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, pendant7 (pin (6 : Fin 7) y) = cycle6 y) x
  apply lower_one_step pendant7 6 (row 65) (row 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRename : Fin 6 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,4,3,2,1],![1,0,4,3,2],![2,1,0,4,3],![1,2,3,4,0],![0,1,2,3,4]]

theorem cycle6_deleted (v : Fin 6) : Lower (cycle6 ∘ pin v) 3 := by
  have all : ∀ i x, (cycle6 ∘ pin i) (x ∘ cycleRename i) = path5 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle6 ∘ pin v) (x ∘ cycleRename v)) = path5 := funext (all v)
  exact eq.symm ▸ path5_lower

def thetaRename : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,2,4,3,5,1,6],![0,2,4,3,5,6,1],![0,2,4,3,6,5,1],![0,1,2,3,4,5,6],![3,1,5,6,0,4,2],![3,1,6,5,0,4,2],![3,6,1,5,0,4,2]]

theorem theta_deleted (rec : Lower cycle6 5) (v : Fin 8) (hv : v ∈ low) :
    Lower (ThetaAnd3241.theta ∘ pin v) 6 := by
  have all : ∀ i : Fin 8, i ≠ 0 ∧ i ≠ 4 → ∀ x,
      (ThetaAnd3241.theta ∘ pin i) (x ∘ thetaRename i) = pendant7 x := by
    decide +kernel
  apply lower_rename (thetaRename v)
  have eq : (fun x => (ThetaAnd3241.theta ∘ pin v) (x ∘ thetaRename v)) = pendant7 :=
    funext (all v hv)
  exact eq.symm ▸ pendant7_from_core rec

def Classifier {n : Nat} (f : Signal (Fin n → Bool)) (L : Set (Fin n))
    (S : Set (Signal (Fin n → Bool))) : Prop :=
  inputs n ⊆ S ∧ ¬ Free S f ∧
    ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ L, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S

theorem cycle6_of_classifier {S} (h : Classifier cycle6 Set.univ S) : Lower cycle6 5 :=
  lower_two_step cycle6 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle6_deleted v)

theorem theta_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) : Lower ThetaAnd3241.theta 8 :=
  lower_two_step ThetaAnd3241.theta low T th.1 th.2.1 th.2.2
    (theta_deleted (cycle6_of_classifier cycle))

theorem total_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ao : PEqualNP.TopForm.IsAO2 8 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 8 C x = ThetaAnd3241.theta x) : 12 ≤ C.size :=
  ThetaAnd3241.theta_twelve_of_eight_or C ao sem
    (lower_circuit (theta_of_classifiers cycle th) C ao (funext sem))

end ThetaCores3241

namespace ThetaClass3241
open ThetaPin3241

abbrev X (n : Nat) := Fin n → Bool
abbrev Sig (n : Nat) := Signal (X n)
def raw {n} (v : Fin n) : Sig n := fun x => x v
def bits {n} (s : Finset (Fin n)) : X n := fun i => decide (i ∈ s)

def High {n} (H : Finset (Fin n)) (a : Sig n) : Prop :=
  Monotone a ∧ ∀ x y : X n, (∀ i ∈ H, x i = y i) → a x = a y
def pool {n} (H : Finset (Fin n)) : Set (Sig n) :=
  {a | High H a ∨ ∃ i ∉ H, a = raw i}

theorem base_subset {n} (H : Finset (Fin n)) : inputs n ⊆ pool H := by
  rintro _ ⟨i,rfl⟩
  by_cases hi : i ∈ H
  · exact Or.inl ⟨fun _ _ h => h i, fun _ _ h => h i hi⟩
  · exact Or.inr ⟨i,hi,rfl⟩

theorem high_const {n} (H : Finset (Fin n)) (b : Bool) : High H (fun _ => b) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩

theorem high_join {n} {H : Finset (Fin n)} {a b : Sig n} (ha : High H a) (hb : High H b) :
    High H (join a b) := by
  constructor
  · intro x y xy
    exact sup_le_sup (ha.1 xy) (hb.1 xy)
  · intro x y h
    simp only [join,ha.2 x y h,hb.2 x y h]

theorem high_all {n} (H : Finset (Fin n)) (xs : List (Sig n))
    (hx : ∀ a ∈ xs, High H a) : High H (fun x => xs.all (fun a => a x)) := by
  induction xs with
  | nil => exact high_const H true
  | cons a xs ih =>
    have ha := hx a List.mem_cons_self
    have ht := ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))
    constructor
    · intro x y xy
      exact inf_le_inf (ha.1 xy) (ht.1 xy)
    · intro x y eq
      simp only [List.all_cons, ha.2 x y eq, ht.2 x y eq]

theorem high_or_dead {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a) :
    High H a ∨ ∃ v ∉ H, a (topMiss v) = false := by
  classical
  by_contra! bad
  obtain ⟨notHigh,live⟩ := bad
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · exact notHigh (high_const _ _)
  apply notHigh (high_all H xs ?_)
  intro f hf
  rcases hxs f hf with h | ⟨v,hv,rfl⟩
  · exact h
  · have alive : xs.all (fun g => g (topMiss v)) = true := by simpa using live v hv
    have one := List.all_eq_true.mp alive (raw v) hf
    simp [raw,topMiss] at one

theorem arm_invariant {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v : Fin n} (low : v ∉ H) (alive : a (topMiss v) = true)
    (x y : X n) (same : ∀ i, i ≠ v → x i = y i) : a x = a y := by
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · rfl
  have equal (f : Sig n) (hf : f ∈ xs) : f x = f y := by
    rcases hxs f hf with h | ⟨i,_,rfl⟩
    · exact h.2 x y (fun j hj => same j (fun eq => low (eq ▸ hj)))
    · have val := List.all_eq_true.mp alive (raw i) hf
      exact same i (by simpa [raw,topMiss] using val)
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun all f hf => equal f hf ▸ all f hf, fun all f hf => (equal f hf).symm ▸ all f hf⟩

theorem forced_raw {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v u w : Fin n} (low : v ∉ H) (ulow : u ∉ H) (diff : u ≠ w)
    (dead : a (topMiss v) = false)
    (e1 : a (bits {v,u}) = true) (e2 : a (bits {v,w}) = true) : a = raw v := by
  classical
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · contradiction
  have classify (z : Sig n) (hz : z ∈ xs) : z = (fun _ => true) ∨ z = raw v := by
    have first := List.all_eq_true.mp e1 z hz
    have second := List.all_eq_true.mp e2 z hz
    rcases hxs z hz with high | ⟨i,_,rfl⟩
    · left
      have atZero : z (fun _ => false) = true := by
        rw [← first]
        apply high.2
        intro i hi
        have iv : i ≠ v := fun eq => low (eq ▸ hi)
        have iu : i ≠ u := fun eq => ulow (eq ▸ hi)
        simp [bits,iv,iu]
      funext x
      have le := high.1 (show (fun _ : Fin n => false) ≤ x from fun _ => bot_le)
      exact Bool.eq_true_of_true_le (atZero ▸ le)
    · right
      have h1 : i = v ∨ i = u := by simpa [raw,bits] using first
      have h2 : i = v ∨ i = w := by simpa [raw,bits] using second
      have eq : i = v := by grind
      rw [eq]
  have contains : raw v ∈ xs := by
    by_contra hn
    have t : xs.all (fun a => a (topMiss v)) = true := List.all_eq_true.mpr (by
      intro z hz
      rcases classify z hz with rfl | rfl
      · rfl
      · contradiction)
    simp [t] at dead
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro all
    exact List.all_eq_true.mp all _ contains
  · intro hv
    apply List.all_eq_true.mpr
    intro z hz
    rcases classify z hz with rfl | rfl
    · rfl
    · exact hv

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241

structure Geometry {n : Nat} (H : Finset (Fin n)) (f : Sig n) : Prop where
  surviving : ∀ v ∉ H, f (topMiss v) = true
  singleton_false : ∀ u, f (bits {u}) = false
  neighbors : ∀ v ∉ H, ∃ u w, u ∉ H ∧ u ≠ w ∧
    f (bits {v,u}) = true ∧ f (bits {v,w}) = true
  poles : ∀ v ∉ H, ∃ u, f (bits {v,u}) = true ∧ f (bits (insert u H)) = false
  twins : ∀ v ∉ H, ∀ w ∉ H, v ≠ w → ∃ u, f (bits {v,u}) = true ∧ f (bits {u,w}) = false

def Checks {n} (H : Finset (Fin n)) (f a b : Sig n) : Prop := ∀ v ∉ H,
  deadAt (topMiss v) (a,b) = true → Admissible (inputs n) f (topMiss v) (a,b)

theorem checks_swap {n} {H : Finset (Fin n)} {f a b : Sig n} (c : Checks H f a b) :
    Checks H f b a := by
  intro v hv hd e z pass ft fe fz
  have h := c v hv (by simpa [deadAt,Bool.and_comm] using hd) e z pass ft fe fz
  simpa only [join,Bool.or_comm] using h

theorem probe {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    {v u : Fin n} (hv : v ∉ H) (c : Checks H f a b) (dead : a (topMiss v) = false)
    (z : Finset (Fin n)) (inside : u ∈ z) (fe : f (bits {v,u}) = true) (fz : f (bits z) = false) :
    join a b (topMiss v) = true ∧ join a b (bits {v,u}) = true ∧ join a b (bits z) = false := by
  apply c v hv (by simp [deadAt,dead]) _ _ _ (geo.surviving v hv) fe fz
  apply pass_inputs
  intro i ti ei
  have ne : i ≠ v := by simpa [topMiss] using ti
  have eq : i = u := by simpa [bits,ne] using ei
  simpa [bits,eq] using inside

theorem collapse {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : a = raw v := by
  obtain ⟨u,w,lu,ne,eu,ew⟩ := geo.neighbors v hv
  have activate (i : Fin n) (e : f (bits {v,i}) = true) : a (bits {v,i}) = true := by
    obtain ⟨st,se,sz⟩ := probe geo hv c dead {i} (by simp) e (geo.singleton_false i)
    have live : b (topMiss v) = true := by simpa [join,dead] using st
    have same := arm_invariant hb hv live (bits {v,i}) (bits {i}) (fun j hj => by simp [bits,hj])
    have bz : b (bits {i}) = false := (Bool.or_eq_false_iff.mp sz).2
    simpa [join,same,bz] using se
  exact forced_raw ha hv lu ne dead (activate u eu) (activate w ew)

theorem reject_side {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : False := by
  have av := collapse geo ha hb c hv dead
  rcases high_or_dead hb with high | ⟨w,hw,dw⟩
  · obtain ⟨u,eu,zu⟩ := geo.poles v hv
    obtain ⟨st,_,sz⟩ := probe geo hv c dead (insert u H) (by simp) eu zu
    have bt : b (topMiss v) = true := by simpa [join,dead] using st
    have bz : b (bits (insert u H)) = false := (Bool.or_eq_false_iff.mp sz).2
    have eq := high.2 (topMiss v) (bits (insert u H)) (fun i hi => by
      have ne : i ≠ v := fun e => hv (e ▸ hi)
      simp [topMiss,bits,ne,hi])
    simp [bt,bz] at eq
  · have bw := collapse geo hb ha (checks_swap c) hw dw
    have ne : v ≠ w := by
      rintro rfl
      obtain ⟨u,_,_,_,eu,_⟩ := geo.neighbors v hv
      have st := (probe geo hv c dead {u} (by simp) eu (geo.singleton_false u)).1
      simp [join,dead,dw] at st
    obtain ⟨u,eu,zu⟩ := geo.twins v hv w hw ne
    have sz := (probe geo hv c dead {u,w} (by simp) eu zu).2.2
    simp [join,bw,raw,bits] at sz

theorem classify {n} {H : Finset (Fin n)} {f : Sig n} (geo : Geometry H f)
    (g : Gate (X n)) (ha : Free (pool H) g.1) (hb : Free (pool H) g.2)
    (c : ∀ v ∈ {v | v ∉ H}, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) :
    join g.1 g.2 ∈ pool H := by
  have ck : Checks H f g.1 g.2 := c
  rcases high_or_dead ha with aa | ⟨v,hv,dead⟩
  · rcases high_or_dead hb with bb | ⟨v,hv,dead⟩
    · exact Or.inl (high_join aa bb)
    · exact (reject_side geo hb ha (checks_swap ck) hv dead).elim
  · exact (reject_side geo ha hb ck hv dead).elim

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241 ThetaCores3241

theorem nonfree {n} (f : Sig n) (H : Finset (Fin n)) (x y z : X n)
    (hhigh : ∀ i ∈ H, x i = z i) (draw : ∀ i, x i = true → y i = true → z i = true)
    (fx : f x = true) (fy : f y = true) (fz : f z = false) : ¬ Free (pool H) f := by
  intro ok
  have base : ∀ a ∈ pool H, Pass x y z a := by
    intro a ha
    rcases ha with h | ⟨i,_,rfl⟩
    · intro ax _
      exact (h.2 x z hhigh) ▸ ax
    · exact draw i
  have pos := free_pass base ok fx fy
  simp [fz] at pos

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cycle_geo : Geometry ∅ cycle6 := by constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem theta_geo : Geometry {0,4} ThetaAnd3241.theta := by constructor <;> decide +kernel

theorem cycle_classifier : Classifier cycle6 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle6 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem theta_classifier : Classifier ThetaAnd3241.theta low (pool {0,4}) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree ThetaAnd3241.theta {0,4} (bits {1,7}) (bits {2,6}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    apply classify theta_geo g a b
    intro v hv
    apply h v
    simpa [low,Set.mem_ofPred_eq,not_or] using hv

theorem theta_total (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 8 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 8 C x = ThetaAnd3241.theta x) : 12 ≤ C.size :=
  total_of_classifiers cycle_classifier theta_classifier C ao sem

end ThetaClass3241

namespace ThetaPrune3241
open ThetaPin3241

def Private {α : Type} (P : Set α) (g : Gate α) : Prop :=
  (∃ e ∈ P, g.1 e = true ∧ g.2 e = false) ∧
  (∃ e ∈ P, g.2 e = true ∧ g.1 e = false)

def Refines {α : Type} (P : Set α) (new old : Signal α) : Prop :=
  (∀ e ∈ P, new e = old e) ∧ (∀ x, new x = true → old x = true)

theorem self_refines {α : Type} (P : Set α) (f : Signal α) : Refines P f f :=
  ⟨fun _ _ => rfl,fun _ h => h⟩

theorem ref_meet {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (meet a c) (meet b d) := by
  constructor
  · intro e he
    simp [meet,h.1 e he,i.1 e he]
  · intro x hx
    obtain ⟨hx,hy⟩ : a x = true ∧ c x = true := by simpa [meet] using hx
    simp [meet,h.2 x hx,i.2 x hy]

theorem ref_join {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (join a c) (join b d) := by
  constructor
  · intro e he
    simp [join,h.1 e he,i.1 e he]
  · intro x hx
    have one : a x = true ∨ c x = true := by simpa [join] using hx
    rcases one with p | p
    · simp [join,h.2 x p]
    · simp [join,i.2 x p]

theorem ref_comp {α : Type} {P : Set α} {a b c : Signal α}
    (h : Refines P a b) (i : Refines P b c) : Refines P a c :=
  ⟨fun e he => (h.1 e he).trans (i.1 e he),fun x p => i.2 x (h.2 x p)⟩

theorem refine_free {α : Type} (P : Set α) {B D : Set (Signal α)}
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) {a} (ok : Free B a) :
    ∃ b, Free D b ∧ Refines P b a := by
  apply ok {a | ∃ b, Free D b ∧ Refines P b a}
  · exact base
  · exact ⟨_,free_zero,self_refines _ _⟩
  · exact ⟨_,free_one,self_refines _ _⟩
  · intro a ha b hb
    obtain ⟨c,hc,rc⟩ := ha
    obtain ⟨d,hd,rd⟩ := hb
    exact ⟨meet c d,free_meet hc hd,ref_meet rc rd⟩

theorem choose_arm {α : Type} {P : Set α} {g : Gate α} (bad : ¬ Private P g) :
    ∃ u, (u = g.1 ∨ u = g.2) ∧ Refines P u (join g.1 g.2) := by
  classical
  by_cases left : ∃ e ∈ P, g.1 e = true ∧ g.2 e = false
  · have right : ¬∃ e ∈ P, g.2 e = true ∧ g.1 e = false := fun h => bad ⟨left,h⟩
    refine ⟨g.1,Or.inl rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact right ⟨e,he,b,a⟩
  · refine ⟨g.2,Or.inr rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact left ⟨e,he,a,b⟩

theorem prune {α : Type} (P : Set α) (B D : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) (ok : Valid B gs f) :
    ∃ out f', Valid D out f' ∧ Refines P f' f ∧ out.length ≤ gs.length ∧
      ∀ g ∈ out, Private P g := by
  classical
  induction gs generalizing B D with
  | nil =>
    obtain ⟨f',h,r⟩ := refine_free P base ok
    exact ⟨[],f',h,r,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    obtain ⟨a,fa,ra⟩ := refine_free P base ha
    obtain ⟨b,fb,rb⟩ := refine_free P base hb
    have combined := ref_join ra rb
    by_cases use : Private P (a,b)
    · let D' := insert (join a b) D
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D' w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨join a b, atom (Set.mem_insert _ _), combined⟩
        · obtain ⟨w,hw,hv⟩ := base _ old
          exact ⟨w,widen (Set.subset_insert _ _) hw,hv⟩
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D' next tail
      refine ⟨(a,b)::out,f',⟨fa,fb,sem⟩,r,by simpa using cost,?_⟩
      intro u hu
      exact (List.mem_cons.mp hu).elim (fun h => h ▸ use) (all u)
    · obtain ⟨u,side,ref⟩ := choose_arm use
      have fu : Free D u := side.elim (fun h => h ▸ fa) (fun h => h ▸ fb)
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨u,fu,ref_comp ref combined⟩
        · exact base _ old
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D next tail
      exact ⟨out,f',sem,r,by simp; omega,all⟩

theorem increasing_output {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) : Increasing f := by
  induction gs generalizing B with
  | nil => exact free_increasing base ok
  | cons g gs ih =>
    obtain ⟨l,r,tail⟩ := ok
    apply ih _ tail
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | old
    · intro x y le hx
      have either : g.1 x = true ∨ g.2 x = true := by simpa [join] using hx
      rcases either with h | h
      · simp [join,free_increasing base l x y le h]
      · simp [join,free_increasing base r x y le h]
    · exact base _ old

def Generates {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x, f x = true → ∃ e ∈ P, f e = true ∧ ∀ i, e i = true → x i = true

theorem private_program {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool))
    (cover : Generates P f) (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ out, Valid (inputs n) out f ∧ out.length ≤ gs.length ∧ ∀ g ∈ out, Private P g := by
  have ids : ∀ a ∈ inputs n, ∃ b, Free (inputs n) b ∧ Refines P b a :=
    fun a h => ⟨a,atom h,self_refines _ _⟩
  obtain ⟨out,v,sem,ref,cost,all⟩ := prune P _ _ gs f ids ok
  have mon := increasing_output (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) sem
  have eq : v = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨ref.2 x,?_⟩
    intro h
    obtain ⟨e,pe,pos,le⟩ := cover x h
    exact mon e x le ((ref.1 e pe).trans pos)
  exact ⟨out,eq ▸ sem,cost,all⟩

theorem private_lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (low : Set (Fin (n+1))) (S : Set (Signal (Fin (n+1) → Bool))) (P : Set (Fin (n+1) → Bool))
    (inc : inputs (n+1) ⊆ S) (nonfree : ¬ Free S f) (cover : Generates P f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  classical
  intro gs ok
  obtain ⟨out,sem,short,priv⟩ := private_program P f cover gs ok
  have hit : ∃ v ∈ low, 2 ≤ out.countP (deadAt (topMiss v)) := by
    by_contra no
    apply nonfree
    apply propagate_property (inputs _) S out f inc sem
    intro g hg a b
    apply classify g a b (priv g hg)
    intro v hv dg e z raw ft fe fz
    have small : out.countP (deadAt (topMiss v)) ≤ 1 := by
      by_contra h
      exact no ⟨v,hv,by omega⟩
    exact single_charge_passes sem g hg (topMiss v) e z raw ft fe fz dg small
  obtain ⟨v,hv,charge⟩ := hit
  obtain ⟨sub,sok,cost⟩ := delete_charge sem v
  have lb := rec v hv sub sok
  omega

end ThetaPrune3241

namespace Theta244Cores
open ThetaPin3241 ThetaCores3241 ThetaPrune3241
def path6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)
def path7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def cycle8 (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 0)
def twoEnds (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 2 && x 7)
def tailTwo (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 6 && x 7)
def theta (x : Fin 9 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)

theorem path6_lower (rec : Lower path5 3) : Lower path6 4 := by
  have eq : path6 ∘ pin (5 : Fin 6) = path5 := by
    funext x
    exact (by decide +kernel : ∀ y, path6 (pin (5 : Fin 6) y) = path5 y) x
  apply lower_one_step path6 5 (row 48) (row 16)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path7_lower (rec : Lower path6 4) : Lower path7 5 := by
  have eq : path7 ∘ pin (6 : Fin 7) = path6 := by
    funext x
    exact (by decide +kernel : ∀ y, path7 (pin (6 : Fin 7) y) = path6 y) x
  apply lower_one_step path7 6 (row 96) (row 32)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem twoEnds_lower (rec : Lower pendant7 6) : Lower twoEnds 7 := by
  have eq : twoEnds ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, twoEnds (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step twoEnds 7 (row 132) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem tailTwo_lower (rec : Lower pendant7 6) : Lower tailTwo 7 := by
  have eq : tailTwo ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, tailTwo (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step tailTwo 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRelabel : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,6,5,4,3,2,1],![1,0,6,5,4,3,2],![2,1,0,6,5,4,3],![3,2,1,0,6,5,4],![2,3,4,5,6,0,1],![1,2,3,4,5,6,0],![0,1,2,3,4,5,6]]
def thetaRelabel : Fin 9 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,4,1,2,3,7,6,5],![2,0,1,7,6,3,4,5],![0,2,1,6,7,5,4,3],![0,2,1,6,7,5,4,3],![2,0,1,3,4,5,7,6],![0,2,1,5,4,3,6,7],![0,2,1,5,4,3,6,7]]
def lows : Set (Fin 9) := {v | 2 ≤ v.val}
def cofactor (v : Fin 9) :=
  if v = 2 then cycle8 else if v = 4 ∨ v = 7 then twoEnds else tailTwo

theorem cycle8_deleted (v : Fin 8) : Lower (cycle8 ∘ pin v) 5 := by
  have all : ∀ i x, (cycle8 ∘ pin i) (x ∘ cycleRelabel i) = path7 x := by decide +kernel
  apply lower_rename (cycleRelabel v)
  have eq : (fun x => (cycle8 ∘ pin v) (x ∘ cycleRelabel v)) = path7 := funext (all v)
  exact eq.symm ▸ path7_lower (path6_lower path5_lower)

theorem theta_deleted (h6 : Lower cycle6 5) (h8 : Lower cycle8 7) (v : Fin 9) (hv : v ∈ lows) :
    Lower (theta ∘ pin v) 7 := by
  have all : ∀ i : Fin 9, 2 ≤ i.val → ∀ x, (theta ∘ pin i) (x ∘ thetaRelabel i) = cofactor i x := by
    decide +kernel
  apply lower_rename (thetaRelabel v)
  have eq : (fun x => (theta ∘ pin v) (x ∘ thetaRelabel v)) = cofactor v := funext (all v hv)
  rw [eq]
  unfold cofactor
  split
  · exact h8
  · split
    · exact twoEnds_lower (pendant7_from_core h6)
    · exact tailTwo_lower (pendant7_from_core h6)

theorem cycle8_of_classifier {S} (h : Classifier cycle8 Set.univ S) : Lower cycle8 7 :=
  lower_two_step cycle8 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle8_deleted v)

def positive : Set (Fin 9 → Bool) := {x |
  ∃ i j : Fin 9, ((i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat))) ∧
    x = row (2^i.val+2^j.val)}

theorem generates : Generates positive theta := by
  intro x hx
  have all : ∀ y : Fin 9 → Bool, theta y = true →
      ∃ i j : Fin 9, (i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat)) ∧
        theta (row (2^i.val+2^j.val)) = true ∧ ∀ l : Fin 9, row (2^i.val+2^j.val) l = true → y l = true := by
    decide +kernel
  obtain ⟨i,j,edge,yes,le⟩ := all x hx
  exact ⟨_,⟨i,j,edge,rfl⟩,yes,le⟩

end Theta244Cores

namespace Theta244Finish
open ThetaPin3241 ThetaPrune3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem cycle_geo : Geometry ∅ cycle8 := by constructor <;> decide +kernel

theorem cycle_classifier : ThetaCores3241.Classifier cycle8 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle8 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem deleted (v : Fin 9) (hv : v ∈ lows) : Lower (theta ∘ pin v) 7 :=
  theta_deleted (ThetaCores3241.cycle6_of_classifier ThetaClass3241.cycle_classifier)
    (cycle8_of_classifier cycle_classifier) v hv

theorem nine_of_classifier {P : Set (Fin 9 → Bool)} {S : Set (Signal (Fin 9 → Bool))}
    (base : inputs 9 ⊆ S) (nonfree : ¬ Free S theta) (cover : Generates P theta)
    (classify : ∀ g : Gate (Fin 9 → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ lows, deadAt (topMiss v) g = true → Admissible (inputs 9) theta (topMiss v) g) →
      join g.1 g.2 ∈ S) : Lower theta 9 :=
  private_lower_two_step theta lows S P base nonfree cover classify deleted

def eleven : Fin 11 → Finset (Fin 9) :=
  ![{1,3,6}, {1,4,6}, {1,3,7}, {0,1,4,7}, {2,4,7}, {0,5,7}, {2,3,5,7}, {0,4,8},
    {0,5,8}, {2,4,6,8}, {2,3,5,6,8}]

theorem theta_total_of_or (lb : Lower theta 9) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (ao : PEqualNP.TopForm.IsAO2 9 C) (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = theta x) :
    13 ≤ C.size := by
  have no : ∀ i, theta (PEqualNP.ReadK.setInput (eleven i)) = false := by decide +kernel
  have yes : ∀ i j, i ≠ j → theta (PEqualNP.ReadK.setInput (eleven i ∪ eleven j)) = true := by
    decide +kernel
  have ands := ThetaAnd3241.false_family_bound C ao eleven (fun i => (sem _).trans (no i))
    (fun i j h => (sem _).trans (yes i j h))
  have ors := lower_circuit lb C ao (funext sem)
  change 9 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ors
  by_contra low
  have limit : C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) ≤ 3 := by omega
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) limit
  omega

def upper : PEqualNP.CircuitLowerBounds.Circuit := ⟨
  [⟨.or,[2,3]⟩,⟨.or,[9,6]⟩,⟨.and,[0,10]⟩,
   ⟨.or,[2,5]⟩,⟨.or,[12,8]⟩,⟨.and,[1,13]⟩,
   ⟨.or,[3,5]⟩,⟨.and,[4,15]⟩,⟨.or,[6,8]⟩,⟨.and,[7,17]⟩,
   ⟨.or,[11,14]⟩,⟨.or,[16,18]⟩,⟨.or,[19,20]⟩],21⟩

theorem upper_ok : PEqualNP.TopForm.IsAO2 9 upper ∧ upper.size = 13 ∧
    upper.gates.countP isOr = 9 ∧
    ∀ x, PEqualNP.MetaComplexity.circuitFun 9 upper x = theta x := by decide +kernel

end Theta244Finish

namespace Theta244
open ThetaPin3241
abbrev X := Fin 9 → Bool
abbrev W := BitVec 28
def readBit (w : W) (i : Fin 28) : Bool := w[i.val]
def rowMasks : List Nat := [5,6,9,24,48,34,65,192,384,258,74,82,138,147,148,161,172,273,289,340,364,507,503,495,479,447,383,255]
def row (i : Fin 28) (v : Fin 9) : Bool := (rowMasks.getD i.val 0).testBit v.val
def target (x : X) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)
def code : W := 266339327
def rawMasks : List W := [266772549,266354210,265895939,263263244,258631704,250970160,234360000,199356800,134087424]
def base : List W := [0,134087424,199356800,234360000,250970160,258631704,263263244,265895939,266346496,266354210,266772549,266780263,268435455]
def arm : List W := [0,2097152,4194304,6291456,8388608,10485760,12582912,14680064,16777216,18874368,20971520,23068672,25165824,27262976,29360128,31457280,33554432,35651584,37748736,39845888,41943040,44040192,46137344,48234496,50331648,52428800,54525952,56623104,58720256,60817408,62914560,65011712,65011968,67108864,69206016,71303168,73400320,75497472,76546048,77594624,78643200,79691776,80740352,81788928,82837504,83886080,85983232,88080384,88604672,90177536,90701824,92274688,93323264,94371840,95420416,96468992,98041856,98566144,100139008,100663296,102760448,104857600,106954752,109051904,110100480,111149056,112197632,113246208,114294784,115343360,115605504,116654080,117440512,119537664,121634816,122159104,123731968,123863040,124387328,125829120,126877696,127926272,128974848,130023424,131596288,132120576,132121088,132513792,132514304,134087424,134217728,136314880,138412032,140509184,142606336,144703488,146800640,148897792,150994944,153092096,155189248,157286400,159383552,161480704,163577856,165675008,165675136,167772160,169869312,171966464,174063616,176160768,176226304,178257920,178323456,180355072,180420608,182452224,182484992,182550528,184549376,186646528,188743680,188760064,190849024,190865408,192937984,193003520,195035136,195039232,195104768,197132288,197214208,199237632,199241728,199270400,199274496,199356800,201326592,203423744,205520896,207618048,209715200,210763776,211812352,212860928,213909504,214958080,216006656,217055232,218103808,220200960,222298112,222822400,224395264,224397312,224921600,226492416,227540992,228589568,228590592,229639168,230686720,232259584,232783872,232783936,232786944,232787008,234360000,234881024,236978176,239075328,241172480,241172496,243269632,244383744,245366784,246480896,247463936,248578048,249561088,249561120,249856000,249856032,250970160,251658240,253755392,253755400,255852544,256393216,257957888,257959936,258088960,258091008,258631704,260046848,261160960,262144000,262144004,262149120,262149124,263263244,264241152,264241153,264241154,264241155,265895939,266346496,266354210,266772549,266780263,268435455]
def posArm : List W := [65011968,132121088,132514304,134087424,165675136,199356800,232783936,232787008,234360000,241172496,249561120,249856032,250970160,253755400,258631704,262144004,262149124,263263244,264241153,264241154,264241155,265895939,266354210,266772549,266780263,268435455]
structure Test where
  v : Fin 9
  t : Fin 28
  e : Fin 28
  z : Fin 28
  deriving DecidableEq
def tests : List Test := [⟨2,21,0,13⟩,⟨2,21,0,15⟩,⟨2,21,0,17⟩,⟨2,21,0,18⟩,⟨2,21,1,10⟩,⟨2,21,1,11⟩,⟨2,21,1,12⟩,⟨2,21,1,13⟩,⟨3,22,2,13⟩,⟨3,22,2,15⟩,⟨3,22,2,17⟩,⟨3,22,2,18⟩,⟨3,22,3,11⟩,⟨3,22,3,13⟩,⟨3,22,3,14⟩,⟨3,22,3,17⟩,⟨3,22,3,19⟩,⟨4,23,3,10⟩,⟨4,23,3,12⟩,⟨4,23,3,16⟩,⟨4,23,3,20⟩,⟨4,23,4,15⟩,⟨4,23,4,16⟩,⟨4,23,4,18⟩,⟨4,23,4,20⟩,⟨5,24,4,11⟩,⟨5,24,4,13⟩,⟨5,24,4,14⟩,⟨5,24,4,17⟩,⟨5,24,4,19⟩,⟨5,24,5,10⟩,⟨5,24,5,11⟩,⟨5,24,5,12⟩,⟨5,24,5,13⟩,⟨6,25,6,13⟩,⟨6,25,6,15⟩,⟨6,25,6,17⟩,⟨6,25,6,18⟩,⟨6,25,7,12⟩,⟨6,25,7,13⟩,⟨6,25,7,14⟩,⟨6,25,7,15⟩,⟨6,25,7,16⟩,⟨7,26,7,10⟩,⟨7,26,7,11⟩,⟨7,26,7,19⟩,⟨7,26,7,20⟩,⟨7,26,8,17⟩,⟨7,26,8,18⟩,⟨7,26,8,19⟩,⟨7,26,8,20⟩,⟨8,27,8,12⟩,⟨8,27,8,13⟩,⟨8,27,8,14⟩,⟨8,27,8,15⟩,⟨8,27,8,16⟩,⟨8,27,9,10⟩,⟨8,27,9,11⟩,⟨8,27,9,12⟩,⟨8,27,9,13⟩]
def edgeIdx (i : Fin 10) : Fin 28 := i.castLE (by decide)
def positives : Set X := Set.range (fun i : Fin 10 => row (edgeIdx i))
def low : Set (Fin 9) := {v | 2 ≤ v.val}
def represents (a : Signal X) (w : W) : Prop := ∀ i, a (row i) = readBit w i
def pool : Set (Signal X) := {a | ∃ w ∈ base, represents a w}

def privateMask (a b : W) : Prop :=
  (∃ i : Fin 10, readBit a (edgeIdx i) = true ∧ readBit b (edgeIdx i) = false) ∧
  (∃ i : Fin 10, readBit b (edgeIdx i) = true ∧ readBit a (edgeIdx i) = false)

def good (a b : W) (q : Test) : Prop :=
  (readBit a q.t && readBit b q.t) = false →
    readBit (a ||| b) q.t = true ∧ readBit (a ||| b) q.e = true ∧ readBit (a ||| b) q.z = false

instance (a b : W) : Decidable (privateMask a b) := by unfold privateMask; infer_instance
instance (a b : W) (q : Test) : Decidable (good a b q) := by unfold good; infer_instance

theorem and_table (a b : W) (ha : a ∈ posArm) (hb : b ∈ base)
    (i : Fin 10) (hit : readBit (b &&& a) (edgeIdx i) = true) : (b &&& a) ∈ posArm := by
  have table : posArm.all (fun u => base.all (fun v => posArm.contains (v &&& u) ||
      decide (∀ j : Fin 10, readBit (v &&& u) (edgeIdx j) = false))) = true := by decide +kernel
  have either := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  rcases Bool.or_eq_true_iff.mp either with yes | no
  · simpa using yes
  · have v := of_decide_eq_true no i
    simp [hit] at v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem or_table (a : W) (ha : a ∈ posArm) (b : W) (hb : b ∈ posArm)
    (p : privateMask a b) (h : ∀ q ∈ tests, good a b q) : (a ||| b) ∈ base := by
  have table : posArm.all (fun u => posArm.all (fun v =>
      base.contains (u ||| v) || !decide (privateMask u v) ||
      !tests.all (fun q => decide (good u v q)))) = true := by decide +kernel
  have atPair := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  have gates : tests.all (fun q => decide (good a b q)) = true :=
    List.all_eq_true.mpr (fun q hq => decide_eq_true (h q hq))
  simpa [p,gates] using atPair

theorem probes : ∀ q ∈ tests, 2 ≤ q.v.val ∧ (∀ i, row q.t i = topMiss q.v i) ∧
    target (row q.t) = true ∧ target (row q.e) = true ∧ target (row q.z) = false ∧
    ∀ i, row q.t i = true → row q.e i = true → row q.z i = true := by decide +kernel

theorem represent_and {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (meet a b) (u &&& v) := by
  intro i
  simp [meet,ha i,hb i,readBit]

theorem represent_or {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (join a b) (u ||| v) := by
  intro i
  simp [join,ha i,hb i,readBit]

theorem free_arm {a : Signal X} (h : Free pool a) (i : Fin 10) (onEdge : a (row (edgeIdx i)) = true) :
    ∃ w ∈ posArm, represents a w := by
  rcases factors h with rfl | ⟨xs,hs,rfl⟩
  · contradiction
  · clear h
    induction xs with
    | nil => exact ⟨268435455,by decide +kernel,(by decide +kernel : ∀ i : Fin 28, true = readBit 268435455 i)⟩
    | cons a xs ih =>
      obtain ⟨u,hu,ra⟩ := hs a (by simp)
      obtain ⟨_,tail⟩ := Bool.and_eq_true_iff.mp onEdge
      obtain ⟨v,hv,rs⟩ := ih (fun b hb => hs b (by simp [hb])) tail
      have allRep : represents (fun x => (a::xs).all (fun f => f x)) (u &&& v) := by
        intro k
        change ((a::xs).all (fun f => f (row k))) = _
        rw [List.all_cons]
        exact (represent_and ra rs) k
      exact ⟨_,and_table v u hv hu i ((allRep _).symm.trans onEdge),allRep⟩

theorem inputs_pool : inputs 9 ⊆ pool := by
  rintro _ ⟨i,rfl⟩
  have tab : ∀ j : Fin 9, rawMasks.getD j.val 0 ∈ base ∧
      ∀ k, row k j = readBit (rawMasks.getD j.val 0) k := by decide +kernel
  exact ⟨_,(tab i).1,(tab i).2⟩

theorem target_nonfree : ¬ Free pool target := by
  intro h
  obtain ⟨a,ha,rep⟩ := free_arm h 0 (by decide +kernel)
  have fixed : ∀ i : Fin 28, target (row i) = readBit code i := by decide +kernel
  have different : code ∉ posArm := by decide +kernel
  have eq : a = code := by
    apply BitVec.eq_of_getElem_eq
    intro k hk
    exact (rep ⟨k,hk⟩).symm.trans (fixed ⟨k,hk⟩)
  exact different (eq ▸ ha)

theorem classify (g : Gate X) (fa : Free pool g.1) (fb : Free pool g.2)
    (priv : ThetaPrune3241.Private positives g)
    (valid : ∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs 9) target (topMiss v) g) :
    join g.1 g.2 ∈ pool := by
  obtain ⟨⟨_,⟨i,rfl⟩,ia,ib⟩,⟨_,⟨j,rfl⟩,jb,ja⟩⟩ := priv
  obtain ⟨a,pa,ra⟩ := free_arm fa i ia
  obtain ⟨b,pb,rb⟩ := free_arm fb j jb
  rw [ra] at ia ja
  rw [rb] at ib jb
  have joined := represent_or ra rb
  refine ⟨_,or_table a pa b pb ⟨⟨i,ia,ib⟩,⟨j,jb,ja⟩⟩ ?_,joined⟩
  intro q hq dead
  obtain ⟨lo,point,ft,fe,fz,pass⟩ := probes q hq
  have eq := funext point
  have dg : deadAt (topMiss q.v) g = true := by
    simp [← eq,deadAt,ra q.t,rb q.t,dead]
  have adm := valid q.v lo dg
  rw [← eq] at adm
  obtain ⟨st,se,sz⟩ := adm (row q.e) (row q.z) (pass_inputs _ _ _ pass) ft fe fz
  exact ⟨(joined q.t).symm.trans st,(joined q.e).symm.trans se,(joined q.z).symm.trans sz⟩

theorem generates : ThetaPrune3241.Generates positives target := by
  have all : ∀ x : X, target x = true → ∃ i : Fin 10, target (row (edgeIdx i)) = true ∧
      ∀ j, row (edgeIdx i) j = true → x j = true := by decide +kernel
  intro x hx
  obtain ⟨i,yes,le⟩ := all x hx
  exact ⟨_,⟨i,rfl⟩,yes,le⟩

theorem nine : Lower Theta244Cores.theta 9 :=
  Theta244Finish.nine_of_classifier inputs_pool target_nonfree generates classify

theorem thirteen (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 9 C)
    (sem : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = target x) : 13 ≤ C.size :=
  Theta244Finish.theta_total_of_or nine C ao sem

end Theta244

namespace LeafAnd3241
open ThetaPin3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev X (n : Nat) := Fin n → Bool
def dual {n : Nat} (f : Signal (X n)) : Signal (X n) := fun x => !(f fun i => !(x i))

theorem dual_wire {n : Nat} {B : Set (Signal (X n))} {w : List (Signal (X n))}
    (hw : ∀ a ∈ w, Free B (dual a)) (i : Nat) : Free B (dual (wire w i)) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_one
  | cons a w ih => cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

theorem dual_compress {n : Nat} (gs : List PhysicalGate) (output : Nat) (w : List (Signal (X n)))
    (B : Set (Signal (X n))) (hw : ∀ a ∈ w, Free B (dual a)) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (ThetaPin3241.Gate (X n)), Valid B ops (dual (wire (gs.foldl step w) output)) ∧
      ops.length = gs.countP ThetaAnd3241.andGate := by
  induction gs generalizing w B with
  | nil => exact ⟨[],dual_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    let a := dual (wire w i)
    let b := dual (wire w j)
    rcases hop with kind | kind
    · let D := insert (join a b) B
      have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_and : dual (meet (wire w i) (wire w j)) = join a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_and]
      have ext : ∀ f ∈ step w g, Free D (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact widen (Set.subset_insert _ _) (hw f old)
        · rw [dual_and]
          exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨dual_wire hw i,dual_wire hw j,sem⟩,?_⟩
      have yes : ThetaAnd3241.andGate g = true := by simp [ThetaAnd3241.andGate,kind]
      simp [cost,yes]
    · have eq : step w g = w ++ [join (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_or : dual (join (wire w i) (wire w j)) = meet a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_or]
      have ext : ∀ f ∈ step w g, Free B (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact hw f old
        · rw [dual_or]
          exact free_meet (dual_wire hw i) (dual_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : ThetaAnd3241.andGate g = false := by simp [ThetaAnd3241.andGate,kind]
      simpa [no] using cost

theorem and_lower_circuit {n k : Nat} (f : Signal (X n)) (lb : Lower (dual f) k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP ThetaAnd3241.andGate := by
  let w : List (Signal (X n)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) (dual a) := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    apply atom
    exact ⟨i,funext (fun x => by simp [dual])⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := dual_compress C.gates C.output w (inputs n) ok shapes
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  rw [eq,correct] at sem
  exact cost ▸ lb ops sem

theorem save_at {m n k : Nat} (f : Signal (X n)) (v : Fin n) (e z : X n) (p : X m → X n)
    (inputs_ok : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (bounded : ∀ x i, p x i = true → topMiss v i = true)
    (pass : ∀ i, topMiss v i = true → e i = true → z i = true)
    (top : f (topMiss v) = true) (edge : f e = true) (neg : f z = false)
    (sub : Lower (f ∘ p) k) : Lower f (k+1) := by
  intro gs ok
  obtain ⟨g,hg,dead,_⟩ := critical_gate gs (inputs n) f _ _ _ (pass_inputs _ _ _ pass) ok top edge neg
  obtain ⟨l,r⟩ := active_monotone (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) ok g hg
  have zero {a : Signal (X n)} (inc : Increasing a) (off : a (topMiss v) = false) :
      ∀ x, a (p x) = false := by
    intro x
    cases h : a (p x) with
    | false => rfl
    | true => simp [inc _ _ (bounded x) h] at off
  have killed : Killed p g := dead.imp (zero l) (zero r)
  have charge : 0 < gs.countP (killedBit p) :=
    List.countP_pos_iff.mpr ⟨g,hg,by simp [killedBit,killed]⟩
  obtain ⟨out,sem,cost⟩ := restrict_transfer p gs _ _ f inputs_ok ok
  have lower := sub out sem
  omega

def cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∀ a b, G.Adj a b → x a = true ∨ x b = true)

theorem cover_dual {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    dual (NestedCover.graphFun G ∅) = cover G := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [dual,NestedCover.graphFun,cover]
  grind

def pinLeaf {n : Nat} (v w : Fin n) (x : X n) (i : Fin n) : Bool :=
  if i = v then false else if i = w then true else x i

theorem leaf_step {n k : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (adj : G.Adj v w) (leaf : ∀ i, G.Adj v i → i = w)
    (sub : Lower (cover (G.deleteIncidenceSet w)) k) : Lower (cover G) (k+1) := by
  have ne := G.ne_of_adj adj
  have hi (i : Fin n) : cover G (topMiss i) = true := by
    simp only [cover,decide_eq_true_eq,topMiss]
    intro a b ab
    by_cases av : a = i
    · exact Or.inr (fun (bv : b = i) => G.ne_of_adj ab (av.trans bv.symm))
    · exact Or.inl (by simp [av])
  let z : X n := fun i => decide (i ≠ v ∧ i ≠ w)
  have neg : cover G z = false := by
    apply decide_eq_false_iff_not.mpr
    intro h
    simpa [z] using h v w adj
  have cof : cover G ∘ pinLeaf v w = cover (G.deleteIncidenceSet w) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · intro h a b ⟨ab,aw,bw⟩
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ab
    · intro h a b ab
      by_cases aw : a = w
      · simp [pinLeaf,aw,ne.symm]
      by_cases bw : b = w
      · simp [pinLeaf,bw,ne.symm]
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ⟨ab,aw,bw⟩
  apply save_at (cover G) v (topMiss w) z (pinLeaf v w) _ _ _ (hi v) (hi w) neg (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinLeaf,iv] using (free_zero (B := inputs n))
    by_cases iw : i = w
    · simpa [Function.comp_def,pinLeaf,iv,iw,ne.symm] using (free_one (B := inputs n))
    · simpa [Function.comp_def,pinLeaf,iv,iw] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i pi
    by_contra h
    have iv : i = v := by simpa [topMiss] using h
    simp [pinLeaf,iv] at pi
  · intro i tv tw
    simpa [z,topMiss] using And.intro tv tw

end LeafAnd3241

namespace LeafCore3241
open ThetaPin3241 LeafAnd3241 PEqualNP.MetaComplexity PEqualNP.TopForm

def edgeFun {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)

theorem ordinary_eq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    NestedCover.graphFun G ∅ = edgeFun G := by
  funext x
  simp [NestedCover.graphFun,edgeFun]

def Leafless {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ ∃ v w, G.Adj v w ∧ ∀ a, G.Adj v a → a = w

def Counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Lower (edgeFun G) (G.edgeFinset.card - 1) ∧
    ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ Lower (cover G) S.card

def pinZero {n : Nat} (v : Fin n) (x : X n) (i : Fin n) := if i = v then false else x i

theorem or_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (vw : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (sub : Lower (edgeFun (G.deleteIncidenceSet v)) ((G.deleteIncidenceSet v).edgeFinset.card - 1)) :
    Lower (edgeFun G) (G.edgeFinset.card - 1) := by
  have dg : G.degree v = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w,vw,leaf⟩
  have card := G.card_edgeFinset_deleteIncidenceSet v
  rw [dg] at card
  by_cases small : G.edgeFinset.card ≤ 1
  · have h : G.edgeFinset.card - 1 = 0 := by omega
    rw [h]
    exact lower_zero _
  have pos : (G.deleteIncidenceSet v).edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have nonzero := (G.deleteIncidenceSet v).edgeFinset_nonempty.mp pos
  have pair : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    by_contra! no
    exact nonzero (SimpleGraph.eq_bot_iff_forall_not_adj.mpr no)
  obtain ⟨a,b,ab⟩ := pair
  obtain ⟨edge,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
  have top : edgeFun G (topMiss v) = true := by
    exact decide_eq_true ⟨a,b,edge,by simp [topMiss,av],by simp [topMiss,bv]⟩
  let e : X n := fun i => decide (i = v ∨ i = w)
  let z : X n := fun i => decide (i = w)
  have fe : edgeFun G e = true := decide_eq_true ⟨v,w,vw,by simp [e],by simp [e]⟩
  have fz : edgeFun G z = false := by
    apply decide_eq_false_iff_not.mpr
    rintro ⟨c,d,hcd,hc,hd⟩
    exact hcd.ne ((by simpa [z] using hc : c = w).trans (by simpa [z] using hd : d = w).symm)
  have cof : edgeFun G ∘ pinZero v = edgeFun (G.deleteIncidenceSet v) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      have iv : i ≠ v := fun eq => by simp [pinZero,eq] at hi
      have jv : j ≠ v := fun eq => by simp [pinZero,eq] at hj
      exact ⟨i,j,⟨ij,iv,jv⟩,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
    · rintro ⟨i,j,⟨ij,iv,jv⟩,hi,hj⟩
      exact ⟨i,j,ij,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
  have eq : G.edgeFinset.card - 1 = ((G.deleteIncidenceSet v).edgeFinset.card - 1) + 1 := by omega
  rw [eq]
  apply save_at (edgeFun G) v e z (pinZero v) _ _ _ top fe fz (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinZero,iv] using (free_zero (B := inputs n))
    · simpa [Function.comp_def,pinZero,iv] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i h
    by_contra no
    have iv : i = v := by simpa [topMiss] using no
    simp [pinZero,iv] at h
  · intro i tv ei
    have iv : i ≠ v := by simpa [topMiss] using tv
    simpa [e,z,iv] using ei

theorem add_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (adj : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (dropV : Counts (G.deleteIncidenceSet v)) (dropW : Counts (G.deleteIncidenceSet w)) :
    Counts G := by
  refine ⟨or_leaf G v w adj leaf dropV.1,?_⟩
  obtain ⟨S,cv,lo⟩ := dropW.2
  refine ⟨insert w S,?_,?_⟩
  · intro a b ab
    by_cases aw : a = w
    · exact Or.inl (by simp [aw])
    by_cases bw : b = w
    · exact Or.inr (by simp [bw])
    exact (cv (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,aw,bw⟩)).imp
      (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
  · have pay := leaf_step G v w adj leaf lo
    intro ops valid
    exact (Finset.card_insert_le _ _).trans (pay ops valid)

theorem peel_to_core {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (base : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → Leafless H → Counts H) :
    Counts G := by
  classical
  have work (k : Nat) : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H ≤ G → H.edgeFinset.card = k → Counts H := by
    induction k using Nat.strong_induction_on with
    | ind k rec =>
      intro H _ hg count
      by_cases last : Leafless H
      · exact base H hg last
      obtain ⟨v,w,adj,leaf⟩ := not_not.mp last
      apply add_leaf H v w adj leaf
      all_goals
        apply rec _ _ _ (le_trans (H.deleteIncidenceSet_le _) hg) rfl
        rw [H.card_edgeFinset_deleteIncidenceSet,← count]
      · have h := (H.degree_pos_iff_exists_adj v).mpr ⟨w,adj⟩
        have c := H.degree_le_card_edgeFinset v
        omega
      · have h := (H.degree_pos_iff_exists_adj w).mpr ⟨v,adj.symm⟩
        have c := H.degree_le_card_edgeFinset w
        omega
  exact work _ G le_rfl rfl

theorem forest_leaf {n : Nat} (G : SimpleGraph (Fin n)) (h : G.IsAcyclic)
    (a b : Fin n) (adj : G.Adj a b) : ¬ Leafless G := by
  let _ : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u,t,p,path,maximal⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have pathAB : (SimpleGraph.Walk.cons adj .nil).IsPath :=
    SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [adj.ne])
  have pos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 1) (maximal a b _ pathAB)
  have nonempty : ¬p.Nil := by grind
  intro none
  apply none
  refine ⟨u,p.snd,p.adj_snd nonempty,?_⟩
  intro w uw
  apply h.eq_snd_of_adj_start path uw
  by_contra miss
  have bigger := maximal _ _ (p.cons uw.symm) (path.cons miss)
  simp at bigger

theorem forest_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsAcyclic) : Counts G := by
  apply peel_to_core G
  intro H _ hg last
  have all (v w) : ¬ H.Adj v w := fun adj => forest_leaf H (h.anti hg) v w adj last
  have empty : H = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr all
  refine ⟨?_,∅,?_,lower_zero _⟩
  · have zero : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun he => H.edgeFinset_nonempty.mp he empty)
    have eq : H.edgeFinset.card - 1 = 0 := by simp [zero]
    rw [eq]
    exact lower_zero _
  · exact fun a b ab => (all a b ab).elim

theorem bound_of_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (proof : Counts G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : IsAO2 n C)
    (h : circuitFun n C = edgeFun G) : ∃ S : Finset (Fin n),
    G.IsVertexCover (S : Set (Fin n)) ∧ G.edgeFinset.card + S.card ≤ C.size + 1 := by
  obtain ⟨orr,S,cv,andd⟩ := proof
  have ol := lower_circuit orr C ao h
  rw [← ordinary_eq] at h
  have al := and_lower_circuit _ ((cover_dual G).symm ▸ andd) C ao h
  rw [← ThetaAnd3241.subtract_or_eq_and C ao] at al
  change G.edgeFinset.card - 1 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ol
  have le := List.countP_le_length (p := fun g => PEqualNP.SharedBlockCost.isOrOp g.op) (l := C.gates)
  change _ ≤ C.size at le
  exact ⟨S,cv,by omega⟩

end LeafCore3241

namespace ForestBipartite3241
open LeafCore3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev bip {n m : Nat} (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n+m)) :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ E, a = Fin.castAdd m e.1 ∧ b = Fin.natAdd n e.2

theorem sides {n m : Nat} (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro eq
  have h := congrArg Fin.val eq
  change a.val = n + b.val at h
  omega

def pair {n m : Nat} (e : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(Fin.castAdd m e.1,Fin.natAdd n e.2)

theorem injective_pair {n m : Nat} : Function.Injective (pair (n := n) (m := m)) := by
  intro e f eq
  rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,_⟩
  · exact Prod.ext (Fin.castAdd_injective n m a) (Fin.ext (by
      have h := congrArg Fin.val b
      change n + e.2.val = n + f.2.val at h
      omega))
  · exact (sides _ _ a).elim

theorem bip_adjacency {n m : Nat} {E : Finset (Fin n × Fin m)} {e : Fin n × Fin m} (he : e ∈ E) :
    (bip E).Adj (Fin.castAdd m e.1) (Fin.natAdd n e.2) :=
  ⟨sides _ _,Or.inl ⟨e,he,rfl,rfl⟩⟩

theorem bip_edges {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj] :
    (bip E).edgeFinset.card = E.card := by
  have eq : (bip E).edgeFinset = E.image pair := by
    ext t
    induction t using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨e,he,rfl⟩
        · exact Finset.mem_image.mpr ⟨e,he,Sym2.eq_swap⟩
      · intro h
        obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,b⟩
        · exact a ▸ b ▸ bip_adjacency he
        · exact a ▸ b ▸ (bip_adjacency he).symm
  rw [eq,Finset.card_image_of_injective _ injective_pair]

theorem formula {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj]
    (x : Fin (n+m) → Bool) : edgeFun (bip E) x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFun,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩,ha,hb⟩
    · exact ⟨e,he,ha,hb⟩
    · exact ⟨e,he,hb,ha⟩
  · rintro ⟨e,he,l,r⟩
    exact ⟨_,_,bip_adjacency he,l,r⟩

theorem main (n m : Nat) (E : Finset (Fin n × Fin m)) (C : Circuit)
    (acyclic : (bip E).IsAcyclic) (ao : IsAO2 (n+m) C)
    (h : ∀ x, circuitFun (n+m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) :
    ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  obtain ⟨S,cv,budget⟩ := bound_of_counts (bip E) (forest_counts _ acyclic) C ao
    (funext (fun x => (h x).trans (formula E x).symm))
  let P := Finset.univ.filter fun i : Fin n => Fin.castAdd m i ∈ S
  let Q := Finset.univ.filter fun i : Fin m => Fin.natAdd n i ∈ S
  let L := P.image (Fin.castAdd m)
  let R := Q.image (Fin.natAdd n)
  have dis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    rintro i hl hr
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hr
    exact sides a b eq.symm
  have inc : L ∪ R ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with l | r
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp l
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      exact (Finset.mem_filter.mp hb).2
  have card := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis] at card
  change (P.image (Fin.castAdd m)).card + (Q.image (Fin.natAdd n)).card ≤ S.card at card
  rw [Finset.card_image_of_injective _ (Fin.castAdd_injective n m),
    Finset.card_image_of_injective _ (Fin.natAdd_injective m n)] at card
  rw [bip_edges] at budget
  refine ⟨P,Q,?_,by omega⟩
  intro e he
  exact (cv (bip_adjacency he)).imp (fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _,l⟩)
    (fun r => Finset.mem_filter.mpr ⟨Finset.mem_univ _,r⟩)

end ForestBipartite3241

namespace CoreTransfer3241
open ThetaPin3241 LeafAnd3241 LeafCore3241

theorem padded {m n : Nat} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : Fin m → Fin n) (inj : Function.Injective f)
    (adj : ∀ i j, H.Adj i j ↔ ∃ u v, G.Adj u v ∧ f u = i ∧ f v = j)
    (src : Counts G) : Counts H := by
  classical
  let p : X m → X n := fun x => Function.extend f x (fun _ => false)
  have put (x : X m) (i : Fin m) : p x (f i) = x i := inj.extend_apply x _ i
  have raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p) := by
    rintro _ ⟨i,rfl⟩
    by_cases mem : ∃ t, f t = i
    · obtain ⟨t,rfl⟩ := mem
      have eq : (fun (x : X n) => x (f t)) ∘ p = (fun (x : X m) => x t) := funext (fun x => put x t)
      exact eq ▸ atom ⟨t,rfl⟩
    · have eq : (fun (x : X n) => x i) ∘ p = (fun _ => false) :=
        funext (fun x => Function.extend_apply' x (fun _ => false) i mem)
      exact eq ▸ free_zero
  have spec (u v : Fin m) (uv : G.Adj u v) : H.Adj (f u) (f v) := (adj _ _).mpr ⟨u,v,uv,rfl,rfl⟩
  have edge : edgeFun H ∘ p = edgeFun G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,yes,also⟩
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      exact ⟨u,v,uv,(put x u).symm.trans yes,(put x v).symm.trans also⟩
    · rintro ⟨u,v,uv,yes,also⟩
      exact ⟨_,_,spec u v uv,(put x u).trans yes,(put x v).trans also⟩
  have covers : cover H ∘ p = cover G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok u v uv
      simpa only [put] using ok _ _ (spec u v uv)
    · intro ok i j ij
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      simpa only [put] using ok _ _ uv
  have subset : H.edgeFinset ⊆ G.edgeFinset.image (Sym2.map f) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j =>
      intro he
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp (H.mem_edgeFinset.mp he)
      exact Finset.mem_image.mpr ⟨s(u,v),G.mem_edgeFinset.mpr uv,rfl⟩
  have count := (Finset.card_le_card subset).trans Finset.card_image_le
  obtain ⟨ors,S,cv,ands⟩ := src
  refine ⟨?_,S.image f,?_,?_⟩
  · have lo : Lower (edgeFun H) (G.edgeFinset.card - 1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs ok => (Nat.sub_le_sub_right count 1).trans (lo gs ok)
  · intro i j ij
    obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp ij
    exact (cv uv).imp (fun hu => Finset.mem_image_of_mem _ hu) (fun hv => Finset.mem_image_of_mem _ hv)
  · rw [Finset.card_image_of_injective _ inj]
    exact lower_transport p raw (covers.symm ▸ ands)

theorem pass_of_choices {n : Nat} (gs : List (ThetaPin3241.Gate (X n))) (B : Set (Signal (X n)))
    (f : Signal (X n)) (x y z : X n) (base : ∀ a ∈ B, Pass x y z a)
    (agree : ∀ g ∈ gs, g.1 x = g.1 y) (ok : Valid B gs f) : Pass x y z f := by
  induction gs generalizing B with
  | nil => exact free_pass base ok
  | cons g gs ih =>
    obtain ⟨fa,fb,tail⟩ := ok
    have pass_a := free_pass base fa
    have pass_b := free_pass base fb
    have pass_g : Pass x y z (join g.1 g.2) := by
      have eq := agree g List.mem_cons_self
      intro gx gy
      cases ax : g.1 x with
      | true =>
        have az := pass_a ax (eq.symm.trans ax)
        simp [join,az]
      | false =>
        have ay := eq.symm.trans ax
        have bz := pass_b (by simpa [join,ax] using gx) (by simpa [join,ay] using gy)
        simp [join,bz]
    refine ih (insert (join g.1 g.2) B) ?_ ?_ tail
    · intro a ha
      exact (Set.mem_insert_iff.mp ha).elim (fun eq => eq ▸ pass_g) (base a)
    · exact fun g hg => agree g (List.mem_cons_of_mem _ hg)

theorem separated_rows {n k r : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i) = true)
    (off : ∀ i j, i ≠ j → f (fun v => rows i v && rows j v) = false)
    (many : 2^(k-1) < r) : Lower f k := by
  intro gs ok
  let key (i : Fin r) (g : Fin gs.length) := (gs.get g).1 (rows i)
  have distinguish : Function.Injective key := by
    intro i j eq
    by_contra ne
    have agree (g) (hg : g ∈ gs) : g.1 (rows i) = g.1 (rows j) := by
      obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hg
      exact congrFun eq t
    have pass := pass_of_choices gs (inputs n) f (rows i) (rows j) (fun v => rows i v && rows j v)
      (pass_inputs _ _ _ (fun v a b => by simp [a,b])) agree ok
    have both := pass (yes i) (yes j)
    simp [off i j ne] at both
  have count := Fintype.card_le_of_injective key distinguish
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at count
  by_contra bad
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) (show gs.length ≤ k-1 by omega)
  omega

end CoreTransfer3241

namespace SmallCores3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 CoreTransfer3241
open ThetaCores3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path8 (x : LeafAnd3241.X 8) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path8_lower (rec : Lower path7 5) : Lower path8 6 := by
  have eq : path8 ∘ pin (7 : Fin 8) = path7 := by
    funext x
    exact (by decide +kernel : ∀ y, path8 (pin (7 : Fin 8) y) = path7 y) x
  apply lower_one_step path8 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path9 (x : LeafAnd3241.X 9) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path9_lower (rec : Lower path8 6) : Lower path9 7 := by
  have eq : path9 ∘ pin (8 : Fin 9) = path8 := by
    funext x
    exact (by decide +kernel : ∀ y, path9 (pin (8 : Fin 9) y) = path8 y) x
  apply lower_one_step path9 8 (row 384) (row 128)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycle10 (x : LeafAnd3241.X 10) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycleRename : Fin 10 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],![8,0,1,2,3,4,5,6,7],![7,8,0,1,2,3,4,5,6],![6,7,8,0,1,2,3,4,5],![5,6,7,8,0,1,2,3,4],![4,5,6,7,8,0,1,2,3],![3,4,5,6,7,8,0,1,2],![2,3,4,5,6,7,8,0,1],![1,2,3,4,5,6,7,8,0],![0,1,2,3,4,5,6,7,8]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_deleted (v : Fin 10) : Lower (cycle10 ∘ pin v) 7 := by
  have all : ∀ i x, (cycle10 ∘ pin i) (x ∘ cycleRename i) = path9 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle10 ∘ pin v) (x ∘ cycleRename v)) = path9 := funext (all v)
  exact eq.symm ▸ path9_lower (path8_lower (path7_lower (path6_lower path5_lower)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_geometry : Geometry ∅ cycle10 := by constructor <;> decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_lower : Lower cycle10 9 := by
  apply lower_two_step cycle10 Set.univ (pool ∅) (base_subset _)
  · exact nonfree cycle10 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle10_geometry g a b (fun v _ => h v (Set.mem_univ v))
  · exact fun v _ => cycle10_deleted v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev graph (n : Nat) (edges : List (Nat × Nat)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun (i j : Fin n) => (i.val,j.val) ∈ edges)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev six := graph 6 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def sixRows : Fin 5 → Nat := ![21,27,42,45,54]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem sixCounts : Counts six := by
  have eq : edgeFun six = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun six y = cycle6 y) x
  have card : six.edgeFinset.card - 1 = 5 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle6_of_classifier ThetaClass3241.cycle_classifier
  · let S : Finset (Fin 6) := {0,2,4}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, six.Adj a b → a ∈ ({0,2,4} : Finset (Fin 6)) ∨ b ∈ ({0,2,4} : Finset (Fin 6)))
    have sc : S.card = 3 := by decide +kernel
    have dualEq : cover six = dual cycle6 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle6) (fun i => row (sixRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev eight := graph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def eightRows : Fin 9 → Nat := ![85,91,107,109,170,173,181,182,214]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem eightCounts : Counts eight := by
  have eq : edgeFun eight = cycle8 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun eight y = cycle8 y) x
  have card : eight.edgeFinset.card - 1 = 7 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle8_of_classifier Theta244Finish.cycle_classifier
  · let S : Finset (Fin 8) := {0,2,4,6}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, eight.Adj a b → a ∈ ({0,2,4,6} : Finset (Fin 8)) ∨ b ∈ ({0,2,4,6} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover eight = dual cycle8 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle8) (fun i => row (eightRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev ten := graph 10 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def tenRows : Fin 17 → Nat := ![341,347,363,365,427,429,437,682,685,693,694,725,726,730,854,858,874]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem tenCounts : Counts ten := by
  have eq : edgeFun ten = cycle10 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun ten y = cycle10 y) x
  have card : ten.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle10_lower
  · let S : Finset (Fin 10) := {0,2,4,6,8}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, ten.Adj a b → a ∈ ({0,2,4,6,8} : Finset (Fin 10)) ∨ b ∈ ({0,2,4,6,8} : Finset (Fin 10)))
    have sc : S.card = 5 := by decide +kernel
    have dualEq : cover ten = dual cycle10 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle10) (fun i => row (tenRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev threeThreeThree := graph 8 [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def threeThreeThreeRows : Fin 9 → Nat := ![15,55,91,115,157,181,217,238,240]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem threeThreeThreeCounts : Counts threeThreeThree := by
  have eq : edgeFun threeThreeThree = ThetaAnd3241.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun threeThreeThree y = ThetaAnd3241.theta y) x
  have card : threeThreeThree.edgeFinset.card - 1 = 8 := by decide +kernel
  constructor
  · rw [eq,card]
    exact theta_of_classifiers ThetaClass3241.cycle_classifier theta_classifier
  · let S : Finset (Fin 8) := {0,1,2,3}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, threeThreeThree.Adj a b → a ∈ ({0,1,2,3} : Finset (Fin 8)) ∨ b ∈ ({0,1,2,3} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover threeThreeThree = dual ThetaAnd3241.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual ThetaAnd3241.theta) (fun i => row (threeThreeThreeRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev twoFourFour := graph 9 [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def twoFourFourRows : Fin 9 → Nat := ![147,171,222,238,339,350,363,364,373]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem twoFourFourCounts (extra : Lower Theta244Cores.theta 9) : Counts twoFourFour := by
  have eq : edgeFun twoFourFour = Theta244Cores.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun twoFourFour y = Theta244Cores.theta y) x
  have card : twoFourFour.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact extra
  · let S : Finset (Fin 9) := {0,1,4,7}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, twoFourFour.Adj a b → a ∈ ({0,1,4,7} : Finset (Fin 9)) ∨ b ∈ ({0,1,4,7} : Finset (Fin 9)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover twoFourFour = dual Theta244Cores.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual Theta244Cores.theta) (fun i => row (twoFourFourRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

end SmallCores3241

namespace GraphPacking3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 ForestBipartite3241

abbrev Matrix (n m : Nat) := Finset (Fin n × Fin m)
abbrev Left {n m : Nat} (a : Fin n) := Fin.castAdd m a
abbrev Right {n m : Nat} (b : Fin m) := Fin.natAdd n b

def FourFree {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ p q l s, p ≠ q → l ≠ s → ¬((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)

def HasPartners {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ a b, (a,b) ∈ E →
    (∃ c, c ≠ b ∧ (a,c) ∈ E) ∧ (∃ d, d ≠ a ∧ (d,b) ∈ E)

theorem adj_left {n m : Nat} (E : Matrix n m) (a : Fin n) (j : Fin (n+m)) :
    (bip E).Adj (Left a) j ↔ ∃ b, (a,b) ∈ E ∧ j = Right b := by
  constructor
  · rintro ⟨_,⟨e,he,eq,rfl⟩ | ⟨e,_,_,eq⟩⟩
    · have ea : a = e.1 := Fin.castAdd_injective n m eq
      exact ⟨e.2,ea ▸ he,rfl⟩
    · exact (sides _ _ eq).elim
  · rintro ⟨b,h,rfl⟩
    exact bip_adjacency h

theorem adj_right {n m : Nat} (E : Matrix n m) (b : Fin m) (i : Fin (n+m)) :
    (bip E).Adj (Right b) i ↔ ∃ a, (a,b) ∈ E ∧ i = Left a := by
  constructor
  · rintro ⟨_,⟨e,_,eq,_⟩ | ⟨e,he,rfl,eq⟩⟩
    · exact (sides _ _ eq.symm).elim
    · have eb : b = e.2 := Fin.natAdd_injective m n eq
      exact ⟨e.1,eb ▸ he,rfl⟩
  · rintro ⟨a,h,rfl⟩
    exact (bip_adjacency h).symm

theorem leafless_iff {n m : Nat} (E : Matrix n m) : Leafless (bip E) ↔ HasPartners E := by
  classical
  constructor
  · intro no a b ab
    constructor
    · by_contra! bad
      apply no
      refine ⟨Left a,Right b,bip_adjacency ab,?_⟩
      intro i hi
      obtain ⟨c,hc,rfl⟩ := (adj_left E a i).mp hi
      have cb : c = b := by_contra (fun ne => bad c ne hc)
      rw [cb]
    · by_contra! bad
      apply no
      refine ⟨Right b,Left a,(bip_adjacency ab).symm,?_⟩
      intro i hi
      obtain ⟨d,hd,rfl⟩ := (adj_right E b i).mp hi
      have da : d = a := by_contra (fun ne => bad d ne hd)
      rw [da]
  · rintro partners ⟨i,j,ij,leaf⟩
    rcases ij with ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨c,ne,hc⟩ := (partners a b h).1
      exact ne (Fin.natAdd_injective m n (leaf _ (bip_adjacency hc)))
    · obtain ⟨d,ne,hd⟩ := (partners a b h).2
      exact ne (Fin.castAdd_injective n m (leaf _ (bip_adjacency hd).symm))

theorem side_count {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (two : ∀ a b, (a,b) ∈ E → ∃ c, c ≠ b ∧ (a,c) ∈ E) :
    (E.image Prod.fst).card * 2 ≤ E.card := by
  classical
  let P := E.image Prod.fst
  have picks (p : P) : ∃ b c, b ≠ c ∧ (p.val,b) ∈ E ∧ (p.val,c) ∈ E := by
    obtain ⟨⟨a,b⟩,ab,e⟩ := Finset.mem_image.mp p.property
    change a = p.val at e
    obtain ⟨c,ne,ac⟩ := two a b ab
    exact ⟨b,c,ne.symm,e ▸ ab,e ▸ ac⟩
  choose first second diff one two using picks
  let edge (p : P) (b : Bool) : E := if b then ⟨(p.val,first p),one p⟩ else ⟨(p.val,second p),two p⟩
  have inj : Function.Injective (fun x : P × Bool => edge x.1 x.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have row (r : P) (b : Bool) : (edge r b).val.1 = r.val := by cases b <;> rfl
    have pe : p = q := Subtype.ext ((row p i).symm.trans ((congrArg (fun t : E => t.val.1) eq).trans (row q j)))
    subst q
    cases i <;> cases j
    · rfl
    · exact ((diff p).symm (congrArg (fun t : E => t.val.2) eq)).elim
    · exact (diff p (congrArg (fun t : E => t.val.2) eq)).elim
    · rfl
  have bound := Fintype.card_le_of_injective _ inj
  simpa [P] using bound

theorem both_sides {n m : Nat} (E : Matrix n m) (partners : HasPartners E) (small : E.card ≤ 10) :
    (E.image Prod.fst).card ≤ 5 ∧ (E.image Prod.snd).card ≤ 5 := by
  have left := side_count E (fun a b ab => (partners a b ab).1)
  have flip {a : Fin n} {b : Fin m} : (b,a) ∈ E.image Prod.swap ↔ (a,b) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨p,q⟩,pq,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact pq
    · exact fun h => Finset.mem_image_of_mem Prod.swap h
  have right := side_count (E.image Prod.swap) (fun b a ba => by
    obtain ⟨d,ne,db⟩ := (partners a b (flip.mp ba)).2
    exact ⟨d,ne,flip.mpr db⟩)
  rw [Finset.image_image,Finset.card_image_of_injective _ Prod.swap_injective] at right
  change (E.image Prod.snd).card * 2 ≤ E.card at right
  omega

theorem from_index {n k : Nat} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (lab : Fin n → Option (Fin k))
    (unique : ∀ i j a, lab i = some a → lab j = some a → i = j)
    (forward : ∀ i j, G.Adj i j → ∃ a b, lab i = some a ∧ lab j = some b ∧ H.Adj a b)
    (back : ∀ a b, H.Adj a b → ∃ i j, lab i = some a ∧ lab j = some b ∧ G.Adj i j)
    (size : G.edgeFinset.card ≤ H.edgeFinset.card) (h : Counts H) : Counts G := by
  classical
  let p : X k → X n := fun x i => (lab i).elim false x
  have read (x : X k) (i a) (hi : lab i = some a) : p x i = x a := by simp [p,hi]
  have raw : ∀ t ∈ inputs n, Free (inputs k) (t ∘ p) := by
    rintro _ ⟨i,rfl⟩
    cases hi : lab i with
    | none => simpa [Function.comp_def,p,hi] using (free_zero (B := inputs k))
    | some a => simpa [Function.comp_def,p,hi] using (atom (B := inputs k) ⟨a,rfl⟩)
  have edge : edgeFun G ∘ p = edgeFun H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,pi,pj⟩
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      exact ⟨a,b,ab,(read x i a li).symm.trans pi,(read x j b lj).symm.trans pj⟩
    · rintro ⟨a,b,ab,pa,pb⟩
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      exact ⟨i,j,ij,(read x i a li).trans pa,(read x j b lj).trans pb⟩
  have cover_eq : cover G ∘ p = cover H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok a b ab
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      simpa only [read x i a li,read x j b lj] using ok i j ij
    · intro ok i j ij
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      simpa only [read x i a li,read x j b lj] using ok a b ab
  obtain ⟨ors,S,cv,ands⟩ := h
  let T := Finset.univ.filter fun i => ∃ a ∈ S, lab i = some a
  have lift (i : T) : ∃ a : S, lab i.val = some a.val := by
    obtain ⟨a,ha,eq⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨a,ha⟩,eq⟩
  choose assign spec using lift
  have inj : Function.Injective assign := fun i j eq =>
    Subtype.ext (unique _ _ _ (spec i) (eq ▸ spec j))
  have card : T.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  refine ⟨?_,T,?_,?_⟩
  · have bound : Lower (edgeFun G) (H.edgeFinset.card-1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs val => (Nat.sub_le_sub_right size 1).trans (bound gs val)
  · intro i j ij
    obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
    exact (cv ab).imp (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,mem,li⟩)
      (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,mem,lj⟩)
  · have bound : Lower (cover G) S.card := lower_transport p raw (cover_eq.symm ▸ ands)
    exact fun gs val => card.trans (bound gs val)

end GraphPacking3241

namespace MatrixPacking3241
open GraphPacking3241 LeafCore3241 ForestBipartite3241

def optional {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β) (i : α) : Option β :=
  if h : i ∈ P then some (f ⟨i,h⟩) else none

theorem optional_unique {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β)
    (inj : Function.Injective f) (i j : α) (a : β) (hi : optional P f i = some a)
    (hj : optional P f j = some a) : i = j := by
  unfold optional at hi hj
  split at hi <;> rename_i pi
  · split at hj <;> rename_i pj
    · exact congrArg Subtype.val (inj ((Option.some.inj hi).trans (Option.some.inj hj).symm))
    · contradiction
  · contradiction

def combine {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5)) :
    Fin (n+m) → Option (Fin 10) :=
  Fin.addCases (fun a => (r a).map (Fin.castAdd 5)) (fun b => (c b).map (Fin.natAdd 5))

theorem combined_unique {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5))
    (ri : ∀ i j a, r i = some a → r j = some a → i = j)
    (ci : ∀ i j b, c i = some b → c j = some b → i = j) :
    ∀ i j t, combine r c i = some t → combine r c j = some t → i = j := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    intro j <;> refine Fin.addCases (fun u => ?_) (fun v => ?_) j <;>
    intro t hi hj <;> simp only [combine,Fin.addCases_left,Fin.addCases_right,Option.map_eq_some_iff] at hi hj <;>
    obtain ⟨x,hx,rfl⟩ := hi <;> obtain ⟨y,hy,eq⟩ := hj
  · obtain rfl : y = x := Fin.castAdd_injective 5 5 eq
    exact congrArg _ (ri _ _ _ hx hy)
  · exact (sides x y eq.symm).elim
  · exact (sides y x eq).elim
  · obtain rfl : y = x := Fin.natAdd_injective 5 5 eq
    exact congrArg _ (ci _ _ _ hx hy)

abbrev Rows {n m} (E : Matrix n m) := E.image Prod.fst
abbrev Cols {n m} (E : Matrix n m) := E.image Prod.snd
def erow {n m} {E : Matrix n m} (e : E) : Rows E := ⟨e.val.1,Finset.mem_image_of_mem _ e.property⟩
def ecol {n m} {E : Matrix n m} (e : E) : Cols E := ⟨e.val.2,Finset.mem_image_of_mem _ e.property⟩

def pack {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5) : Matrix 5 5 :=
  E.attach.image (fun e => (r (erow e),c (ecol e)))

theorem decode {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5} {a b} :
    (a,b) ∈ pack E r c ↔ ∃ e : E, r (erow e) = a ∧ c (ecol e) = b := by
  simp [pack]

theorem rows_eq {n m} {E : Matrix n m} {r : Rows E → Fin 5} (inj : Function.Injective r) (e f : E) :
    r (erow e) = r (erow f) ↔ e.val.1 = f.val.1 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg r (Subtype.ext h)⟩

theorem cols_eq {n m} {E : Matrix n m} {c : Cols E → Fin 5} (inj : Function.Injective c) (e f : E) :
    c (ecol e) = c (ecol f) ↔ e.val.2 = f.val.2 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg c (Subtype.ext h)⟩

theorem pack_card {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) : (pack E r c).card = E.card := by
  unfold pack
  rw [Finset.card_image_of_injective,Finset.card_attach]
  intro e f eq
  exact Subtype.ext (Prod.ext ((rows_eq ri _ _).mp (congrArg Prod.fst eq))
    ((cols_eq ci _ _).mp (congrArg Prod.snd eq)))

theorem pack_free {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (free : FourFree E) :
    FourFree (pack E r c) := by
  intro p q l s pq ls h
  obtain ⟨a,ap,al⟩ := decode.mp h.1
  obtain ⟨b,bp,bs⟩ := decode.mp h.2.1
  obtain ⟨d,dq,dl⟩ := decode.mp h.2.2.1
  obtain ⟨e,eq,es⟩ := decode.mp h.2.2.2
  have ab := (rows_eq ri a b).mp (ap.trans bp.symm)
  have de := (rows_eq ri d e).mp (dq.trans eq.symm)
  have ad := (cols_eq ci a d).mp (al.trans dl.symm)
  have be := (cols_eq ci b e).mp (bs.trans es.symm)
  have pr : a.val.1 ≠ d.val.1 := fun hh => pq (ap.symm.trans (((rows_eq ri a d).mpr hh).trans dq))
  have lc : a.val.2 ≠ b.val.2 := fun hh => ls (al.symm.trans (((cols_eq ci a b).mpr hh).trans bs))
  apply free _ _ _ _ pr lc
  exact ⟨a.property,ab ▸ b.property,ad ▸ d.property,de ▸ be ▸ e.property⟩

theorem pack_partners {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (has : HasPartners E) :
    HasPartners (pack E r c) := by
  intro a b ab
  obtain ⟨e,rfl,rfl⟩ := decode.mp ab
  obtain ⟨⟨v,ne,ev⟩,⟨u,diff,ue⟩⟩ := has _ _ e.property
  let f : E := ⟨(e.val.1,v),ev⟩
  let g : E := ⟨(u,e.val.2),ue⟩
  exact ⟨⟨c (ecol f),fun eq => ne ((cols_eq ci f e).mp eq),
      decode.mpr ⟨f,(rows_eq ri f e).mpr rfl,rfl⟩⟩,
    ⟨r (erow g),fun eq => diff ((rows_eq ri g e).mp eq),
      decode.mpr ⟨g,rfl,(cols_eq ci g e).mpr rfl⟩⟩⟩

theorem unpack_counts {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5)
    (ri : Function.Injective r) (ci : Function.Injective c)
    (src : Counts (bip (pack E r c))) : Counts (bip E) := by
  let lab := combine (optional (Rows E) r) (optional (Cols E) c)
  have l (e : E) : lab (Left e.val.1) = some (Fin.castAdd 5 (r (erow e))) := by
    simp only [lab,combine,Left,Fin.addCases_left,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (erow e).property).elim
  have rr (e : E) : lab (Right e.val.2) = some (Fin.natAdd 5 (c (ecol e))) := by
    simp only [lab,combine,Right,Fin.addCases_right,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (ecol e).property).elim
  apply from_index (bip E) (bip (pack E r c)) lab
    (combined_unique _ _ (optional_unique _ _ ri) (optional_unique _ _ ci)) _ _ _ src
  · rintro i j ⟨_,⟨p,h,rfl,rfl⟩ | ⟨p,h,rfl,rfl⟩⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,l e,rr e,bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,rr e,l e,(bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)).symm⟩
  · rintro i j ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,l e,rr e,bip_adjacency e.property⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,rr e,l e,(bip_adjacency e.property).symm⟩
  · rw [bip_edges,bip_edges,pack_card ri ci]

def Census : Prop := ∀ E : Matrix 5 5, E.card ≤ 10 → FourFree E → Leafless (bip E) → Counts (bip E)

theorem compressed {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (last : Leafless (bip E)) (census : Census) : Counts (bip E) := by
  let h := (leafless_iff E).mp last
  obtain ⟨pr,pc⟩ := both_sides E h size
  let r (p : Rows E) := Fin.castLE pr (((Rows E).orderIsoOfFin rfl).symm p)
  let c (p : Cols E) := Fin.castLE pc (((Cols E).orderIsoOfFin rfl).symm p)
  have ri : Function.Injective r := (Fin.castLE_injective pr).comp ((Rows E).orderIsoOfFin rfl).symm.injective
  have ci : Function.Injective c := (Fin.castLE_injective pc).comp ((Cols E).orderIsoOfFin rfl).symm.injective
  apply unpack_counts E r c ri ci
  apply census
  · simpa [pack_card ri ci] using size
  · exact pack_free ri ci free
  · exact (leafless_iff _).mpr (pack_partners ri ci h)

theorem full {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (census : Census) : Counts (bip E) := by
  classical
  apply peel_to_core (bip E)
  intro H _ sub last
  let F := E.filter (fun p => H.Adj (Left p.1) (Right p.2))
  have eq : H = bip F := by
    ext i j
    constructor
    · intro ij
      rcases sub ij with ⟨ne,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact bip_adjacency (Finset.mem_filter.mpr ⟨he,ij⟩ : e ∈ F)
      · exact (bip_adjacency (Finset.mem_filter.mpr ⟨he,ij.symm⟩ : e ∈ F)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact (Finset.mem_filter.mp he).2
      · exact ((Finset.mem_filter.mp he).2).symm
  have subset : F ⊆ E := Finset.filter_subset _ _
  have freeF : FourFree F := fun p q l s pq ls ⟨a,b,c,d⟩ =>
    free p q l s pq ls ⟨subset a,subset b,subset c,subset d⟩
  have carry {K L : SimpleGraph (Fin (n+m))} [d : DecidableRel K.Adj] [e : DecidableRel L.Adj]
      (same : K = L) (ok : Counts L) : Counts K := by
    subst L
    have sameInst : d = e := Subsingleton.elim _ _
    cases sameInst
    exact ok
  exact carry eq (compressed F freeF ((Finset.card_le_card subset).trans size) (eq ▸ last) census)

theorem officialBudget (census : Census) {n m} (E : Matrix n m) (free : FourFree E)
    (size : E.card ≤ 10) (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : PEqualNP.TopForm.IsAO2 (n+m) C)
    (correct : ∀ x, PEqualNP.MetaComplexity.circuitFun (n+m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) :
    ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  obtain ⟨S,cv,budget⟩ := bound_of_counts (bip E) (full E free size census) C ao
    (funext (fun x => (correct x).trans (formula E x).symm))
  let P := Finset.univ.filter (fun i : Fin n => Fin.castAdd m i ∈ S)
  let Q := Finset.univ.filter (fun j : Fin m => Fin.natAdd n j ∈ S)
  let push : (P ⊕ Q) → S := Sum.elim
    (fun i => ⟨Fin.castAdd m i.val,(Finset.mem_filter.mp i.property).2⟩)
    (fun j => ⟨Fin.natAdd n j.val,(Finset.mem_filter.mp j.property).2⟩)
  have inj : Function.Injective push := by
    intro i j eq
    have h := congrArg Subtype.val eq
    cases i with
    | inl a => cases j with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Fin.castAdd_injective n m h))
      | inr b => exact (sides a.val b.val h).elim
    | inr a => cases j with
      | inl b => exact (sides b.val a.val h.symm).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext (Fin.natAdd_injective m n h))
  have bound : P.card + Q.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  rw [bip_edges] at budget
  refine ⟨P,Q,?_,by omega⟩
  intro e he
  exact (cv (bip_adjacency he)).imp (fun hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
    (fun hq => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)

end MatrixPacking3241

namespace CoreCensus
open LeafCore3241 SmallCores3241 ForestBipartite3241

inductive Shape | six | eight | ten | theta333 | theta244 deriving DecidableEq, Repr

abbrev order : Shape → Nat
  | .six => 6 | .eight => 8 | .ten => 10 | .theta333 => 8 | .theta244 => 9

instance (s : Shape) : NeZero (order s) := by cases s <;> exact ⟨by decide⟩

def edges : Shape → List (Nat × Nat)
  | .six => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
  | .eight => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
  | .ten => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
  | .theta333 => [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
  | .theta244 => [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]

abbrev source (s : Shape) := graph (order s) (edges s)

theorem counts_source (s) (h : ThetaPin3241.Lower Theta244Cores.theta 9) : Counts (source s) := by
  cases s
  · exact sixCounts
  · exact eightCounts
  · exact tenCounts
  · exact threeThreeThreeCounts
  · exact twoFourFourCounts h

def pairs (rows : List Nat) : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun (i,j) => (rows.getD i.val 0).testBit j.val

def matrix (rows : List Nat) := bip (pairs rows)

instance (rows : List Nat) : DecidableRel (matrix rows).Adj := by unfold matrix bip; infer_instance

structure Item where
  rows : List Nat
  shape : Shape
  forward : List Nat
  backward : List Nat
  deriving Repr

def emb (r : Item) (i : Fin (order r.shape)) : Fin 10 := Fin.ofNat 10 (r.forward.getD i.val 0)
def inv (r : Item) (i : Fin 10) : Fin (order r.shape) := Fin.ofNat (order r.shape) (r.backward.getD i.val 0)

def Certified (r : Item) : Prop :=
  (∀ u, inv r (emb r u) = u) ∧ ∀ i j, (matrix r.rows).Adj i j ↔
     emb r (inv r i) = i ∧ emb r (inv r j) = j ∧ (source r.shape).Adj (inv r i) (inv r j)

instance (r : Item) : Decidable (Certified r) := by unfold Certified; infer_instance

theorem count_item (r : Item) (hc : Certified r) (h : ThetaPin3241.Lower Theta244Cores.theta 9) :
    Counts (matrix r.rows) := by
  apply CoreTransfer3241.padded (source r.shape) (matrix r.rows) (emb r) (Function.LeftInverse.injective hc.1) _ (counts_source _ h)
  intro i j
  constructor
  · intro a
    obtain ⟨hi,hj,adj⟩ := (hc.2 i j).mp a
    exact ⟨_,_,adj,hi,hj⟩
  · rintro ⟨u,v,a,rfl,rfl⟩
    apply (hc.2 _ _).mpr
    rw [hc.1 u,hc.1 v]
    exact ⟨rfl,rfl,a⟩

end CoreCensus

namespace CoreCensus

def batch0 : List Item := [
  ⟨[3, 5, 6],.six,[1, 5, 0, 6, 2, 7],[2, 0, 4, 0, 0, 1, 3, 5, 0, 0]⟩,
  ⟨[3, 5, 6, 9, 10],.theta244,[5, 6, 0, 1, 7, 2, 3, 8, 4],[2, 3, 5, 6, 8, 0, 1, 4, 7, 0]⟩,
  ⟨[3, 5, 6, 9, 12],.theta244,[5, 7, 1, 0, 6, 2, 3, 8, 4],[3, 2, 5, 6, 8, 0, 4, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 10, 12],.theta244,[6, 7, 2, 0, 5, 1, 3, 8, 4],[3, 5, 2, 6, 8, 4, 0, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 17, 18],.theta244,[5, 6, 0, 1, 7, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 4, 0, 7]⟩,
  ⟨[3, 5, 6, 17, 20],.theta244,[5, 7, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 1, 0, 7]⟩]

def batch1 : List Item := [
  ⟨[3, 5, 6, 18, 20],.theta244,[6, 7, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 1, 0, 7]⟩,
  ⟨[3, 5, 9, 10, 12],.theta244,[5, 8, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 1, 0]⟩,
  ⟨[3, 5, 9, 14],.theta333,[3, 2, 1, 0, 5, 6, 7, 8],[3, 2, 1, 0, 0, 4, 5, 6, 7, 0]⟩,
  ⟨[3, 5, 10, 12],.eight,[1, 5, 0, 6, 2, 8, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 5, 0]⟩,
  ⟨[3, 5, 10, 20, 24],.ten,[1, 5, 0, 6, 2, 8, 4, 9, 3, 7],[2, 0, 4, 8, 6, 1, 3, 9, 5, 7]⟩,
  ⟨[3, 5, 12, 18, 24],.ten,[1, 5, 0, 6, 3, 9, 4, 8, 2, 7],[2, 0, 8, 4, 6, 1, 3, 9, 7, 5]⟩]

def batch2 : List Item := [
  ⟨[3, 5, 17, 18, 20],.theta244,[5, 9, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 0, 1]⟩,
  ⟨[3, 5, 17, 22],.theta333,[3, 2, 1, 0, 5, 6, 7, 9],[3, 2, 1, 0, 0, 4, 5, 6, 0, 7]⟩,
  ⟨[3, 5, 18, 20],.eight,[1, 5, 0, 6, 2, 9, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 0, 5]⟩,
  ⟨[3, 6, 9, 10, 12],.theta244,[6, 8, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 1, 0]⟩,
  ⟨[3, 6, 9, 12],.eight,[2, 5, 0, 6, 1, 7, 3, 8],[2, 4, 0, 6, 0, 1, 3, 5, 7, 0]⟩,
  ⟨[3, 6, 9, 20, 24],.ten,[2, 5, 0, 6, 1, 7, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 3, 5, 9, 7]⟩]

def batch3 : List Item := [
  ⟨[3, 6, 10, 13],.theta333,[3, 2, 1, 0, 6, 5, 7, 8],[3, 2, 1, 0, 0, 5, 4, 6, 7, 0]⟩,
  ⟨[3, 6, 12, 17, 24],.ten,[3, 5, 0, 6, 1, 7, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 3, 5, 7, 9]⟩,
  ⟨[3, 6, 17, 18, 20],.theta244,[6, 9, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 0, 1]⟩,
  ⟨[3, 6, 17, 20],.eight,[2, 5, 0, 6, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 3, 5, 0, 7]⟩,
  ⟨[3, 6, 18, 21],.theta333,[3, 2, 1, 0, 6, 5, 7, 9],[3, 2, 1, 0, 0, 5, 4, 6, 0, 7]⟩,
  ⟨[3, 9, 10],.six,[1, 5, 0, 6, 2, 8],[2, 0, 4, 0, 0, 1, 3, 0, 5, 0]⟩]

def batch4 : List Item := [
  ⟨[3, 9, 10, 17, 18],.theta244,[5, 6, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 0, 4, 7]⟩,
  ⟨[3, 9, 10, 17, 24],.theta244,[5, 8, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[3, 9, 10, 18, 24],.theta244,[6, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[3, 9, 12, 18, 20],.ten,[1, 5, 0, 6, 3, 9, 4, 7, 2, 8],[2, 0, 8, 4, 6, 1, 3, 7, 9, 5]⟩,
  ⟨[3, 9, 17, 18, 24],.theta244,[5, 9, 2, 0, 6, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[3, 9, 17, 26],.theta333,[3, 2, 1, 0, 5, 6, 8, 9],[3, 2, 1, 0, 0, 4, 5, 0, 6, 7]⟩]

def batch5 : List Item := [
  ⟨[3, 9, 18, 24],.eight,[1, 5, 0, 6, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 3, 0, 7, 5]⟩,
  ⟨[3, 10, 12, 17, 20],.ten,[3, 5, 0, 6, 1, 8, 2, 7, 4, 9],[2, 4, 6, 0, 8, 1, 3, 7, 5, 9]⟩,
  ⟨[3, 10, 17, 18, 24],.theta244,[6, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[3, 10, 17, 24],.eight,[2, 5, 0, 6, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 3, 0, 5, 7]⟩,
  ⟨[3, 10, 18, 25],.theta333,[3, 2, 1, 0, 6, 5, 8, 9],[3, 2, 1, 0, 0, 5, 4, 0, 6, 7]⟩,
  ⟨[3, 12, 21, 26],.theta244,[2, 3, 9, 5, 0, 6, 7, 1, 8],[4, 7, 0, 1, 0, 3, 5, 6, 8, 2]⟩]

def batch6 : List Item := [
  ⟨[3, 12, 22, 25],.theta244,[3, 2, 9, 5, 0, 6, 8, 1, 7],[4, 7, 1, 0, 0, 3, 5, 8, 6, 2]⟩,
  ⟨[3, 13, 20, 26],.theta244,[1, 3, 8, 5, 0, 6, 7, 2, 9],[4, 0, 7, 1, 0, 3, 5, 6, 2, 8]⟩,
  ⟨[3, 13, 22, 24],.theta244,[1, 2, 7, 5, 0, 6, 8, 3, 9],[4, 0, 1, 7, 0, 3, 5, 2, 6, 8]⟩,
  ⟨[3, 14, 20, 25],.theta244,[3, 1, 8, 5, 0, 6, 9, 2, 7],[4, 1, 7, 0, 0, 3, 5, 8, 2, 6]⟩,
  ⟨[3, 14, 21, 24],.theta244,[2, 1, 7, 5, 0, 6, 9, 3, 8],[4, 1, 0, 7, 0, 3, 5, 2, 8, 6]⟩,
  ⟨[3, 17, 18],.six,[1, 5, 0, 6, 2, 9],[2, 0, 4, 0, 0, 1, 3, 0, 0, 5]⟩]

def batch7 : List Item := [
  ⟨[5, 6, 9, 10],.eight,[2, 5, 0, 7, 1, 6, 3, 8],[2, 4, 0, 6, 0, 1, 5, 3, 7, 0]⟩,
  ⟨[5, 6, 9, 10, 12],.theta244,[7, 8, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 1, 0]⟩,
  ⟨[5, 6, 9, 18, 24],.ten,[2, 5, 0, 7, 1, 6, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 5, 3, 9, 7]⟩,
  ⟨[5, 6, 10, 17, 24],.ten,[3, 5, 0, 7, 1, 6, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 5, 3, 7, 9]⟩,
  ⟨[5, 6, 11, 12],.theta333,[2, 3, 1, 0, 7, 5, 6, 8],[3, 2, 0, 1, 0, 5, 6, 4, 7, 0]⟩,
  ⟨[5, 6, 17, 18],.eight,[2, 5, 0, 7, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 3, 0, 7]⟩]

def batch8 : List Item := [
  ⟨[5, 6, 17, 18, 20],.theta244,[7, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[5, 6, 19, 20],.theta333,[2, 3, 1, 0, 7, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 4, 0, 7]⟩,
  ⟨[5, 9, 10, 18, 20],.ten,[1, 5, 0, 7, 4, 9, 3, 6, 2, 8],[2, 0, 8, 6, 4, 1, 7, 3, 9, 5]⟩,
  ⟨[5, 9, 12],.six,[1, 5, 0, 7, 2, 8],[2, 0, 4, 0, 0, 1, 0, 3, 5, 0]⟩,
  ⟨[5, 9, 12, 17, 20],.theta244,[5, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[5, 9, 12, 17, 24],.theta244,[5, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩]

def batch9 : List Item := [
  ⟨[5, 9, 12, 20, 24],.theta244,[7, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[5, 9, 17, 20, 24],.theta244,[5, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩,
  ⟨[5, 9, 17, 28],.theta333,[3, 2, 1, 0, 5, 7, 8, 9],[3, 2, 1, 0, 0, 4, 0, 5, 6, 7]⟩,
  ⟨[5, 9, 20, 24],.eight,[1, 5, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 0, 3, 7, 5]⟩,
  ⟨[5, 10, 12, 17, 18],.ten,[3, 5, 0, 7, 2, 8, 1, 6, 4, 9],[2, 6, 4, 0, 8, 1, 7, 3, 5, 9]⟩,
  ⟨[5, 10, 19, 28],.theta244,[2, 3, 9, 5, 0, 7, 6, 1, 8],[4, 7, 0, 1, 0, 3, 6, 5, 8, 2]⟩]

def batch10 : List Item := [
  ⟨[5, 10, 22, 25],.theta244,[3, 2, 9, 5, 0, 7, 8, 1, 6],[4, 7, 1, 0, 0, 3, 8, 5, 6, 2]⟩,
  ⟨[5, 11, 18, 28],.theta244,[1, 3, 8, 5, 0, 7, 6, 2, 9],[4, 0, 7, 1, 0, 3, 6, 5, 2, 8]⟩,
  ⟨[5, 11, 22, 24],.theta244,[1, 2, 6, 5, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 3, 2, 5, 6, 8]⟩,
  ⟨[5, 12, 17, 20, 24],.theta244,[7, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[5, 12, 17, 24],.eight,[2, 5, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 0, 3, 5, 7]⟩,
  ⟨[5, 12, 20, 25],.theta333,[3, 2, 1, 0, 7, 5, 8, 9],[3, 2, 1, 0, 0, 5, 0, 4, 6, 7]⟩]

def batch11 : List Item := [
  ⟨[5, 14, 18, 25],.theta244,[3, 1, 8, 5, 0, 7, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 5, 2, 6]⟩,
  ⟨[5, 14, 19, 24],.theta244,[2, 1, 6, 5, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 3, 2, 5, 8, 6]⟩,
  ⟨[5, 17, 20],.six,[1, 5, 0, 7, 2, 9],[2, 0, 4, 0, 0, 1, 0, 3, 0, 5]⟩,
  ⟨[6, 9, 10, 17, 20],.ten,[3, 5, 1, 8, 2, 6, 0, 7, 4, 9],[6, 2, 4, 0, 8, 1, 5, 7, 3, 9]⟩,
  ⟨[6, 9, 12, 17, 18],.ten,[3, 5, 1, 8, 2, 7, 0, 6, 4, 9],[6, 2, 4, 0, 8, 1, 7, 5, 3, 9]⟩,
  ⟨[6, 9, 19, 28],.theta244,[2, 3, 9, 5, 1, 8, 6, 0, 7],[7, 4, 0, 1, 0, 3, 6, 8, 5, 2]⟩]

def batch12 : List Item := [
  ⟨[6, 9, 21, 26],.theta244,[2, 3, 9, 5, 1, 8, 7, 0, 6],[7, 4, 0, 1, 0, 3, 8, 6, 5, 2]⟩,
  ⟨[6, 10, 12],.six,[1, 6, 0, 7, 2, 8],[2, 0, 4, 0, 0, 0, 1, 3, 5, 0]⟩,
  ⟨[6, 10, 12, 18, 20],.theta244,[6, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[6, 10, 12, 18, 24],.theta244,[6, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩,
  ⟨[6, 10, 12, 20, 24],.theta244,[7, 8, 2, 0, 6, 1, 3, 9, 4],[3, 5, 2, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[6, 10, 18, 20, 24],.theta244,[6, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩]

def batch13 : List Item := [
  ⟨[6, 10, 18, 28],.theta333,[3, 2, 1, 0, 6, 7, 8, 9],[3, 2, 1, 0, 0, 0, 4, 5, 6, 7]⟩,
  ⟨[6, 10, 20, 24],.eight,[1, 6, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 0, 1, 3, 7, 5]⟩,
  ⟨[6, 11, 17, 28],.theta244,[1, 3, 8, 5, 2, 9, 6, 0, 7],[7, 0, 4, 1, 0, 3, 6, 8, 2, 5]⟩,
  ⟨[6, 11, 21, 24],.theta244,[1, 2, 5, 6, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 2, 3, 5, 6, 8]⟩,
  ⟨[6, 12, 18, 20, 24],.theta244,[7, 9, 3, 0, 6, 2, 1, 8, 4],[3, 6, 5, 2, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[6, 12, 18, 24],.eight,[2, 6, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 0, 1, 3, 5, 7]⟩]

def batch14 : List Item := [
  ⟨[6, 12, 20, 26],.theta333,[3, 2, 1, 0, 7, 6, 8, 9],[3, 2, 1, 0, 0, 0, 5, 4, 6, 7]⟩,
  ⟨[6, 13, 17, 26],.theta244,[1, 3, 8, 5, 2, 9, 7, 0, 6],[7, 0, 4, 1, 0, 3, 8, 6, 2, 5]⟩,
  ⟨[6, 13, 19, 24],.theta244,[2, 1, 5, 6, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 2, 3, 5, 8, 6]⟩,
  ⟨[6, 18, 20],.six,[1, 6, 0, 7, 2, 9],[2, 0, 4, 0, 0, 0, 1, 3, 0, 5]⟩,
  ⟨[7, 9, 10, 12],.theta333,[0, 3, 2, 1, 8, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 4, 0]⟩,
  ⟨[7, 9, 18, 28],.theta244,[0, 3, 7, 5, 1, 8, 6, 2, 9],[0, 4, 7, 1, 0, 3, 6, 2, 5, 8]⟩]

def batch15 : List Item := [
  ⟨[7, 9, 20, 26],.theta244,[0, 3, 6, 5, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 3, 2, 6, 5, 8]⟩,
  ⟨[7, 10, 17, 28],.theta244,[0, 3, 7, 5, 2, 9, 6, 1, 8],[0, 7, 4, 1, 0, 3, 6, 2, 8, 5]⟩,
  ⟨[7, 10, 20, 25],.theta244,[0, 3, 5, 6, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 2, 3, 6, 5, 8]⟩,
  ⟨[7, 12, 17, 26],.theta244,[0, 3, 6, 5, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 3, 2, 6, 8, 5]⟩,
  ⟨[7, 12, 18, 25],.theta244,[0, 3, 5, 6, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 2, 3, 6, 8, 5]⟩,
  ⟨[7, 17, 18, 20],.theta333,[0, 3, 2, 1, 9, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 0, 4]⟩]

def batch16 : List Item := [
  ⟨[9, 10, 17, 18],.eight,[2, 5, 0, 8, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 0, 3, 7]⟩,
  ⟨[9, 10, 17, 18, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[9, 10, 19, 24],.theta333,[2, 3, 1, 0, 8, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 0, 4, 7]⟩,
  ⟨[9, 12, 17, 20],.eight,[2, 5, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 0, 5, 3, 7]⟩,
  ⟨[9, 12, 17, 20, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 7, 3],[3, 6, 5, 8, 2, 4, 0, 7, 0, 1]⟩,
  ⟨[9, 12, 21, 24],.theta333,[2, 3, 1, 0, 8, 5, 7, 9],[3, 2, 0, 1, 0, 5, 0, 6, 4, 7]⟩]

def batch17 : List Item := [
  ⟨[9, 14, 18, 21],.theta244,[3, 1, 7, 5, 0, 8, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 2, 5, 6]⟩,
  ⟨[9, 14, 19, 20],.theta244,[2, 1, 6, 5, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 3, 2, 8, 5, 6]⟩,
  ⟨[9, 17, 24],.six,[1, 5, 0, 8, 2, 9],[2, 0, 4, 0, 0, 1, 0, 0, 3, 5]⟩,
  ⟨[10, 12, 18, 20],.eight,[2, 6, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 0, 1, 5, 3, 7]⟩,
  ⟨[10, 12, 18, 20, 24],.theta244,[8, 9, 4, 0, 6, 2, 1, 7, 3],[3, 6, 5, 8, 2, 0, 4, 7, 0, 1]⟩,
  ⟨[10, 12, 22, 24],.theta333,[2, 3, 1, 0, 8, 6, 7, 9],[3, 2, 0, 1, 0, 0, 5, 6, 4, 7]⟩]

def batch18 : List Item := [
  ⟨[10, 13, 17, 22],.theta244,[1, 3, 7, 5, 2, 9, 8, 0, 6],[7, 0, 4, 1, 0, 3, 8, 2, 6, 5]⟩,
  ⟨[10, 13, 19, 20],.theta244,[2, 1, 5, 6, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 2, 3, 8, 5, 6]⟩,
  ⟨[10, 18, 24],.six,[1, 6, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 1, 0, 3, 5]⟩,
  ⟨[11, 12, 17, 22],.theta244,[0, 3, 6, 5, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 3, 2, 8, 6, 5]⟩,
  ⟨[11, 12, 18, 21],.theta244,[0, 3, 5, 6, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 2, 3, 8, 6, 5]⟩,
  ⟨[11, 17, 18, 24],.theta333,[0, 3, 2, 1, 9, 5, 6, 8],[0, 3, 2, 1, 0, 5, 6, 0, 7, 4]⟩]

def batch19 : List Item := [
  ⟨[12, 20, 24],.six,[1, 7, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 0, 1, 3, 5]⟩,
  ⟨[13, 17, 20, 24],.theta333,[0, 3, 2, 1, 9, 5, 7, 8],[0, 3, 2, 1, 0, 5, 0, 6, 7, 4]⟩,
  ⟨[14, 18, 20, 24],.theta333,[0, 3, 2, 1, 9, 6, 7, 8],[0, 3, 2, 1, 0, 0, 5, 6, 7, 4]⟩]

def items := batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6 ++ batch7 ++ batch8 ++ batch9 ++ batch10 ++ batch11 ++ batch12 ++ batch13 ++ batch14 ++ batch15 ++ batch16 ++ batch17 ++ batch18 ++ batch19

end CoreCensus

namespace CoreCensus

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check0 : batch0.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check1 : batch1.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check2 : batch2.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check3 : batch3.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check4 : batch4.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check5 : batch5.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check6 : batch6.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check7 : batch7.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check8 : batch8.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check9 : batch9.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check10 : batch10.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check11 : batch11.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check12 : batch12.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check13 : batch13.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check14 : batch14.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check15 : batch15.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check16 : batch16.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check17 : batch17.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check18 : batch18.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check19 : batch19.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem validated {r : Item} (hr : r ∈ items) : Certified r := by
  have h : items.all (fun e => decide (Certified e)) = true := by
    simp only [items,List.all_append,check0,check1,check2,check3,check4,check5,check6,check7,check8,check9,check10,check11,check12,check13,check14,check15,check16,check17,check18,check19,Bool.true_and]
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

end CoreCensus

namespace CoreCensus
open List

def wt (r : Nat) := (r % 2) + (r / 2 % 2) + (r / 4 % 2) + (r / 8 % 2) + (r / 16 % 2)

def eligible (lo budget : Nat) (pre : List Nat) (r : Nat) : Bool :=
  decide (lo < r ∧ 2 ≤ wt r ∧ wt r ≤ budget) && pre.all (fun p => decide (wt (p &&& r) ≤ 1))

def generate : Nat → Nat → Nat → List Nat → List (List Nat)
  | 0, _, _, pre => [pre]
  | k+1, lo, budget, pre => pre :: ((range 32).filter (eligible lo budget pre)).flatMap
      fun r => generate k r (budget - wt r) (pre ++ [r])

theorem current_mem (k lo budget) (pre : List Nat) : pre ∈ generate k lo budget pre := by
  cases k <;> simp [generate]

def Compatible (r s : Nat) := r < s ∧ wt (r &&& s) ≤ 1

theorem listed (ys : List Nat) (fuel lo budget : Nat) (pre : List Nat)
    (len : ys.length ≤ fuel) (bounds : ∀ r ∈ ys, lo < r ∧ r < 32 ∧ 2 ≤ wt r)
    (total : (ys.map wt).sum ≤ budget) (pair : ys.Pairwise Compatible)
    (past : ∀ r ∈ ys, ∀ p ∈ pre, wt (p &&& r) ≤ 1) :
    pre ++ ys ∈ generate fuel lo budget pre := by
  induction ys generalizing fuel lo budget pre with
  | nil => simpa using current_mem fuel lo budget pre
  | cons r rs ih =>
    cases fuel with
    | zero => simp at len
    | succ k =>
      obtain ⟨rtop,rr,rlower⟩ := bounds r (by simp)
      have cost : wt r + (rs.map wt).sum ≤ budget := by simpa using total
      obtain ⟨first,tail⟩ := List.pairwise_cons.mp pair
      have elig : eligible lo budget pre r = true := by
        unfold eligible
        apply Bool.and_eq_true_iff.mpr
        exact ⟨decide_eq_true ⟨rtop,rlower,by omega⟩,
          List.all_eq_true.mpr (fun p hp => decide_eq_true (past r (by simp) p hp))⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr rr,elig⟩,?_⟩
      have hmem := ih k r (budget - wt r) (pre ++ [r]) (by simpa using len)
          (fun s hs => ⟨(first s hs).1,(bounds s (by simp [hs])).2⟩) (by omega) tail (by
            intro s hs p hp
            rcases List.mem_append.mp hp with old | new
            · exact past s (by simp [hs]) p old
            · obtain rfl : p = r := by simpa using new
              exact (first s hs).2)
      simpa only [List.append_assoc,List.singleton_append] using hmem

def liveCols (xs : List Nat) : Bool :=
  (range 5).all fun i => decide (xs.countP (fun r => r.testBit i) ≠ 1)

def recognized (xs : List Nat) : Bool := items.any (fun c => c.rows == xs)

def acceptedRows (xs : List Nat) : Bool := xs.isEmpty || !liveCols xs || recognized xs

theorem exists_item {xs : List Nat} (h : recognized xs = true) : ∃ r ∈ items, r.rows = xs := by
  obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp h
  exact ⟨r,hr,by simpa using eq⟩

end CoreCensus

namespace CoreCensus
open List

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first3 : (generate 4 3 (10 - wt 3) [3]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first5 : (generate 4 5 (10 - wt 5) [5]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first6 : (generate 4 6 (10 - wt 6) [6]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first7 : (generate 4 7 (10 - wt 7) [7]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first9 : (generate 4 9 (10 - wt 9) [9]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first10 : (generate 4 10 (10 - wt 10) [10]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first11 : (generate 4 11 (10 - wt 11) [11]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first12 : (generate 4 12 (10 - wt 12) [12]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first13 : (generate 4 13 (10 - wt 13) [13]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first14 : (generate 4 14 (10 - wt 14) [14]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first15 : (generate 4 15 (10 - wt 15) [15]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first17 : (generate 4 17 (10 - wt 17) [17]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first18 : (generate 4 18 (10 - wt 18) [18]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first19 : (generate 4 19 (10 - wt 19) [19]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first20 : (generate 4 20 (10 - wt 20) [20]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first21 : (generate 4 21 (10 - wt 21) [21]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first22 : (generate 4 22 (10 - wt 22) [22]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first23 : (generate 4 23 (10 - wt 23) [23]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first24 : (generate 4 24 (10 - wt 24) [24]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first25 : (generate 4 25 (10 - wt 25) [25]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first26 : (generate 4 26 (10 - wt 26) [26]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first27 : (generate 4 27 (10 - wt 27) [27]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first28 : (generate 4 28 (10 - wt 28) [28]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first29 : (generate 4 29 (10 - wt 29) [29]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first30 : (generate 4 30 (10 - wt 30) [30]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first31 : (generate 4 31 (10 - wt 31) [31]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem all_rows : (generate 5 0 10 []).all acceptedRows = true := by
  have opts : (range 32).filter (eligible 0 10 []) = [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  change (acceptedRows [] && (((range 32).filter (eligible 0 10 [])).flatMap (fun r => generate 4 r (10 - wt r) ([] ++ [r]))).all acceptedRows) = true
  rw [List.all_flatMap,opts]
  have empty : acceptedRows [] = true := rfl
  simp only [empty,List.nil_append,List.all_cons,List.all_nil,Bool.true_and,first3,first5,first6,first7,first9,first10,first11,first12,first13,first14,first15,first17,first18,first19,first20,first21,first22,first23,first24,first25,first26,first27,first28,first29,first30,first31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem recognized_of_rows (xs : List Nat) (hne : xs ≠ [])
    (len : xs.length ≤ 5) (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r)
    (w : (xs.map wt).sum ≤ 10) (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) :
    ∃ c ∈ items, c.rows = xs := by
  have mem := listed xs 5 0 10 [] len bounds w s (by simp)
  have result := List.all_eq_true.mp all_rows xs (by simpa using mem)
  apply exists_item
  have notEmpty : xs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simpa [acceptedRows,notEmpty,hcol] using result

end CoreCensus

namespace CoreCensus
open LeafCore3241

theorem sorted_counts (xs : List Nat) (hne : xs ≠ []) (len : xs.length ≤ 5)
    (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) (w : (xs.map wt).sum ≤ 10)
    (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) : Counts (matrix xs) := by
  obtain ⟨r,member,rfl⟩ := recognized_of_rows xs hne len bounds w s hcol
  exact count_item r (validated member) Theta244.nine

end CoreCensus

namespace NormalizeCores3241
open CoreCensus GraphPacking3241 MatrixPacking3241 LeafCore3241 ForestBipartite3241

def encode (x : Fin 5 → Bool) : Nat :=
  (x 0).toNat + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16

theorem encode_bound : ∀ x : Fin 5 → Bool, encode x < 32 := by decide +kernel
theorem encode_bit : ∀ (x : Fin 5 → Bool) (i : Fin 5), (encode x).testBit i.val = x i := by decide +kernel
theorem encode_weight : ∀ x : Fin 5 → Bool, wt (encode x) = (Finset.univ.filter (fun i => x i)).card := by
  decide +kernel
theorem weight_two : ∀ (r : Fin 32) (a b : Fin 5), a ≠ b → r.val.testBit a.val = true →
    r.val.testBit b.val = true → 2 ≤ wt r.val := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem weight_shared : ∀ a b : Fin 32,
    (∀ i j : Fin 5, a.val.testBit i.val = true → b.val.testBit i.val = true →
      a.val.testBit j.val = true → b.val.testBit j.val = true → i = j) → wt (a.val &&& b.val) ≤ 1 := by
  decide +kernel

def mask (E : Matrix 5 5) (i : Fin 5) : Nat := encode fun j => decide ((i,j) ∈ E)

theorem bit_iff (E : Matrix 5 5) (i j : Fin 5) : (mask E i).testBit j.val = true ↔ (i,j) ∈ E := by
  simp [mask,encode_bit]

theorem wt_fiber (E : Matrix 5 5) (i : Fin 5) :
    wt (mask E i) = (E.filter (fun p => p.1 = i)).card := by
  let T := Finset.univ.filter (fun j : Fin 5 => (i,j) ∈ E)
  have eq : E.filter (fun p => p.1 = i) = T.image (Prod.mk i) := by
    ext p
    constructor
    · rintro h
      obtain ⟨he,pi⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [← pi] using he⟩,
        Prod.ext pi.symm rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2,rfl⟩
  have wt_eq := encode_weight (fun j : Fin 5 => decide ((i,j) ∈ E))
  rw [eq,Finset.card_image_of_injective _ (fun j k h => congrArg Prod.snd h)]
  simpa [mask,T] using wt_eq

theorem separated (E : Matrix 5 5) (free : FourFree E) (p q : Fin 5) (ne : p ≠ q) :
    wt (mask E p &&& mask E q) ≤ 1 := by
  apply weight_shared ⟨mask E p,encode_bound _⟩ ⟨mask E q,encode_bound _⟩
  intro i j pi qi pj qj
  by_contra ij
  exact free p q i j ne ij ⟨(bit_iff E p i).mp pi,(bit_iff E p j).mp pj,
    (bit_iff E q i).mp qi,(bit_iff E q j).mp qj⟩

theorem row_bounds (E : Matrix 5 5) (rich : HasPartners E) (p : Fin 5) (hp : p ∈ Rows E) :
    0 < mask E p ∧ mask E p < 32 ∧ 2 ≤ wt (mask E p) := by
  obtain ⟨⟨a,b⟩,ab,eq⟩ := Finset.mem_image.mp hp
  change a = p at eq
  subst a
  obtain ⟨c,cb,pc⟩ := (rich p b ab).1
  have positive : mask E p ≠ 0 := by
    intro bad
    have bit := (bit_iff E p b).mpr ab
    simp [bad] at bit
  exact ⟨Nat.pos_of_ne_zero positive,encode_bound _,
    weight_two ⟨mask E p,encode_bound _⟩ c b cb ((bit_iff E p c).mpr pc) ((bit_iff E p b).mpr ab)⟩

theorem mask_inj (E : Matrix 5 5) (free : FourFree E) (rich : HasPartners E) :
    Set.InjOn (mask E) (Rows E : Set (Fin 5)) := by
  intro a ha b _ eq
  by_contra ne
  have cap := separated E free a b ne
  rw [← eq,Nat.and_self] at cap
  have low := (row_bounds E rich a ha).2.2
  omega

theorem sum_list (xs : List Nat) (f : Nat → Nat) (distinct : xs.Nodup) :
    (xs.map f).sum = ∑ i ∈ xs.toFinset, f i := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := List.nodup_cons.mp distinct
    simp [h.1,ih h.2]

def SortedProof := ∀ xs : List Nat, xs ≠ [] → xs.length ≤ 5 →
  (∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) → (xs.map wt).sum ≤ 10 →
  xs.Pairwise Compatible → liveCols xs = true → Counts (matrix xs)

theorem census_of_sorted (done : SortedProof) : MatrixPacking3241.Census := by
  classical
  intro E size free last
  by_cases zero : E = ∅
  · have ac : (bip E).IsAcyclic := by
      have bot : bip E = ⊥ := by
        apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
        intro i j h
        rcases h with ⟨_,⟨e,he,_,_⟩ | ⟨e,he,_,_⟩⟩ <;> simp [zero] at he
      rw [bot]
      exact SimpleGraph.isAcyclic_bot
    exact forest_counts _ ac
  have rich := (leafless_iff E).mp last
  let A := (Rows E).image (mask E)
  let xs := A.sort
  have inj := mask_inj E free rich
  have cap : A.card ≤ 5 := (Finset.card_image_le).trans (Finset.card_le_univ (Rows E))
  have len : xs.length ≤ 5 := by simpa [xs] using cap
  have mem (r : Nat) : r ∈ xs ↔ ∃ p ∈ Rows E, mask E p = r := by simp [xs,A]
  have nonempty : xs ≠ [] := by
    obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    have hm := (mem _).mpr ⟨e.1,Finset.mem_image_of_mem _ he,rfl⟩
    intro eq
    simp [eq] at hm
  have rn : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    exact row_bounds E rich p hp
  have total : (xs.map wt).sum = E.card := by
    rw [sum_list _ _ (A.sort_nodup _)]
    have eq : xs.toFinset = A := by ext r; simp [xs]
    rw [eq,Finset.sum_image]
    · rw [Finset.card_eq_sum_card_image Prod.fst E]
      exact Finset.sum_congr rfl (fun x _ => wt_fiber E x)
    · exact inj
  have sorted : xs.Pairwise (· < ·) := A.sortedLT_sort.pairwise
  have pair : xs.Pairwise Compatible := by
    apply sorted.imp_of_mem
    intro a b ha hb lt
    obtain ⟨p,_,rfl⟩ := (mem a).mp ha
    obtain ⟨q,_,rfl⟩ := (mem b).mp hb
    exact ⟨lt,separated E free p q (fun eq => (Nat.ne_of_lt lt) (congrArg (mask E) eq))⟩
  have cols : liveCols xs = true := by
    apply List.all_eq_true.mpr
    intro j hj
    apply decide_eq_true
    intro unique
    have pos : 0 < xs.countP (fun r => r.testBit j) := by omega
    obtain ⟨r,hr,bit⟩ := List.countP_pos_iff.mp pos
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    let c : Fin 5 := ⟨j,List.mem_range.mp hj⟩
    have pc : (p,c) ∈ E := (bit_iff E p c).mp bit
    obtain ⟨q,qp,qc⟩ := (rich p c pc).2
    have hq : q ∈ Rows E := Finset.mem_image_of_mem Prod.fst qc
    have hq' := (mem _).mpr ⟨q,hq,rfl⟩
    have diff := ThetaPin3241.count_one_unique xs (fun a => a.testBit j) _ _ hq' hr
      ((bit_iff E q c).mpr qc) bit (by omega)
    exact qp (inj hq hp diff)
  have ok := done xs nonempty len rn (total ▸ size) pair cols
  let val (p : Rows E) : A := ⟨mask E p.val,Finset.mem_image_of_mem _ p.property⟩
  have bij : Function.Bijective val := by
    refine ⟨fun p q eq => Subtype.ext (inj p.property q.property (congrArg Subtype.val eq)),?_⟩
    intro a
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨p,hp⟩,Subtype.ext eq⟩
  let order := (Equiv.ofBijective val bij).trans ((A.orderIsoOfFin rfl).symm.toEquiv)
  let r (p : Rows E) : Fin 5 := (order p).castLE cap
  have ri : Function.Injective r := (Fin.castLE_injective cap).comp order.injective
  let c (p : Cols E) : Fin 5 := p.val
  have read (p : Rows E) : xs.getD (r p).val 0 = mask E p.val := by
    have hl : (r p).val < xs.length := by simp [xs,r]
    rw [List.getD_eq_getElem _ _ hl]
    have ev := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply (val p))
    exact ev
  have pe : pack E r c = pairs xs := by
    ext ij
    obtain ⟨i,j⟩ := ij
    change (i,j) ∈ pack E r c ↔ (i,j) ∈ pairs xs
    rw [decode]
    simp only [pairs,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨e,rfl,rfl⟩
      rw [read]
      exact (bit_iff E _ _).mpr e.property
    · intro bit
      have hl : i.val < xs.length := by
        by_contra! bad
        rw [List.getD_eq_default _ _ bad] at bit
        simp at bit
      have ha : i.val < A.card := by simpa [xs] using hl
      let p := order.symm ⟨i.val,ha⟩
      have pos : r p = i := Fin.ext (by simp [r,p])
      rw [← pos,read] at bit
      have cell := (bit_iff E p.val j).mp bit
      let e : E := ⟨(p.val,j),cell⟩
      exact ⟨e,pos,rfl⟩
  apply unpack_counts E r c ri Subtype.val_injective
  rw [pe]
  exact ok

theorem census : MatrixPacking3241.Census := census_of_sorted CoreCensus.sorted_counts

end NormalizeCores3241

end PEqualNP.Outside.L_meta_17265_aux

theorem PEqualNP.Outside.L_meta_17265 :
∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → x3.card ≤ (10 : ℕ) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C
  dsimp only
  intro free ao correct _ size
  exact PEqualNP.Outside.L_meta_17265_aux.MatrixPacking3241.officialBudget PEqualNP.Outside.L_meta_17265_aux.NormalizeCores3241.census E free size C ao correct
