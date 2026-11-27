import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Use the twelve edge inputs followed by the twelve maximal independent sets.
-- The three private readers agree with their input bits on every maximal independent set.
-- After a rotation, the first ordinary operation has one of four fixed signatures.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4223_518
    (edgeAnd :
      let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
      let M : List (BitVec 24) := [11083800,902208,13501056]
      let seed : BitVec 24 := 1
      (∀ U : Fin 3 → BitVec 24,
        (∀ s : Fin 3, U s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
          U s ||| M.getD s.val 0 = U s) →
        let ok (l : List (BitVec 24)) (w : BitVec 24) := w ∈ H ++ l ∨
          ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
        ∀ ys : List (BitVec 24), ys.length ≤ 11 →
          (∀ s : Fin 3, ∃ y ∈ seed :: ys, U s = M.getD s.val 0 ||| y) →
          (∀ (i : ℕ) (hi : i < ys.length), ∃ p q : BitVec 24,
            ok (seed :: ys.take i) p ∧ ok (seed :: ys.take i) q ∧
              (ys[i] = p &&& q ∨ ys[i] = p ||| q)) → ¬ ok (seed :: ys) 4095))
    (nearOr :
      let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
      let M : List (BitVec 24) := [11083800,902208,13501056]
      let seed : BitVec 24 := 14053491
      (∀ U : Fin 3 → BitVec 24,
        (∀ s : Fin 3, U s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
          U s ||| M.getD s.val 0 = U s) →
        let ok (l : List (BitVec 24)) (w : BitVec 24) := w ∈ H ++ l ∨
          ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
        ∀ ys : List (BitVec 24), ys.length ≤ 11 →
          (∀ s : Fin 3, ∃ y ∈ seed :: ys, U s = M.getD s.val 0 ||| y) →
          (∀ (i : ℕ) (hi : i < ys.length), ∃ p q : BitVec 24,
            ok (seed :: ys.take i) p ∧ ok (seed :: ys.take i) q ∧
              (ys[i] = p &&& q ∨ ys[i] = p ||| q)) → ¬ ok (seed :: ys) 4095))
    (nextOr :
      let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
      let M : List (BitVec 24) := [11083800,902208,13501056]
      let seed : BitVec 24 := 7684279
      (∀ U : Fin 3 → BitVec 24,
        (∀ s : Fin 3, U s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
          U s ||| M.getD s.val 0 = U s) →
        let ok (l : List (BitVec 24)) (w : BitVec 24) := w ∈ H ++ l ∨
          ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
        ∀ ys : List (BitVec 24), ys.length ≤ 11 →
          (∀ s : Fin 3, ∃ y ∈ seed :: ys, U s = M.getD s.val 0 ||| y) →
          (∀ (i : ℕ) (hi : i < ys.length), ∃ p q : BitVec 24,
            ok (seed :: ys.take i) p ∧ ok (seed :: ys.take i) q ∧
              (ys[i] = p &&& q ∨ ys[i] = p ||| q)) → ¬ ok (seed :: ys) 4095))
    (oppositeOr :
      let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
      let M : List (BitVec 24) := [11083800,902208,13501056]
      let seed : BitVec 24 := 5689661
      (∀ U : Fin 3 → BitVec 24,
        (∀ s : Fin 3, U s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
          U s ||| M.getD s.val 0 = U s) →
        let ok (l : List (BitVec 24)) (w : BitVec 24) := w ∈ H ++ l ∨
          ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
        ∀ ys : List (BitVec 24), ys.length ≤ 11 →
          (∀ s : Fin 3, ∃ y ∈ seed :: ys, U s = M.getD s.val 0 ||| y) →
          (∀ (i : ℕ) (hi : i < ys.length), ∃ p q : BitVec 24,
            ok (seed :: ys.take i) p ∧ ok (seed :: ys.take i) q ∧
              (ys[i] = p &&& q ∨ ys[i] = p ||| q)) → ¬ ok (seed :: ys) 4095))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∀ (x8 : Fin x1.size), (x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  classical
  intro C minimal small computes wiring unique separated noNot
  let E : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let graph (x : Fin 9 → Bool) := E.any fun e => x e.1 && x e.2
  let sel (s : Fin 3) : Fin 9 := if s = 0 then 4 else if s = 1 then 6 else 7
  let A : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968]
  let H : List (BitVec 24) := [5521457,8532035,3227782,430348,113184,15731968]
  let M : List (BitVec 24) := [11083800,902208,13501056]
  let X (r : Fin 24) (v : Fin 9) := (A.getD v.val 0).getLsbD r.val
  let V (x : Fin 9 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
  let gt (j : Fin C.size) := C.gates.get j
  have inp (x : Fin 9 → Bool) (v : Fin 9) : V x v.val = x v := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have ext (gs : List Gate) (xs : List Bool) : ∃ tail, gs.foldl step xs = xs ++ tail := by
      induction gs generalizing xs with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht⟩ := ih (step xs g)
        exact ⟨[_] ++ t, by simpa [List.foldl_cons, step, List.append_assoc] using ht⟩
    obtain ⟨t, ht⟩ := ext C.gates (List.ofFn x)
    change (C.gates.foldl step (List.ofFn x)).getD v.val false = x v
    rw [ht, List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt), List.getElem_ofFn]
  have equation (j : Fin C.size) (x : Fin 9 → Bool) :
      V x (9 + j.val) = (gt j).op.eval ((gt j).inputs.map (V x)) := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let pref (k : ℕ) := (C.gates.take k).foldl step (List.ofFn x)
    have sizeFold (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
      induction gs generalizing xs with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
    have sizePref (k : ℕ) (hk : k ≤ C.size) : (pref k).length = 9 + k := by
      unfold pref
      rw [sizeFold,List.length_ofFn,List.length_take_of_le hk]
    have ext (gs : List Gate) (xs : List Bool) : ∃ tail, gs.foldl step xs = xs ++ tail := by
      induction gs generalizing xs with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht⟩ := ih (step xs g)
        exact ⟨[_] ++ t, by simpa [List.foldl_cons, step, List.append_assoc] using ht⟩
    have stable (k w : ℕ) (hk : k ≤ C.size) (hw : w < 9+k) : V x w = (pref k).getD w false := by
      obtain ⟨t, ht⟩ := ext (C.gates.drop k) (pref k)
      change (C.gates.foldl step (List.ofFn x)).getD w false = _
      conv_lhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
      rw [show (C.gates.drop k).foldl step ((C.gates.take k).foldl step (List.ofFn x)) = pref k ++ t from ht]
      exact List.getD_append _ _ _ _ (by rwa [sizePref k hk])
    have hn : j.val < C.gates.length := j.isLt
    have next : pref (j.val+1) = step (pref j.val) (gt j) := by
      unfold pref
      rw [List.take_succ_eq_append_getElem hn, List.foldl_append]
      rfl
    rw [stable (j.val+1) _ (by have := j.isLt; omega) (by omega), next]
    have getLast (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
      induction l with
      | nil => rfl
      | cons h t ih => exact ih
    change ((pref j.val) ++ [_]).getD (9+j.val) false = _
    rw [← sizePref j.val (Nat.le_of_lt j.isLt), getLast]
    apply congrArg (gt j).op.eval
    apply List.map_congr_left
    intro i hi
    exact (stable j.val i (Nat.le_of_lt j.isLt) ((wiring j).1 i hi)).symm
  have out (x : Fin 9 → Bool) : V x C.output = graph x := congrFun computes x
  have validOut : 9 ≤ C.output ∧ C.output < 9+C.size := by
    constructor
    · by_contra! h
      let v : Fin 9 := ⟨C.output,h⟩
      let x : Fin 9 → Bool := fun i => decide (i = v)
      have noSingleton : ∀ (i : Fin 9), graph (fun j => decide (j = i)) = false := by decide
      have vv := inp x v
      change V x C.output = _ at vv
      rw [out, noSingleton v] at vv
      simp [x] at vv
    · by_contra! h
      let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have sizeFold (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
        induction gs generalizing xs with
        | nil => simp
        | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
      have hx : graph (X 0) = true := by decide
      have hv := out (X 0)
      change (C.gates.foldl step (List.ofFn (X 0))).getD C.output false = _ at hv
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp only [sizeFold,List.length_ofFn]; rw [show C.gates.length = C.size from rfl]; exact h)] at hv
      rw [hx] at hv
      exact Bool.noConfusion hv
  have selmem : ∀ s, sel s ∈ ([4,6,7] : List (Fin 9)) := by decide
  choose key hkey using fun s : Fin 3 => unique (sel s) (selmem s)
  have keyIn (s : Fin 3) : (sel s).val ∈ (gt (key s)).inputs := ((hkey s).1 (key s)).mpr rfl
  have keyInj : Function.Injective key := by
    intro s t h
    have ht := keyIn t
    rw [← h] at ht
    have memNat : ∀ q, (sel q).val ∈ ([4,6,7] : List ℕ) := by decide
    have e := separated (key s) _ (keyIn s) _ ht (memNat s) (memNat t)
    have inj : ∀ a b : Fin 3, (sel a).val = (sel b).val → a = b := by decide
    exact inj _ _ e
  have agree (s : Fin 3) (x y : Fin 9 → Bool)
      (same : ∀ v, v ≠ sel s → x v = y v)
      (reader : V x (9+(key s).val) = V y (9+(key s).val)) : graph x = graph y := by
    have go (k : ℕ) (hk : k < C.size) : V x (9+k) = V y (9+k) := by
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        let j : Fin C.size := ⟨k,hk⟩
        change V x (9+j.val) = V y (9+j.val)
        by_cases e : j = key s
        · simpa [e] using reader
        rw [equation j x, equation j y]
        apply congrArg (gt j).op.eval
        apply List.map_congr_left
        intro w hw
        by_cases low : w < 9
        · let v : Fin 9 := ⟨w,low⟩
          have ne : v ≠ sel s := by
            intro eq
            apply e
            apply ((hkey s).1 j).mp
            exact (congrArg Fin.val eq) ▸ hw
          exact (inp x v).trans ((same v ne).trans (inp y v).symm)
        · have back := (wiring j).1 w hw
          change w < 9+k at back
          have eq : w = 9 + (w-9) := by omega
          rw [eq]
          exact ih (w-9) (by omega) (by omega)
    rw [← out x, ← out y]
    have outeq : C.output = 9 + (C.output-9) := by omega
    rw [outeq]
    exact go _ (by omega)
  have binary (j : Fin C.size) : ∃ a b : ℕ, (gt j).inputs = [a,b] ∧ a ≠ b ∧
      ((gt j).op = .and ∨ (gt j).op = .or) := by
    have count := ((wiring j).2.2.resolve_left fun h => noNot j h.1).2
    have nd := (wiring j).2.1
    have kind := (minimal.1 _ (List.get_mem C.gates j)).1
    change (gt j).op = .and ∨ (gt j).op = .or ∨ (gt j).op = .not at kind
    change (gt j).inputs.length = 2 at count
    change (gt j).inputs.Nodup at nd
    have arity (l : List ℕ) (h : l.length = 2) : ∃ a b, l = [a,b] := by
      cases l with
      | nil => simp at h
      | cons a t =>
        cases t with
        | nil => simp at h
        | cons b u =>
          cases u with
          | nil => exact ⟨a,b,rfl⟩
          | cons c u => simp at h
    obtain ⟨a,b,ab⟩ := arity _ count
    refine ⟨a,b,ab,by simpa [ab] using nd,?_⟩
    exact kind.elim Or.inl (fun rest => Or.inr (rest.resolve_right (noNot j)))
  have packed (s : Fin 3) : ∃ b : ℕ, b ≠ (sel s).val ∧ b < 9+(key s).val ∧
      ∀ x, V x (9+(key s).val) = (x (sel s) || V x b) := by
    obtain ⟨a,b,ab,diff,_⟩ := binary (key s)
    have reads := keyIn s
    rw [ab] at reads
    have back := (wiring (key s)).1
    change ∀ w ∈ (gt (key s)).inputs, w < 9+(key s).val at back
    rw [ab] at back
    have orPair (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    rcases (show (sel s).val = a ∨ (sel s).val = b by simpa using reads) with ha | hb
    · subst a
      refine ⟨b,Ne.symm diff,back b (by simp),?_⟩
      intro x
      rw [equation, (show (gt (key s)).op = .or from (hkey s).2),ab]
      simp only [List.map_cons,List.map_nil,orPair,inp]
    · subst b
      refine ⟨a,diff,back a (by simp),?_⟩
      intro x
      rw [equation, (show (gt (key s)).op = .or from (hkey s).2),ab]
      simp only [List.map_cons,List.map_nil,orPair,inp,Bool.or_comm (V x a)]
  choose side sideProp using packed
  have tests : ∀ r : Fin 24, graph (X r) = (4095 : BitVec 24).getLsbD r.val := by decide
  have neg : ∀ r : Fin 24, 12 ≤ r.val → graph (X r) = false := by decide
  have up : ∀ (r : Fin 24) (s : Fin 3), 12 ≤ r.val → X r (sel s) = false →
      graph (Function.update (X r) (sel s) true) = true := by decide
  have negVal (s : Fin 3) (r : Fin 24) (hr : 12 ≤ r.val) :
      V (X r) (9+(key s).val) = X r (sel s) := by
    rcases valEq : X r (sel s) with _ | _
    · apply Bool.eq_false_iff.mpr
      intro yes
      let y := Function.update (X r) (sel s) true
      have on : V y (9+(key s).val) = true := by
        rw [(sideProp s).2.2]
        simp [y]
      have same := agree s (X r) y (fun v hv => by simp [y,Function.update_of_ne hv]) (yes.trans on.symm)
      rw [neg r hr, up r s hr valEq] at same
      exact Bool.noConfusion same
    · rw [(sideProp s).2.2,valEq]
      rfl
  let word (w : ℕ) : BitVec 24 :=
    (BitVec.ofBoolListLE (List.ofFn fun r : Fin 24 => V (X r) w)).cast (by simp)
  have bit (w : ℕ) (r : Fin 24) : (word w).getLsbD r.val = V (X r) w := by
    simp only [word,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using r.isLt),List.getElem_ofFn]
  have raw (i : Fin 9) : word i.val = A.getD i.val 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [bit _ ⟨r,hr⟩,inp]
  let U (s : Fin 3) := word (9+(key s).val)
  have marked : ∀ s : Fin 3, A.getD (sel s).val 0 = M.getD s.val 0 := by decide
  have nmask (s : Fin 3) : U s &&& 16773120 = M.getD s.val 0 &&& 16773120 := by
    have off : ∀ r : Fin 24, r.val < 12 → (16773120 : BitVec 24).getLsbD r.val = false := by decide
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [BitVec.getLsbD_and,BitVec.getLsbD_and]
    by_cases low : r < 12
    · have clear : (16773120 : BitVec 24).getLsbD r = false := off ⟨r,hr⟩ low
      rw [clear]
      simp
    · change ((word _).getLsbD r && _) = _
      rw [bit _ ⟨r,hr⟩,negVal s ⟨r,hr⟩ (by change 12 ≤ r; omega)]
      simp only [X,marked]
  have join (s : Fin 3) : U s = M.getD s.val 0 ||| word (side s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    change (word _).getLsbD r = _
    rw [BitVec.getLsbD_or,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,(sideProp s).2.2]
    simp only [X,marked]
  have testSep : ∀ (s : Fin 3) (i : Fin 9), i ≠ sel s →
      ∃ r : Fin 24, 12 ≤ r.val ∧ X r i = true ∧ X r (sel s) = false := by decide
  have sideInternal (s : Fin 3) : ∃ j : Fin C.size, side s = 9+j.val ∧ j.val < (key s).val ∧
      ∀ t : Fin 3, j ≠ key t := by
    have offOn (r : Fin 24) (hr : 12 ≤ r.val) (isOff : X r (sel s) = false) :
        V (X r) (side s) = false := by
      have v := negVal s r hr
      rw [(sideProp s).2.2,isOff] at v
      simpa using v
    have hside := (sideProp s).2.1
    have kval := (key s).isLt
    have lower : 9 ≤ side s := by
      by_contra! low
      let i : Fin 9 := ⟨side s,low⟩
      have diff : i ≠ sel s := fun e => (sideProp s).1 (congrArg Fin.val e)
      obtain ⟨r,hr,on,off⟩ := testSep s i diff
      have contradictionAt := offOn r hr off
      rw [show V (X r) (side s) = X r i from inp _ i,on] at contradictionAt
      exact Bool.noConfusion contradictionAt
    let j : Fin C.size := ⟨side s-9,by omega⟩
    have eq : side s = 9+j.val := by dsimp [j]; omega
    have earlier : j.val < (key s).val := by omega
    refine ⟨j,eq,earlier,?_⟩
    intro t e
    have diff : sel t ≠ sel s := by
      intro same
      have inj : ∀ a b : Fin 3, sel a = sel b → a = b := by decide
      have ts := inj _ _ same
      subst t
      rw [e] at earlier
      omega
    obtain ⟨r,hr,on,off⟩ := testSep s (sel t) diff
    have contradictionAt := offOn r hr off
    rw [eq,e,negVal t r hr,on] at contradictionAt
    exact Bool.noConfusion contradictionAt
  let keys : Finset ℕ := Finset.univ.image fun s : Fin 3 => (key s).val
  have keyMem (s : Fin 3) : (key s).val ∈ keys :=
    Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
  have cardKeys : keys.card = 3 := by
    have inj : Function.Injective (fun s : Fin 3 => (key s).val) :=
      fun _ _ e => keyInj (Fin.ext e)
    simp [keys, Finset.card_image_of_injective _ inj]
  have keySub : keys ⊆ Finset.range C.size := by
    intro i hi
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (key s).isLt
  have firstFree : 0 ∉ keys := by
    intro mem
    obtain ⟨s,_,h⟩ := Finset.mem_image.mp mem
    obtain ⟨j,_,earlier,_⟩ := sideInternal s
    omega
  let P (k : ℕ) := ((List.range k).filter fun i => decide (i ∉ keys)).map fun i => word (9+i)
  have snoc (k : ℕ) : P (k+1) = if k ∈ keys then P k else P k ++ [word (9+k)] := by
    by_cases h : k ∈ keys <;> simp [P,List.range_succ,List.filter_append,h]
  have lengthBound : (P C.size).length ≤ 12 := by
    let ix := (List.range C.size).filter fun i => decide (i ∉ keys)
    have distinct : ix.Nodup := (List.nodup_range).filter _
    have asSet : ix.toFinset = Finset.range C.size \ keys := by ext i; simp [ix]
    have count := List.toFinset_card_of_nodup distinct
    rw [asSet, Finset.card_sdiff_of_subset keySub,Finset.card_range,cardKeys] at count
    change (ix.map _).length ≤ 12
    rw [List.length_map,← count]
    omega
  have inP (k i : ℕ) (hi : i < k) (ordinary : i ∉ keys) : word (9+i) ∈ P k := by
    apply List.mem_map.mpr
    exact ⟨i,by simp [hi,ordinary],rfl⟩
  let Av (l : List (BitVec 24)) (w : BitVec 24) : Prop :=
    w ∈ H ++ l ∨ ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
  have available (k w : ℕ) (hw : w < 9+k) (ordinary : ∀ s, w ≠ (sel s).val) : Av (P k) (word w) := by
    by_cases lo : w < 9
    · let v : Fin 9 := ⟨w,lo⟩
      have highs : ∀ i : Fin 9, (∀ s : Fin 3, i.val ≠ (sel s).val) → A.getD i.val 0 ∈ H := by decide
      left
      apply List.mem_append_left
      rw [show word w = A.getD v.val 0 from raw v]
      exact highs v ordinary
    · have eq : w = 9 + (w-9) := by omega
      by_cases h : w-9 ∈ keys
      · obtain ⟨s,_,hs⟩ := Finset.mem_image.mp h
        have reader : w = 9+(key s).val := by omega
        have ue : word w = U s := by rw [reader]
        obtain ⟨j,sideEq,earlier,unmarked⟩ := sideInternal s
        have free : j.val ∉ keys := by
          intro mark
          obtain ⟨t,_,et⟩ := Finset.mem_image.mp mark
          exact unmarked t (Fin.ext et.symm)
        right
        refine ⟨s,ue,word (9+j.val),inP k _ (by omega) free,?_⟩
        rw [ue,join s,sideEq]
      · left
        apply List.mem_append_right
        rw [eq]
        exact inP _ _ (by omega) h
  have sizePos : 0 < C.size := (key 0).isLt.trans_le' (Nat.zero_le _)
  let Good (l : List (BitVec 24)) := ∀ (i : ℕ) (hi : i < l.length), ∃ p q : BitVec 24,
    Av (l.take i) p ∧ Av (l.take i) q ∧
    (l[i] = p &&& q ∨ l[i] = p ||| q)
  have appendGood (l : List (BitVec 24)) (w : BitVec 24) (prev : Good l)
      (one : ∃ p q : BitVec 24, Av l p ∧ Av l q ∧
        (w = p &&& q ∨ w = p ||| q)) :
      Good (l ++ [w]) := by
    intro i hi
    by_cases old : i < l.length
    · rw [List.take_append_of_le_length (le_of_lt old),List.getElem_append_left old]
      exact prev i old
    · have eq : i = l.length := by simp at hi; omega
      subst i
      simpa [List.take_append_of_le_length le_rfl] using one
  have good (k : ℕ) (hk : k ≤ C.size) : Good (P k) := by
    induction k with
    | zero => intro i hi; simp [P] at hi
    | succ k ih =>
      have hK : k < C.size := by omega
      have old := ih (by omega)
      rw [snoc]
      by_cases mark : k ∈ keys
      · simpa [mark] using old
      rw [ite_eq_right mark]
      apply appendGood _ _ old
      let j : Fin C.size := ⟨k,hK⟩
      obtain ⟨a,b,ab,_,kind⟩ := binary j
      have member (w : ℕ) (hw : w ∈ [a,b]) : Av (P k) (word w) := by
        have read : w ∈ (gt j).inputs := ab ▸ hw
        apply available k w ((wiring j).1 w read)
        intro s eq
        have same : j = key s := ((hkey s).1 j).mp (eq ▸ read)
        apply mark
        change j.val ∈ keys
        rw [same]
        exact keyMem s
      refine ⟨word a,word b,member a (by simp),member b (by simp),?_⟩
      have andVal (t u : Bool) : GateOp.and.eval [t,u] = (t && u) := by cases t <;> cases u <;> rfl
      have orVal (t u : Bool) : GateOp.or.eval [t,u] = (t || u) := by cases t <;> cases u <;> rfl
      rcases kind with h | h
      · left
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        rw [BitVec.getLsbD_and,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,equation j,h,ab]
        simp [andVal]
      · right
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        rw [BitVec.getLsbD_or,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,equation j,h,ab]
        simp [orVal]
  have finalWord : word C.output = 4095 := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [bit _ ⟨r,hr⟩,out,tests ⟨r,hr⟩]
  have outputAv : Av (P C.size) 4095 := by
    rw [← finalWord]
    apply available _ _ validOut.2
    intro s _
    have h := (sel s).isLt
    omega
  -- Each row lists the preimages of the twenty-four tests under one rotation of the six-cycle.
  let shifts : List (List (Fin 24)) := [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
    [5,0,1,7,9,11,4,6,2,10,3,8,20,22,13,21,23,14,16,19,12,17,15,18],
    [11,5,0,6,10,8,9,4,1,3,7,2,12,15,22,17,18,13,23,19,20,14,21,16],
    [8,11,5,4,3,2,10,9,0,7,6,1,20,21,15,14,16,22,18,19,12,13,17,23],
    [2,8,11,9,7,1,3,10,5,6,4,0,12,17,21,13,23,15,16,19,20,22,14,18],
    [1,2,8,10,6,0,7,3,11,4,9,5,20,14,17,22,18,21,23,19,12,15,13,16]]
  let perm (t : Fin 6) (r : Fin 24) := ((shifts.getD t.val []).getD r.val 0)
  let T (t : Fin 6) (w : BitVec 24) : BitVec 24 :=
    (BitVec.ofBoolListLE (List.ofFn fun r : Fin 24 => w.getLsbD (perm t r).val)).cast (by simp)
  have tbit (t : Fin 6) (w : BitVec 24) (r : Fin 24) :
      (T t w).getLsbD r.val = w.getLsbD (perm t r).val := by
    simp only [T,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have tAnd (t : Fin 6) (a b : BitVec 24) : T t (a &&& b) = T t a &&& T t b := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [tbit _ _ ⟨r,hr⟩,BitVec.getLsbD_and,BitVec.getLsbD_and,tbit _ _ ⟨r,hr⟩,tbit _ _ ⟨r,hr⟩]
  have tOr (t : Fin 6) (a b : BitVec 24) : T t (a ||| b) = T t a ||| T t b := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    rw [tbit _ _ ⟨r,hr⟩,BitVec.getLsbD_or,BitVec.getLsbD_or,tbit _ _ ⟨r,hr⟩,tbit _ _ ⟨r,hr⟩]
  have constants : ∀ t : Fin 6, T t 4095 = 4095 ∧ T t 16773120 = 16773120 := by decide
  have lowRotate : ∀ (t : Fin 6) (s : Fin 3), T t (M.getD s.val 0) =
      M.getD (s + (Fin.ofNat 3 t.val)).val 0 := by decide
  have highRotate : ∀ (t i : Fin 6), T t (H.getD i.val 0) ∈ H := by decide
  have orbitOr : ∀ (i j : Fin 6), i ≠ j → ∃ t : Fin 6,
      T t (H.getD i.val 0 ||| H.getD j.val 0) ∈ ([14053491,7684279,5689661] : List (BitVec 24)) := by decide
  have orbitAnd : ∀ (i j : Fin 6), (H.getD i.val 0 &&& H.getD j.val 0 &&& 4095) ≠ 0 → i ≠ j →
      ∃ t : Fin 6, T t (H.getD i.val 0 &&& H.getD j.val 0) = 1 := by decide
  let Cut (seed : BitVec 24) : Prop :=
    (∀ U : Fin 3 → BitVec 24,
        (∀ s : Fin 3, U s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
          U s ||| M.getD s.val 0 = U s) →
        let ok (l : List (BitVec 24)) (w : BitVec 24) := w ∈ H ++ l ∨
          ∃ s : Fin 3, w = U s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
        ∀ ys : List (BitVec 24), ys.length ≤ 11 →
          (∀ s : Fin 3, ∃ y ∈ seed :: ys, U s = M.getD s.val 0 ||| y) →
          (∀ (i : ℕ) (hi : i < ys.length), ∃ p q : BitVec 24,
            ok (seed :: ys.take i) p ∧ ok (seed :: ys.take i) q ∧
              (ys[i] = p &&& q ∨ ys[i] = p ||| q)) → ¬ ok (seed :: ys) 4095)
  have starts (k : ℕ) (pos : 0 < k) : ∃ ys, P k = word 9 :: ys := by
    induction k with
    | zero => omega
    | succ k ih =>
      rw [snoc]
      by_cases z : k = 0
      · subst k
        exact ⟨[],by simp [firstFree,P]⟩
      · obtain ⟨ys,hy⟩ := ih (by omega)
        by_cases member : k ∈ keys
        · exact ⟨ys,by simpa [member] using hy⟩
        · exact ⟨ys ++ [word (9+k)],by simp [member,hy]⟩
  obtain ⟨ys,hys⟩ := starts C.size sizePos
  have restLen : ys.length ≤ 11 := by rw [hys,List.length_cons] at lengthBound; omega
  have companion (s : Fin 3) : ∃ y ∈ word 9 :: ys, U s = M.getD s.val 0 ||| y := by
    obtain ⟨j,eq,_,free⟩ := sideInternal s
    have unmarked : j.val ∉ keys := by
      intro h
      obtain ⟨t,_,et⟩ := Finset.mem_image.mp h
      exact free t (Fin.ext et.symm)
    refine ⟨word (9+j.val),?_,?_⟩
    · rw [← hys]
      exact inP _ _ j.isLt unmarked
    · rw [join s,eq]
  have close (t : Fin 6) (seed : BitVec 24) (first : T t (word 9) = seed) (ban : Cut seed) : False := by
    let d : Fin 3 := (Fin.ofNat 3 t.val)
    let U' (s : Fin 3) := T t (U (s-d))
    let Av' (l : List (BitVec 24)) (w : BitVec 24) : Prop :=
      w ∈ H ++ l ∨ ∃ s : Fin 3, w = U' s ∧ ∃ y ∈ l, w = M.getD s.val 0 ||| y
    have special (s : Fin 3) : U' (s+d) = T t (U s) := by simp [U']
    have liftAv (l : List (BitVec 24)) (w : BitVec 24) (hw : Av l w) : Av' (l.map (T t)) (T t w) := by
      rcases hw with mem | ⟨s,hu,y,hy,he⟩
      · left
        rcases List.mem_append.mp mem with h | h
        · obtain ⟨i,eq⟩ := List.get_of_mem h
          have i' : i.val < 6 := by simpa [H] using i.isLt
          apply List.mem_append_left
          have hi := highRotate t ⟨i.val,i'⟩
          have idw : H.getD i.val 0 = w := (List.getD_eq_getElem _ _ i.isLt).trans eq
          rw [← idw]
          exact hi
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨w,h,rfl⟩)
      · right
        refine ⟨s+d,by rw [special,hu],T t y,List.mem_map.mpr ⟨y,hy,rfl⟩,?_⟩
        rw [he,tOr,lowRotate]
    have upMask (s : Fin 3) : U' s &&& 16773120 = M.getD s.val 0 &&& 16773120 ∧
        U' s ||| M.getD s.val 0 = U' s := by
      let z := s-d
      have back : z+d = s := sub_add_cancel _ _
      have trans := congrArg (T t) (nmask z)
      rw [tAnd,tAnd,(constants t).2,lowRotate] at trans
      change (T t (U z) &&& 16773120) = _ ∧ (T t (U z) ||| M.getD s.val 0) = T t (U z)
      constructor
      · simpa only [show z+(Fin.ofNat 3 t.val) = s from back] using trans
      · rw [join z,tOr,lowRotate,show z+(Fin.ofNat 3 t.val) = s from back]
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        simp only [BitVec.getLsbD_or]
        cases (M.getD s.val 0).getLsbD r <;> simp
    apply ban U' upMask (ys.map (T t)) (by simpa using restLen)
    · intro s
      obtain ⟨y,hy,eq⟩ := companion (s-d)
      refine ⟨T t y,?_,?_⟩
      · have h : T t y ∈ (word 9 :: ys).map (T t) := List.mem_map.mpr ⟨y,hy,rfl⟩
        simpa only [List.map_cons,first] using h
      · change T t (U (s-d)) = _
        rw [eq,tOr,lowRotate,show (s-d)+(Fin.ofNat 3 t.val) = s from sub_add_cancel _ _]
    · intro i hi
      have bound : i < ys.length := by simpa using hi
      have hg := good C.size le_rfl
      rw [hys] at hg
      obtain ⟨p,q,hp,hq,eq⟩ := hg (i+1) (by simp; omega)
      simp only [List.take_succ_cons,List.getElem_cons_succ] at hp hq eq
      refine ⟨T t p,T t q,?_,?_,?_⟩
      · have h := liftAv _ _ hp
        simpa only [List.map_cons,first,List.map_take] using h
      · have h := liftAv _ _ hq
        simpa only [List.map_cons,first,List.map_take] using h
      · rw [List.getElem_map]
        exact eq.elim (fun e => Or.inl ((congrArg (T t) e).trans (tAnd _ _ _)))
          (fun e => Or.inr ((congrArg (T t) e).trans (tOr _ _ _)))
    · rw [hys] at outputAv
      have h := liftAv _ _ outputAv
      simpa only [List.map_cons,first,(constants t).1] using h
  have firstGateEdgeWitness (C : Circuit) (E : List (Fin 9 × Fin 9))
      (minimal : IsMinimalCircuit 9 C)
      (computes : circuitFun 9 C = fun x => E.any fun e => x e.1 && x e.2)
      (mon : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
      (g : Gate) (gs : List Gate) (shape : C.gates = g :: gs) :
      ∃ e ∈ E, g.op.eval (g.inputs.map (fun i =>
        (List.ofFn (fun v : Fin 9 => decide (v = e.1 ∨ v = e.2))).getD i false)) = true := by
    classical
    by_contra! absent
    let last := 9 + gs.length
    let rename (i : ℕ) := if i < 9 then i else if i = 9 then last else i - 1
    let renGate (h : Gate) : Gate := ⟨h.op, h.inputs.map rename⟩
    let D : Circuit := ⟨gs.map renGate, rename C.output⟩
    have fanD : FanInTwo D := by
      intro h hh
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hh
      have orig := minimal.1 q (by rw [shape]; simp [hq])
      exact ⟨orig.1,by simpa [renGate] using orig.2⟩
    let step (w : List Bool) (q : Gate) := w ++ [q.op.eval (q.inputs.map (fun i => w.getD i false))]
    have readSnoc (ws : List Bool) (b : Bool) (i : ℕ) :
        (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
      induction ws generalizing i with
      | nil => cases i <;> rfl
      | cons h ws ih =>
        cases i with
        | zero => rfl
        | succ i => simpa using ih i
    have opMono (q : Gate) (hq : q ∈ gs) (A B : ℕ → Bool)
        (le : ∀ i, A i = true → B i = true) :
        q.op.eval (q.inputs.map A) = true → q.op.eval (q.inputs.map B) = true := by
      rcases mon q (by rw [shape]; simp [hq]) with kind | kind
      · rw [kind]
        change (q.inputs.map A).all id = true → (q.inputs.map B).all id = true
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        intro h i hi
        exact le _ (h i hi)
      · rw [kind]
        change (q.inputs.map A).any id = true → (q.inputs.map B).any id = true
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,h⟩
        exact ⟨i,hi,le _ h⟩
    -- Relate the original run and the run after the first gate is fixed to false.
    -- In the smaller circuit the missing value is read at its first nonexistent wire.
    have simulate (R : Bool → Bool → Prop) (x y : Fin 9 → Bool)
        (zero : R false false) (initial : ∀ v, R (x v) (y v))
        (bottom : R false (g.op.eval (g.inputs.map (fun i => (List.ofFn y).getD i false))))
        (move : ∀ q ∈ gs, ∀ A B : ℕ → Bool, (∀ i, R (A i) (B i)) →
          R (q.op.eval (q.inputs.map A)) (q.op.eval (q.inputs.map B))) :
        R (D.eval (List.ofFn x)) (C.eval (List.ofFn y)) := by
      have go (rem : List Gate) (sub : ∀ q ∈ rem, q ∈ gs) (w v : List Bool)
          (range : w.length + rem.length = last) (lo : 9 ≤ w.length)
          (lengths : v.length = w.length + 1)
          (rel : ∀ i, R (w.getD (rename i) false) (v.getD i false)) :
          ∀ i, R (((rem.map renGate).foldl step w).getD (rename i) false)
            ((rem.foldl step v).getD i false) := by
        induction rem generalizing w v with
        | nil => exact rel
        | cons q rem ih =>
          simp only [List.length_cons] at range
          have nextRel := move q (sub q (by simp)) (fun i => w.getD (rename i) false)
            (fun i => v.getD i false) rel
          simp only [List.map_cons,List.foldl_cons]
          apply ih (fun h mem => sub h (by simp [mem])) (step w (renGate q)) (step v q)
          · simp [step]; omega
          · simp [step]; omega
          · simp [step]; omega
          · intro i
            change R ((_ ++ [_]).getD (rename i) false) ((_ ++ [_]).getD i false)
            rw [readSnoc,readSnoc]
            by_cases eq : i = v.length
            · have eq' : rename i = w.length := by dsimp [rename]; split_ifs <;> omega
              rw [ite_eq_left eq', ite_eq_left eq]
              simpa only [renGate,List.map_map,Function.comp_def] using nextRel
            · have ne' : rename i ≠ w.length := by dsimp [rename]; split_ifs <;> omega
              simpa only [ite_eq_right ne',ite_eq_right eq] using rel i
      let byVal := g.op.eval (g.inputs.map (fun i => (List.ofFn y).getD i false))
      have init : ∀ i, R ((List.ofFn x).getD (rename i) false)
          (((List.ofFn y) ++ [byVal]).getD i false) := by
        intro i
        rw [readSnoc,List.length_ofFn]
        by_cases lt : i < 9
        · have h : i ≠ 9 := by omega
          have rd (z : Fin 9 → Bool) : (List.ofFn z).getD i false = z ⟨i,lt⟩ := by
            rw [List.getD_eq_getElem _ _ (by simpa using lt : i < (List.ofFn z).length),List.getElem_ofFn]
          simpa only [rename,ite_eq_left lt,ite_eq_right h,rd] using initial ⟨i,lt⟩
        · have got (z : Fin 9 → Bool) (k : ℕ) (hk : 9 ≤ k) : (List.ofFn z).getD k false = false := by
            simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using hk : (List.ofFn z).length ≤ k),Option.getD_none]
          by_cases eq : i = 9
          · simpa only [rename,ite_eq_right lt,ite_eq_left eq,got x last (by dsimp [last]; omega),byVal] using bottom
          · have r : 9 ≤ i-1 := by omega
            simpa only [rename,ite_eq_right lt,ite_eq_right eq,got x (i-1) r,got y i (by omega)] using zero
      have result := go gs (fun _ h => h) (List.ofFn x) ((List.ofFn y) ++ [byVal])
        (by simp [last]) (by simp) (by simp) init C.output
      change R (((gs.map renGate).foldl step (List.ofFn x)).getD (rename C.output) false)
        ((C.gates.foldl step (List.ofFn y)).getD C.output false)
      rw [shape,List.foldl_cons]
      exact result
    have same : circuitFun 9 D = circuitFun 9 C := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact simulate (fun d c => d = true → c = true) x x (fun h => h)
          (fun _ h => h) (by simp) (fun q h A B le => opMono q h A B le)
      · intro one
        have tog : (E.any fun e => x e.1 && x e.2) = true := (congrFun computes x).symm.trans one
        obtain ⟨e,he,h1,h2⟩ := (show ∃ e ∈ E, x e.1 = true ∧ x e.2 = true by simpa using tog)
        let y (v : Fin 9) := decide (v = e.1 ∨ v = e.2)
        have yin : circuitFun 9 C y = true := by
          rw [computes]
          apply List.any_eq_true.mpr
          exact ⟨e,he,by simp [y]⟩
        have diff : ∀ v, y v = true → x v = true := by
          intro v h
          rcases of_decide_eq_true h with rfl | rfl <;> assumption
        exact simulate (fun d c => c = true → d = true) x y (fun h => h) diff
          (fun hi => (absent e he hi).elim)
          (fun q h A B le => opMono q h B A le) yin
    have small := minimal.2 D fanD same
    change C.gates.length ≤ (gs.map renGate).length at small
    simp [shape] at small

  have bottomAndIsEdge (C : Circuit) (E : List (Fin 9 × Fin 9))
      (minimal : IsMinimalCircuit 9 C)
      (computes : circuitFun 9 C = fun x => E.any fun e => x e.1 && x e.2)
      (mon : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
      (a b : Fin 9) (ne : a ≠ b) (gs : List Gate)
      (shape : C.gates = ⟨.and, [a.val,b.val]⟩ :: gs) : (a,b) ∈ E ∨ (b,a) ∈ E := by
    obtain ⟨e,he,h⟩ := firstGateEdgeWitness C E minimal computes mon _ gs shape
    have read (u : Fin 9) :
        (List.ofFn (fun v : Fin 9 => decide (v = e.1 ∨ v = e.2))).getD u.val false =
        decide (u = e.1 ∨ u = e.2) := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have both : (a = e.1 ∨ a = e.2) ∧ (b = e.1 ∨ b = e.2) := by
      have pair (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
      change GateOp.and.eval [_,_] = true at h
      rw [pair,Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true ((read a).symm.trans h.1),of_decide_eq_true ((read b).symm.trans h.2)⟩
    rcases e with ⟨u,v⟩
    obtain ⟨au | av, bu | bv⟩ := both
    · exact (ne (au.trans bu.symm)).elim
    · exact Or.inl (by simpa only [au,bv] using he)
    · exact Or.inr (by simpa only [av,bu] using he)
    · exact (ne (av.trans bv.symm)).elim
  let j0 : Fin C.size := ⟨0,sizePos⟩
  obtain ⟨a,b,ab,diff,kind⟩ := binary j0
  have direct (w : ℕ) (hw : w ∈ [a,b]) : w < 9 ∧ ∀ s : Fin 3, w ≠ (sel s).val := by
    have reads : w ∈ (gt j0).inputs := ab ▸ hw
    refine ⟨by simpa [j0] using (wiring j0).1 w reads,?_⟩
    intro s eq
    have firstKey : j0 = key s := ((hkey s).1 j0).mp (eq ▸ reads)
    apply firstFree
    change j0.val ∈ keys
    rw [firstKey]
    exact keyMem s
  let x : Fin 9 := ⟨a,(direct a (by simp)).1⟩
  let y : Fin 9 := ⟨b,(direct b (by simp)).1⟩
  have highIndex : ∀ v : Fin 9, (∀ s : Fin 3, v.val ≠ (sel s).val) →
      ∃ i : Fin 6, A.getD v.val 0 = H.getD i.val 0 := by decide
  obtain ⟨i,pi⟩ := highIndex x (direct a (by simp)).2
  obtain ⟨j,pj⟩ := highIndex y (direct b (by simp)).2
  have cols : ∀ u v : Fin 9, A.getD u.val 0 = A.getD v.val 0 → u = v := by decide
  have dij : i ≠ j := by
    intro eq
    have xy := cols x y (pi.trans (eq ▸ pj.symm))
    exact diff (congrArg Fin.val xy)
  have ra : word a = H.getD i.val 0 := (raw x).trans pi
  have rb : word b = H.getD j.val 0 := (raw y).trans pj
  have mono : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    obtain ⟨j,hj⟩ := List.get_of_mem hg
    obtain ⟨_,_,_,_,h⟩ := binary j
    change (C.gates.get j).op = .and ∨ (C.gates.get j).op = .or at h
    rwa [hj] at h
  have firstEq (z : Fin 9 → Bool) : V z 9 = (gt j0).op.eval ((gt j0).inputs.map (V z)) := equation j0 z
  rcases kind with isAnd | isOr
  · have abWord : word 9 = H.getD i.val 0 &&& H.getD j.val 0 := by
      rw [← ra,← rb]
      apply BitVec.eq_of_getLsbD_eq
      intro r hr
      rw [bit _ ⟨r,hr⟩,BitVec.getLsbD_and,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,firstEq,isAnd,ab]
      simp only [List.map_cons,List.map_nil]
      cases V (X ⟨r,hr⟩) a <;> cases V (X ⟨r,hr⟩) b <;> rfl
    obtain ⟨gs,shape⟩ : ∃ gs, C.gates = gt j0 :: gs := by
      cases h : C.gates with
      | nil => have len : C.size = 0 := by change C.gates.length = 0; simp only [h,List.length_nil]
               omega
      | cons g gs =>
        have headEq : gt j0 = g := by
          change C.gates[0] = g
          simp [h]
        exact ⟨gs,by rw [headEq]⟩
    have gEq : gt j0 = ⟨.and,[x.val,y.val]⟩ := by
      cases hg : gt j0 with
      | mk op ins =>
        rw [hg] at isAnd ab
        simp only at isAnd ab
        subst op
        subst ins
        rfl
    have isEdge := bottomAndIsEdge C E minimal computes mono x y (fun e => diff (congrArg Fin.val e)) gs
      (shape.trans (congrArg (fun g => g :: gs) gEq))
    have edgeVal : ∀ u v : Fin 9, (u,v) ∈ E ∨ (v,u) ∈ E →
        (A.getD u.val 0 &&& A.getD v.val 0 &&& 4095) ≠ 0 := by decide
    have lit := edgeVal x y isEdge
    rw [pi,pj] at lit
    obtain ⟨t,canon⟩ := orbitAnd i j lit dij
    exact close t 1 ((congrArg (T t) abWord).trans canon) edgeAnd
  · have abWord : word 9 = H.getD i.val 0 ||| H.getD j.val 0 := by
      rw [← ra,← rb]
      apply BitVec.eq_of_getLsbD_eq
      intro r hr
      rw [bit _ ⟨r,hr⟩,BitVec.getLsbD_or,bit _ ⟨r,hr⟩,bit _ ⟨r,hr⟩,firstEq,isOr,ab]
      simp only [List.map_cons,List.map_nil]
      cases V (X ⟨r,hr⟩) a <;> cases V (X ⟨r,hr⟩) b <;> rfl
    obtain ⟨t,canon⟩ := orbitOr i j dij
    rw [← abWord] at canon
    simp only [List.mem_cons,List.not_mem_nil,or_false] at canon
    rcases canon with h | h | h
    · exact close t _ h nearOr
    · exact close t _ h nextOr
    · exact close t _ h oppositeOr
