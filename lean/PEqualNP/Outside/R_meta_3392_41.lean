import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A raw conjunction can be supplied before the two designated gates. Its later
-- occurrence is then free to remove, even in a list containing forward reads.
theorem PEqualNP.Outside.R_meta_3392_41
    (canonical : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)),
      ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x p.1 && x p.2)) →
      circuitFun 9 D = (fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 16 ≤ D.size)
    (remaining : ∀ k ∈ ([1,2,3,4,6] : List (Fin 9)), ∀ C : Circuit, FanInTwo C →
      C.size ≤ 13 → (∀ a b : Fin 9, a ≠ b → (⟨.and, [a.val,b.val]⟩ : Gate) ∉ C.gates) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x k]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  have simulate (f : ℕ → ℕ) (u v : List Bool)
      (reads : ∀ z i, (u ++ z).getD i false = (v ++ z).getD (f i) false)
      (gs : List Gate) (z : List Bool) :
      ∃ t : List Bool, gs.foldl step (u ++ z) = u ++ t ∧
        (gs.map (ren f)).foldl step (v ++ z) = v ++ t ∧ t.length = z.length + gs.length := by
    induction gs generalizing z with
    | nil => exact ⟨z,rfl,rfl,by simp⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map (fun i => (u ++ z).getD i false))
      have eqbit : g.op.eval (g.inputs.map (fun i => (u ++ z).getD i false)) =
          (ren f g).op.eval ((ren f g).inputs.map (fun i => (v ++ z).getD i false)) := by
        congr 1
        simp only [ren, List.map_map]
        apply List.map_congr_left
        intro i _
        exact reads z i
      obtain ⟨t,hs,ht,hl⟩ := ih (z ++ [bit])
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa only [List.foldl_cons, step, List.append_assoc, bit] using hs
      · change (gs.map (ren f)).foldl step ((v ++ z) ++ [_]) = _
        rw [← eqbit, List.append_assoc]
        exact ht
      · simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega
  let edge (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have firstAnd (a b : Fin 9) (hab : a ≠ b) (T : Circuit) (hf : FanInTwo T) (hz : T.size ≤ 14) :
      ∃ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [x a && x b]) ≠ edge x := by
    let keys : List (Fin 9 × Fin 9) := [(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]
    let perms : Fin 12 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
      ![0,5,8,3,4,1,7,6,2],
      ![1,0,5,8,6,2,4,7,3],
      ![1,2,3,8,6,0,7,4,5],
      ![2,1,0,5,7,3,6,4,8],
      ![2,3,8,5,7,1,4,6,0],
      ![3,2,1,0,4,8,7,6,5],
      ![3,8,5,0,4,2,6,7,1],
      ![5,0,1,2,7,8,4,6,3],
      ![5,8,3,2,7,0,6,4,1],
      ![8,3,2,1,6,5,4,7,0],
      ![8,5,0,1,6,3,7,4,2]]
    have covers : ∀ u v : Fin 9, u ≠ v → ∃ j : Fin 12,
        (perms j u,perms j v) ∈ keys ∨ (perms j v,perms j u) ∈ keys := by decide +kernel
    have invariant (j : Fin 12) (y : Fin 9 → Bool) : edge (fun i => y (perms j i)) = edge y := by
      fin_cases j
      · change (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 0 && y 5 || y 5 && y 8 || y 8 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 1 || y 5 && y 7 || y 8 && y 6 || y 3 && y 2 || y 1 && y 6 || y 7 && y 2 || y 2 && y 1) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 1 && y 0 || y 0 && y 5 || y 5 && y 8 || y 8 && y 6 || y 6 && y 1 || y 1 && y 2 || y 0 && y 4 || y 5 && y 7 || y 8 && y 3 || y 2 && y 7 || y 4 && y 3 || y 3 && y 2) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 1 && y 2 || y 2 && y 3 || y 3 && y 8 || y 8 && y 6 || y 6 && y 1 || y 1 && y 0 || y 2 && y 7 || y 3 && y 4 || y 8 && y 5 || y 0 && y 4 || y 7 && y 5 || y 5 && y 0) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 2 && y 1 || y 1 && y 0 || y 0 && y 5 || y 5 && y 7 || y 7 && y 2 || y 2 && y 3 || y 1 && y 6 || y 0 && y 4 || y 5 && y 8 || y 3 && y 4 || y 6 && y 8 || y 8 && y 3) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 2 && y 3 || y 3 && y 8 || y 8 && y 5 || y 5 && y 7 || y 7 && y 2 || y 2 && y 1 || y 3 && y 4 || y 8 && y 6 || y 5 && y 0 || y 1 && y 6 || y 4 && y 0 || y 0 && y 1) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 3 && y 2 || y 2 && y 1 || y 1 && y 0 || y 0 && y 4 || y 4 && y 3 || y 3 && y 8 || y 2 && y 7 || y 1 && y 6 || y 0 && y 5 || y 8 && y 6 || y 7 && y 5 || y 5 && y 8) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 3 && y 8 || y 8 && y 5 || y 5 && y 0 || y 0 && y 4 || y 4 && y 3 || y 3 && y 2 || y 8 && y 6 || y 5 && y 7 || y 0 && y 1 || y 2 && y 7 || y 6 && y 1 || y 1 && y 2) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 5 && y 0 || y 0 && y 1 || y 1 && y 2 || y 2 && y 7 || y 7 && y 5 || y 5 && y 8 || y 0 && y 4 || y 1 && y 6 || y 2 && y 3 || y 8 && y 6 || y 4 && y 3 || y 3 && y 8) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 5 && y 8 || y 8 && y 3 || y 3 && y 2 || y 2 && y 7 || y 7 && y 5 || y 5 && y 0 || y 8 && y 6 || y 3 && y 4 || y 2 && y 1 || y 0 && y 4 || y 6 && y 1 || y 1 && y 0) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 8 && y 3 || y 3 && y 2 || y 2 && y 1 || y 1 && y 6 || y 6 && y 8 || y 8 && y 5 || y 3 && y 4 || y 2 && y 7 || y 1 && y 0 || y 5 && y 7 || y 4 && y 0 || y 0 && y 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
      · change (y 8 && y 5 || y 5 && y 0 || y 0 && y 1 || y 1 && y 6 || y 6 && y 8 || y 8 && y 3 || y 5 && y 7 || y 0 && y 4 || y 1 && y 2 || y 3 && y 4 || y 7 && y 2 || y 2 && y 3) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
        ac_rfl
    obtain ⟨j,hj⟩ := covers a b hab
    let u := perms j a
    let v := perms j b
    let p := if (u,v) ∈ keys then (u,v) else (v,u)
    have hp : p ∈ keys := by
      change (u,v) ∈ keys ∨ (v,u) ∈ keys at hj
      by_cases h : (u,v) ∈ keys
      · simpa only [p,ite_eq_left h] using h
      · simpa only [p,ite_eq_right h] using hj.resolve_left h
    have pval (y : Fin 9 → Bool) : (y (perms j a) && y (perms j b)) = (y p.1 && y p.2) := by
      change (y u && y v) = _
      dsimp only [p]; split
      · rfl
      · exact Bool.and_comm ..
    let f (i : ℕ) := if h : i < 9 then (perms j ⟨i,h⟩).val else i
    let H : Circuit := ⟨⟨.and,[p.1.val,p.2.val]⟩ :: T.gates.map (ren f), f T.output⟩
    have hfH : FanInTwo H := by
      intro g hg
      change g ∈ _ :: _ at hg
      simp only [List.mem_cons,List.mem_map] at hg
      rcases hg with rfl | ⟨s,hs,rfl⟩
      · exact ⟨by simp, Nat.le_refl 2⟩
      · exact ⟨(hf s hs).1,by simpa [ren] using (hf s hs).2⟩
    by_contra bad
    push Not at bad
    have simy (y : Fin 9 → Bool) : ∃ t : List Bool,
        H.wires (List.ofFn y) = (List.ofFn y ++ [y p.1 && y p.2]) ++ t ∧
        H.eval (List.ofFn y) = edge y := by
      let x (i : Fin 9) := y (perms j i)
      let U := List.ofFn x ++ [x a && x b]
      let V := List.ofFn y ++ [y p.1 && y p.2]
      have rd (z : List Bool) (i : ℕ) : (U ++ z).getD i false = (V ++ z).getD (f i) false := by
        simp only [U,V,List.append_assoc,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn]
        by_cases hi : i < 9
        · simp only [f,dite_eq_left hi,ite_eq_left hi,ite_eq_left (perms j ⟨i,hi⟩).isLt,List.getElem?_ofFn]
          rw [dite_eq_left (perms j ⟨i,hi⟩).isLt]
        · simp only [f,dite_eq_right hi,ite_eq_right hi,x,pval]
      have readY (i : Fin 9) : (List.ofFn y).getD i.val false = y i := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt]; rfl
      have hs : step (List.ofFn y) ⟨.and,[p.1.val,p.2.val]⟩ = V := by
        change _ ++ [((List.ofFn y).getD p.1.val false && ((List.ofFn y).getD p.2.val false && true))] = _
        rw [readY,readY,Bool.and_true]
      obtain ⟨t,hsT,hsH,_⟩ := simulate f U V rd T.gates []
      simp only [List.append_nil] at hsT hsH
      have hw : H.wires (List.ofFn y) = V ++ t := by
        change (T.gates.map (ren f)).foldl step (step (List.ofFn y) _) = _
        rw [hs,hsH]
      refine ⟨t,hw,?_⟩
      have he := bad x
      change (T.gates.foldl step U).getD T.output false = edge x at he
      change (H.wires (List.ofFn y)).getD (f T.output) false = edge y
      rw [hw,← rd t T.output,← hsT,he]
      exact invariant j y
    have wire (y : Fin 9 → Bool) : (H.wires (List.ofFn y)).getD 9 false = (y p.1 && y p.2) := by
      obtain ⟨t,ht,_⟩ := simy y
      rw [ht, List.append_assoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
      simp
    have computes : circuitFun 9 H = edge := by
      funext y
      obtain ⟨_,_,h⟩ := simy y
      exact h
    have lb := canonical p hp H hfH wire computes
    change 16 ≤ (_ :: _).length at lb
    simp only [List.length_cons,List.length_map] at lb
    change T.gates.length ≤ 14 at hz
    omega

  intro k hk C hfan hsize
  by_cases clean : ∀ a b : Fin 9, a ≠ b → (⟨.and, [a.val,b.val]⟩ : Gate) ∉ C.gates
  · exact remaining k hk C hfan hsize clean
  push Not at clean
  obtain ⟨a,b,hab,occurs⟩ := clean
  obtain ⟨P,Q,splitGates⟩ := List.append_of_mem occurs
  let mark := 11 + P.length
  let early (i : ℕ) := if i < 9 then i else i+1
  let late (i : ℕ) := if i < mark then early i else if i = mark then 9 else i
  let D : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.or,[4,k.val]⟩ :: (P.map (ren early) ++ Q.map (ren late)), late C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ _ :: _ :: (_ ++ _) at hg
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hg
    rcases hg with rfl | rfl | ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact ⟨by simp, by decide⟩
    · exact ⟨by simp, Nat.le_refl 2⟩
    · have H := hfan s (by rw [splitGates]; simp [hs])
      exact ⟨H.1, by simpa [ren] using H.2⟩
    · have H := hfan s (by rw [splitGates]; simp [hs])
      exact ⟨H.1, by simpa [ren] using H.2⟩
  have sizeD : D.size ≤ 14 := by
    change C.gates.length ≤ 13 at hsize
    rw [splitGates] at hsize
    simp only [List.length_append, List.length_cons] at hsize
    change (_ :: _ :: (_ ++ _)).length ≤ 14
    simp only [List.length_cons, List.length_append, List.length_map]
    omega
  obtain ⟨x,hx⟩ := firstAnd a b hab D fanD sizeD
  refine ⟨x, ?_⟩
  suffices eq : C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x k]) = D.eval (List.ofFn x ++ [x a && x b]) from
    fun h => hx (eq.symm.trans h)
  let raw := List.ofFn x
  let val := x a && x b
  let pair := [!x 0, x 4 || x k]
  have rawLen : raw.length = 9 := List.length_ofFn
  have lookup (i : Fin 9) (s : List Bool) : (raw ++ s).getD i.val false = x i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rawLen]; exact i.isLt)]
    change (((List.ofFn x)[i.val]?).getD false) = x i
    rw [List.getElem?_ofFn, dite_eq_left i.isLt]
    rfl
  have insertRead (s : List Bool) (i : ℕ) :
      (raw ++ s).getD i false = (raw ++ val :: s).getD (early i) false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, rawLen]
    by_cases hi : i < 9
    · simp [early, hi]
    · have h₁ : ¬ i + 1 < 9 := by omega
      have h₂ : i+1-9 = (i-9)+1 := by omega
      simp [early, hi, h₁, h₂]
  have rotateRead (s z : List Bool) (hlen : 9 + s.length = mark) (i : ℕ) :
      (raw ++ (s ++ val :: z)).getD i false =
        (raw ++ val :: (s ++ z)).getD (late i) false := by
    have hm : 9 ≤ mark := by omega
    by_cases hr : i < 9
    · have ht : i < mark := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, rawLen, late, early, ht, hr]
    by_cases ht : i < mark
    · have h₁ : ¬ i+1 < 9 := by omega
      have h₂ : i+1-9 = (i-9)+1 := by omega
      have h₃ : i-9 < s.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, rawLen, late, early, ht, hr, h₁, h₂, h₃]
    by_cases he : i = mark
    · subst i
      have h₁ : mark-9 = s.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, rawLen, late, hr, h₁]
    · have h₁ : i-9 = (i-10)+1 := by omega
      have h₂ : ¬ i-10 < s.length := by omega
      have h₃ : ¬ i-9 < s.length := by omega
      have h₄ : (i-10+1)-s.length = (i-10-s.length)+1 := by omega
      have h₅ : ¬ i-10+1 < s.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, rawLen, late, ht, he, hr, h₁, h₂, h₅, h₄]
  let U := raw ++ pair
  let V := raw ++ val :: pair
  have reads₁ : ∀ z i, (U ++ z).getD i false = (V ++ z).getD (early i) false := by
    intro z i
    simpa only [U,V,List.append_assoc,List.cons_append] using insertRead (pair ++ z) i
  obtain ⟨s,pold,pnew,slen⟩ := simulate early U V reads₁ P []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at pold pnew slen
  have picked : step (U ++ s) ⟨.and,[a.val,b.val]⟩ = (U ++ s) ++ [val] := by
    have l (i : Fin 9) : (U ++ s).getD i.val false = x i := by
      simpa only [U,List.append_assoc] using lookup i (pair ++ s)
    change _ ++ [( (U ++ s).getD a.val false && ((U ++ s).getD b.val false && true))] = _
    rw [l a,l b,Bool.and_true]
  have nlen : 9 + (pair ++ s).length = mark := by simp [pair,mark,slen]; omega
  have reads₂ : ∀ z i, (((U ++ s) ++ [val]) ++ z).getD i false =
      ((V ++ s) ++ z).getD (late i) false := by
    intro z i
    simpa only [U,V,List.append_assoc,List.cons_append,List.nil_append] using
      rotateRead (pair ++ s) z nlen i
  obtain ⟨t,qold,qnew,_⟩ := simulate late ((U ++ s) ++ [val]) (V ++ s) reads₂ Q []
  simp only [List.append_nil] at qold qnew
  have pref : step (step (raw ++ [val]) ⟨.not,[0]⟩) ⟨.or,[4,k.val]⟩ = V := by
    have p0 := lookup (0 : Fin 9) [val]
    have p4 := lookup (4 : Fin 9) [val,!x 0]
    have pk := lookup k [val,!x 0]
    change ((raw ++ [val]) ++ [!(raw ++ [val]).getD 0 false]) ++
      [(((raw ++ [val]) ++ [!(raw ++ [val]).getD 0 false]).getD 4 false ||
        (((raw ++ [val]) ++ [!(raw ++ [val]).getD 0 false]).getD k.val false || false))] = _
    change (raw ++ [val]).getD 0 false = _ at p0
    change (raw ++ [val,!x 0]).getD 4 false = _ at p4
    simp only [p0, List.append_assoc, List.cons_append, List.nil_append, p4, pk, Bool.or_false]
    rfl
  change (C.gates.foldl step ((raw ++ [!x 0]) ++ [x 4 || x k])).getD C.output false =
    (D.gates.foldl step (raw ++ [val])).getD (late C.output) false
  rw [List.append_assoc,splitGates,List.foldl_append]
  change (Q.foldl step (step (P.foldl step U) _)).getD C.output false =
    ((P.map (ren early) ++ Q.map (ren late)).foldl step (step (step (raw ++ [val]) _) _)).getD _ false
  rw [pold,picked,pref,List.foldl_append,pnew,qold,qnew]
  exact reads₂ t C.output
