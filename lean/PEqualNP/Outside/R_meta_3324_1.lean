import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- A pruned circuit with 26 binary gates has at most 27 primary input reads.
-- Every vertex is essential, so one is read once. Vertex transitivity lets us choose vertex 0.
-- At the three edge rows containing 0 and the 25 maximal independent rows omitting 0,
-- flipping input 0 changes the answer. Its sole reader must therefore copy input 0 there.
-- An AND reader can vary on only the other 12 negative rows, an OR reader on 18 edge rows.
-- Each other input misses one of the three edge rows and occurs in one of the 25 negative rows.
-- The partner is therefore a computed wire. Place the reader just after its partner.
-- A repeated boundary column can use its earlier wire, saving a gate while preserving all 58 rows.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3324_1
    (synthesis :
      let seed : List ℕ := [63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
      let grow := fun (w p : List ℕ) => ∀ i : Fin p.length,
        p.get i ∉ w ++ p.take i.val ∧ ∃ a ∈ w ++ p.take i.val, ∃ b ∈ w ++ p.take i.val,
          p.get i = a &&& b ∨ p.get i = a ||| b
      ∃ (p s : List ℕ) (q z : ℕ) (o : Bool), p.length + s.length ≤ 24 ∧ grow seed (p ++ [q]) ∧
        let v := 95229015649943559
        let t := if o then v ||| (z &&& 2097144) else 7 ||| (z &&& 95229015649943552)
        (if o then v ||| q else v &&& q) = t ∧ grow (seed ++ p ++ [q,t]) s ∧ 2097151 ∈ s)
    (boundary : ∀ C : Circuit, Monotone2 C →
      (∀ j : ℕ, C.eval (([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ).map (fun v => v.testBit j)) = (2097151 : ℕ).testBit j) →
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 14,
        (a.val,b.val) ∈ ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x a = true ∧ x b = true) :
have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ (2 : ℕ) ≤ x2.size ∧ x2.size ≤ (26 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Decidable.decide (∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ x1 ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true)
:= by
  let v : ℕ := 95229015649943559
  let seed : List ℕ := [63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  let grow := fun (w p : List ℕ) => ∀ i : Fin p.length,
    p.get i ∉ w ++ p.take i.val ∧ ∃ a ∈ w ++ p.take i.val, ∃ b ∈ w ++ p.take i.val,
      p.get i = a &&& b ∨ p.get i = a ||| b
  let bits := fun (w : List ℕ) (j : ℕ) => w.map (fun a => a.testBit j)
  let built := fun (w : List ℕ) => ∃ gs : List Gate,
    IsAO2 14 ⟨gs,0⟩ ∧ (∀ g ∈ gs, g.inputs.Nodup) ∧ 14 + gs.length = w.length ∧
    ∀ j, (Circuit.mk gs 0).wires (bits (v :: seed) j) = bits w j
  have addGate (w : List ℕ) (hw : built w) (a b : ℕ) (ha : a < w.length) (hb : b < w.length)
      (hab : a ≠ b) (o : Bool) :
      built (w ++ [if o then w[a] ||| w[b] else w[a] &&& w[b]]) := by
    obtain ⟨gs, ⟨ops, back, arity⟩, distinct, len, trace⟩ := hw
    let g : Gate := ⟨if o then .or else .and, [a,b]⟩
    have op : g.op = .and ∨ g.op = .or := by cases o <;> simp [g]
    have nd : g.inputs.Nodup := by simpa [g] using hab
    refine ⟨gs ++ [g], ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact ops h hh
      · exact List.mem_singleton.mp hh ▸ op
    · intro i hi j hj
      change i < (gs ++ [g]).length at hi
      change j ∈ ((gs ++ [g]).getD i _).inputs at hj
      rw [List.getD_eq_getElem _ _ hi] at hj
      by_cases old : i < gs.length
      · rw [List.getElem_append_left old] at hj
        apply back i old j
        change j ∈ (gs.getD i _).inputs
        rwa [List.getD_eq_getElem _ _ old]
      · have last : i = gs.length := by simp at hi; omega
        subst i
        simp [g] at hj
        rcases hj with rfl | rfl <;> omega
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact arity h hh
      · exact List.mem_singleton.mp hh ▸ (show g.inputs.length = 2 from rfl)
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact distinct h hh
      · exact List.mem_singleton.mp hh ▸ nd
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    · intro j
      change (gs ++ [g]).foldl _ _ = _
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (Circuit.mk gs 0).wires (bits (v :: seed) j) ++
        [g.op.eval (g.inputs.map (fun i => ((Circuit.mk gs 0).wires (bits (v :: seed) j)).getD i false))] = _
      rw [trace]
      have get (i : ℕ) (hi : i < w.length) : (bits w j).getD i false = w[i].testBit j := by
        rw [List.getD_eq_getElem (bits w j) false (by simpa [bits] using hi)]
        simp [bits]
      simp only [g, List.map_cons, List.map_nil, get a ha, get b hb]
      have andVal (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
      have orVal (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
      cases o <;> simp [bits, andVal, orVal, Nat.testBit_and, Nat.testBit_or]
  have realize (w p : List ℕ) (hw : built (v :: w)) (hp : grow w p) :
      built (v :: (w ++ p)) := by
    induction p generalizing w with
    | nil => simpa using hw
    | cons c cs ih =>
      obtain ⟨fresh, a, ha, b, hb, kind⟩ := hp ⟨0, Nat.zero_lt_succ _⟩
      simp at fresh ha hb
      have ne : a ≠ b := by
        rintro rfl
        have ca : c = a := by rcases kind with h | h <;> simpa using h
        exact fresh (ca ▸ ha)
      obtain ⟨i, hi, ei⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hb
      have ij : i+1 ≠ j+1 := by
        intro h
        have : i = j := by omega
        subst j
        exact ne (ei.symm.trans ej)
      have ext (o : Bool) (hc : c = if o then a ||| b else a &&& b) : built (v :: (w ++ [c])) := by
        have h := addGate (v :: w) hw (i+1) (j+1) (by simpa using hi) (by simpa using hj) ij o
        simpa [ei, ej, hc] using h
      have more : built (v :: (w ++ [c])) := by
        rcases kind with h | h
        · exact ext false h
        · exact ext true h
      have tail : grow (w ++ [c]) cs := by
        intro i
        simpa [List.append_assoc] using hp i.succ
      simpa [List.append_assoc] using ih (w ++ [c]) more tail
  obtain ⟨p,s,q,z,o,budget,hp,hmark,hs,out⟩ := synthesis
  let t := if o then v ||| (z &&& 2097144) else 7 ||| (z &&& 95229015649943552)
  change (if o then v ||| q else v &&& q) = t at hmark
  have start : built (v :: seed) := by
    exact ⟨[], by decide, by simp, rfl, fun _ => rfl⟩
  have pre := realize seed (p ++ [q]) start hp
  let w := v :: (seed ++ p ++ [q])
  change built (v :: (seed ++ (p ++ [q]))) at pre
  have hw : built w := by simpa [w, List.append_assoc] using pre
  have last : (seed ++ p).length + 1 < w.length := by simp [w]
  have hq : w[(seed ++ p).length+1] = q := by simp [w]
  have marked := addGate w hw 0 ((seed ++ p).length+1) (by simp [w]) last (by omega) o
  have ht : built (v :: (seed ++ p ++ [q,t])) := by
    simpa [w, hq, List.append_assoc, hmark] using marked
  obtain ⟨gs, good, nd, len, trace⟩ := realize (seed ++ p ++ [q,t]) s ht hs
  let final := v :: ((seed ++ p ++ [q,t]) ++ s)
  have hy : 2097151 ∈ final := List.mem_cons_of_mem _ (List.mem_append_right _ out)
  obtain ⟨k,hk,ek⟩ := List.mem_iff_getElem.mp hy
  let C : Circuit := ⟨gs,k⟩
  have size : C.size = p.length + s.length + 2 := by
    have hseed : seed.length = 13 := rfl
    simp only [List.length_cons, List.length_append, List.length_nil, hseed] at len
    change gs.length = _
    omega
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨good.1 g hg, (good.2.2 g hg).le⟩
  have correctBits (j : ℕ) : C.eval (bits (v :: seed) j) = (2097151 : ℕ).testBit j := by
    change ((Circuit.mk gs 0).wires _).getD k false = _
    rw [trace]
    change (bits final j).getD k false = _
    rw [List.getD_eq_getElem (bits final j) false (by simpa [bits] using hk)]
    simp [bits, ek]
  refine ⟨C, good, nd, by omega, by omega, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using boundary C mono correctBits x
