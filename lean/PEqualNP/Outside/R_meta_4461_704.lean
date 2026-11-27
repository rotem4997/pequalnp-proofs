import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Compress away the isolated indices, then count direct readers of a nonadjacent pair.
-- The reader count separates a constant-folding argument from the residual circuit bound.
set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_4461_704
    (elimReaders : ∀ (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool) (u v : Fin n),
      FanInTwo C → circuitFun n C = f →
      (∃ x y : Fin n → Bool, f (Function.update (Function.update x u false) v false) ≠
        f (Function.update (Function.update y u false) v false)) →
      8 ≤ C.gates.countP (fun g =>
        bif g.op.eval [false] then
          (g.inputs.take 1).contains u.val || (g.inputs.take 1).contains v.val
        else g.inputs.contains u.val || g.inputs.contains v.val) →
      ∃ t : ℕ, t + 8 ≤ C.size ∧ HasCircuitSize n
        (fun x => f (Function.update (Function.update x u false) v false)) t)
    (tight : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (C : Circuit),
      H.Colorable 2 → (∀ i, (H.neighborSet i).ncard = 3) →
      (∀ v (w : H.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ i j, H.Adj i j) →
      FanInTwo C → circuitFun m C = graphFun H ∅ → C.size < 2 * m - 1 →
      (∀ u v, u ≠ v → ¬H.Adj u v → C.gates.countP (fun g =>
        bif g.op.eval [false] then
          (g.inputs.take 1).contains u.val || (g.inputs.take 1).contains v.val
        else g.inputs.contains u.val || g.inputs.contains v.val) < 8) →
      ∃ u v, u ≠ v ∧ ¬H.Adj u v ∧ ∃ t : ℕ,
        t + 8 ≤ C.size ∧ HasCircuitSize m
          (fun x => graphFun H ∅ (Function.update (Function.update x u false) v false)) t) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x10 → x10 < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x4 ∧ x14 ∉ x4 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  have rewire : ∀ (n m : ℕ) (r : Fin n → Fin m) (f : (Fin n → Bool) → Bool) (s : ℕ),
      HasCircuitSize n f s → HasCircuitSize m (fun x => f (fun i => x (r i))) s := by
    intro n m r f s
    rintro ⟨C, hfan, hsize, hfun⟩
    let route (i : ℕ) : ℕ := if h : i < n then (r ⟨i, h⟩).val else m + (i - n)
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map route⟩
    let run (gs : List Gate) (w : List Bool) :=
      gs.foldl (fun vals g => vals ++ [g.op.eval (g.inputs.map fun i => vals.getD i false)]) w
    refine ⟨⟨C.gates.map rename, route C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [rename] using hfan g' hg'
    · delta Circuit.size at hsize ⊢
      simpa only [List.length_map] using hsize
    · intro x
      let X := List.ofFn x
      let Y := List.ofFn (fun i => x (r i))
      have access (ss : List Bool) (i : ℕ) :
          (Y ++ ss).getD i false = (X ++ ss).getD (route i) false := by
        by_cases hi : i < n
        · have hY : i < Y.length := by simpa [Y] using hi
          have hr : (r ⟨i, hi⟩).val < X.length := by simp [X]
          rw [show route i = (r ⟨i, hi⟩).val from dite_eq_left hi]
          rw [List.getD_append _ _ _ _ hY, List.getD_append _ _ _ _ hr,
            List.getD_eq_getElem _ _ hY, List.getD_eq_getElem _ _ hr]
          simp [X, Y]
        · have hY : Y.length ≤ i := by simpa [Y] using (Nat.le_of_not_lt hi)
          have hr : X.length ≤ route i := by simp [X, route, hi]
          rw [List.getD_append_right _ _ _ _ hY, List.getD_append_right _ _ _ _ hr]
          simp [X, Y, route, hi]
      have both (gs : List Gate) (ss : List Bool) :
          ∃ out, run gs (Y ++ ss) = Y ++ out ∧ run (gs.map rename) (X ++ ss) = X ++ out := by
        induction gs generalizing ss with
        | nil => exact ⟨ss, rfl, rfl⟩
        | cons g gs ih =>
          let bit := g.op.eval (g.inputs.map fun i => (Y ++ ss).getD i false)
          have hbit : (rename g).op.eval ((rename g).inputs.map fun i => (X ++ ss).getD i false) = bit := by
            simp only [rename, List.map_map, Function.comp_def, bit]
            congr 1
            apply List.map_congr_left
            intro j _
            exact (access ss j).symm
          obtain ⟨out, hY, hX⟩ := ih (ss ++ [bit])
          refine ⟨out, ?_, ?_⟩
          · simpa [run, List.append_assoc, bit] using hY
          · simp only [run, List.map_cons, List.foldl_cons]
            rw [hbit, List.append_assoc]
            exact hX
      obtain ⟨out, hY, hX⟩ := both C.gates []
      have h₁ : C.wires Y = Y ++ out := by
        delta Circuit.wires
        simpa [run] using hY
      have h₂ : (Circuit.mk (C.gates.map rename) (route C.output)).wires X = X ++ out := by
        delta Circuit.wires
        simpa [run] using hX
      calc
        (Circuit.mk (C.gates.map rename) (route C.output)).eval X =
            (X ++ out).getD (route C.output) false := by delta Circuit.eval; rw [h₂]
        _ = (Y ++ out).getD C.output false := (access out C.output).symm
        _ = C.eval Y := by delta Circuit.eval; rw [h₁]
        _ = f (fun i => x (r i)) := hfun _
  intro n G d A color deg girth isolated edge s size small
  classical
  let m := n - A.card
  let U := {i : Fin n // i ∉ A}
  have hcard : Fintype.card U = m := by
    dsimp [U, m]
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (Fintype.card_subtype_compl fun i : Fin n => i ∈ A)
  let e : Fin m ≃ U := (finCongr hcard.symm).trans (Fintype.equivFin U).symm
  let emb (i : Fin m) : Fin n := (e i).val
  have inj : Function.Injective emb := fun _ _ h => e.injective (Subtype.ext h)
  obtain ⟨a, b, ab⟩ := edge
  let back (i : Fin n) : Fin m :=
    if h : i ∉ A then e.symm ⟨i, h⟩ else e.symm ⟨a, isolated a b ab⟩
  have inU (i : Fin m) : emb i ∉ A := (e i).property
  have back_emb (i : Fin m) : back (emb i) = i := by
    simp only [back, dite_eq_left (inU i)]
    exact e.symm_apply_apply i
  have emb_back (i : Fin n) (hi : i ∉ A) : emb (back i) = i := by
    simp [emb, back, hi]
  let H : SimpleGraph (Fin m) := G.comap emb
  let hom : H →g G := ⟨emb, fun h => h⟩
  have degH (i : Fin m) : (H.neighborSet i).ncard = 3 := by
    rw [← deg (emb i) (inU i)]
    apply Set.ncard_congr (fun j _ => emb j) (fun _ h => h) (fun _ _ _ _ h => inj h)
    intro z hz
    change G.Adj (emb i) z at hz
    have he := emb_back z (isolated _ _ hz.symm)
    refine ⟨back z, ?_, he⟩
    change G.Adj (emb i) (emb (back z))
    rwa [he]
  have girthH (i : Fin m) (w : H.Walk i i) (h : w.IsCycle) : 7 ≤ w.length := by
    have hinj : Function.Injective hom := inj
    simpa using girth (emb i) (w.map hom) (h.map hinj)
  have edgeH : ∃ i j, H.Adj i j := by
    refine ⟨back a, back b, ?_⟩
    change G.Adj (emb (back a)) (emb (back b))
    rwa [emb_back _ (isolated _ _ ab), emb_back _ (isolated _ _ ab.symm)]
  have preserve (y : Fin m → Bool) : graphFun G ∅ (fun i => y (back i)) = graphFun H ∅ y := by
    apply Bool.eq_iff_iff.mpr
    delta graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨i, j, ij, oneI, oneJ⟩
      refine ⟨back i, back j, ?_, oneI, oneJ⟩
      change G.Adj (emb (back i)) (emb (back j))
      rwa [emb_back _ (isolated _ _ ij), emb_back _ (isolated _ _ ij.symm)]
    · rintro ⟨i, j, ij, oneI, oneJ⟩
      exact ⟨emb i, emb j, ij, by rwa [back_emb], by rwa [back_emb]⟩
  have smallH : HasCircuitSize m (graphFun H ∅) s := by
    have hs := rewire n m back _ s size
    rwa [funext preserve] at hs
  have choose : ∃ p q : Fin m, p ≠ q ∧ ¬H.Adj p q ∧ ∃ t, t + 8 ≤ s ∧
      HasCircuitSize m (fun y => graphFun H ∅ (Function.update (Function.update y p false) q false)) t := by
    obtain ⟨C, fan, csize, ev⟩ := smallH
    have hev : circuitFun m C = graphFun H ∅ := funext ev
    by_cases readers : ∃ u v : Fin m, u ≠ v ∧ ¬H.Adj u v ∧
        8 ≤ C.gates.countP (fun g =>
          bif g.op.eval [false] then
            (g.inputs.take 1).contains u.val || (g.inputs.take 1).contains v.val
          else g.inputs.contains u.val || g.inputs.contains v.val)
    · obtain ⟨u, v, huv, noAdj, many⟩ := readers
      have hpos : 0 < (H.neighborSet u).ncard := by rw [degH u]; decide
      obtain ⟨a, ha⟩ := (Set.ncard_pos (s := H.neighborSet u)).mp hpos
      change H.Adj u a at ha
      have hau : a ≠ u := (H.ne_of_adj ha).symm
      have hav : a ≠ v := fun h => noAdj (h ▸ ha)
      obtain ⟨b, hab, hbu, hbv⟩ : ∃ b, H.Adj a b ∧ b ≠ u ∧ b ≠ v := by
        by_contra missing
        have sub : H.neighborSet a ⊆ ({u, v} : Set (Fin m)) := by
          intro b hb
          by_cases hbu : b = u
          · simp [hbu]
          by_cases hbv : b = v
          · simp [hbv]
          · exact False.elim (missing ⟨b, hb, hbu, hbv⟩)
        have hle := Set.ncard_le_ncard sub
        rw [degH a, Set.ncard_pair huv] at hle
        omega
      have nonconstant : ∃ x y : Fin m → Bool,
          graphFun H ∅ (Function.update (Function.update x u false) v false) ≠
          graphFun H ∅ (Function.update (Function.update y u false) v false) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have hzero : Function.update (Function.update (fun _ : Fin m => false) u false) v false =
            fun _ => false := by
          funext w
          by_cases hwu : w = u <;> by_cases hwv : w = v <;>
            simp [hwu, hwv, Function.update_of_ne]
        rw [hzero]
        have htrue : graphFun H ∅
            (Function.update (Function.update (fun _ => true) u false) v false) = true := by
          delta graphFun
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
            Bool.false_or, decide_eq_true_eq]
          refine ⟨a, b, hab, ?_, ?_⟩
          · simp [Function.update_of_ne, hau, hav]
          · simp [Function.update_of_ne, hbu, hbv]
        rw [htrue]
        delta graphFun
        simp
      obtain ⟨t, ht, model⟩ := elimReaders m C (graphFun H ∅) u v fan hev nonconstant many
      exact ⟨u, v, huv, noAdj, t, ht.trans csize, model⟩
    · have few (u v : Fin m) (huv : u ≠ v) (noAdj : ¬H.Adj u v) :
          C.gates.countP (fun g =>
            bif g.op.eval [false] then
              (g.inputs.take 1).contains u.val || (g.inputs.take 1).contains v.val
            else g.inputs.contains u.val || g.inputs.contains v.val) < 8 :=
        Nat.lt_of_not_ge fun many => readers ⟨u, v, huv, noAdj, many⟩
      obtain ⟨u, v, huv, noAdj, t, ht, model⟩ :=
        tight m H C (SimpleGraph.Colorable.of_hom hom color) degH girthH edgeH
          fan hev (lt_of_le_of_lt csize small) few
      exact ⟨u, v, huv, noAdj, t, ht.trans csize, model⟩
  obtain ⟨p, q, hpq, hnot, t, ht, short⟩ := choose
  let u := emb p
  let v := emb q
  have neq : u ≠ v := fun eq => hpq (inj eq)
  refine ⟨u, v, inU p, inU q, neq, hnot, t, ht, ?_⟩
  have lift := rewire m n emb _ t short
  have eqf : (fun x : Fin n → Bool =>
      graphFun H ∅ (Function.update (Function.update (fun i => x (emb i)) p false) q false)) =
    (fun x => graphFun G ∅ (Function.update (Function.update x u false) v false)) := by
    funext x
    rw [← preserve]
    apply Bool.eq_iff_iff.mpr
    delta graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    have agrees (i : Fin n) (hi : i ∉ A) :
        (Function.update (Function.update (fun k => x (emb k)) p false) q false) (back i) =
        (Function.update (Function.update x u false) v false) i := by
      by_cases eq : i = emb q
      · subst i
        simp [v, back_emb]
      have nbq : back i ≠ q := fun h => eq ((emb_back i hi).symm.trans (congrArg emb h))
      rw [Function.update_of_ne nbq, Function.update_of_ne (show i ≠ v from eq)]
      by_cases eq' : i = emb p
      · subst i
        simp [u, back_emb]
      have nbp : back i ≠ p := fun h => eq' ((emb_back i hi).symm.trans (congrArg emb h))
      rw [Function.update_of_ne nbp, Function.update_of_ne (show i ≠ u from eq'), emb_back i hi]
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    apply and_congr_right
    intro ij
    rw [agrees i (isolated i j ij), agrees j (isolated j i ij.symm)]
  rw [eqf] at lift
  exact lift
