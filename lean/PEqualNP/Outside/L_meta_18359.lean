import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18359
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


def Wire (n : ℕ) (C : Circuit) (i : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  i < n + C.size ∧ ∀ x, (C.wires (List.ofFn x)).getD i false = f x

theorem primary {n} (C : Circuit) (i : Fin n) : Wire n C i (fun x => x i) := by
  refine ⟨by have := i.isLt; omega, ?_⟩
  intro x
  change (wiresFrom C.gates _).getD i.val false = _
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem keep {n C i f} (w : Wire n C i f) (gs : List Gate) (out : ℕ) :
    Wire n ⟨C.gates ++ gs, out⟩ i f := by
  refine ⟨by have := w.1; simp only [Circuit.size,List.length_append] at *; omega, ?_⟩
  intro x
  change (wiresFrom (C.gates ++ gs) _).getD i false = _
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom,List.length_ofFn]; exact w.1)]
  exact w.2 x

def append (C : Circuit) (o : Bool) (u v : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨if o then .or else .and, [u,v]⟩], C.output⟩
theorem keepOne {n C i f} (w : Wire n C i f) (o : Bool) (u v : ℕ) :
    Wire n (append C o u v) i f := keep w _ _
theorem added {n C u v f h} (a : Wire n C u f) (b : Wire n C v h) (o : Bool) :
    Wire n (append C o u v) (n + C.size) (fun x => if o then f x || h x else f x && h x) := by
  refine ⟨by simp [append,Circuit.size], ?_⟩
  intro x
  let W := wiresFrom C.gates (List.ofFn x)
  have hl : W.length = n + C.size := by simp [W,length_wiresFrom,Circuit.size]
  have ha : (wiresFrom C.gates (List.ofFn x)).getD u false = f x := a.2 x
  have hb : (wiresFrom C.gates (List.ofFn x)).getD v false = h x := b.2 x
  change (wiresFrom (C.gates ++ [_]) _).getD _ false = _
  rw [wiresFrom_append]
  change (W ++ [_]).getD (n+C.size) false = _
  rw [← hl]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, ha,hb] <;>
    cases o <;> simpa [GateOp.eval, ← List.getD_eq_getElem?_getD, ha,hb]
theorem monoAppend {C : Circuit} (hc : Monotone2 C) (o : Bool) (u v : ℕ) :
    Monotone2 (append C o u v) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc g hg
  · obtain rfl := List.mem_singleton.mp hg
    cases o <;> simp
theorem monoPad {C : Circuit} (hc : Monotone2 C) (d out : ℕ) :
    Monotone2 ⟨C.gates ++ List.replicate d ⟨.or,[]⟩, out⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc g hg
  · obtain rfl := List.eq_of_mem_replicate hg
    simp
end PEqualNP.Outside.L_meta_18359
open PEqualNP.Outside.L_meta_18359 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.L_meta_18359 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (3 : ℕ) → Fin x1) (x6 : Fin (3 : ℕ) → Fin (4 : ℕ) → Fin x1) (x7 : Fin x1), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ x2 → x3.output < x1 + x3.size → x4 < x1 + x3.size → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ), PEqualNP.MetaComplexity.Monotone2 x12 ∧ x12.size = x2 + (16 : ℕ) ∧ x12.output < x1 + x12.size ∧ x13 < x1 + x12.size ∧ ∀ (x14 : Fin x1 → Bool), x12.eval (List.ofFn x14) = (x3.eval (List.ofFn x14) || x14 (x5 (0 : Fin (3 : ℕ))) && (x14 (x6 (0 : Fin (3 : ℕ)) (0 : Fin (4 : ℕ))) || x14 (x6 (0 : Fin (3 : ℕ)) (1 : Fin (4 : ℕ))) || x14 (x6 (0 : Fin (3 : ℕ)) (2 : Fin (4 : ℕ))) || x14 (x6 (0 : Fin (3 : ℕ)) (3 : Fin (4 : ℕ)))) || x14 (x5 (1 : Fin (3 : ℕ))) && (x14 (x6 (1 : Fin (3 : ℕ)) (0 : Fin (4 : ℕ))) || x14 (x6 (1 : Fin (3 : ℕ)) (1 : Fin (4 : ℕ))) || x14 (x6 (1 : Fin (3 : ℕ)) (2 : Fin (4 : ℕ))) || x14 (x6 (1 : Fin (3 : ℕ)) (3 : Fin (4 : ℕ)))) || x14 (x5 (2 : Fin (3 : ℕ))) && (x14 (x6 (2 : Fin (3 : ℕ)) (0 : Fin (4 : ℕ))) || x14 (x6 (2 : Fin (3 : ℕ)) (1 : Fin (4 : ℕ))) || x14 (x6 (2 : Fin (3 : ℕ)) (2 : Fin (4 : ℕ))) || x14 (x6 (2 : Fin (3 : ℕ)) (3 : Fin (4 : ℕ))))) ∧ (x12.wires (List.ofFn x14)).getD x13 Bool.false = ((x3.wires (List.ofFn x14)).getD x4 Bool.false || x14 x7) := by
  intro n budget C0 side centers leaves extra hm0 hs ho hw
  have root : Wire n C0 C0.output (fun x => C0.eval (List.ofFn x)) := ⟨ho, fun _ => rfl⟩
  have sideWire : Wire n C0 side (fun x => (C0.wires (List.ofFn x)).getD side false) := ⟨hw, fun _ => rfl⟩
  let C1 := append C0 true ((leaves 0 0).val) ((leaves 0 1).val)
  have hm1 : Monotone2 C1 := monoAppend hm0 _ _ _
  have pres1 {i f} (w : Wire n C0 i f) : Wire n C1 i f := keepOne w _ _ _
  have w1 := added (primary C0 (leaves 0 0)) (primary C0 (leaves 0 1)) true
  change Wire n C1 (n+C0.size) _ at w1
  let C2 := append C1 true (n+C0.size) ((leaves 0 2).val)
  have hm2 : Monotone2 C2 := monoAppend hm1 _ _ _
  have pres2 {i f} (w : Wire n C1 i f) : Wire n C2 i f := keepOne w _ _ _
  have w2 := added w1 (primary C1 (leaves 0 2)) true
  change Wire n C2 (n+C1.size) _ at w2
  let C3 := append C2 true (n+C1.size) ((leaves 0 3).val)
  have hm3 : Monotone2 C3 := monoAppend hm2 _ _ _
  have pres3 {i f} (w : Wire n C2 i f) : Wire n C3 i f := keepOne w _ _ _
  have w3 := added w2 (primary C2 (leaves 0 3)) true
  change Wire n C3 (n+C2.size) _ at w3
  let C4 := append C3 false ((centers 0).val) (n+C2.size)
  have hm4 : Monotone2 C4 := monoAppend hm3 _ _ _
  have pres4 {i f} (w : Wire n C3 i f) : Wire n C4 i f := keepOne w _ _ _
  have w4 := added (primary C3 (centers 0)) w3 false
  change Wire n C4 (n+C3.size) _ at w4
  let C5 := append C4 true C0.output (n+C3.size)
  have hm5 : Monotone2 C5 := monoAppend hm4 _ _ _
  have pres5 {i f} (w : Wire n C4 i f) : Wire n C5 i f := keepOne w _ _ _
  have w5 := added (pres4 (pres3 (pres2 (pres1 root)))) w4 true
  change Wire n C5 (n+C4.size) _ at w5
  let C6 := append C5 true ((leaves 1 0).val) ((leaves 1 1).val)
  have hm6 : Monotone2 C6 := monoAppend hm5 _ _ _
  have pres6 {i f} (w : Wire n C5 i f) : Wire n C6 i f := keepOne w _ _ _
  have w6 := added (primary C5 (leaves 1 0)) (primary C5 (leaves 1 1)) true
  change Wire n C6 (n+C5.size) _ at w6
  let C7 := append C6 true (n+C5.size) ((leaves 1 2).val)
  have hm7 : Monotone2 C7 := monoAppend hm6 _ _ _
  have pres7 {i f} (w : Wire n C6 i f) : Wire n C7 i f := keepOne w _ _ _
  have w7 := added w6 (primary C6 (leaves 1 2)) true
  change Wire n C7 (n+C6.size) _ at w7
  let C8 := append C7 true (n+C6.size) ((leaves 1 3).val)
  have hm8 : Monotone2 C8 := monoAppend hm7 _ _ _
  have pres8 {i f} (w : Wire n C7 i f) : Wire n C8 i f := keepOne w _ _ _
  have w8 := added w7 (primary C7 (leaves 1 3)) true
  change Wire n C8 (n+C7.size) _ at w8
  let C9 := append C8 false ((centers 1).val) (n+C7.size)
  have hm9 : Monotone2 C9 := monoAppend hm8 _ _ _
  have pres9 {i f} (w : Wire n C8 i f) : Wire n C9 i f := keepOne w _ _ _
  have w9 := added (primary C8 (centers 1)) w8 false
  change Wire n C9 (n+C8.size) _ at w9
  let C10 := append C9 true (n+C4.size) (n+C8.size)
  have hm10 : Monotone2 C10 := monoAppend hm9 _ _ _
  have pres10 {i f} (w : Wire n C9 i f) : Wire n C10 i f := keepOne w _ _ _
  have w10 := added (pres9 (pres8 (pres7 (pres6 w5)))) w9 true
  change Wire n C10 (n+C9.size) _ at w10
  let C11 := append C10 true ((leaves 2 0).val) ((leaves 2 1).val)
  have hm11 : Monotone2 C11 := monoAppend hm10 _ _ _
  have pres11 {i f} (w : Wire n C10 i f) : Wire n C11 i f := keepOne w _ _ _
  have w11 := added (primary C10 (leaves 2 0)) (primary C10 (leaves 2 1)) true
  change Wire n C11 (n+C10.size) _ at w11
  let C12 := append C11 true (n+C10.size) ((leaves 2 2).val)
  have hm12 : Monotone2 C12 := monoAppend hm11 _ _ _
  have pres12 {i f} (w : Wire n C11 i f) : Wire n C12 i f := keepOne w _ _ _
  have w12 := added w11 (primary C11 (leaves 2 2)) true
  change Wire n C12 (n+C11.size) _ at w12
  let C13 := append C12 true (n+C11.size) ((leaves 2 3).val)
  have hm13 : Monotone2 C13 := monoAppend hm12 _ _ _
  have pres13 {i f} (w : Wire n C12 i f) : Wire n C13 i f := keepOne w _ _ _
  have w13 := added w12 (primary C12 (leaves 2 3)) true
  change Wire n C13 (n+C12.size) _ at w13
  let C14 := append C13 false ((centers 2).val) (n+C12.size)
  have hm14 : Monotone2 C14 := monoAppend hm13 _ _ _
  have pres14 {i f} (w : Wire n C13 i f) : Wire n C14 i f := keepOne w _ _ _
  have w14 := added (primary C13 (centers 2)) w13 false
  change Wire n C14 (n+C13.size) _ at w14
  let C15 := append C14 true (n+C9.size) (n+C13.size)
  have hm15 : Monotone2 C15 := monoAppend hm14 _ _ _
  have pres15 {i f} (w : Wire n C14 i f) : Wire n C15 i f := keepOne w _ _ _
  have w15 := added (pres14 (pres13 (pres12 (pres11 w10)))) w14 true
  change Wire n C15 (n+C14.size) _ at w15
  let C16 := append C15 true side ((extra).val)
  have hm16 : Monotone2 C16 := monoAppend hm15 _ _ _
  have pres16 {i f} (w : Wire n C15 i f) : Wire n C16 i f := keepOne w _ _ _
  have w16 := added (pres15 (pres14 (pres13 (pres12 (pres11 (pres10 (pres9 (pres8 (pres7 (pres6 (pres5 (pres4 (pres3 (pres2 (pres1 sideWire))))))))))))))) (primary C15 (extra)) true
  change Wire n C16 (n+C15.size) _ at w16
  let gs : List Gate := List.replicate (budget-C0.size) ⟨.or,[]⟩
  let final : Circuit := ⟨C16.gates ++ gs,n+C14.size⟩
  have a := keep (pres16 w15) gs (n+C14.size)
  have b := keep w16 gs (n+C14.size)
  change Wire n final _ _ at a b
  refine ⟨final,n+C15.size,monoPad hm16 _ _,?_,a.1,b.1,fun x => ⟨a.2 x,b.2 x⟩⟩
  simp only [final, gs, C16, C15, C14, C13, C12, C11, C10, C9, C8, C7, C6, C5, C4, C3, C2, C1, append, Circuit.size,List.length_append,List.length_singleton,List.length_replicate]
  change C0.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (budget - C0.size) = budget + 16
  omega
