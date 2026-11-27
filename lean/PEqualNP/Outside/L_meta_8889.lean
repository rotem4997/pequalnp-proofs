import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8889

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




def rn (n m : ℕ) (π : Fin n → Fin m) (i : ℕ) : ℕ := if h : i < n then (π ⟨i, h⟩ : ℕ) else i - n + m

theorem ren (n m : ℕ) (π : Fin n → Fin m) (y : Fin m → Bool) : ∀ hs : List Gate,
    ∀ i, (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).getD (rn n m π i) false =
      (run hs (List.ofFn (y ∘ π))).getD i false := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil]
    by_cases hi : i < n
    · have e : rn n m π i = (π ⟨i, hi⟩ : ℕ) := dif_pos hi
      rw [e, run_input [] (List.ofFn y) (π ⟨i, hi⟩ : ℕ) (by simp),
        run_input [] (List.ofFn (y ∘ π)) i (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
    · have e : rn n m π i = i - n + m := dif_neg hi
      rw [e, List.getD_eq_default _ _ (by rw [run_length]; simp),
        List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  | append_singleton hs g ih =>
    intro i
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc]
    have l1 : (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).length = m + hs.length := by
      rw [run_length]; simp
    have l2 : (run hs (List.ofFn (y ∘ π))).length = n + hs.length := by rw [run_length]; simp
    have hrn : i < n → rn n m π i < m := by
      intro h
      have e : rn n m π i = (π ⟨i, h⟩ : ℕ) := dif_pos h
      rw [e]; exact (π ⟨i, h⟩).isLt
    have hrn2 : ¬ i < n → rn n m π i = i - n + m := fun h => dif_neg h
    rcases Nat.lt_trichotomy i (n + hs.length) with h | h | h
    · have : rn n m π i < m + hs.length := by
        by_cases hi : i < n
        · have := hrn hi; omega
        · rw [hrn2 hi]; omega
      rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega), ih i]
    · have hi : ¬ i < n := by omega
      have e1 : rn n m π i = (run (hs.map fun g => (⟨g.op, g.inputs.map (rn n m π)⟩ : Gate)) (List.ofFn y)).length := by
        rw [l1, hrn2 hi]; omega
      have e2 : i = (run hs (List.ofFn (y ∘ π))).length := by omega
      rw [e1, getD_at]
      conv_rhs => rw [e2, getD_at]
      rw [List.map_map]
      congr 1
      exact List.map_congr_left fun k _ => ih k
    · have hi : ¬ i < n := by omega
      rw [List.getD_eq_default _ _ (by rw [List.length_append, l1, hrn2 hi]; simp; omega),
        List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

def Ok (m : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧ ∃ a b, gs[j].inputs = [a, b] ∧ a < m + j ∧ b < m + j

theorem Ok.snoc {m : ℕ} {gs : List Gate} (h : Ok m gs) {o : GateOp} {a b : ℕ} (ho : o = GateOp.and ∨ o = GateOp.or) (ha : a < m + gs.length) (hb : b < m + gs.length) :
    Ok m (gs ++ [⟨o, [a, b]⟩]) := by
  intro j hj
  by_cases hjl : j < gs.length
  · rw [List.getElem_append_left hjl]; exact h j hjl
  · have e : j = gs.length := by simp at hj; omega
    subst e
    simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
    exact ⟨ho, a, b, rfl, ha, hb⟩

theorem toAO {m : ℕ} {gs : List Gate} {o : ℕ} (h : Ok m gs) : PEqualNP.TopForm.IsAO2 m ⟨gs, o⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (h j hj).1
  · intro j hj i hi
    have hj : j < gs.length := hj
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
    rw [e] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, hab, _⟩ := h j hj
    rw [hab]; rfl

theorem ofAO {m : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 m C) : Ok m C.gates := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h3 _ (List.getElem_mem hj))
  have h4 := h2 j hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  rw [e, hab] at h4
  exact ⟨h1 _ (List.getElem_mem hj), a, b, hab, h4 a (by simp), h4 b (by simp)⟩

def W {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (w : ℕ) : Bool := (run gs (List.ofFn x)).getD w false

theorem W_old {m : ℕ} (gs hs : List Gate) (x : Fin m → Bool) (w : ℕ) (hw : w < m + gs.length) : W (gs ++ hs) x w = W gs x w :=
  run_prefix gs hs _ w (by rw [List.length_ofFn]; exact hw)

theorem W_new {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (o : GateOp) (a b : ℕ) : W (gs ++ [⟨o, [a, b]⟩]) x (m + gs.length) = o.eval [W gs x a, W gs x b] := by
  unfold W
  rw [run_snoc]
  have : m + gs.length = (run gs (List.ofFn x)).length := by rw [run_length, List.length_ofFn]
  rw [this, getD_at]
  rfl

theorem W_in {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (v : Fin m) : W gs x v = x v := by
  unfold W
  rw [run_input _ _ _ (by rw [List.length_ofFn]; exact v.isLt)]
  simp

theorem orchain {m : ℕ} : ∀ (ls : List (Fin m)) (gs : List Gate) (c : ℕ), Ok m gs → c < m + gs.length →
    ∃ hs : List Gate, hs.length = ls.length ∧ Ok m (gs ++ hs) ∧ ∃ c' < m + gs.length + hs.length, ∀ x, W (gs ++ hs) x c' = (W gs x c || ls.any x)
  | [], gs, c, h, hc => ⟨[], rfl, by simpa using h, c, by simpa using hc, fun x => by simp⟩
  | v :: ls, gs, c, h, hc => by
    have hv : (v : ℕ) < m + gs.length := by have := v.isLt; omega
    have h' := h.snoc (Or.inr rfl) hc hv (o := GateOp.or)
    obtain ⟨hs, h1, h2, c', h3, h4⟩ := orchain ls (gs ++ [⟨GateOp.or, [c, v]⟩]) (m + gs.length) h' (by simp)
    refine ⟨⟨GateOp.or, [c, v]⟩ :: hs, by simp [h1], by simpa using h2, c', by simp at h3 ⊢; omega, fun x => ?_⟩
    have := h4 x
    rw [W_new, W_in] at this
    simp only [List.append_assoc, List.singleton_append] at this
    rw [this]
    simp [GateOp.eval, Bool.or_assoc]

theorem term {m : ℕ} (gs : List Gate) (o : ℕ) (h : Ok m gs) (v : Fin m) (ls : List (Fin m)) (hl : ls ≠ []) :
    ∃ (gs' : List Gate) (o' : ℕ), Ok m gs' ∧ gs'.length ≤ gs.length + (ls.length + 1) ∧ ∀ x, W gs' x o' = (W gs x o || (x v && ls.any x)) := by
  rcases ls with _ | ⟨w, ls⟩
  · exact absurd rfl hl
  obtain ⟨hs, h1, h2, c, h3, h4⟩ := orchain ls gs w h (by have := w.isLt; omega)
  have hv : (v : ℕ) < m + (gs ++ hs).length := by have := v.isLt; omega
  have hc : c < m + (gs ++ hs).length := by simp; omega
  have h5 := h2.snoc (Or.inl rfl) hv hc (o := GateOp.and)
  have val : ∀ x : Fin m → Bool, W (gs ++ hs ++ [(⟨GateOp.and, [(v : ℕ), c]⟩ : Gate)]) x (m + (gs ++ hs).length) = (x v && (w :: ls).any x) := by
    intro x
    rw [W_new, W_in, h4, W_in]
    simp [GateOp.eval]
  by_cases ho : o < m + gs.length
  · have ho' : o < m + (gs ++ hs ++ [(⟨GateOp.and, [(v : ℕ), c]⟩ : Gate)]).length := by simp; omega
    have h6 := h5.snoc (Or.inr rfl) ho' (b := m + (gs ++ hs).length) (by simp) (o := GateOp.or)
    refine ⟨_, _, h6, by simp; omega, fun x => W_new _ x GateOp.or o (m + (gs ++ hs).length) |>.trans ?_⟩
    rw [val, List.append_assoc, W_old _ _ x o ho]
    simp [GateOp.eval]
  · refine ⟨_, _, h5, by simp; omega, fun x => (val x).trans ?_⟩
    have : W gs x o = false := by
      unfold W
      rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
    rw [this, Bool.false_or]

theorem terms {m : ℕ} : ∀ (L : List (Fin m × List (Fin m))) (gs : List Gate) (o : ℕ), Ok m gs → (∀ p ∈ L, p.2 ≠ []) →
    ∃ (gs' : List Gate) (o' : ℕ), Ok m gs' ∧ gs'.length ≤ gs.length + (L.map fun p => p.2.length + 1).sum ∧ ∀ x, W gs' x o' = (W gs x o || L.any fun p => x p.1 && p.2.any x)
  | [], gs, o, h, _ => ⟨gs, o, h, by simp, fun x => by simp⟩
  | p :: L, gs, o, h, hL => by
    obtain ⟨g1, o1, a1, a2, a3⟩ := term gs o h p.1 p.2 (hL p (by simp))
    obtain ⟨g2, o2, b1, b2, b3⟩ := terms L g1 o1 a1 fun q hq => hL q (List.mem_cons_of_mem _ hq)
    refine ⟨g2, o2, b1, by simp only [List.map_cons, List.sum_cons]; omega, fun x => ?_⟩
    rw [b3, a3]
    simp [Bool.or_assoc]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8889

theorem PEqualNP.Outside.L_meta_8889 : ∀ {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → ∀ (x6 : List (Fin x2 × List (Fin x2))), (∀ x7 ∈ x6, x7.2 ≠ []) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x8 ∧ x8.size ≤ x4.size + (List.map (fun (x9 : Fin x2 × List (Fin x2)) => x9.2.length + (1 : ℕ)) x6).sum ∧ ∀ (x9 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x8 x9 = (PEqualNP.MetaComplexity.circuitFun x1 x4 (x9 ∘ x3) || x6.any fun (x10 : Fin x2 × List (Fin x2)) => x9 x10.1 && x10.2.any x9) := by
  intro n m π C hC L hL
  have hO := PEqualNP.Outside.L_meta_8889.ofAO hC
  let gs : List PEqualNP.CircuitLowerBounds.Gate := C.gates.map fun g => ⟨g.op, g.inputs.map (PEqualNP.Outside.L_meta_8889.rn n m π)⟩
  have hgs : PEqualNP.Outside.L_meta_8889.Ok m gs := by
    intro j hj
    have hj' : j < C.gates.length := by simpa [gs] using hj
    obtain ⟨h1, a, b, hab, ha, hb⟩ := hO j hj'
    have rl : ∀ i, i < n + j → PEqualNP.Outside.L_meta_8889.rn n m π i < m + j := by
      intro i hi
      unfold PEqualNP.Outside.L_meta_8889.rn
      split_ifs with h
      · have := (π ⟨i, h⟩).isLt; omega
      · omega
    simp only [gs, List.getElem_map]
    exact ⟨h1, _, _, by rw [hab]; rfl, rl a ha, rl b hb⟩
  obtain ⟨g', o', h1, h2, h3⟩ := PEqualNP.Outside.L_meta_8889.terms L gs (PEqualNP.Outside.L_meta_8889.rn n m π C.output) hgs hL
  refine ⟨⟨g', o'⟩, PEqualNP.Outside.L_meta_8889.toAO h1, ?_, fun x => ?_⟩
  · have : gs.length = C.gates.length := by simp [gs]
    rw [this] at h2
    exact h2
  · refine (h3 x).trans ?_
    congr 1
    exact PEqualNP.Outside.L_meta_8889.ren n m π x C.gates C.output
