import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8853

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




def sg (c i : ℕ) : ℕ := if i < c then i else i - 1

def sh (c : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg c)⟩

theorem del (x : List Bool) (n : ℕ) (hx : x.length = n) (p : List Gate) (g : Gate) : ∀ q : List Gate, (∀ h ∈ q, n + p.length ∉ h.inputs) →
    ∀ i, i ≠ n + p.length → (run (p ++ q.map (sh (n + p.length))) x).getD (sg (n + p.length) i) false = (run (p ++ [g] ++ q) x).getD i false := by
  intro q
  induction q using List.reverseRecOn with
  | nil =>
    intro _ i hi
    simp only [List.map_nil, List.append_nil]
    rcases Nat.lt_or_ge i (n + p.length) with h | h
    · rw [sg, if_pos h]
      exact (run_prefix p [g] x i (by omega)).symm
    · rw [sg, if_neg (by omega), List.getD_eq_default _ _ (by rw [run_length]; omega), List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  | append_singleton q h ih =>
    intro hq i hi
    have ih := ih (fun h' hh => hq h' (List.mem_append_left _ hh))
    have hh : n + p.length ∉ h.inputs := hq h (by simp)
    rw [List.map_append, List.map_singleton, ← List.append_assoc, ← List.append_assoc, run_snoc, run_snoc]
    have l1 : (run (p ++ q.map (sh (n + p.length))) x).length = n + p.length + q.length := by rw [run_length]; simp [hx]; omega
    have l2 : (run (p ++ [g] ++ q) x).length = n + p.length + 1 + q.length := by rw [run_length]; simp [hx]; omega
    rcases Nat.lt_trichotomy i (n + p.length + 1 + q.length) with h1 | h1 | h1
    · rw [getD_lt _ _ _ (by rw [l1, sg]; split_ifs <;> omega), getD_lt _ _ _ (by rw [l2]; omega), ih i hi]
    · have e1 : sg (n + p.length) i = (run (p ++ q.map (sh (n + p.length))) x).length := by rw [l1, sg, if_neg (by omega)]; omega
      have e2 : i = (run (p ++ [g] ++ q) x).length := by rw [l2]; exact h1
      rw [e1, getD_at]
      conv_rhs => rw [e2, getD_at]
      simp only [sh, List.map_map]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      exact ih k (fun e => hh (e ▸ hk))
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1, sg, if_neg (by omega)]; simp; omega),
        List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

theorem indep (w : ℕ) (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ i, i ≠ w → x.getD i false = y.getD i false) : ∀ gs : List Gate, (∀ g ∈ gs, w ∉ g.inputs) →
    ∀ i, i ≠ w → (run gs x).getD i false = (run gs y).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ i hi; simpa [run] using hxy i hi
  | append_singleton gs g ih =>
    intro hg i hi
    have ih := ih (fun h hh => hg h (List.mem_append_left _ hh))
    have hw : w ∉ g.inputs := hg g (by simp)
    rw [run_snoc, run_snoc]
    have l1 : (run gs x).length = x.length + gs.length := run_length gs x
    have l2 : (run gs y).length = x.length + gs.length := by rw [run_length, hl]
    rcases Nat.lt_trichotomy i (x.length + gs.length) with h1 | h1 | h1
    · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega), ih i hi]
    · conv_lhs => rw [show i = (run gs x).length by omega, getD_at]
      conv_rhs => rw [show i = (run gs y).length by omega, getD_at]
      congr 1
      exact List.map_congr_left fun k hk => ih k (fun e => hw (e ▸ hk))
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega), List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

theorem cntp {α : Type} (p : α → Bool) (l : List α) : ∃ S : Finset ℕ, S.card = (l.filter p).length ∧ ∀ j ∈ S, ∃ h : j < l.length, p l[j] = true := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨S, h1, h2⟩ := ih
    have h3 : ∀ j ∈ S, ∃ h : j < (l ++ [a]).length, p (l ++ [a])[j] = true := by
      intro j hj
      obtain ⟨h, hp⟩ := h2 j hj
      exact ⟨by simp; omega, by rw [List.getElem_append_left h]; exact hp⟩
    by_cases ha : p a = true
    · refine ⟨insert l.length S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem, h1]
        · simp [ha]
        · intro hm
          obtain ⟨h, _⟩ := h2 _ hm
          omega
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact ⟨by simp, by simpa using ha⟩
        · exact h3 j hj
    · exact ⟨S, by rw [h1]; simp [ha], h3⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8853

theorem PEqualNP.Outside.L_meta_8853 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∀ x5 ∈ x3, ∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), (∀ (x9 : Fin x1), x9 ≠ x5 → x7 x9 = x8 x9) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x7 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x8) → x3.card + ∑ x6 ∈ x3ᶜ, (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x2.gates).length ≤ x2.size + (1 : ℕ) := by
  intro n C A hm hess
  classical
  let act : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g => List.take (bif g.op.eval [false] then 1 else 2) g.inputs
  have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := fun g hg => by simpa using (hm.1 g hg).1
  have hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hm.1 g hg).2
  let gs : List PEqualNP.CircuitLowerBounds.Gate := C.gates.map fun g => ⟨g.op, act g⟩
  have hrun : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate) (y : List Bool), (∀ g ∈ l, g ∈ C.gates) → PEqualNP.Outside.L_meta_8853.run (l.map fun g => ⟨g.op, act g⟩) y = PEqualNP.Outside.L_meta_8853.run l y := by
    intro l y
    induction l using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton l g ih =>
      intro hl
      rw [List.map_append, List.map_singleton, PEqualNP.Outside.L_meta_8853.run_snoc, PEqualNP.Outside.L_meta_8853.run_snoc, ih fun g' h => hl g' (List.mem_append_left _ h)]
      congr 2
      have hg := hl g (by simp)
      have h2 := hlen g hg
      rcases hops g hg with ho | ho | ho
      · simp only [act, ho]
        rw [show (bif (PEqualNP.CircuitLowerBounds.GateOp.and).eval [false] then 1 else 2) = 2 from rfl, List.take_of_length_le h2]
      · simp only [act, ho]
        rw [show (bif (PEqualNP.CircuitLowerBounds.GateOp.or).eval [false] then 1 else 2) = 2 from rfl, List.take_of_length_le h2]
      · simp only [act, ho]
        rw [show (bif (PEqualNP.CircuitLowerBounds.GateOp.not).eval [false] then 1 else 2) = 1 from rfl]
        rcases g.inputs with _ | ⟨a, l'⟩
        · rfl
        · simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have ev : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = (PEqualNP.Outside.L_meta_8853.run gs (List.ofFn x)).getD C.output false := fun x => by
    rw [show PEqualNP.Outside.L_meta_8853.run gs (List.ofFn x) = PEqualNP.Outside.L_meta_8853.run C.gates (List.ofFn x) from hrun C.gates _ fun _ h => h]
    rfl
  have gl : gs.length = C.gates.length := by simp [gs]
  -- every gate that is not the output is read by some gate
  have rd : ∀ j < C.gates.length, n + j ≠ C.output → ∃ k, ∃ hk : k < C.gates.length, n + j ∈ act C.gates[k] := by
    intro j hj hne
    by_contra hno
    push Not at hno
    have hno : ∀ g ∈ gs, n + j ∉ g.inputs := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg'
      exact hno k hk
    have hj' : j < gs.length := by omega
    let p := gs.take j
    let q := gs.drop (j + 1)
    have hp : p.length = j := by simp [p]; omega
    have hsplit : gs = p ++ [gs[j]] ++ q := by
      simp only [p, q]
      rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨p ++ q.map (PEqualNP.Outside.L_meta_8853.sh (n + p.length)), PEqualNP.Outside.L_meta_8853.sg (n + p.length) C.output⟩
    have hsize : D.size = C.gates.length - 1 := by
      simp only [D, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map, hp, q, List.length_drop, gl]
      omega
    have hgs : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      refine ⟨(hm.1 g' hg').1, ?_⟩
      have := hlen g' hg'
      simp only [act, List.length_take]
      omega
    have hD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hgs g (List.mem_of_mem_take hg)
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
        have := hgs g' (List.mem_of_mem_drop hg')
        exact ⟨this.1, by simpa [PEqualNP.Outside.L_meta_8853.sh] using this.2⟩
    have hDf : PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
      funext x
      rw [ev, hsplit]
      exact PEqualNP.Outside.L_meta_8853.del (List.ofFn x) n (by simp) p gs[j] q (fun h hh => by rw [hp]; exact hno h (List.mem_of_mem_drop hh)) C.output (by rw [hp]; exact hne.symm)
    have := hm.2 D hD hDf
    have h5 : C.size = C.gates.length := rfl
    omega
  have rdA : ∀ a ∈ A, (a : ℕ) ≠ C.output → ∃ k, ∃ hk : k < C.gates.length, (a : ℕ) ∈ act C.gates[k] := by
    intro a ha hne
    by_contra hno
    push Not at hno
    obtain ⟨x, y, hxy, hd⟩ := hess a ha
    apply hd
    rw [ev, ev]
    refine PEqualNP.Outside.L_meta_8853.indep a _ _ (by simp) ?_ gs ?_ _ hne.symm
    · intro i hi
      by_cases hin : i < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn, List.getElem_ofFn]
        exact hxy _ fun e => hi (by rw [← e])
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg'
      exact hno k hk
  -- the reads
  let ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun j => C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
  have hga : ∀ j (hj : j < C.gates.length), ga j = C.gates[j] := fun j hj => by simp [ga, hj]
  let R : Finset (ℕ × ℕ) := (Finset.range C.gates.length).biUnion fun j => (act (ga j)).toFinset.image fun w => (j, w)
  have hR : ∀ j w, (j, w) ∈ R ↔ j < C.gates.length ∧ w ∈ act (ga j) := by
    intro j w
    simp only [R, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.mem_toFinset, Prod.mk.injEq]
    constructor
    · rintro ⟨j', hj', w', hw', rfl, rfl⟩; exact ⟨hj', hw'⟩
    · rintro ⟨h1, h2⟩; exact ⟨j, h1, w, h2, rfl, rfl⟩
  have hRc : R.card ≤ 2 * C.gates.length := by
    refine (Finset.card_biUnion_le_card_mul _ _ 2 fun j hj => ?_).trans (by rw [Finset.card_range]; omega)
    refine Finset.card_image_le.trans ((List.toFinset_card_le _).trans ?_)
    rw [hga j (Finset.mem_range.1 hj)]
    have := hlen _ (List.getElem_mem (Finset.mem_range.1 hj))
    simp only [act, List.length_take]
    omega
  let Nd : Finset ℕ := ((A.map Fin.valEmbedding) ∪ (Finset.range C.gates.length).image fun j => n + j).erase C.output
  have hNd : A.card + C.gates.length ≤ Nd.card + 1 := by
    have h1 : ((A.map Fin.valEmbedding) ∪ (Finset.range C.gates.length).image fun j => n + j).card = A.card + C.gates.length := by
      rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
      rw [Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hw
      obtain ⟨j, _, e⟩ := Finset.mem_image.1 hw'
      have := a.isLt
      have e : n + j = (a : ℕ) := e
      omega
    have h2 := Finset.pred_card_le_card_erase (a := C.output) (s := (A.map Fin.valEmbedding) ∪ (Finset.range C.gates.length).image fun j => n + j)
    change _ ≤ Nd.card at h2
    omega
  have fib : ∀ w ∈ Nd, 1 ≤ (R.filter fun e => e.2 = w).card := by
    intro w hw
    obtain ⟨hne, hw⟩ := Finset.mem_erase.1 hw
    have : ∃ k, ∃ hk : k < C.gates.length, w ∈ act C.gates[k] := by
      rcases Finset.mem_union.1 hw with hw | hw
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hw
        exact rdA a ha hne
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        exact rd j (Finset.mem_range.1 hj) hne
    obtain ⟨k, hk, hkw⟩ := this
    exact Finset.card_pos.2 ⟨(k, w), Finset.mem_filter.2 ⟨(hR k w).2 ⟨hk, by rw [hga k hk]; exact hkw⟩, rfl⟩⟩
  have fib2 : ∀ a : Fin n, (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => (act g).contains (a : ℕ)) C.gates).length ≤ (R.filter fun e => e.2 = (a : ℕ)).card := by
    intro a
    obtain ⟨S, h1, h2⟩ := PEqualNP.Outside.L_meta_8853.cntp (fun g : PEqualNP.CircuitLowerBounds.Gate => (act g).contains (a : ℕ)) C.gates
    rw [← h1]
    refine Finset.card_le_card_of_injOn (fun j => (j, (a : ℕ))) ?_ (fun _ _ _ _ h => (Prod.ext_iff.1 h).1)
    intro j hj
    obtain ⟨hj', hc⟩ := h2 j hj
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(hR j a).2 ⟨hj', by rw [hga j hj']; simpa using hc⟩, rfl⟩)
  let B : Finset ℕ := Aᶜ.map Fin.valEmbedding
  have hdis : Disjoint Nd B := by
    rw [Finset.disjoint_left]
    intro w hw hb
    obtain ⟨b, hb2, rfl⟩ := Finset.mem_map.1 hb
    obtain ⟨_, hw⟩ := Finset.mem_erase.1 hw
    rcases Finset.mem_union.1 hw with hw | hw
    · obtain ⟨a, ha, e⟩ := Finset.mem_map.1 hw
      have : a = b := Fin.ext e
      subst this
      exact (Finset.mem_compl.1 hb2) ha
    · obtain ⟨j, _, e⟩ := Finset.mem_image.1 hw
      have := b.isLt
      have e : n + j = (b : ℕ) := e
      omega
  have tot : ∑ w ∈ Nd ∪ B, (R.filter fun e => e.2 = w).card ≤ R.card := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_card (Finset.biUnion_subset.2 fun w _ => Finset.filter_subset _ _)
    · intro w _ w' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e h1 h2
      exact hne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
  rw [Finset.sum_union hdis] at tot
  have s1 : Nd.card ≤ ∑ w ∈ Nd, (R.filter fun e => e.2 = w).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fib
  have s2 : ∑ a ∈ Aᶜ, (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => (act g).contains (a : ℕ)) C.gates).length ≤ ∑ w ∈ B, (R.filter fun e => e.2 = w).card := by
    rw [Finset.sum_map]
    exact Finset.sum_le_sum fun a _ => fib2 a
  have h5 : C.size = C.gates.length := rfl
  change A.card + ∑ a ∈ Aᶜ, (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => (act g).contains (a : ℕ)) C.gates).length ≤ C.size + 1
  omega
