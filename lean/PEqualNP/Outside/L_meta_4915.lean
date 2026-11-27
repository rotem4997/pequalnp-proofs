import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4915_aux

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C (fun a : Fin n => decide (a = i)) w = true

theorem mem_T {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ (T C w : Finset (Fin n)) ↔ val C (fun a : Fin n => decide (a = i)) w = true := by
  simp [T]

theorem T_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext i
  rw [mem_T]
  have h := val_input C (fun a : Fin n => decide (a = i)) ⟨w, hw⟩
  change val C (fun a : Fin n => decide (a = i)) w = _ at h
  rw [h]
  simp only [decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

theorem T_gate {n : ℕ} (C : Circuit) (hC : IsOrCircuit n C) (p : ℕ) (hp : p < C.gates.length) :
    ∃ a b, a < n + p ∧ b < n + p ∧ (T C (n + p) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hop, hlen, hin⟩ := hC p hp
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  have hor : (C.gates[p]).op = GateOp.or := by
    generalize (C.gates[p]).op = o at hop
    cases o <;> first | rfl | (simp [isOrOp] at hop)
  obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p]).inputs = [a, b] := by
    match h : (C.gates[p]).inputs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have ha : a < n + p := hin a (by simp [hab])
  have hb : b < n + p := hin b (by simp [hab])
  refine ⟨a, b, ha, hb, ?_⟩
  ext i
  rw [Finset.mem_union, mem_T, mem_T, mem_T, val_gate C _ hg, hor, hab]
  simp [GateOp.eval, operand, ha, hb]

theorem T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp

def cenS {n : ℕ} (p : Block n) : Finset (Fin n) := if p.1.card = 1 then p.1 else p.2

def leaf {n : ℕ} (p : Block n) : Finset (Fin n) := if p.1.card = 1 then p.2 else p.1

theorem star_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hN : PEqualNP.TopForm.NoFourCycle G) (p : Block n) (hp : IsBlock G p) :
    (cenS p).card = 1 ∧ (leaf p).Nonempty ∧ (∀ c ∈ cenS p, ∀ u ∈ leaf p, G.Adj c u) := by
  obtain ⟨hd, h1, h2, hadj⟩ := hp
  unfold cenS leaf
  by_cases hc : p.1.card = 1
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact ⟨hc, h2, hadj⟩
  · rw [ite_eq_right hc, ite_eq_right hc]
    refine ⟨?_, h1, fun c hc' u hu => (hadj u hu c hc').symm⟩
    have h1' : 1 < p.1.card := by
      have := h1.card_pos
      omega
    obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.1 h1'
    have hle := hN a1 a2 hne
    have hsub : p.2.card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hle
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj a1 ha1 b hb, hadj a2 ha2 b hb⟩
    have := h2.card_pos
    omega

theorem leaf_mem_sides {n : ℕ} (F : Finset (Block n)) (p : Block n) (hp : p ∈ F) :
    leaf p ∈ sides F := by
  unfold leaf sides
  by_cases hc : p.1.card = 1
  · rw [ite_eq_left hc]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  · rw [ite_eq_right hc]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)

theorem covers_star {n : ℕ} (p : Block n) (u v : Fin n) (h : BlockCovers p u v) :
    (u ∈ cenS p ∧ v ∈ leaf p) ∨ (v ∈ cenS p ∧ u ∈ leaf p) := by
  unfold BlockCovers at h
  unfold cenS leaf
  by_cases hc : p.1.card = 1
  · rw [ite_eq_left hc, ite_eq_left hc]; exact h
  · rw [ite_eq_right hc, ite_eq_right hc]; tauto

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (c u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ t ∈ (T C (n + j) : Finset (Fin n)), G.Adj c t) ∧
    u ∈ (T C (n + j) : Finset (Fin n)) ∧ ∃ u0 ∈ (T C (n + j) : Finset (Fin n)), u0 < u

theorem no_below {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (c u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j)
    (hadj : ∀ t ∈ (T C a : Finset (Fin n)), G.Adj c t) (hu : u ∈ (T C a : Finset (Fin n)))
    (hmin : ∀ j', j' < j → ¬ Good G C c u j') : ∀ t ∈ (T C a : Finset (Fin n)), ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j', rfl⟩ : ∃ j', a = n + j' := ⟨a - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hadj, hu, t, ht, hlt⟩

theorem no_lt_aux {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (c u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j) (hb : b < n + j)
    (hT : (T C (n + j) : Finset (Fin n)) = T C a ∪ T C b)
    (hg : Good G C c u j)
    (hmin : ∀ j', j' < j → ¬ Good G C c u j') (hmin' : ∀ j', j' < j → ¬ Good G C c u' j')
    (hlt : u < u') (hu'a : u' ∈ (T C a : Finset (Fin n))) : False := by
  obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
  have hadja : ∀ t ∈ (T C a : Finset (Fin n)), G.Adj c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hadjb : ∀ t ∈ (T C b : Finset (Fin n)), G.Adj c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := no_below G C c u' j a hj ha hadja hu'a hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below G C c u j b hj hb hadjb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

theorem no_lt {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (hC : IsOrCircuit n C)
    (c u u' : Fin n) (j : ℕ) (hg : Good G C c u j) (hg' : Good G C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good G C c u j') (hmin' : ∀ j', j' < j → ¬ Good G C c u' j')
    (hlt : u < u') : False := by
  have hj := hg.1
  obtain ⟨a, b, ha, hb, hT⟩ := T_gate C hC j hj
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux G C c u u' j a b hj ha hb hT hg hmin hmin' hlt h
  · exact no_lt_aux G C c u u' j b a hj hb ha (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

theorem inj_core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hN : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (hC : IsOrCircuit n C)
    (c u c' u' : Fin n) (j : ℕ) (hg : Good G C c u j) (hg' : Good G C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good G C c u j') (hmin' : ∀ j', j' < j → ¬ Good G C c' u' j') :
    c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
    have hle := hN u0 u (ne_of_lt hu0lt)
    refine Finset.card_le_one.1 hle c ?_ c' ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hadj u0 hu0).symm, (hadj u hu).symm⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hg'.2.1 u0 hu0).symm, (hg'.2.1 u hu).symm⟩
  subst hcc
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt G C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt G C hC c u' u j hg' hg hmin' hmin h).elim

theorem leaf_min {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (F : Finset (Block n))
    (hS : ∀ s ∈ sides F, ∃ w < n + C.gates.length, ComputesOr n C w s)
    (p : Block n) (hp : p ∈ F) (c u : Fin n)
    (hadj : ∀ t ∈ leaf p, G.Adj c t) (hu : u ∈ leaf p)
    (hng : ¬ ∃ j, Good G C c u j) : ∀ t ∈ leaf p, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hcomp⟩ := hS (leaf p) (leaf_mem_sides F p hp)
  have hT := T_computes C w (leaf p) hcomp
  by_cases hwn : w < n
  · rw [← hT, T_input C w hwn, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT]; exact hadj, by rw [hT]; exact hu, t,
      by rw [hT]; exact ht, hlt⟩

theorem count_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hN : PEqualNP.TopForm.NoFourCycle G) (C : Circuit) (hC : IsOrCircuit n C)
    (F : Finset (Block n)) (hF : ∀ p ∈ F, IsBlock G p)
    (hS : ∀ s ∈ sides F, ∃ w < n + C.gates.length, ComputesOr n C w s)
    (P : Finset (Σ _ : Fin n, Fin n))
    (hP : ∀ q ∈ P, ∃ p ∈ F, q.1 ∈ cenS p ∧ q.2 ∈ leaf p) :
    P.card ≤ C.gates.length + F.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good G C q.1 q.2 j).card ≤ C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    refine Finset.card_le_card_of_forall_subsingleton
      (fun q j => Good G C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good G C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_range.2 (Nat.find_spec hex).1
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core G hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good G C q.1 q.2 j).card ≤ F.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun q p => q.1 ∈ cenS p ∧ q.2 ∈ leaf p) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro p hp q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      obtain ⟨hcard, _, hadj⟩ := star_facts G hN p (hF p hp)
      have hcc : c = c' := Finset.card_le_one.1 (le_of_eq hcard) c hqc c' hqc'
      subst hcc
      have h1 := leaf_min G C F hS p hp c u (hadj c hqc) hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min G C F hS p hp c u' (hadj c hqc) hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good G C q.1 q.2 j)
  omega

def centres {n : ℕ} (F : Finset (Block n)) : Finset (Fin n) := F.biUnion cenS

def U {n : ℕ} (F : Finset (Block n)) (c : Fin n) : Finset (Fin n) :=
  (F.filter fun p => c ∈ cenS p).biUnion leaf

theorem mem_U {n : ℕ} (F : Finset (Block n)) (c u : Fin n) :
    u ∈ U F c ↔ ∃ p ∈ F, c ∈ cenS p ∧ u ∈ leaf p := by
  simp only [U, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, hu⟩; exact ⟨p, hp, hc, hu⟩
  · rintro ⟨p, hp, hc, hu⟩; exact ⟨p, ⟨hp, hc⟩, hu⟩

theorem mem_centres {n : ℕ} (F : Finset (Block n)) (c : Fin n) :
    c ∈ centres F ↔ ∃ p ∈ F, c ∈ cenS p := by
  simp only [centres, Finset.mem_biUnion]

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ)
    (hN : PEqualNP.TopForm.NoFourCycle G) (h : HasSharedBlockCost G m) : HasBlockCost G m := by
  obtain ⟨F, ⟨hF, hcov⟩, k, ⟨C, ⟨hC, hS⟩, hlen⟩, hk⟩ := h
  refine ⟨(centres F).image fun c => (({c} : Finset (Fin n)), U F c), ⟨?_, ?_⟩, ?_⟩
  · intro p' hp'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp'
    obtain ⟨p, hp, hcp⟩ := (mem_centres F c).1 hc
    obtain ⟨_, ⟨u, hu⟩, _⟩ := star_facts G hN p (hF p hp)
    refine ⟨?_, Finset.singleton_nonempty c, ⟨u, (mem_U F c u).2 ⟨p, hp, hcp, hu⟩⟩, ?_⟩
    · rw [Finset.disjoint_singleton_left]
      intro hcc
      obtain ⟨p2, hp2, hc2, hu2⟩ := (mem_U F c c).1 hcc
      exact G.ne_of_adj ((star_facts G hN p2 (hF p2 hp2)).2.2 c hc2 c hu2) rfl
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha
      subst ha
      obtain ⟨p2, hp2, hc2, hu2⟩ := (mem_U F a b).1 hb
      exact (star_facts G hN p2 (hF p2 hp2)).2.2 a hc2 b hu2
  · intro u v huv
    obtain ⟨p, hp, hcv⟩ := hcov u v huv
    rcases covers_star p u v hcv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(({u} : Finset (Fin n)), U F u),
        Finset.mem_image.2 ⟨u, (mem_centres F u).2 ⟨p, hp, h1⟩, rfl⟩,
        Or.inl ⟨Finset.mem_singleton_self u, (mem_U F u v).2 ⟨p, hp, h1, h2⟩⟩⟩
    · exact ⟨(({v} : Finset (Fin n)), U F v),
        Finset.mem_image.2 ⟨v, (mem_centres F v).2 ⟨p, hp, h1⟩, rfl⟩,
        Or.inr ⟨Finset.mem_singleton_self v, (mem_U F v u).2 ⟨p, hp, h1, h2⟩⟩⟩
  · unfold familyCost
    have hsum : ∑ p' ∈ (centres F).image (fun c => (({c} : Finset (Fin n)), U F c)),
        blockCost p' = ((centres F).sigma (U F)).card := by
      rw [Finset.sum_image (fun c _ c' _ hcc => Finset.singleton_injective (Prod.mk.inj hcc).1),
        Finset.card_sigma]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [blockCost]
    have hcard : ((centres F).image fun c => (({c} : Finset (Fin n)), U F c)).card ≤ F.card := by
      refine le_trans Finset.card_image_le ?_
      refine le_trans Finset.card_biUnion_le ?_
      have h1 : ∀ p ∈ F, (cenS p).card = 1 := fun p hp => (star_facts G hN p (hF p hp)).1
      rw [Finset.sum_congr rfl h1]
      simp
    have hP := count_le G hN C hC F hF hS ((centres F).sigma (U F)) (by
      intro q hq
      obtain ⟨_, hq2⟩ := Finset.mem_sigma.1 hq
      exact (mem_U F q.1 q.2).1 hq2)
    rw [hsum]
    omega

end PEqualNP.Outside.L_meta_4915_aux

theorem PEqualNP.Outside.L_meta_4915 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4 := by
  intro x1 x2 _ x4 h1 h2
  exact PEqualNP.Outside.L_meta_4915_aux.main x2 x4 h1 h2
