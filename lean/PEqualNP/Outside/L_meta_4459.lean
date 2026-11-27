import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4459

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (G : List Gate) (x : List Bool) : List Bool := G.foldl stp x

lemma W_append (G H : List Gate) (x : List Bool) : W (G ++ H) x = W H (W G x) := by
  simp [W, List.foldl_append]

lemma W_single (G : List Gate) (g : Gate) (x : List Bool) :
    W (G ++ [g]) x = W G x ++ [g.op.eval (g.inputs.map fun i => (W G x).getD i false)] := by
  simp [W, List.foldl_append, stp]

lemma W_getD (H : List Gate) (l : List Bool) (i : ℕ) (hi : i < l.length) :
    (W H l).getD i false = l.getD i false := by
  induction H generalizing l with
  | nil => rfl
  | cons g H ih =>
    have e : W (g :: H) l = W H (stp l g) := rfl
    rw [e, ih _ (by simp [stp]; omega)]
    simp only [stp]
    exact List.getD_append _ _ _ _ hi

lemma W_length (G : List Gate) (l : List Bool) : (W G l).length = l.length + G.length := by
  induction G generalizing l with
  | nil => simp [W]
  | cons g G ih =>
    have e : W (g :: G) l = W G (stp l g) := rfl
    rw [e, ih]
    simp [stp]
    omega

def Comp (n : ℕ) (G : List Gate) (w : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD w false = F x

def Build (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ P : List Gate, ∃ H : List Gate, H.length ≤ s ∧
    (∀ g ∈ H, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ∃ w, w < n + (P ++ H).length ∧ Comp n (P ++ H) w F

lemma Comp.extend {n : ℕ} {G : List Gate} {w : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Comp n G w F) (hw : w < n + G.length) (H : List Gate) : Comp n (G ++ H) w F := by
  intro x
  rw [W_append, W_getD H _ _ (by rw [W_length]; simp; omega)]
  exact h x

lemma Build.var {n : ℕ} (i : Fin n) : Build n (fun x => x i) 0 := by
  intro P
  refine ⟨[], by simp, by simp, i, by have := i.isLt; simp only [List.append_nil]; omega, ?_⟩
  intro x
  rw [List.append_nil, W_getD P _ _ (by simp)]
  simp

lemma Build.congr {n : ℕ} {F F' : (Fin n → Bool) → Bool} {s : ℕ} (h : Build n F s)
    (e : ∀ x, F x = F' x) : Build n F' s := by
  have : F = F' := funext e
  subst this
  exact h

lemma Build.mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Build n F s)
    (hs : s ≤ s') : Build n F s' := by
  intro P
  obtain ⟨H, hl, hf, hw⟩ := h P
  exact ⟨H, hl.trans hs, hf, hw⟩

lemma Build.bin {n : ℕ} (op : GateOp) (f : Bool → Bool → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hf : ∀ a b, op.eval [a, b] = f a b)
    {F1 F2 : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (h1 : Build n F1 s1) (h2 : Build n F2 s2) :
    Build n (fun x => f (F1 x) (F2 x)) (s1 + s2 + 1) := by
  intro P
  obtain ⟨H1, hl1, hf1, w1, hw1, hc1⟩ := h1 P
  obtain ⟨H2, hl2, hf2, w2, hw2, hc2⟩ := h2 (P ++ H1)
  refine ⟨H1 ++ H2 ++ [{ op := op, inputs := [w1, w2] }], ?_, ?_,
    n + (P ++ H1 ++ H2).length, ?_, ?_⟩
  · simp; omega
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact hf1 g hg
    · exact hf2 g hg
    · subst hg
      exact ⟨hop, by simp⟩
  · simp
  · intro x
    have e : P ++ (H1 ++ H2 ++ [{ op := op, inputs := [w1, w2] }])
        = (P ++ H1 ++ H2) ++ [{ op := op, inputs := [w1, w2] }] := by simp
    rw [e, W_single]
    have hlen : (W (P ++ H1 ++ H2) (List.ofFn x)).length = n + (P ++ H1 ++ H2).length := by
      rw [W_length]; simp
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
    have c1 : (W (P ++ H1 ++ H2) (List.ofFn x)).getD w1 false = F1 x :=
      (hc1.extend hw1 H2) x
    have c2 : (W (P ++ H1 ++ H2) (List.ofFn x)).getD w2 false = F2 x := hc2 x
    dsimp only
    simp only [List.getD_cons_zero, List.map_cons, List.map_nil, c1, c2, hf]

lemma Build.or {n : ℕ} {F1 F2 : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (h1 : Build n F1 s1) (h2 : Build n F2 s2) :
    Build n (fun x => F1 x || F2 x) (s1 + s2 + 1) :=
  Build.bin GateOp.or (fun a b => a || b) (Or.inr rfl) (by intro a b; simp [GateOp.eval]) h1 h2

lemma Build.and {n : ℕ} {F1 F2 : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (h1 : Build n F1 s1) (h2 : Build n F2 s2) :
    Build n (fun x => F1 x && F2 x) (s1 + s2 + 1) :=
  Build.bin GateOp.and (fun a b => a && b) (Or.inl rfl) (by intro a b; simp [GateOp.eval]) h1 h2

lemma Build.orOver {n : ℕ} {α : Type*} [DecidableEq α] (S : Finset α)
    (g : α → (Fin n → Bool) → Bool) (k : ℕ)
    (hg : ∀ a ∈ S, Build n (g a) k) (hS : S.Nonempty) :
    Build n (fun x => decide (∃ a ∈ S, g a x = true)) ((S.card - 1) + S.card * k) := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS (by simp)
  | insert a s has ih =>
    by_cases hs : s = ∅
    · subst hs
      refine ((hg a (by simp)).congr (fun x => by simp)).mono ?_
      simp
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      have h1 := ih (fun b hb => hg b (Finset.mem_insert_of_mem hb)) hne
      have h2 := Build.or (hg a (Finset.mem_insert_self a s)) h1
      refine (h2.congr (fun x => ?_)).mono ?_
      · simp [Finset.mem_insert, exists_eq_or_imp]
      · rw [Finset.card_insert_of_notMem has]
        have := hne.card_pos
        have e : (s.card + 1) * k = s.card * k + k := by ring
        omega

lemma Build.hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Build n F s) :
    HasCircuitSize n F s := by
  obtain ⟨H, hl, hf, w, hw, hc⟩ := h []
  refine ⟨⟨H, w⟩, ?_, hl, ?_⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hf g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 <;> simp [h1]
  · intro x
    exact hc x

theorem core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (c : Fin n → Fin 2) (hc : ∀ u v, G.Adj u v → c u ≠ c v) (i : Fin 2)
    (hdeg : ∀ v ∉ T, (G.neighborSet v).ncard = 3) (hT : ∀ u v, G.Adj u v → u ∉ T)
    (hedge : ∃ u v, G.Adj u v)
    (hle : (Finset.filter (fun v => c v = i) Tᶜ).card ≤
      (Finset.filter (fun v => ¬ c v = i) Tᶜ).card) :
    ∃ a b, a ∉ T ∧ b ∉ T ∧ a ≠ b ∧ ¬ G.Adj a b ∧ ∃ s, s + 8 ≤ 2 * (n - T.card) - 1 ∧
      HasCircuitSize n (fun x => NestedCover.graphFun G ∅
        (Function.update (Function.update x a false) b false)) s := by
  set P := Finset.filter (fun v => c v = i) Tᶜ with hP
  set Q := Finset.filter (fun v => ¬ c v = i) Tᶜ with hQ
  have hmemP : ∀ v, v ∈ P ↔ v ∉ T ∧ c v = i := by intro v; simp [hP]
  have hmemQ : ∀ v, v ∈ Q ↔ v ∉ T ∧ ¬ c v = i := by intro v; simp [hQ]
  have two : ∀ y z j : Fin 2, y ≠ z → y ≠ j → z = j := by decide
  have hcard : ∀ v ∉ T, (G.neighborFinset v).card = 3 := by
    intro v hv
    have := hdeg v hv
    rwa [← G.coe_neighborFinset v, Set.ncard_coe_finset] at this
  obtain ⟨u, v, huv⟩ := hedge
  have huT := hT u v huv
  have hvT := hT v u huv.symm
  obtain ⟨q, hq⟩ : ∃ q, q ∈ Q := by
    by_cases h : c u = i
    · exact ⟨v, (hmemQ v).2 ⟨hvT, fun h' => hc u v huv (h.trans h'.symm)⟩⟩
    · exact ⟨u, (hmemQ u).2 ⟨huT, h⟩⟩
  have hq' := (hmemQ q).1 hq
  have hsub : G.neighborFinset q ⊆ P := by
    intro r hr
    rw [SimpleGraph.mem_neighborFinset] at hr
    exact (hmemP r).2 ⟨hT r q hr.symm, two _ _ _ (hc q r hr) hq'.2⟩
  have hP3 : 3 ≤ P.card := by
    have := Finset.card_le_card hsub
    rw [hcard q hq'.1] at this
    exact this
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have ha' := (hmemP a).1 ha
  have hb' := (hmemP b).1 hb
  have hnadj : ¬ G.Adj a b := fun h => hc a b h (ha'.2.trans hb'.2.symm)
  set P' := (P.erase a).erase b with hP'
  have hmemP' : ∀ v, v ∈ P' ↔ v ≠ b ∧ v ≠ a ∧ v ∈ P := by
    intro v; simp [hP', Finset.mem_erase]
  have hcard' : P'.card + 2 = P.card := by
    rw [hP', Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha]
    omega
  let g : Fin n → (Fin n → Bool) → Bool := fun p x =>
    x p && decide (∃ q ∈ G.neighborFinset p, x q = true)
  have hstar : ∀ p ∈ P', Build n (g p) 3 := by
    intro p hp
    have hpP := ((hmemP' p).1 hp).2.2
    have hpT := ((hmemP p).1 hpP).1
    have hN := hcard p hpT
    have hne : (G.neighborFinset p).Nonempty := by
      rw [← Finset.card_pos]; omega
    have h1 := Build.orOver (G.neighborFinset p) (fun q x => x q) 0
      (fun q _ => Build.var q) hne
    have h2 := Build.and (Build.var p) h1
    refine (h2.congr (fun x => ?_)).mono ?_
    · rw [Bool.eq_iff_iff]
      simp [g]
    · simp [hN]
  have hne' : P'.Nonempty := by rw [← Finset.card_pos]; omega
  have hbuild := Build.orOver P' g 3 hstar hne'
  have hfun : ∀ x : Fin n → Bool, NestedCover.graphFun G ∅
      (Function.update (Function.update x a false) b false) = true ↔
      ∃ p ∈ P', g p x = true := by
    intro x
    set y := Function.update (Function.update x a false) b false with hy
    have hyv : ∀ v, y v = if v = b then false else if v = a then false else x v := by
      intro v; simp [hy, Function.update_apply]
    have hy1 : ∀ v, y v = true → x v = true ∧ v ≠ a ∧ v ≠ b := by
      intro v hv
      rw [hyv v] at hv
      by_cases hvb : v = b
      · simp [hvb] at hv
      · by_cases hva : v = a
        · simp [hvb, hva] at hv
        · simp [hvb, hva] at hv
          exact ⟨hv, hva, hvb⟩
    have hy2 : ∀ v, v ≠ a → v ≠ b → y v = x v := by
      intro v hva hvb
      rw [hyv v]
      simp [hva, hvb]
    unfold NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
      false_or]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      by_cases hcu : c u = i
      · obtain ⟨hxu, hua, hub⟩ := hy1 u hu
        obtain ⟨hxv, _, _⟩ := hy1 v hv
        refine ⟨u, (hmemP' u).2 ⟨hub, hua, (hmemP u).2 ⟨hT u v huv, hcu⟩⟩, ?_⟩
        simp only [g, Bool.and_eq_true, decide_eq_true_eq, SimpleGraph.mem_neighborFinset]
        exact ⟨hxu, v, huv, hxv⟩
      · have hcv : c v = i := two _ _ _ (hc u v huv) hcu
        obtain ⟨hxu, _, _⟩ := hy1 u hu
        obtain ⟨hxv, hva, hvb⟩ := hy1 v hv
        refine ⟨v, (hmemP' v).2 ⟨hvb, hva, (hmemP v).2 ⟨hT v u huv.symm, hcv⟩⟩, ?_⟩
        simp only [g, Bool.and_eq_true, decide_eq_true_eq, SimpleGraph.mem_neighborFinset]
        exact ⟨hxv, u, huv.symm, hxu⟩
    · rintro ⟨p, hp, hpx⟩
      simp only [g, Bool.and_eq_true, decide_eq_true_eq, SimpleGraph.mem_neighborFinset] at hpx
      obtain ⟨hxp, q, hpq, hxq⟩ := hpx
      obtain ⟨hpb, hpa, hpP⟩ := (hmemP' p).1 hp
      have hcp := ((hmemP p).1 hpP).2
      have hqa : q ≠ a := by
        intro h
        rw [h] at hpq
        exact hc p a hpq (hcp.trans ha'.2.symm)
      have hqb : q ≠ b := by
        intro h
        rw [h] at hpq
        exact hc p b hpq (hcp.trans hb'.2.symm)
      refine ⟨p, q, hpq, ?_, ?_⟩
      · rw [hy2 p hpa hpb]; exact hxp
      · rw [hy2 q hqa hqb]; exact hxq
  have hN : n - T.card = P.card + Q.card := by
    have h1 : P.card + Q.card = (Tᶜ).card :=
      Finset.card_filter_add_card_filter_not (s := Tᶜ) (fun v => c v = i)
    have h2 : (Tᶜ).card = n - T.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    omega
  refine ⟨a, b, ha'.1, hb'.1, hab, hnadj, (P'.card - 1) + P'.card * 3, ?_, ?_⟩
  · omega
  · obtain ⟨C, h1, h2, h3⟩ := hbuild.hasCircuitSize
    refine ⟨C, h1, h2, fun x => ?_⟩
    rw [h3 x, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    exact (hfun x).symm

end PEqualNP.Outside.L_meta_4459

open PEqualNP.Outside.L_meta_4459 in
theorem PEqualNP.Outside.L_meta_4459 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∃ (x10 : Fin x1) (x11 : Fin x1), x10 ∉ x4 ∧ x11 ∉ x4 ∧ x10 ≠ x11 ∧ ¬x2.Adj x10 x11 ∧ ∃ (x12 : ℕ), x12 + (8 : ℕ) ≤ (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x13 x10 Bool.false) x11 Bool.false)) x12 := by
  intro n G inst T hcol hdeg _ hT hedge
  obtain ⟨col⟩ := hcol
  have hc : ∀ u v, G.Adj u v → col u ≠ col v := fun u v h => col.valid h
  by_cases h : (Finset.filter (fun v => col v = 0) Tᶜ).card ≤
      (Finset.filter (fun v => ¬ col v = 0) Tᶜ).card
  · exact core G T col hc 0 hdeg hT hedge h
  · refine core G T col hc 1 hdeg hT hedge ?_
    have f1 : ∀ y : Fin 2, (y = 1 ↔ ¬ y = 0) := by decide
    have f2 : ∀ y : Fin 2, (¬ y = 1 ↔ y = 0) := by decide
    have e1 : Finset.filter (fun v => col v = 1) Tᶜ = Finset.filter (fun v => ¬ col v = 0) Tᶜ :=
      Finset.filter_congr (fun v _ => f1 (col v))
    have e2 : Finset.filter (fun v => ¬ col v = 1) Tᶜ = Finset.filter (fun v => col v = 0) Tᶜ :=
      Finset.filter_congr (fun v _ => f2 (col v))
    rw [e1, e2]
    omega
