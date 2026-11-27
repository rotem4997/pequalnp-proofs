import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4863

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

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


def ok (gs : List Gate) : Prop := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Q (n : ℕ) (gs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  w < n + gs.length ∧ ∀ x, (run gs (List.ofFn x)).getD w false = f x

theorem q_app (n : ℕ) (gs hs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool) (h : Q n gs w f) :
    Q n (gs ++ hs) w f := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [run_prefix _ _ _ _ (by simpa using h.1)]
  exact h.2 x

theorem q_in (n : ℕ) (gs : List Gate) (c : Fin n) : Q n gs c.val fun x => x c := by
  refine ⟨by have := c.isLt; omega, fun x => ?_⟩
  rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem q_op (n : ℕ) (gs : List Gate) (hok : ok gs) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or)
    (u v : ℕ) (f g : (Fin n → Bool) → Bool) (hu : Q n gs u f) (hv : Q n gs v g) :
    ok (gs ++ [⟨o, [u, v]⟩]) ∧ Q n (gs ++ [⟨o, [u, v]⟩]) (n + gs.length) fun x => o.eval [f x, g x] := by
  refine ⟨fun a ha => ?_, by simp, fun x => ?_⟩
  · rcases List.mem_append.1 ha with h | h
    · exact hok a h
    · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
  · rw [run_snoc, getD_sn, if_pos (by rw [run_length, List.length_ofFn])]
    simp only [List.map_cons, List.map_nil, hu.2 x, hv.2 x]

theorem orN (n : ℕ) (N : Finset (Fin n)) (hN : N.Nonempty) : ∀ gs, ok gs →
    ∃ hs w, ok (gs ++ hs) ∧ hs.length + 1 = N.card ∧
      Q n (gs ++ hs) w fun x => decide (∃ u ∈ N, x u = true) := by
  induction hN using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro gs hok
    refine ⟨[], a.val, by simpa using hok, by simp, ?_⟩
    have := q_in n gs a
    simpa using this
  | cons a N ha hN ih =>
    intro gs hok
    obtain ⟨hs, w, h1, h2, h3⟩ := ih gs hok
    obtain ⟨k1, k2⟩ := q_op n (gs ++ hs) h1 GateOp.or (Or.inr rfl) a.val w _ _ (q_in n _ a) h3
    refine ⟨hs ++ [⟨GateOp.or, [a.val, w]⟩], n + (gs ++ hs).length,
      by rw [← List.append_assoc]; exact k1, by rw [Finset.card_cons, ← h2]; simp, ?_⟩
    have e : (fun x : Fin n → Bool => decide (∃ u ∈ Finset.cons a N ha, x u = true)) =
        fun x => GateOp.or.eval [x a, decide (∃ u ∈ N, x u = true)] := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [GateOp.eval]
    rw [e, ← List.append_assoc]
    exact k2

theorem star (n : ℕ) (c : Fin n) (N : Finset (Fin n)) (hN : N.Nonempty) (gs : List Gate) (hok : ok gs) :
    ∃ hs w, ok (gs ++ hs) ∧ hs.length = N.card ∧
      Q n (gs ++ hs) w fun x => x c && decide (∃ u ∈ N, x u = true) := by
  obtain ⟨hs, w, h1, h2, h3⟩ := orN n N hN gs hok
  obtain ⟨k1, k2⟩ := q_op n (gs ++ hs) h1 GateOp.and (Or.inl rfl) c.val w _ _ (q_in n _ c) h3
  refine ⟨hs ++ [⟨GateOp.and, [c.val, w]⟩], n + (gs ++ hs).length,
    by rw [← List.append_assoc]; exact k1, by rw [← h2]; simp, ?_⟩
  have e : (fun x : Fin n → Bool => x c && decide (∃ u ∈ N, x u = true)) =
      fun x => GateOp.and.eval [x c, decide (∃ u ∈ N, x u = true)] := by
    funext x
    simp [GateOp.eval]
  rw [e, ← List.append_assoc]
  exact k2

theorem stars (n : ℕ) (N : Fin n → Finset (Fin n)) (S : Finset (Fin n)) :
    (∀ c ∈ S, N c = ∅) ∨ ∃ gs w, ok gs ∧ gs.length + 1 ≤ ∑ c ∈ S, ((N c).card + 1) ∧
      Q n gs w fun x => decide (∃ c ∈ S, x c = true ∧ ∃ u ∈ N c, x u = true) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a S ha ih =>
    rcases Finset.eq_empty_or_nonempty (N a) with h | h
    · rcases ih with ih | ⟨gs, w, h1, h2, h3⟩
      · refine Or.inl fun c hc => ?_
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact h
        · exact ih c hc
      · refine Or.inr ⟨gs, w, h1, ?_, ?_⟩
        · rw [Finset.sum_insert ha]; omega
        · have e : (fun x : Fin n → Bool => decide (∃ c ∈ insert a S, x c = true ∧
              ∃ u ∈ N c, x u = true)) = fun x => decide (∃ c ∈ S, x c = true ∧ ∃ u ∈ N c, x u = true) := by
            funext x
            rw [Bool.eq_iff_iff]
            simp [h]
          rw [e]; exact h3
    · rcases ih with ih | ⟨gs, w, h1, h2, h3⟩
      · obtain ⟨hs, w, k1, k2, k3⟩ := star n a (N a) h [] (by intro g hg; simp at hg)
        refine Or.inr ⟨hs, w, by simpa using k1, ?_, ?_⟩
        · rw [Finset.sum_insert ha, k2]; omega
        · have e : (fun x : Fin n → Bool => decide (∃ c ∈ insert a S, x c = true ∧
              ∃ u ∈ N c, x u = true)) = fun x => x a && decide (∃ u ∈ N a, x u = true) := by
            funext x
            rw [Bool.eq_iff_iff]
            simp only [decide_eq_true_eq, Bool.and_eq_true]
            constructor
            · rintro ⟨c, hc, hx, u, hu, hxu⟩
              rcases Finset.mem_insert.1 hc with rfl | hc
              · exact ⟨hx, u, hu, hxu⟩
              · rw [ih c hc] at hu
                simp at hu
            · rintro ⟨hx, u, hu, hxu⟩
              exact ⟨a, Finset.mem_insert_self _ _, hx, u, hu, hxu⟩
          rw [e]; simpa using k3
      · obtain ⟨hs, v, k1, k2, k3⟩ := star n a (N a) h gs h1
        obtain ⟨l1, l2⟩ := q_op n (gs ++ hs) k1 GateOp.or (Or.inr rfl) v w _ _ k3 (q_app n gs hs w _ h3)
        refine Or.inr ⟨gs ++ hs ++ [⟨GateOp.or, [v, w]⟩], n + (gs ++ hs).length, l1, ?_, ?_⟩
        · rw [Finset.sum_insert ha]
          simp only [List.length_append, List.length_singleton]
          omega
        · have e : (fun x : Fin n → Bool => decide (∃ c ∈ insert a S, x c = true ∧
              ∃ u ∈ N c, x u = true)) = fun x => GateOp.or.eval [x a && decide (∃ u ∈ N a, x u = true),
              decide (∃ c ∈ S, x c = true ∧ ∃ u ∈ N c, x u = true)] := by
            funext x
            rw [Bool.eq_iff_iff]
            simp [GateOp.eval, Finset.exists_mem_insert]
          rw [e]; exact l2

theorem ors (n : ℕ) (A : Finset (Fin n)) (gs : List Gate) (w : ℕ) (f : (Fin n → Bool) → Bool)
    (hok : ok gs) (h : Q n gs w f) : ∃ hs v, ok hs ∧ hs.length = gs.length + A.card ∧
      Q n hs v fun x => decide (∃ a ∈ A, x a = true) || f x := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨gs, w, hok, by simp, by simpa using h⟩
  | insert a A ha ih =>
    obtain ⟨hs, v, h1, h2, h3⟩ := ih
    obtain ⟨k1, k2⟩ := q_op n hs h1 GateOp.or (Or.inr rfl) a.val v _ _ (q_in n _ a) h3
    refine ⟨hs ++ [⟨GateOp.or, [a.val, v]⟩], n + hs.length, k1,
      by rw [Finset.card_insert_of_notMem ha, List.length_append, h2]; simp; omega, ?_⟩
    have e : (fun x : Fin n → Bool => decide (∃ b ∈ insert a A, x b = true) || f x) =
        fun x => GateOp.or.eval [x a, decide (∃ b ∈ A, x b = true) || f x] := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [GateOp.eval, Finset.exists_mem_insert, or_assoc]
    rw [e]; exact k2

def Nb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)) (t c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => G.Adj c v ∧ v ≠ t ∧ (v ∉ T ∨ c < v)

theorem count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (t : Fin n) (hdeg : (G.neighborSet t).ncard = 3) :
    ∑ c ∈ T.erase t, (Nb G T t c).card + 3 ≤ G.edgeFinset.card := by
  classical
  let M := (T.erase t).sigma fun c => Nb G T t c
  let e1 := M.image fun p : (_ : Fin n) × Fin n => s(p.1, p.2)
  let e2 := (G.neighborFinset t).image fun v => s(t, v)
  have hM : M.card = ∑ c ∈ T.erase t, (Nb G T t c).card := Finset.card_sigma _ _
  have i1 : e1.card = M.card := by
    refine Finset.card_image_of_injOn ?_
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
    obtain ⟨hc, hd⟩ := Finset.mem_sigma.1 (Finset.mem_coe.1 hq)
    have hb' := (Finset.mem_filter.1 hb).2
    have hd' := (Finset.mem_filter.1 hd).2
    dsimp only at ha hb' hc hd' h
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · rfl
    · exfalso
      subst h1 h2
      have l1 : a < b := hb'.2.2.resolve_left fun h => h (Finset.mem_of_mem_erase hc)
      have l2 : b < a := hd'.2.2.resolve_left fun h => h (Finset.mem_of_mem_erase ha)
      exact lt_asymm l1 l2
  have i2 : e2.card = 3 := by
    rw [Finset.card_image_of_injective _ fun a b h => by
      rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1]
    rw [← hdeg, ← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
  have hdis : Disjoint e1 e2 := by
    refine Finset.disjoint_left.2 fun x h1 h2 => ?_
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.1 hp
    have hat : a ≠ t := Finset.ne_of_mem_erase ha
    have hbt : b ≠ t := (Finset.mem_filter.1 hb).2.2.1
    rcases Sym2.eq_iff.1 hv with ⟨h, _⟩ | ⟨h, _⟩
    · exact hat h.symm
    · exact hbt h.symm
  have hsub : e1 ∪ e2 ⊆ G.edgeFinset := by
    intro x hx
    rw [SimpleGraph.mem_edgeFinset]
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_filter.1 (Finset.mem_sigma.1 hp).2).2.1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact (SimpleGraph.mem_neighborFinset G t v).1 hv
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, i1, i2, hM] at this
  exact this

end PEqualNP.Outside.L_meta_4863

open PEqualNP.Outside.L_meta_4863 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4863 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12 := by
  intro n G _ A T t hdeg hA hT hcov ht
  have htA : t ∉ A := fun h => Finset.mem_compl.1 (hT ht) h
  have edge_mem : ∀ u v, G.Adj u v → u ≠ t → v ≠ t →
      (u ∈ T.erase t ∧ v ∈ Nb G T t u) ∨ (v ∈ T.erase t ∧ u ∈ Nb G T t v) := by
    intro u v huv hu hv
    have m1 : u ∈ T → (v ∉ T ∨ u < v) → (u ∈ T.erase t ∧ v ∈ Nb G T t u) := fun h1 h2 =>
      ⟨Finset.mem_erase.2 ⟨hu, h1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, hv, h2⟩⟩
    have m2 : v ∈ T → (u ∉ T ∨ v < u) → (v ∈ T.erase t ∧ u ∈ Nb G T t v) := fun h1 h2 =>
      ⟨Finset.mem_erase.2 ⟨hv, h1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, hu, h2⟩⟩
    by_cases h1 : u ∈ T
    · by_cases h2 : v ∈ T
      · rcases lt_or_gt_of_ne huv.ne with h | h
        · exact Or.inl (m1 h1 (Or.inr h))
        · exact Or.inr (m2 h2 (Or.inr h))
      · exact Or.inl (m1 h1 (Or.inl h2))
    · have h2 : v ∈ T := (hcov u v huv).resolve_left h1
      exact Or.inr (m2 h2 (Or.inl h1))
  have nbr : ∀ u, u ∉ A → ∀ w : Fin n, ∃ v, G.Adj u v ∧ v ≠ w := by
    intro u hu w
    by_contra hcon
    push Not at hcon
    have hs : G.neighborSet u ⊆ {w} := fun v hv => hcon v hv
    have h1 := Set.ncard_le_ncard hs (Set.finite_singleton w)
    rw [hdeg u hu, Set.ncard_singleton] at h1
    omega
  rcases stars n (fun c => Nb G T t c) (T.erase t) with h | ⟨gs, w, h1, h2, h3⟩
  · exfalso
    obtain ⟨u, hu, _⟩ := nbr t htA t
    obtain ⟨v, hv, hvt⟩ := nbr u (hA u t hu.symm) t
    rcases edge_mem u v hv hu.ne.symm hvt with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [h u k1] at k2; simp at k2
    · rw [h v k1] at k2; simp at k2
  · obtain ⟨hs, v, k1, k2, k3⟩ := ors n A gs w _ h1 h3
    have hc := count G T t (hdeg t htA)
    have hT1 : (T.erase t).card + 1 = T.card := Finset.card_erase_add_one ht
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h2
    refine ⟨hs.length, by omega, ⟨hs, v⟩, fun g hg => ?_, le_rfl, fun x => ?_⟩
    · obtain ⟨e1, e2⟩ := k1 g hg
      refine ⟨?_, e2.le⟩
      rcases e1 with e | e <;> simp [e]
    · refine (k3.2 x).trans ?_
      rw [Bool.eq_iff_iff]
      simp only [NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
      have hup : ∀ u, Function.update x t false u = true ↔ u ≠ t ∧ x u = true := by
        intro u
        by_cases h : u = t
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      refine or_congr (exists_congr fun a => and_congr_right fun ha => ?_) ⟨?_, ?_⟩
      · rw [hup]
        exact ⟨fun h => ⟨fun e => htA (e ▸ ha), h⟩, fun h => h.2⟩
      · rintro ⟨c, hcm, hx, u, hu, hxu⟩
        have hu' := (Finset.mem_filter.1 hu).2
        exact ⟨c, u, hu'.1, (hup c).2 ⟨Finset.ne_of_mem_erase hcm, hx⟩, (hup u).2 ⟨hu'.2.1, hxu⟩⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨a1, a2⟩ := (hup u).1 hu
        obtain ⟨b1, b2⟩ := (hup v).1 hv
        rcases edge_mem u v huv a1 b1 with ⟨l1, l2⟩ | ⟨l1, l2⟩
        · exact ⟨u, l1, a2, v, l2, b2⟩
        · exact ⟨v, l1, b2, u, l2, a2⟩
