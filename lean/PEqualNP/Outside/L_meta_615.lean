import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L615Aux.Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, le_trans len hs, ho, ev⟩

lemma bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len, ho, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

lemma bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, nn1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, nn2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact nn1 g hg
    · exact nn2 g hg
    · subst hg; rcases hop with h | h <;> simp [h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

lemma bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

lemma bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2


lemma bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ GateOp.not) ∧
      circuitFun n D = F ∧ D.size ≤ s := by
  obtain ⟨gs, out, ok, nn, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, nn, ?_, len⟩
  funext x
  have e := ev (List.ofFn x) (by simp)
  simp only [circuitFun, Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i


lemma bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp


lemma bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

lemma bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

lemma upper_cover {n : ℕ} (E : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (hne : E.Nonempty) (hcov : ∀ e ∈ E, ∃ v ∈ T, v ∈ e) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ E.card + T.card ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ e ∈ E, ∀ v ∈ e, x v = true := by
  classical
  obtain ⟨C, fan, hnot, hev, hsize⟩ := bld_circuit (bld_edges n T E hne hcov)
  refine ⟨C, ?_, by have := hne.card_pos; omega, ?_⟩
  · intro g hg
    obtain ⟨hops, hlen⟩ := fan g hg
    refine ⟨?_, hlen⟩
    simpa [hnot g hg] using hops
  · intro x
    have hx := congrFun hev x
    change C.eval (List.ofFn x) = _ at hx
    rw [hx, decide_eq_true_eq]

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Sym2

def edgeOfPair (n : ℕ) (e : ℕ × ℕ) : Option (Sym2 (Fin n)) :=
  if h : e.1 < n ∧ e.2 < n then some s(⟨e.1, h.1⟩, ⟨e.2, h.2⟩) else none

def edgeSetOfList (n : ℕ) (l : List (ℕ × ℕ)) : Finset (Sym2 (Fin n)) :=
  (l.filterMap (edgeOfPair n)).toFinset

lemma edgeSet_mem {n : ℕ} {l : List (ℕ × ℕ)} {e : Sym2 (Fin n)} :
    e ∈ edgeSetOfList n l ↔
      ∃ u v : Fin n, (u.val, v.val) ∈ l ∧ e = s(u,v) := by
  simp only [edgeSetOfList, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a,b⟩, hab, he⟩
    unfold edgeOfPair at he
    split at he
    · rename_i h
      exact ⟨⟨a,h.1⟩, ⟨b,h.2⟩, hab, (Option.some.inj he).symm⟩
    · contradiction
  · rintro ⟨u,v, huv, rfl⟩
    exact ⟨(u.val, v.val), huv, by simp [edgeOfPair, u.isLt, v.isLt]⟩

lemma edgeSet_card_le (n : ℕ) (l : List (ℕ × ℕ)) :
    (edgeSetOfList n l).card ≤ l.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

lemma upper_list {n : ℕ} (l : List (ℕ × ℕ)) (S : Finset (Fin n))
    (hne : ∃ u v : Fin n, (u.val, v.val) ∈ l)
    (hcov : ∀ u v : Fin n, (u.val, v.val) ∈ l → u ∈ S ∨ v ∈ S) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ l.length + S.card ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, (u.val, v.val) ∈ l ∧ x u = true ∧ x v = true := by
  let E := edgeSetOfList n l
  obtain ⟨u₀, v₀, h₀⟩ := hne
  have hn : E.Nonempty := ⟨s(u₀,v₀), edgeSet_mem.mpr ⟨u₀, v₀, h₀, rfl⟩⟩
  have hc : ∀ e ∈ E, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨u,v,huv,rfl⟩ := edgeSet_mem.mp he
    rcases hcov u v huv with hu | hv
    · exact ⟨u, hu, Sym2.mem_mk_left _ _⟩
    · exact ⟨v, hv, Sym2.mem_mk_right _ _⟩
  obtain ⟨C, hm, hs, hx⟩ := upper_cover E S hn hc
  refine ⟨C, hm, hs.trans (Nat.add_le_add_right (edgeSet_card_le n l) _), ?_⟩
  intro x
  rw [hx]
  constructor
  · rintro ⟨e, he, hall⟩
    obtain ⟨u,v,huv,rfl⟩ := edgeSet_mem.mp he
    exact ⟨u,v,huv,hall u (Sym2.mem_mk_left _ _),hall v (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    refine ⟨s(u,v), edgeSet_mem.mpr ⟨u,v,huv,rfl⟩, ?_⟩
    intro w hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption

def pathVertices (a k : ℕ) : List ℕ :=
  [0] ++ (List.range k).map (fun i => a+i) ++ [1]

def pathEdges (a k : ℕ) : List (ℕ × ℕ) :=
  (pathVertices a k).zip (pathVertices a k).tail

def thetaEdges (p q r : ℕ) : List (ℕ × ℕ) :=
  pathEdges 2 p ++ pathEdges (2+p) q ++ pathEdges (2+p+q) r

lemma pathEdges_length (a k : ℕ) : (pathEdges a k).length = k+1 := by
  simp [pathEdges, pathVertices, List.length_zip]

lemma thetaEdges_length (p q r : ℕ) : (thetaEdges p q r).length = p+q+r+3 := by
  simp [thetaEdges, pathEdges_length]
  omega

lemma thetaEdges_has_edge (p q r : ℕ) :
    ∃ u v : Fin (p+q+r+2), (u.val,v.val) ∈ thetaEdges p q r := by
  cases p with
  | zero =>
    refine ⟨⟨0,by omega⟩, ⟨1,by omega⟩, ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (by simp [pathEdges, pathVertices]))
  | succ k =>
    refine ⟨⟨0,by omega⟩, ⟨2,by omega⟩, ?_⟩
    apply List.mem_append_left
    apply List.mem_append_left
    simp [pathEdges, pathVertices, List.range_succ_eq_map]

lemma theta_upper (p q r t s : ℕ)
    (hcov : ∃ S : Finset (Fin (p+q+r+2)),
      (∀ u v : Fin (p+q+r+2), (u.val,v.val) ∈ thetaEdges p q r → u ∈ S ∨ v ∈ S) ∧
      S.card = t)
    (hsize : p+q+r+2+t ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin (p+q+r+2) → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (p+q+r+2), (u.val,v.val) ∈ thetaEdges p q r ∧
          x u = true ∧ x v = true := by
  obtain ⟨S,hS,hcard⟩ := hcov
  obtain ⟨C,hC,hbound,hval⟩ := upper_list _ S (thetaEdges_has_edge p q r) hS
  rw [thetaEdges_length,hcard] at hbound
  exact ⟨C,hC,by omega,hval⟩

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

def legArc (a k u v : ℕ) : Prop :=
  (k = 0 ∧ u = 0 ∧ v = 1) ∨ (0 < k ∧ u = 0 ∧ v = a) ∨
  (0 < k ∧ u = a+k-1 ∧ v = 1) ∨ (a ≤ u ∧ u+1 < a+k ∧ v = u+1)

def thetaArc (p q r u v : ℕ) : Prop :=
  legArc 2 p u v ∨ legArc (2+p) q u v ∨ legArc (2+p+q) r u v

def thetaAdj (p q r u v : ℕ) : Prop := thetaArc p q r u v ∨ thetaArc p q r v u

private def runFrom (a k : ℕ) : List ℕ := (List.range k).map (fun i => a+i) ++ [1]

private lemma runFrom_succ (a k : ℕ) : runFrom a (k+1) = a :: runFrom (a+1) k := by
  simp [runFrom, List.range_succ_eq_map, List.map_map, Function.comp_def]
  omega

private def tailEdges (a k : ℕ) : List (ℕ × ℕ) :=
  (a :: runFrom (a+1) k).zip (runFrom (a+1) k)

private lemma tailEdges_mem (a k u v : ℕ) :
    (u,v) ∈ tailEdges a k ↔ (u=a+k ∧ v=1) ∨ (a≤u ∧ u<a+k ∧ v=u+1) := by
  induction k generalizing a with
  | zero => simp [tailEdges, runFrom]; omega
  | succ k ih =>
    have h : tailEdges a (k+1) = (a,a+1) :: tailEdges (a+1) k := by
      simp only [tailEdges, runFrom_succ, List.zip_cons_cons]
    rw [h, List.mem_cons, ih]
    simp only [Prod.mk.injEq]
    omega

lemma pathEdges_mem (a k u v : ℕ) : (u,v) ∈ pathEdges a k ↔ legArc a k u v := by
  cases k with
  | zero => simp [pathEdges,pathVertices,legArc]; omega
  | succ k =>
    have h : pathEdges a (k+1) = (0,a)::tailEdges a k := by
      change ((0::runFrom a (k+1)).zip (runFrom a (k+1))) = _
      rw [runFrom_succ]
      rfl
    rw [h,List.mem_cons,tailEdges_mem]
    simp only [Prod.mk.injEq,legArc]
    omega

lemma thetaEdges_mem (p q r u v : ℕ) :
    (u,v) ∈ thetaEdges p q r ↔ thetaArc p q r u v := by
  simp only [thetaEdges,thetaArc,List.mem_append,pathEdges_mem]
  tauto

def thetaGraph (p q r : ℕ) : SimpleGraph (Fin (p+q+r+2)) where
  Adj u v := thetaAdj p q r u.val v.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by
    intro u
    simp only [thetaAdj, or_self, thetaArc, legArc]
    omega⟩

lemma thetaGraph_adj (p q r : ℕ) (u v : Fin (p+q+r+2)) :
    (thetaGraph p q r).Adj u v ↔ (u.val,v.val) ∈ thetaEdges p q r ∨
      (v.val,u.val) ∈ thetaEdges p q r := by
  simp only [thetaEdges_mem]
  rfl

lemma theta_degrees (p q r : ℕ)
    (hp : p=0 → 1≤q ∧ 1≤r) (hq : q=0 → 1≤p ∧ 1≤r)
    (hr : r=0 → 1≤p ∧ 1≤q) (v : Fin (p+q+r+2)) :
    2 ≤ ((thetaGraph p q r).neighborSet v).ncard := by
  let n := p+q+r+2
  have make (a b : ℕ) (ha : a<n) (hb : b<n) (h : a ≠ b)
      (h₁ : thetaAdj p q r v.val a) (h₂ : thetaAdj p q r v.val b) :
      2 ≤ ((thetaGraph p q r).neighborSet v).ncard := by
    let i : Fin (p+q+r+2) := ⟨a,ha⟩
    let j : Fin (p+q+r+2) := ⟨b,hb⟩
    have hij : i ≠ j := fun H => h (congrArg Fin.val H)
    have hs : ({i,j} : Set (Fin (p+q+r+2))) ⊆ (thetaGraph p q r).neighborSet v := by
      intro w hw
      rcases (Set.mem_insert_iff.mp hw) with rfl | rfl
      · exact h₁
      · exact h₂
    simpa [Set.ncard_pair hij] using Set.ncard_le_ncard hs
  have first (a k : ℕ) (ha : 0<k) : legArc a k 0 a := Or.inr (Or.inl ⟨ha,rfl,rfl⟩)
  have last (a k : ℕ) (ha : 0<k) : legArc a k (a+k-1) 1 :=
    Or.inr (Or.inr (Or.inl ⟨ha,rfl,rfl⟩))
  have subInterior (a k : ℕ) (ha : 2≤a) (hend : a+k≤n)
      (hl : a≤v.val) (hu : v.val<a+k)
      (hleg : ∀ u w, legArc a k u w → thetaArc p q r u w) :
      2 ≤ ((thetaGraph p q r).neighborSet v).ncard := by
    let left := if v.val = a then 0 else v.val-1
    let right := if v.val+1 = a+k then 1 else v.val+1
    apply make left right
    · dsimp [left,n] at *; split <;> omega
    · dsimp [right,n] at *; split <;> omega
    · dsimp [left,right]; split <;> split <;> omega
    · apply Or.inr
      apply hleg
      dsimp [left,legArc]
      split <;> omega
    · apply Or.inl
      apply hleg
      dsimp [right,legArc]
      split <;> omega
  dsimp [n] at *
  by_cases h0 : v.val=0
  · by_cases hp' : p=0
    · obtain ⟨hq',hr'⟩ := hp hp'
      apply make (2+p) (2+p+q) (by omega) (by omega) (by omega)
      · rw [h0]; exact Or.inl (Or.inr (Or.inl (first _ _ hq')))
      · rw [h0]; exact Or.inl (Or.inr (Or.inr (first _ _ hr')))
    · by_cases hq' : q=0
      · apply make 2 (2+p+q) (by omega) (by omega) (by omega)
        · rw [h0]; exact Or.inl (Or.inl (first _ _ (by omega)))
        · rw [h0]; exact Or.inl (Or.inr (Or.inr (first _ _ (hq hq').2)))
      · apply make 2 (2+p) (by omega) (by omega) (by omega)
        · rw [h0]; exact Or.inl (Or.inl (first _ _ (by omega)))
        · rw [h0]; exact Or.inl (Or.inr (Or.inl (first _ _ (by omega))))
  by_cases h1 : v.val=1
  · by_cases hp' : p=0
    · obtain ⟨hq',hr'⟩ := hp hp'
      apply make (2+p+q-1) (2+p+q+r-1) (by omega) (by omega) (by omega)
      · rw [h1]; exact Or.inr (Or.inr (Or.inl (last _ _ hq')))
      · rw [h1]; exact Or.inr (Or.inr (Or.inr (last _ _ hr')))
    · by_cases hq' : q=0
      · apply make (2+p-1) (2+p+q+r-1) (by omega) (by omega) (by omega)
        · rw [h1]; exact Or.inr (Or.inl (last _ _ (by omega)))
        · rw [h1]; exact Or.inr (Or.inr (Or.inr (last _ _ (hq hq').2)))
      · apply make (2+p-1) (2+p+q-1) (by omega) (by omega) (by omega)
        · rw [h1]; exact Or.inr (Or.inl (last _ _ (by omega)))
        · rw [h1]; exact Or.inr (Or.inr (Or.inl (last _ _ (by omega))))
  have hv := v.isLt
  by_cases h₁ : v.val < 2+p
  · exact subInterior 2 p (by omega) (by omega) (by omega) h₁ (fun _ _ h => Or.inl h)
  by_cases h₂ : v.val < 2+p+q
  · exact subInterior (2+p) q (by omega) (by omega) (by omega) h₂ (fun _ _ h => Or.inr (Or.inl h))
  exact subInterior (2+p+q) r (by omega) (by omega) (by omega) (by omega) (fun _ _ h => Or.inr (Or.inr h))

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

open scoped Sym2

private lemma nodup_tailEdges (a k : ℕ) : (tailEdges a k).Nodup := by
  induction k generalizing a with
  | zero => simp [tailEdges,runFrom]
  | succ k ih =>
    have h : tailEdges a (k+1) = (a,a+1) :: tailEdges (a+1) k := by
      simp only [tailEdges, runFrom_succ, List.zip_cons_cons]
    rw [h,List.nodup_cons]
    exact ⟨by rw [tailEdges_mem]; omega, ih _⟩

private lemma nodup_pathEdges (a k : ℕ) (ha : 2≤a) : (pathEdges a k).Nodup := by
  cases k with
  | zero => simp [pathEdges,pathVertices]
  | succ k =>
    have h : pathEdges a (k+1) = (0,a)::tailEdges a k := by
      change ((0::runFrom a (k+1)).zip (runFrom a (k+1))) = _
      rw [runFrom_succ]
      rfl
    rw [h,List.nodup_cons]
    exact ⟨by rw [tailEdges_mem]; omega, nodup_tailEdges _ _⟩

private lemma pathEdges_separate {a k b m : ℕ} (ha : 2≤a) (hab : a+k≤b)
    (hk : k = 0 → 0 < m) :
    (pathEdges a k).Disjoint (pathEdges b m) := by
  intro e he hf
  rcases e with ⟨u,v⟩
  rw [pathEdges_mem] at he hf
  unfold legArc at he hf
  omega

lemma thetaEdges_nodup (p q r : ℕ)
    (hp : p=0 → 1≤q ∧ 1≤r) (hq : q=0 → 1≤p ∧ 1≤r) :
    (thetaEdges p q r).Nodup := by
  have hPQ := pathEdges_separate (a:=2) (k:=p) (b:=2+p) (m:=q) (by omega) (by omega) (by omega)
  have hPR := pathEdges_separate (a:=2) (k:=p) (b:=2+p+q) (m:=r) (by omega) (by omega) (by omega)
  have hQR := pathEdges_separate (a:=2+p) (k:=q) (b:=2+p+q) (m:=r) (by omega) (by omega) (by omega)
  simp only [thetaEdges,List.nodup_append]
  refine ⟨⟨nodup_pathEdges _ _ (by omega),nodup_pathEdges _ _ (by omega),?_⟩,
    nodup_pathEdges _ _ (by omega),?_⟩
  · rintro a ha _ hb rfl
    exact hPQ ha hb
  · rintro a ha _ hb rfl
    rcases List.mem_append.mp ha with h | h
    · exact hPR h hb
    · exact hQR h hb

lemma arc_bounds {p q r u v : ℕ} (h : thetaArc p q r u v) :
    u < p+q+r+2 ∧ v < p+q+r+2 := by
  unfold thetaArc legArc at h
  omega

lemma arc_asymmetric {p q r u v : ℕ} (h : thetaArc p q r u v) :
    ¬thetaArc p q r v u := by
  intro h'
  unfold thetaArc legArc at h h'
  omega

lemma theta_edge_count (p q r : ℕ)
    (hp : p=0 → 1≤q ∧ 1≤r) (hq : q=0 → 1≤p ∧ 1≤r) :
    (thetaGraph p q r).edgeSet.ncard = p+q+r+3 := by
  classical
  let n := p+q+r+2
  let cv (u : ℕ) : Fin n := ⟨u % n, Nat.mod_lt _ (by dsimp [n]; omega)⟩
  let f (z : ℕ × ℕ) : Sym2 (Fin n) := s(cv z.1, cv z.2)
  let L := (thetaEdges p q r).toFinset
  have liftMem {u v : ℕ} (hm : (u,v) ∈ L) :
      (cv u).val = u ∧ (cv v).val = v ∧ thetaArc p q r u v := by
    have h := (thetaEdges_mem p q r u v).mp (List.mem_toFinset.mp hm)
    obtain ⟨hl,hr⟩ := arc_bounds h
    exact ⟨Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr, h⟩
  have hinj : Set.InjOn f L := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd heq
    have h := Sym2.eq_iff.mp heq
    obtain ⟨ha,hb,h₁⟩ := liftMem hab
    obtain ⟨hc,hd,h₂⟩ := liftMem hcd
    rcases h with ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · exact Prod.ext (ha.symm.trans ((congrArg Fin.val hac).trans hc))
        (hb.symm.trans ((congrArg Fin.val hbd).trans hd))
    · have e₁ := ha.symm.trans ((congrArg Fin.val had).trans hd)
      have e₂ := hb.symm.trans ((congrArg Fin.val hbc).trans hc)
      subst c; subst d
      exact False.elim (arc_asymmetric h₁ h₂)
  have image_eq : L.image f = (thetaGraph p q r).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · rintro h
        obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp h
        obtain ⟨ha,hb,h₁⟩ := liftMem hab
        rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · apply Or.inl
          change thetaArc p q r (cv a).val (cv b).val
          simpa only [ha,hb] using h₁
        · apply Or.inr
          change thetaArc p q r (cv a).val (cv b).val
          simpa only [ha,hb] using h₁
      · intro huv
        rcases (thetaGraph_adj p q r u v).mp huv with he | he
        · refine Finset.mem_image.mpr ⟨(u.val,v.val), List.mem_toFinset.mpr he, ?_⟩
          have hu : cv u.val = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
          have hv : cv v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
          simp only [f,hu,hv]
        · refine Finset.mem_image.mpr ⟨(v.val,u.val), List.mem_toFinset.mpr he, ?_⟩
          have hu : cv u.val = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
          have hv : cv v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
          simp only [f,hu,hv,Sym2.eq_swap]
  calc
    _ = (thetaGraph p q r).edgeFinset.card := Set.ncard_eq_toFinset_card' _
    _ = L.card := by rw [← image_eq,Finset.card_image_of_injOn hinj]
    _ = _ := (List.toFinset_card_of_nodup (thetaEdges_nodup p q r hp hq)).trans
      (thetaEdges_length p q r)

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

private def firstInternal (p q r v : ℕ) : Prop :=
  (0 < p ∧ v = 2) ∨ (0 < q ∧ v = 2+p) ∨ (0 < r ∧ v = 2+p+q)

private def lastInternal (p q r v : ℕ) : Prop :=
  (0 < p ∧ v = 2+p-1) ∨ (0 < q ∧ v = 2+p+q-1) ∨ (0 < r ∧ v = 2+p+q+r-1)

private def hasStep (p q r u : ℕ) : Prop :=
  (2 ≤ u ∧ u+1 < 2+p) ∨ (2+p ≤ u ∧ u+1 < 2+p+q) ∨
    (2+p+q ≤ u ∧ u+1 < 2+p+q+r)

private lemma sy {p q r v w : ℕ} (h : thetaAdj p q r v w) : thetaAdj p q r w v := h.symm

private lemma hub0 {p q r x : ℕ} (hx : 2 ≤ x) (h : thetaAdj p q r 0 x) :
    firstInternal p q r x := by
  unfold thetaAdj thetaArc legArc at h
  unfold firstInternal
  omega

private lemma hub1 {p q r x : ℕ} (hx : 2 ≤ x) (h : thetaAdj p q r 1 x) :
    lastInternal p q r x := by
  unfold thetaAdj thetaArc legArc at h
  unfold lastInternal
  omega

private lemma directSize {p q r : ℕ} (h : thetaAdj p q r 0 1) : p=0 ∨ q=0 ∨ r=0 := by
  unfold thetaAdj thetaArc legArc at h
  omega

private lemma insideLink {p q r x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (h : thetaAdj p q r x y) :
    (hasStep p q r x ∧ x+1=y) ∨ (hasStep p q r y ∧ y+1=x) := by
  unfold thetaAdj thetaArc legArc at h
  unfold hasStep
  omega

private lemma last_no_step {p q r x : ℕ} (h : lastInternal p q r x) :
    ¬hasStep p q r x := by
  unfold lastInternal at h
  unfold hasStep
  omega

private lemma first_no_prev {p q r x y : ℕ} (h : firstInternal p q r x) (hy : y+1=x) :
    ¬ hasStep p q r y := by
  unfold firstInternal at h
  unfold hasStep
  omega

private lemma right_unique {p q r v x y : ℕ} (hv : 2 ≤ v) (hx : x ≠ 0) (hy : y ≠ 0)
    (h₁ : thetaAdj p q r v x) (h₂ : thetaAdj p q r v y)
    (ord₁ : x = 1 ∨ v < x) (ord₂ : y = 1 ∨ v < y) : x = y := by
  by_cases ax : x = 1
  · subst x
    by_contra ne
    obtain ⟨hs, _⟩ | ⟨_, _⟩ := insideLink hv (by omega) h₂
    · exact last_no_step (hub1 hv (sy h₁)) hs
    · omega
  · by_cases ay : y = 1
    · subst y
      obtain ⟨hs, _⟩ | ⟨_, _⟩ := insideLink hv (by omega) h₁
      · exact False.elim (last_no_step (hub1 hv (sy h₂)) hs)
      · omega
    · have h₃ := insideLink hv (by omega) h₁
      have h₄ := insideLink hv (by omega) h₂
      omega

private lemma left_unique {p q r v x y : ℕ} (hv : 2 ≤ v) (hx : x ≠ 1) (hy : y ≠ 1)
    (h₁ : thetaAdj p q r v x) (h₂ : thetaAdj p q r v y)
    (ord₁ : x < v) (ord₂ : y < v) : x = y := by
  by_cases ax : x = 0
  · subst x
    by_contra ne
    obtain ⟨_, _⟩ | ⟨hs, he⟩ := insideLink hv (by omega) h₂
    · omega
    · exact first_no_prev (hub0 hv (sy h₁)) he hs
  · by_cases ay : y = 0
    · subst y
      obtain ⟨_, _⟩ | ⟨hs, he⟩ := insideLink hv (by omega) h₁
      · omega
      · exact False.elim (first_no_prev (hub0 hv (sy h₂)) he hs)
    · have h₃ := insideLink hv (by omega) h₁
      have h₄ := insideLink hv (by omega) h₂
      omega

private lemma noParallelTwo {p q r x y : ℕ} (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (hx₁ : firstInternal p q r x) (hx₂ : lastInternal p q r x)
    (hy₁ : firstInternal p q r y) (hy₂ : lastInternal p q r y) : x=y := by
  unfold firstInternal at hx₁ hy₁
  unfold lastInternal at hx₂ hy₂
  omega

private lemma noTwoStepLeg {p q r x y : ℕ} (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (hd : p=0 ∨ q=0 ∨ r=0) (hx : firstInternal p q r x) (hy : lastInternal p q r y)
    (h : (hasStep p q r x ∧ x+1=y) ∨ (hasStep p q r y ∧ y+1=x)) : False := by
  unfold firstInternal at hx
  unfold lastInternal at hy
  unfold hasStep at h
  omega

private lemma square_without_zero {p q r a b c d : ℕ}
    (az : a≠0) (bz : b≠0) (cz : c≠0) (dz : d≠0)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (eab : thetaAdj p q r a b) (ebc : thetaAdj p q r b c)
    (ecd : thetaAdj p q r c d) (eda : thetaAdj p q r d a) : False := by
  have low :
      (2≤a ∧ (b=1 ∨ a<b) ∧ (d=1 ∨ a<d)) ∨
      (2≤b ∧ (a=1 ∨ b<a) ∧ (c=1 ∨ b<c)) ∨
      (2≤c ∧ (b=1 ∨ c<b) ∧ (d=1 ∨ c<d)) ∨
      (2≤d ∧ (a=1 ∨ d<a) ∧ (c=1 ∨ d<c)) := by omega
  rcases low with ⟨v,x,y⟩ | ⟨v,x,y⟩ | ⟨v,x,y⟩ | ⟨v,x,y⟩
  · exact bd (right_unique v bz dz eab (sy eda) x y)
  · exact ac (right_unique v az cz (sy eab) ebc x y)
  · exact bd (right_unique v bz dz (sy ebc) ecd x y)
  · exact ac (right_unique v az cz eda (sy ecd) x y)

private lemma square_without_one {p q r a b c d : ℕ}
    (ao : a≠1) (bo : b≠1) (co : c≠1) (dO : d≠1)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (eab : thetaAdj p q r a b) (ebc : thetaAdj p q r b c)
    (ecd : thetaAdj p q r c d) (eda : thetaAdj p q r d a) : False := by
  have high : (2≤a ∧ b<a ∧ d<a) ∨ (2≤b ∧ a<b ∧ c<b) ∨
      (2≤c ∧ b<c ∧ d<c) ∨ (2≤d ∧ a<d ∧ c<d) := by omega
  rcases high with ⟨v,x,y⟩ | ⟨v,x,y⟩ | ⟨v,x,y⟩ | ⟨v,x,y⟩
  · exact bd (left_unique v bo dO eab (sy eda) x y)
  · exact ac (left_unique v ao co (sy eab) ebc x y)
  · exact bd (left_unique v bo dO (sy ebc) ecd x y)
  · exact ac (left_unique v ao co eda (sy ecd) x y)

private lemma square_from_zero {p q r b c d : ℕ}
    (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (bz : b≠0) (cz : c≠0) (dz : d≠0)
    (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (eab : thetaAdj p q r 0 b) (ebc : thetaAdj p q r b c)
    (ecd : thetaAdj p q r c d) (eda : thetaAdj p q r d 0) : False := by
  by_cases b1 : b=1
  · subst b
    have hc : 2≤c := by omega
    have hd : 2≤d := by omega
    exact noTwoStepLeg hpq hpr hqr (directSize eab) (hub0 hd (sy eda)) (hub1 hc ebc)
      (insideLink hd hc (sy ecd))
  by_cases c1 : c=1
  · subst c
    have hb : 2≤b := by omega
    have hd : 2≤d := by omega
    exact bd (noParallelTwo hpq hpr hqr (hub0 hb eab) (hub1 hb (sy ebc))
      (hub0 hd (sy eda)) (hub1 hd ecd))
  by_cases d1 : d=1
  · subst d
    have hb : 2≤b := by omega
    have hc : 2≤c := by omega
    exact noTwoStepLeg hpq hpr hqr (directSize (sy eda)) (hub0 hb eab) (hub1 hc (sy ecd))
      (insideLink hb hc ebc)
  exact square_without_one (by decide : (0:ℕ)≠1) b1 c1 d1
    (Ne.symm bz) (Ne.symm cz) (Ne.symm dz) bc bd cd eab ebc ecd eda

lemma theta_no_square {p q r a b c d : ℕ}
    (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (eab : thetaAdj p q r a b) (ebc : thetaAdj p q r b c)
    (ecd : thetaAdj p q r c d) (eda : thetaAdj p q r d a) : False := by
  by_cases az : a=0
  · subst a
    exact square_from_zero hpq hpr hqr ab.symm ac.symm ad.symm bc bd cd eab ebc ecd eda
  by_cases bz : b=0
  · subst b
    exact square_from_zero hpq hpr hqr bc.symm bd.symm az cd ac.symm ad.symm ebc ecd eda eab
  by_cases cz : c=0
  · subst c
    exact square_from_zero hpq hpr hqr cd.symm az bz ad.symm bd.symm ab ecd eda eab ebc
  by_cases dz : d=0
  · subst d
    exact square_from_zero hpq hpr hqr az bz cz ab ac bc eda eab ebc ecd
  exact square_without_zero az bz cz dz ab ac ad bc bd cd eab ebc ecd eda

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

private def tailRank (p q r u : ℕ) : ℕ :=
  if u = 1 then 0 else if u < 2+p then 2+p-u else if u < 2+p+q then 2+p+q-u else 2+p+q+r-u

set_option maxHeartbeats 1000000 in
private lemma color_opposite {p q r u v : ℕ} (hu : u≠0) (hv : v≠0) (h : thetaAdj p q r u v) :
    tailRank p q r u % 2 ≠ tailRank p q r v % 2 := by
  unfold thetaAdj thetaArc legArc at h
  unfold tailRank
  split_ifs <;> omega

lemma theta_min_cover_half {p q r t : ℕ}
    (hmin : ∀ S : Finset (Fin (p+q+r+2)),
      (∀ u v, (thetaGraph p q r).Adj u v → u∈S ∨ v∈S) → t≤S.card) :
    2*t ≤ p+q+r+2+1 := by
  classical
  let n := p+q+r+2
  let z : Fin n := ⟨0,by dsimp [n]; omega⟩
  let remaining := (Finset.univ : Finset (Fin n)).erase z
  let evenColor (u : Fin n) : Prop := tailRank p q r u.val % 2 = 0
  let A := remaining.filter evenColor
  let B := remaining.filter (fun u => ¬ evenColor u)
  have cA (u v : Fin n) (h : (thetaGraph p q r).Adj u v) :
      u ∈ insert z A ∨ v ∈ insert z A := by
    by_cases uz : u=z
    · exact Or.inl (uz ▸ Finset.mem_insert_self _ _)
    by_cases vz : v=z
    · exact Or.inr (vz ▸ Finset.mem_insert_self _ _)
    have hzero (w : Fin n) (hw : w≠z) : w.val≠0 := fun e => hw (Fin.ext e)
    have op := color_opposite (hzero u uz) (hzero v vz) h
    have ev : evenColor u ∨ evenColor v := by dsimp [evenColor]; omega
    simpa [A,remaining,uz,vz] using ev
  have cB (u v : Fin n) (h : (thetaGraph p q r).Adj u v) :
      u ∈ insert z B ∨ v ∈ insert z B := by
    by_cases uz : u=z
    · exact Or.inl (uz ▸ Finset.mem_insert_self _ _)
    by_cases vz : v=z
    · exact Or.inr (vz ▸ Finset.mem_insert_self _ _)
    have hzero (w : Fin n) (hw : w≠z) : w.val≠0 := fun e => hw (Fin.ext e)
    have op := color_opposite (hzero u uz) (hzero v vz) h
    have ev : ¬evenColor u ∨ ¬evenColor v := by dsimp [evenColor]; omega
    simpa [B,remaining,uz,vz] using ev
  have hA := hmin _ cA
  have hB := hmin _ cB
  have hsum : A.card+B.card = remaining.card := Finset.card_filter_add_card_filter_not _
  have hrem : remaining.card = n-1 := by simp [remaining]
  have hA' := Finset.card_insert_le z A
  have hB' := Finset.card_insert_le z B
  dsimp [n] at hrem
  omega

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

private def leftOnArm (p q u : ℕ) := if u = (if u < 2+p then 2 else if u < 2+p+q then 2+p else 2+p+q) then 0 else u-1
private def rightOnArm (p q r u : ℕ) := if u+1 = (if u < 2+p then 2+p else if u < 2+p+q then 2+p+q else 2+p+q+r) then 1 else u+1

set_option maxHeartbeats 1000000 in
private lemma arm_adj_cases {p q r u w : ℕ} (hu : 2≤u) (h : thetaAdj p q r u w) :
    w = leftOnArm p q u ∨ w = rightOnArm p q r u := by
  unfold thetaAdj thetaArc legArc at h
  unfold leftOnArm rightOnArm
  split_ifs <;> omega

private lemma forest_if_only_two_labels {V : Type*} (H : SimpleGraph V) (idv : V → ℕ)
    (hinj : Function.Injective idv)
    (hub : ∀ x u v, H.Adj x u → H.Adj x v → u≠v → idv x≤1) : H.IsAcyclic := by
  classical
  intro z w cyc
  have onCycle (x : V) (hx : x ∈ w.support) : idv x ≤ 1 := by
    let q := w.rotate x hx
    have hq : q.IsCycle := cyc.rotate hx
    exact hub x _ _ (q.adj_snd hq.not_nil) (q.adj_penultimate hq.not_nil).symm hq.snd_ne_penultimate
  have h0 := onCycle z w.start_mem_support
  have h1 := onCycle w.snd (w.getVert_mem_support 1)
  have h2 := onCycle w.penultimate (w.getVert_mem_support (w.length-1))
  have h01 : idv z ≠ idv w.snd := fun e => (w.adj_snd cyc.not_nil).ne (hinj e)
  have h02 : idv w.penultimate ≠ idv z := fun e => (w.adj_penultimate cyc.not_nil).ne (hinj e)
  have h12 : idv w.snd ≠ idv w.penultimate := fun e => cyc.snd_ne_penultimate (hinj e)
  omega

open Classical in
lemma theta_internal_strict {p q r : ℕ} (S : Finset (Fin (p+q+r+2)))
    (hout : ∀ u∈S, ∃ v, v∉S ∧ (thetaGraph p q r).Adj u v) :
    let G := thetaGraph p q r
    let A := S.filter (fun u => ∃ v∈S, G.Adj u v)
    let I := G.edgeFinset.filter (fun e => ∀ v∈e, v∈S)
    I.Nonempty → I.card < A.card := by
  classical
  intro G A I hne
  let H := G.induce (A : Set (Fin (p+q+r+2)))
  have act {u : Fin (p+q+r+2)} (hu : u∈A) : u∈S := (Finset.mem_filter.1 hu).1
  have bridge : I = G.edgeFinset.filter (fun e => e.toFinset ⊆ A) := by
    ext e
    refine Sym2.ind (fun u v => ?_) e
    simp only [I, Finset.mem_filter]
    constructor
    · rintro ⟨hed, hs⟩
      have ha : G.Adj u v := by simpa using hed
      have hu := hs u (Sym2.mem_mk_left _ _)
      have hv := hs v (Sym2.mem_mk_right _ _)
      refine ⟨hed, ?_⟩
      intro w hw
      have hmem : w∈s(u,v) := by simpa using hw
      rcases Sym2.mem_iff.1 hmem with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hu,v,hv,ha⟩
      · exact Finset.mem_filter.2 ⟨hv,u,hu,ha.symm⟩
    · rintro ⟨hed,hs⟩
      exact ⟨hed, fun w hw => act (hs (by simpa using hw))⟩
  have ec : I.card = H.edgeFinset.card := by
    rw [bridge]
    exact SimpleGraph.card_filter_edgeFinset_toFinset_subset A
  have hacyc : H.IsAcyclic := by
    apply forest_if_only_two_labels H (fun u => u.val.val)
    · intro x y h
      exact Subtype.ext (Fin.ext h)
    · intro x u v hxu hxv huv
      by_contra hnot
      have hx : 2≤x.val.val := by omega
      obtain ⟨w,hw,haw⟩ := hout x.val (act x.property)
      have ux : u.val.val ≠ w.val := fun e => hw (Fin.ext e ▸ act u.property)
      have vx : v.val.val ≠ w.val := fun e => hw (Fin.ext e ▸ act v.property)
      have uv : u.val.val ≠ v.val.val := fun e => huv (Subtype.ext (Fin.ext e))
      have hu := arm_adj_cases hx (show thetaAdj p q r x.val.val u.val.val from hxu)
      have hv := arm_adj_cases hx (show thetaAdj p q r x.val.val v.val.val from hxv)
      have hw' := arm_adj_cases hx (show thetaAdj p q r x.val.val w.val from haw)
      omega
  have hn : Nonempty (A : Set (Fin (p+q+r+2))) := by
    obtain ⟨e,he⟩ := hne
    rw [bridge,Finset.mem_filter] at he
    have helem : ∃ u, u∈e := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e
    obtain ⟨u, hu⟩ := helem
    exact ⟨u, he.2 (by simpa using hu)⟩
  have cap := hacyc.ncard_edgeSet_add_one_le_card
  rw [ec]
  rw [← H.coe_edgeFinset, Set.ncard_coe_finset] at cap
  simpa [Nat.card_eq_fintype_card] using cap

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
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

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

lemma next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

lemma trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

lemma live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

lemma trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

lemma align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

lemma difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L615Aux.Wires


namespace PEqualNP.Outside.L615Aux.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

lemma acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

lemma point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

lemma point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

lemma carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

lemma singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

lemma influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

lemma next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

lemma mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

lemma nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

lemma firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

lemma firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

lemma no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L615Aux.Wires


namespace PEqualNP.Outside.L615Aux.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, val C x C.output = true ↔
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

lemma edge_of_point (he : GraphEval C G) {S : Finset (Fin n)} :
    val C (point S) C.output = true ↔ ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
  rw [he]
  simp only [point, decide_eq_true_eq]
  aesop

lemma point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := by
  rw [edge_of_point he]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact G.adj_symm hab
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨v, by simp, w, by simp, h⟩

lemma point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

lemma point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

lemma edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

lemma two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

lemma carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

lemma meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

lemma covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := (edge_of_point he).2 ⟨v,by simp,a₀,by simp [S],ha₀⟩
  have hZ : val C z C.output = true := (edge_of_point he).2 ⟨w,by simp,b₀,by simp [S],hb₀⟩
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end PEqualNP.Outside.L615Aux.Wires


namespace PEqualNP.Outside.L615Aux.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

lemma value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

lemma branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

lemma mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

lemma input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

lemma live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

lemma readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

lemma incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

lemma branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L615Aux.Wires


namespace PEqualNP.Outside.L615Aux.Foundation

lemma general_branch_bound :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → n + t ≤ C.size + 1 := by
  open PEqualNP.Outside.L615Aux.Wires in
  classical
  intro n t G C hdegree htwins hadj _ ht hC he
  by_cases hn : n=0
  · subst n
    have ht0 := ht ∅ (fun u => Fin.elim0 u)
    simp at ht0
    omega
  have hE : GraphEval C G := he
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨w, hve⟩ := hdegree v
  have ho := (edge_at_output hE hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hbudget := branch_budget hC hE hdegree ho'
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans hbudget

end PEqualNP.Outside.L615Aux.Foundation

namespace PEqualNP.Outside.L615Aux.Counting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L615Aux.Wires
variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

lemma branch_budget_triple (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    {q : ℕ} (hq : q ∈ living n C) (triple : 3 ≤ (readers n C q).card) :
    open Classical in n + ((living n C).filter (Branch n C)).card < C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card < ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro a ha
      have hl := (mem_living.1 ha).2
      by_cases heq : a=C.output
      · subst a
        simp [hoNone]
      · by_cases hb : Branch n C a
        · have hb' : 2 ≤ (readers n C a).card := hb
          simpa [heq,hb] using hb'
        · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
    · refine ⟨q,hq,?_⟩
      have hbr : Branch n C q := show 2 ≤ (readers n C q).card by omega
      have ne : q ≠ C.output := by rintro rfl; exact hoNone hbr
      simp [ne,hbr]; omega
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card < C.gates.length+1
  omega

end PEqualNP.Outside.L615Aux.Counting
namespace PEqualNP.Outside.L615Aux.Counting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def NoSquare {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃a b c d⦄, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

lemma thetaLowerWithinOne {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (deg : ∀ v : Fin n, 2 ≤ (G.neighborSet v).ncard) (sq : NoSquare G)
    (minCover : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (mono : Monotone2 C)
    (eval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    n + t ≤ C.size + 1 := by
  classical
  let cover : Finset (Fin n) → Prop := fun S => ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S
  have ex : ∃ k : ℕ, ∃ S : Finset (Fin n), cover S ∧ S.card = k :=
    ⟨_, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
  let k := Nat.find ex
  obtain ⟨S,hS,hk⟩ := Nat.find_spec ex
  have tk : t ≤ k := (minCover S hS).trans_eq hk
  suffices n + k ≤ C.size + 1 from (Nat.add_le_add_left tk n).trans this
  apply PEqualNP.Outside.L615Aux.Foundation.general_branch_bound n k G C
  · intro v
    obtain ⟨a,ha,_⟩ := Set.exists_ne_of_one_lt_ncard (deg v) v
    exact ⟨a,ha⟩
  · intro v w hvw _ _ _
    by_contra! same
    obtain ⟨a,ha,b,hb,hab⟩ := (Set.one_lt_ncard (s := G.neighborSet v) (Set.toFinite _)).mp (deg v)
    have hwa : G.Adj w a := (same a).mp ha
    have hwb : G.Adj w b := (same b).mp hb
    exact sq hvw hab ha hwa.symm hwb (G.adj_symm hb)
  · intro v w hvw _ _
    obtain ⟨a,ha,haw⟩ := Set.exists_ne_of_one_lt_ncard (deg v) w
    obtain ⟨b,hb,hbv⟩ := Set.exists_ne_of_one_lt_ncard (deg w) v
    refine ⟨a,b,ha,haw,hb,hbv,Or.inr ?_⟩
    exact fun e => sq hbv.symm haw.symm hvw hb e.symm (G.adj_symm ha)
  · exact ⟨S, fun u v h _ _ => hS u v h, hk⟩
  · intro T hT
    exact Nat.find_min' ex ⟨T, fun u v h => hT u v h (deg u) (deg v), rfl⟩
  · exact mono
  · exact eval

end PEqualNP.Outside.L615Aux.Counting
namespace PEqualNP.Outside.L615Aux.Counting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L615Aux.Wires

lemma firstBranch_false_on_extendible {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {v : Fin n} (mono : Monotone2 C) (eval : GraphEval C G) (eligible : Eligible C v)
    (S : Finset (Fin n)) (indep : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (neighbor : ∃ w ∈ S, G.Adj v w) :
    val C (point S) (firstBranch C v eligible) = false := by
  rw [← Bool.not_eq_true]
  intro hb
  have hb' := acts_mono mono (point_mono (Finset.subset_insert v S)) _ hb
  have eq := value_at_branch eligible (x := point S) (y := point (insert v S))
    (fun _ hi => (point_insert hi).symm) (hb.trans hb'.symm)
  obtain ⟨w,hw,hvw⟩ := neighbor
  have hyes := (edge_of_point eval (S := insert v S)).2
    ⟨v,Finset.mem_insert_self _ _,w,Finset.mem_insert_of_mem hw,hvw⟩
  obtain ⟨a,ha,b,hb,hab⟩ := (edge_of_point eval (S := S)).1 (eq.trans hyes)
  exact indep a ha b hb hab

lemma firstBranch_singleton_iff {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {v : Fin n} (mono : Monotone2 C) (eval : GraphEval C G) (eligible : Eligible C v)
    (degree : 2 ≤ (G.neighborSet v).ncard) (sq : NoSquare G) (w : Fin n) :
    val C (point {w}) (firstBranch C v eligible) = true ↔ w = v := by
  classical
  constructor
  · intro h
    by_contra hne
    obtain ⟨a,ha,b,hb,hab⟩ :=
      (Set.one_lt_ncard (s := G.neighborSet v) (Set.toFinite _)).mp degree
    obtain ⟨z,hvz,hwz⟩ : ∃ z, G.Adj v z ∧ ¬G.Adj w z := by
      by_cases hwa : G.Adj w a
      · exact ⟨b,hb,fun hwb => sq (Ne.symm hne) hab ha hwa.symm hwb (G.adj_symm hb)⟩
      · exact ⟨a,ha,hwa⟩
    have quiet := firstBranch_false_on_extendible mono eval eligible ({w,z} : Finset _)
      (by
        intro a ha b hb e
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
        · exact G.irrefl e
        · exact hwz e
        · exact hwz e.symm
        · exact G.irrefl e)
      ⟨z,by simp,hvz⟩
    have hyes := acts_mono mono (point_mono (show ({w} : Finset _) ⊆ {w,z} by simp)) _ h
    exact Bool.noConfusion (hyes.symm.trans quiet)
  · rintro rfl
    exact ((carries_iff mono).1 (firstBranch_spec _ eligible).2.1).1

end PEqualNP.Outside.L615Aux.Counting
namespace PEqualNP.Outside.L615Aux.Counting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L615Aux.Wires

lemma tight_branch_cover {n t : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (deg : ∀ v : Fin n, 2 ≤ (G.neighborSet v).ncard) (sq : NoSquare G)
    (minCover : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (mono : Monotone2 C) (eval : GraphEval C G) (tight : C.size + 1 = n + t)
    : ∃ S : Finset (Fin n), (∀ v, v ∈ S ↔ Eligible C v) ∧
      (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t ∧
      ∀ b ∈ living n C, Branch n C b →
        ∃ v : Fin n, ∃ h : Eligible C v, firstBranch C v h = b ∧
          (∀ w : Fin n, val C (point {w}) b = true ↔ w = v) ∧ (readers n C b).card = 2 := by
  classical
  by_cases hn : n=0
  · subst n
    have z := minCover ∅ (fun u => Fin.elim0 u)
    simp at z
    omega
  have npos : 0 < n := Nat.pos_of_ne_zero hn
  have neighbors (v : Fin n) : ∃ w, G.Adj v w := by
    obtain ⟨w,hw,_⟩ := Set.exists_ne_of_one_lt_ncard (deg v) v
    exact ⟨w,hw⟩
  obtain ⟨w,hw⟩ := neighbors ⟨0,npos⟩
  have ho := (edge_at_output eval hw).2
  have hout : C.output ∈ living n C := mem_living.2 ⟨ho,Relation.ReflTransGen.refl⟩
  let S := Finset.univ.filter fun v : Fin n => Eligible C v
  let B := (living n C).filter (Branch n C)
  let f (v : Fin n) := if h : Eligible C v then firstBranch C v h else 0
  have eligible (v : Fin n) : v ∈ S ↔ Eligible C v := by simp [S]
  have cov : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
    intro u v huv
    obtain ⟨a,ha,hav⟩ := Set.exists_ne_of_one_lt_ncard (deg u) v
    obtain ⟨c,hc,hcu⟩ := Set.exists_ne_of_one_lt_ncard (deg v) u
    have hi : ¬ G.Adj a c := fun e => sq hcu.symm hav.symm huv hc e.symm (G.adj_symm ha)
    simpa only [eligible] using covers_edge mono eval huv ha hav hc hcu (Or.inr hi)
  have hcard := minCover S cov
  have im : S.image f ⊆ B := by
    rintro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    have e := (eligible v).1 hv
    have hs := firstBranch_spec v e
    simp only [f,dite_eq_left e]
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hs.1).trans_lt ho,hs.1⟩,hs.2.2⟩
  have inj : Set.InjOn f (S : Set (Fin n)) := by
    intro u hu v hv eq
    have eu := (eligible u).1 hu
    have ev := (eligible v).1 hv
    simp only [f,dite_eq_left eu,dite_eq_left ev] at eq
    have one := (firstBranch_singleton_iff mono eval eu (deg u) sq u).2 rfl
    rw [eq] at one
    exact (firstBranch_singleton_iff mono eval ev (deg v) sq u).1 one
  have imageCard := Finset.card_image_of_injOn inj
  have budget := branch_budget mono eval neighbors hout
  have eqB : S.image f = B := Finset.eq_of_subset_of_card_le im (by dsimp [B] at *; omega)
  have card : S.card = t := by
    have h := congrArg Finset.card eqB
    dsimp [B] at h
    omega
  refine ⟨S,eligible,cov,card,?_⟩
  intro b live branch
  have hb : b ∈ S.image f := eqB ▸ Finset.mem_filter.mpr ⟨live,branch⟩
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hb
  have e := (eligible v).1 hv
  have eq : firstBranch C v e = b := by simpa [f,e] using ev
  refine ⟨v,e,eq,fun w => eq ▸ firstBranch_singleton_iff mono eval e (deg v) sq w,?_⟩
  have le : 2 ≤ (readers n C b).card := branch
  by_contra! hne
  have more := branch_budget_triple mono eval neighbors hout live (show 3 ≤ (readers n C b).card by omega)
  have h := Finset.card_le_card im
  dsimp [B] at h
  omega

end PEqualNP.Outside.L615Aux.Counting
namespace PEqualNP.Outside.L615Aux.Counting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L615Aux.Wires Relation

def Consumes {n : ℕ} (C : Circuit) (v : Fin n) (j : ℕ) : Prop :=
  ∃ a, LNext n C a j ∧ Carries C v a ∧ ¬ Carries C v j

lemma consumption_trace {n : ℕ} {C : Circuit} {v : Fin n} {j : ℕ}
    (h : Consumes C v j) : Trace n C (Carries C v) v.val j ∧ ¬ Carries C v j := by
  obtain ⟨a,edge,carry,loss⟩ := h
  exact ⟨(singleton_path (live_before edge.1 edge.2) carry).tail ⟨carry,edge⟩,loss⟩

lemma trace_after {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a j : ℕ}
    (path : Trace n C P a j) : Trace n C (fun i => a ≤ i ∧ P i) a j := by
  induction path with
  | refl => exact .refl
  | tail prev step ih => exact ih.tail ⟨⟨trace_le prev,step.1⟩,step.2⟩

lemma last_of_trace {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (ha : ¬P a) : a=b := by
  rcases h.cases_head with e | ⟨_,step,_⟩
  · exact e
  · exact (ha step.1).elim

lemma consumptions_le_two {n t : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (deg : ∀ v : Fin n, 2 ≤ (G.neighborSet v).ncard) (sq : NoSquare G)
    (minCover : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (mono : Monotone2 C) (eval : GraphEval C G) (tight : C.size + 1 = n + t)
    {v : Fin n} (ev : Eligible C v) (J : Finset ℕ)
    (dies : ∀ j∈J, Consumes C v j) : J.card ≤ 2 := by
  classical
  obtain ⟨_,_,_,_,label⟩ := tight_branch_cover deg sq minCover mono eval tight
  let b := firstBranch C v ev
  have bs := firstBranch_spec v ev
  obtain ⟨u,hu,_⟩ := Set.exists_ne_of_one_lt_ncard (deg v) v
  have out := (edge_at_output eval (show G.Adj v u from hu)).2
  have lb : b ∈ living n C := mem_living.2 ⟨(next_le bs.1).trans_lt out,bs.1⟩
  have bb : Branch n C b := bs.2.2
  obtain ⟨_,_,_,_,cap⟩ := label b lb bb
  have only {a : ℕ} (la : Live n C a) (ca : Carries C v a) (ab : b < a) : ¬Branch n C a := by
    intro ba
    obtain ⟨w,ew,eq,one,_⟩ := label a (mem_living.2 ⟨(next_le la).trans_lt out,la⟩) ba
    have vw := (one v).1 ((carries_iff mono).1 ca).1
    subst w
    exact (Nat.ne_of_lt ab) eq
  have reach {j : ℕ} (hj : Consumes C v j) :
      ∃ a ∈ readers n C b, Trace n C (Carries C v) a j := by
    obtain ⟨path,loss⟩ := consumption_trace hj
    have p := singleton_path bs.1 bs.2.1
    rcases align p (firstBranch_unique v ev) j path with h | h
    · exact (loss h.2).elim
    · rcases h.cases_head with eq | ⟨a,step,rest⟩
      · exact (loss (eq ▸ bs.2.1)).elim
      · exact ⟨a,mem_readers.2 step.2,rest⟩
  have choice (j : {x // x ∈ J}) := reach (dies j.val j.property)
  let f (j : ℕ) := if h : j∈J then (choice ⟨j,h⟩).choose else 0
  have spec (j : ℕ) (hj : j ∈ J) :
      f j ∈ readers n C b ∧ Trace n C (Carries C v) (f j) j := by
    simpa [f,hj] using (choice ⟨j,hj⟩).choose_spec
  rw [← cap]
  apply Finset.card_le_card_of_injOn f
  · exact fun j hj => (spec j hj).1
  · intro j hj k hk eq
    have sj := spec j hj
    have sk := spec k hk
    have kpath : Trace n C (Carries C v) (f j) k := eq ▸ sk.2
    have uq (a y z : ℕ) (_ : a < j) (ha : f j ≤ a ∧ Carries C v a)
        (ey : LNext n C a y) (ez : LNext n C a z) : y=z := by
      have gt := ((mem_readers.1 sj.1).1.1).trans_le ha.1
      exact nonbranch_unique (only (live_before ey.1 ey.2) ha.2 gt) ey ez
    rcases align (trace_after sj.2) uq k kpath with bad | kt
    · exact ((consumption_trace (dies k hk)).2 bad.2.2).elim
    · exact last_of_trace kt (consumption_trace (dies j hj)).2

end PEqualNP.Outside.L615Aux.Counting

namespace PEqualNP.Outside.L615Aux.Counting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L615Aux.Wires
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

lemma value_at_ineligible_carrier {u : Fin n} {a : ℕ} {x y : Fin n → Bool}
    (hu : ¬Eligible C u) (live : Live n C a) (carry : Carries C u a)
    (agrees : ∀ i, i ≠ u → x i = y i) (eq : val C x a = val C y a) :
    val C x C.output = val C y C.output := by
  by_contra diff
  have path := singleton_path live carry
  rcases influence path (fun i j j' _ => no_eligible_unique hu i j j')
      agrees ReflTransGen.refl diff with bad | bad
  · exact (Nat.not_lt_of_ge (next_le live)) bad.1
  · exact bad.2 eq

lemma ineligible_carrier_only (mono : Monotone2 C) (eval : GraphEval C G)
    {u w : Fin n} {a : ℕ} (hu : ¬Eligible C u) (degree : 2 ≤ (G.neighborSet u).ncard)
    (sq : NoSquare G) (live : Live n C a) (cu : Carries C u a) (cw : Carries C w a) :
    w = u := by
  classical
  by_contra ne
  obtain ⟨p,hp,q,hq,pq⟩ :=
    (Set.one_lt_ncard (s := G.neighborSet u) (Set.toFinite _)).mp degree
  obtain ⟨z,huz,hwz⟩ : ∃ z, G.Adj u z ∧ ¬ G.Adj w z := by
    by_cases hwp : G.Adj w p
    · exact ⟨q,hq,fun hwq => sq (Ne.symm ne) pq hp hwp.symm hwq (G.adj_symm hq)⟩
    · exact ⟨p,hp,hwp⟩
  let X : Finset (Fin n) := {w,z}
  have hquiet : val C (point X) C.output = false := point_pair_quiet eval hwz
  have hy : val C (point (insert u X)) C.output = true :=
    (edge_of_point eval).2 ⟨u,by simp,z,by simp [X],huz⟩
  have h1 := (carries_iff mono).1 cw
  have hx := acts_mono mono (point_mono (show ({w} : Finset _) ⊆ X by simp [X])) a h1.1
  have hx' := acts_mono mono (point_mono (Finset.subset_insert u X)) a hx
  have bad := value_at_ineligible_carrier hu live cu (x := point X) (y := point (insert u X))
    (fun _ hi => (point_insert hi).symm) (hx.trans hx'.symm)
  exact Bool.noConfusion (hquiet.symm.trans (bad.trans hy))

def Meets (C : Circuit) (v u : Fin n) (j : ℕ) : Prop :=
  ∃ a b, LNext n C a j ∧ LNext n C b j ∧
    Carries C v a ∧ ¬ Carries C v b ∧ Carries C u b ∧
    ¬ Carries C v j ∧ (∀ k, LNext n C k j → k = a ∨ k = b)

lemma meets_consumes {u v : Fin n} {j : ℕ} (h : Meets C v u j) : Consumes C v j := by
  obtain ⟨a,_,ha,_,ca,_,_,cj,_⟩ := h
  exact ⟨a,ha,ca,cj⟩

lemma edge_meets (mono : Monotone2 C) (eval : GraphEval C G) {u v : Fin n}
    (adj : G.Adj v u) : ∃ j ∈ living n C, Meets C v u j := by
  obtain ⟨p,g,a,b,hg,hand,hj,ha,hb,hva,_,hub,hvb,hs⟩ := meeting_gate mono eval adj
  have mem (i : ℕ) (hi : LNext n C i (n+p)) : i ∈ g.inputs := by
    obtain ⟨⟨_,k,other,hother,eq,hmem⟩,_⟩ := hi
    have kp : k = p := by omega
    subst k
    rw [hg] at hother
    cases hother
    exact hmem
  have hbf : val C (point {v}) b = false := by
    rw [← Bool.not_eq_true]
    exact fun h => hvb ((carries_iff mono).2 ⟨h,((carries_iff mono).1 hub).2⟩)
  have killed : ¬ Carries C v (n+p) := by
    intro cv
    have ht := ((carries_iff mono).1 cv).1
    rw [val_gate C _ hg,hand,GateOp.eval,List.all_map,List.all_eq_true] at ht
    have on := ht b (mem b hb)
    simp [Function.comp_apply,operand,hb.1.1,hbf] at on
  exact ⟨n+p,mem_living.2 ⟨next_in_range ha.1,hj⟩,
    a,b,ha,hb,hva,hvb,hub,killed,fun i hi => hs i (mem i hi)⟩

lemma meets_other_unique (mono : Monotone2 C) (eval : GraphEval C G)
    (deg : ∀ u : Fin n, 2 ≤ (G.neighborSet u).ncard) (sq : NoSquare G)
    {v u w : Fin n} {j : ℕ} (hu : ¬Eligible C u)
    (m1 : Meets C v u j) (m2 : Meets C v w j) : w = u := by
  obtain ⟨a,b,_,hb,ca,_,cu,_,only⟩ := m1
  obtain ⟨_,d,_,hd,_,nd,cw,_,_⟩ := m2
  rcases only d hd with h | h
  · exact (nd (h ▸ ca)).elim
  · subst d
    exact ineligible_carrier_only mono eval hu (deg u) sq (live_before hb.1 hb.2) cu cw

open Classical in
lemma neighbor_slots (mono : Monotone2 C) (eval : GraphEval C G)
    (deg : ∀ u : Fin n, 2 ≤ (G.neighborSet u).ncard) (sq : NoSquare G)
    (v : Fin n) (T : Finset (Fin n)) (adj : ∀ u ∈ T, G.Adj v u)
    (one : ∀ u ∈ T, ∀ w ∈ T, Eligible C u → Eligible C w → u = w) :
    T.card ≤ ((living n C).filter (Consumes C v)).card := by
  classical
  let f (u : Fin n) := if h : u ∈ T then Nat.find (edge_meets mono eval (adj u h)) else 0
  have spec (u : Fin n) (hu : u ∈ T) : f u ∈ living n C ∧ Meets C v u (f u) := by
    simpa [f,hu] using Nat.find_spec (edge_meets mono eval (adj u hu))
  apply Finset.card_le_card_of_injOn f
  · intro u hu
    exact Finset.mem_filter.mpr ⟨(spec u hu).1,meets_consumes (spec u hu).2⟩
  · intro u hu w hw eq
    have m1 := (spec u hu).2
    have m2 := (spec w hw).2
    rw [← eq] at m2
    by_cases eu : Eligible C u
    · by_cases ew : Eligible C w
      · exact one u hu w hw eu ew
      · exact meets_other_unique mono eval deg sq ew m2 m1
    · exact (meets_other_unique mono eval deg sq eu m1 m2).symm

lemma tight_neighbor_slots {t : ℕ} [DecidableRel G.Adj]
    (deg : ∀ u : Fin n, 2 ≤ (G.neighborSet u).ncard) (sq : NoSquare G)
    (minCover : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (mono : Monotone2 C) (eval : GraphEval C G) (tight : C.size + 1 = n + t)
    (S : Finset (Fin n)) (sel : ∀ u, u ∈ S ↔ Eligible C u)
    {v : Fin n} (hv : v ∈ S) :
    ((G.neighborFinset v) \ S).card + (if ∃ w ∈ S, G.Adj v w then 1 else 0) ≤ 2 := by
  classical
  let T := (G.neighborFinset v) \ S
  have adj (u : Fin n) (hu : u ∈ T) : G.Adj v u :=
    (G.mem_neighborFinset v u).mp (Finset.mem_sdiff.mp hu).1
  have quiet (u : Fin n) (hu : u ∈ T) : ¬ Eligible C u :=
    fun eu => (Finset.mem_sdiff.mp hu).2 ((sel u).2 eu)
  let J := (living n C).filter (Consumes C v)
  have bound : J.card ≤ 2 :=
    consumptions_le_two deg sq minCover mono eval tight ((sel v).1 hv) J
      (fun _ h => (Finset.mem_filter.mp h).2)
  by_cases H : ∃ w ∈ S, G.Adj v w
  · obtain ⟨w,hw,hvw⟩ := H
    have hyes : ∃ w ∈ S, G.Adj v w := ⟨w,hw,hvw⟩
    have hwT : w ∉ T := fun h => (Finset.mem_sdiff.mp h).2 hw
    have localBound := neighbor_slots mono eval deg sq v (insert w T)
      (by intro u hu; rcases Finset.mem_insert.mp hu with rfl|h; exact hvw; exact adj u h)
      (by
        intro u hu z hz eu ez
        have hu' := (Finset.mem_insert.mp hu).resolve_right (fun h => quiet u h eu)
        have hz' := (Finset.mem_insert.mp hz).resolve_right (fun h => quiet z h ez)
        exact hu'.trans hz'.symm)
    simpa [hyes,Finset.card_insert_of_notMem hwT,T] using localBound.trans bound
  · have localBound := neighbor_slots mono eval deg sq v T adj
      (fun u hu _ _ eu _ => (quiet u hu eu).elim)
    simpa [H,T] using localBound.trans bound

end PEqualNP.Outside.L615Aux.Counting

namespace PEqualNP.Outside.L615Aux.Theta

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open scoped Sym2 BigOperators

lemma outside_of_minimal {n : ℕ} {G : SimpleGraph (Fin n)} (S : Finset (Fin n))
    (cov : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S)
    (minCov : ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card)
    {v : Fin n} (hv : v ∈ S) : ∃ w, G.Adj v w ∧ w ∉ S := by
  by_contra! all
  have hh := minCov (S.erase v) (by
    intro a b e
    by_cases ha : a=v
    · subst a
      exact Or.inr (Finset.mem_erase.mpr ⟨e.ne.symm,all _ e⟩)
    by_cases hb : b=v
    · subst b
      exact Or.inl (Finset.mem_erase.mpr ⟨e.ne,all _ e.symm⟩)
    rcases cov _ _ e with h | h
    · exact Or.inl (Finset.mem_erase.mpr ⟨ha,h⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hb,h⟩))
  exact (Finset.card_erase_lt_of_mem hv).not_ge hh

lemma total_slots_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n))
    (cov : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S)
    (minCov : ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card)
    (edges : G.edgeFinset.card = n+1) (small : 2*S.card ≤ n+1)
    (forest : let I := G.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ S)
              let A := S.filter (fun v => ∃ w ∈ S, G.Adj v w)
              I.Nonempty → I.card < A.card)
    (cap : ∀ v ∈ S, (G.neighborFinset v \ S).card +
      (if ∃ w ∈ S, G.Adj v w then 1 else 0) ≤ 2) : False := by
  classical
  let I := G.edgeFinset.filter (fun e => ∀ w ∈ e, w ∈ S)
  let A := S.filter (fun v => ∃ w ∈ S, G.Adj v w)
  let B (v : Fin n) := (G.neighborFinset v \ S).image (fun w => s(v,w))
  let Q := ∑ v ∈ S, (G.neighborFinset v \ S).card
  have toB {v w : Fin n} (hvw : G.Adj v w) (hw : w ∉ S) : s(v,w) ∈ B v :=
    Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw,hw⟩,rfl⟩
  have incl : G.edgeFinset ⊆ I ∪ (S.biUnion B) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have huv : G.Adj u v := G.mem_edgeFinset.mp he
      by_cases hu : u ∈ S
      · by_cases hv : v ∈ S
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          intro w hw
          rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u,hu,toB huv hv⟩)
      · have hv := (cov _ _ huv).resolve_left hu
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,hv,Sym2.eq_swap ▸ toB huv.symm hu⟩)
  have costB : (S.biUnion B).card ≤ Q := by
    apply (Finset.card_biUnion_le).trans
    exact Finset.sum_le_sum (fun v _ => show (B v).card ≤ _ from Finset.card_image_le)
  have edges' : G.edgeFinset.card ≤ I.card + Q :=
    (Finset.card_le_card incl).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left costB _))
  have total : Q + A.card ≤ 2*S.card := by
    have h := Finset.sum_le_sum cap
    have hA : (∑ v ∈ S, (if ∃ w ∈ S, G.Adj v w then 1 else 0 : ℕ)) = A.card := by
      rw [← Finset.sum_filter]
      simp [A]
    simpa only [Finset.sum_add_distrib, hA, Finset.sum_const, smul_eq_mul, Nat.mul_comm S.card 2,
      Q] using h
  by_cases hi : I.Nonempty
  · have h := forest hi
    change I.card < A.card at h
    omega
  · have hemi : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have compl : ∀ u v : Fin n, G.Adj u v → u ∈ Sᶜ ∨ v ∈ Sᶜ := by
      intro u v huv
      by_contra! both
      have hu : u ∈ S := by simpa using both.1
      have hv : v ∈ S := by simpa using both.2
      apply hi
      refine ⟨s(u,v),Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr huv,?_⟩⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption
    have hmin := minCov Sᶜ compl
    have hsum := Finset.card_compl_add_card S
    simp only [Fintype.card_fin] at hsum
    rw [hemi,Finset.card_empty,zero_add] at edges'
    omega

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside.L615Aux.Theta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L615Aux.Wires PEqualNP.Outside.L615Aux.Counting

lemma theta_exact (p q r t s : ℕ)
    (hp : p=0 → 1≤q ∧ 1≤r) (hq : q=0 → 1≤p ∧ 1≤r) (hr : r=0 → 1≤p ∧ 1≤q)
    (hpq : p+q≠2) (hpr : p+r≠2) (hqr : q+r≠2)
    (hcov : ∃ S : Finset (Fin (p+q+r+2)), (∀ u v : Fin (p+q+r+2),
      (u.val,v.val) ∈ thetaEdges p q r → u ∈ S ∨ v ∈ S) ∧ S.card = t)
    (hmin : ∀ S : Finset (Fin (p+q+r+2)), (∀ u v : Fin (p+q+r+2),
      (u.val,v.val) ∈ thetaEdges p q r → u ∈ S ∨ v ∈ S) → t ≤ S.card) :
    (∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin (p+q+r+2) → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin (p+q+r+2), (u.val,v.val) ∈ thetaEdges p q r ∧
          x u = true ∧ x v = true) ↔ p+q+r+2+t ≤ s := by
  classical
  constructor
  · rintro ⟨C,mono,hs,heval⟩
    let G := thetaGraph p q r
    have deg := theta_degrees p q r hp hq hr
    have sq : NoSquare G := by
      intro a b c d hac hbd hab hbc hcd hda
      have toNat {i j : Fin (p+q+r+2)} (h : i ≠ j) : i.val ≠ j.val :=
        fun e => h (Fin.ext e)
      exact theta_no_square hpq hpr hqr (toNat hab.ne) (toNat hac) (toNat hda.ne.symm)
        (toNat hbc.ne) (toNat hbd) (toNat hcd.ne) hab hbc hcd hda
    have minCov : ∀ S : Finset (Fin (p+q+r+2)),
        (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card := by
      intro S hS
      apply hmin S
      intro u v huv
      exact hS u v ((thetaGraph_adj p q r u v).mpr (Or.inl huv))
    have eval : GraphEval C G := by
      intro x
      change C.eval (List.ofFn x) = true ↔ _
      rw [heval]
      constructor
      · rintro ⟨u,v,huv,hu,hv⟩
        exact ⟨u,v,(thetaGraph_adj p q r u v).mpr (Or.inl huv),hu,hv⟩
      · rintro ⟨u,v,huv,hu,hv⟩
        rcases (thetaGraph_adj p q r u v).mp huv with h | h
        · exact ⟨u,v,h,hu,hv⟩
        · exact ⟨v,u,h,hv,hu⟩
    have weak := thetaLowerWithinOne G C deg sq minCov mono eval
    by_contra! smaller
    have tight : C.size+1 = p+q+r+2+t := by omega
    obtain ⟨S,sel,cov,sc,_⟩ := tight_branch_cover deg sq minCov mono eval tight
    have minS : ∀ T : Finset (Fin (p+q+r+2)),
        (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → S.card ≤ T.card := sc ▸ minCov
    apply total_slots_impossible G S cov minS
    · calc G.edgeFinset.card = G.edgeSet.ncard := (Set.ncard_eq_toFinset_card' _).symm
           _ = p+q+r+2+1 := theta_edge_count p q r hp hq
    · rw [sc]
      exact theta_min_cover_half minCov
    · apply theta_internal_strict S
      intro u hu
      obtain ⟨w,hw,ho⟩ := outside_of_minimal S cov minS hu
      exact ⟨w,ho,hw⟩
    · exact fun _ hv => tight_neighbor_slots deg sq minCov mono eval tight S sel hv
  · exact theta_upper p q r t s hcov

end PEqualNP.Outside.L615Aux.Theta

namespace PEqualNP.Outside

theorem L_meta_615 : ∀ p q r t s : ℕ, (p = 0 → 1 ≤ q ∧ 1 ≤ r) → (q = 0 → 1 ≤ p ∧ 1 ≤ r) → (r = 0 → 1 ≤ p ∧ 1 ≤ q) → p + q ≠ 2 → p + r ≠ 2 → q + r ≠ 2 → (∃ S : Finset (Fin (p + q + r + 2)), (∀ u v : Fin (p + q + r + 2), (u.val, v.val) ∈ (List.zip ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ) ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ) ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ) ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ).tail) → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin (p + q + r + 2)), (∀ u v : Fin (p + q + r + 2), (u.val, v.val) ∈ (List.zip ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ) ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ) ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ) ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ).tail) → u ∈ S ∨ v ∈ S) → t ≤ S.card) → ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin (p + q + r + 2) → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin (p + q + r + 2), (u.val, v.val) ∈ (List.zip ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ) ([0] ++ (List.range p).map (fun i => 2 + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ) ([0] ++ (List.range q).map (fun i => (2 + p) + i) ++ [1] : List ℕ).tail ++ List.zip ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ) ([0] ++ (List.range r).map (fun i => (2 + p + q) + i) ++ [1] : List ℕ).tail) ∧ x u = true ∧ x v = true)) ↔ p + q + r + 2 + t ≤ s) := by
  intro p q r t s hp hq hr hpq hpr hqr hcov hmin
  exact L615Aux.Theta.theta_exact p q r t s hp hq hr hpq hpr hqr hcov hmin

end PEqualNP.Outside
