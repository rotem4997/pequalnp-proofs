import Mathlib
import PEqualNP.Defs

-- Circuit builder helpers adapted from PEqualNP/MetaComplexity/Helpers/EdgeUpper.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3999

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section CircuitBuilder

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (w : List Bool) : C.wires w = wiresFrom C.gates w := rfl

theorem wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) :
    ∀ w : List Bool, (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    simp only [wiresFrom, List.foldl_cons]
    rw [← wiresFrom, ih]
    simp
    omega

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_wiresFrom (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [wiresFrom, List.foldl_cons]
    rw [← wiresFrom, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
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

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) (fun x => by simp)

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
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

theorem bld_stars {n : ℕ} (N : Fin n → Finset (Fin n)) (hN : ∀ a, (N a).Nonempty ∧ (N a).card ≤ 3) :
    ∀ (as : List (Fin n)) (a0 : Fin n),
    Bld n (fun x => (a0 :: as).any fun a => x a && decide (∃ b ∈ N a, x b = true)) (4 * as.length + 3) := by
  intro as
  induction as with
  | nil =>
    intro a0
    have hstar := bld_and (bld_var a0) (bld_anyFinset (N a0) (hN a0).1)
    have hc := (hN a0).2
    refine bld_congr (bld_mono hstar (by omega)) (fun x => by simp)
  | cons a1 tl ih =>
    intro a0
    have hstar := bld_and (bld_var a0) (bld_anyFinset (N a0) (hN a0).1)
    have hc := (hN a0).2
    have hcomb := bld_or hstar (ih a1)
    refine bld_congr (bld_mono hcomb (by simp; omega)) (fun x => by simp)

theorem bld_starFinset {n : ℕ} (N : Fin n → Finset (Fin n)) (hN : ∀ a, (N a).Nonempty ∧ (N a).card ≤ 3)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ a ∈ S, x a = true ∧ ∃ b ∈ N a, x b = true)) (4 * S.card - 1) := by
  obtain ⟨a0, as, hl⟩ : ∃ a0 as, S.toList = a0 :: as := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons a0 as => exact ⟨a0, as, rfl⟩
  have hc : S.card = as.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_stars N hN as a0) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp only [Finset.mem_toList, Bool.and_eq_true, decide_eq_true_iff]

end CircuitBuilder

section MooreAndCover

theorem four_cycle_false {n : ℕ} (G : SimpleGraph (Fin n))
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length)
    {v0 v1 v2 v3 : Fin n}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (e0 : G.Adj v0 v1) (e1 : G.Adj v1 v2) (e2 : G.Adj v2 v3) (e3 : G.Adj v3 v0) : False := by
  let p : G.Walk v0 v0 := .cons e0 (.cons e1 (.cons e2 (.cons e3 .nil)))
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    refine ⟨?_, by simp [p], ?_⟩
    · simp only [p, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
        Sym2.eq_iff]
      tauto
    · simp only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      tauto
  have hlen : p.length = 4 := rfl
  have hg := hgirth v0 p hcyc
  omega

theorem six_cycle_false {n : ℕ} (G : SimpleGraph (Fin n))
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length)
    {v0 v1 v2 v3 v4 v5 : Fin n}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3) (h04 : v0 ≠ v4) (h05 : v0 ≠ v5)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h14 : v1 ≠ v4) (h15 : v1 ≠ v5)
    (h23 : v2 ≠ v3) (h24 : v2 ≠ v4) (h25 : v2 ≠ v5)
    (h34 : v3 ≠ v4) (h35 : v3 ≠ v5) (h45 : v4 ≠ v5)
    (e0 : G.Adj v0 v1) (e1 : G.Adj v1 v2) (e2 : G.Adj v2 v3)
    (e3 : G.Adj v3 v4) (e4 : G.Adj v4 v5) (e5 : G.Adj v5 v0) : False := by
  let p : G.Walk v0 v0 := .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))))
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    refine ⟨?_, by simp [p], ?_⟩
    · simp only [p, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
        Sym2.eq_iff]
      tauto
    · simp only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      tauto
  have hlen : p.length = 6 := rfl
  have hg := hgirth v0 p hcyc
  omega

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool)
    (hcol : G.Colorable 2)
    (hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 3)
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length)
    (hedge : ∃ a b : Fin n, G.Adj a b)
    (hf : ∀ x : Fin n → Bool, f x = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) :
    30 ≤ n ∧ Even n ∧ ∃ u w : Fin n, u ≠ w ∧ ¬ G.Adj u w ∧ ∃ s : ℕ, s + 9 ≤ 2 * n ∧
      HasCircuitSize n (fun x : Fin n → Bool => f (Function.update (Function.update x u false) w false)) s := by
  obtain ⟨C⟩ := hcol
  have hvalid : ∀ {x y : Fin n}, G.Adj x y → C x ≠ C y := fun h => C.valid h
  let N : Fin n → Finset (Fin n) := fun v => Finset.univ.filter (fun w => G.Adj v w)
  have hmemN : ∀ v w : Fin n, w ∈ N v ↔ G.Adj v w := by
    intro v w; simp [N]
  have hdegF : ∀ v : Fin n, (N v).card = 3 := by
    intro v
    have e : G.neighborSet v = ↑(N v) := by
      ext w; simp [N, SimpleGraph.mem_neighborSet]
    rw [← hdeg v, e, Set.ncard_coe_finset]
  have hcol01 : ∀ v : Fin n, C v = 0 ∨ C v = 1 := by
    intro v
    rcases h : C v with ⟨k, hk⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  let A : Finset (Fin n) := Finset.univ.filter (fun v => C v = 0)
  let B : Finset (Fin n) := Finset.univ.filter (fun v => C v = 1)
  have hmemA : ∀ v, v ∈ A ↔ C v = 0 := fun v => by simp [A]
  have hmemB : ∀ v, v ∈ B ↔ C v = 1 := fun v => by simp [B]
  have hneAB : ∀ {a b}, a ∈ A → b ∈ B → a ≠ b := by
    intro a b ha hb rfl
    rw [hmemA] at ha; rw [hmemB] at hb; rw [ha] at hb; exact absurd hb (by decide)
  have hAB_disj : Disjoint A B := Finset.disjoint_left.mpr fun v hvA hvB => hneAB hvA hvB rfl
  have hAB_union : A ∪ B = Finset.univ := by
    ext v; simp only [Finset.mem_union, hmemA, hmemB, Finset.mem_univ, iff_true]; exact hcol01 v
  have hn_eq : A.card + B.card = n := by
    rw [← Finset.card_union_of_disjoint hAB_disj, hAB_union, Finset.card_univ, Fintype.card_fin]
  have hNA_sub_B : ∀ {a}, a ∈ A → N a ⊆ B := by
    intro a ha w hw
    rw [hmemB]
    have hne := hvalid ((hmemN a w).mp hw)
    rw [(hmemA a).mp ha] at hne
    rcases hcol01 w with hw0 | hw1
    · exact absurd hw0.symm hne
    · exact hw1
  have hNB_sub_A : ∀ {b}, b ∈ B → N b ⊆ A := by
    intro b hb w hw
    rw [hmemA]
    have hne := hvalid ((hmemN b w).mp hw)
    rw [(hmemB b).mp hb] at hne
    rcases hcol01 w with hw0 | hw1
    · exact hw0
    · exact absurd hw1.symm hne
  -- Double counting edges between A and B: 3 * A.card = 3 * B.card
  have hsumA : (∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then (1 : ℕ) else 0) = 3 * A.card := by
    have h1 : ∀ a ∈ A, (∑ b ∈ B, if G.Adj a b then (1 : ℕ) else 0) = 3 := by
      intro a ha
      rw [Finset.sum_boole, Nat.cast_id]
      have heq : B.filter (fun b => G.Adj a b) = N a := by
        ext b; simp only [Finset.mem_filter, hmemN]
        exact ⟨fun h => h.2, fun h => ⟨hNA_sub_B ha ((hmemN a b).mpr h), h⟩⟩
      rw [heq, hdegF a]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsumB : (∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then (1 : ℕ) else 0) = 3 * B.card := by
    rw [Finset.sum_comm]
    have h1 : ∀ b ∈ B, (∑ a ∈ A, if G.Adj a b then (1 : ℕ) else 0) = 3 := by
      intro b hb
      rw [Finset.sum_boole, Nat.cast_id]
      have heq : A.filter (fun a => G.Adj a b) = N b := by
        ext a; simp only [Finset.mem_filter, hmemN]
        exact ⟨fun h => SimpleGraph.adj_symm G h.2, fun h => ⟨hNB_sub_A hb ((hmemN b a).mpr h), SimpleGraph.adj_symm G h⟩⟩
      rw [heq, hdegF b]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_comm]
  have hAB_card : A.card = B.card := by omega
  -- Pick u0 ∈ A from hedge
  obtain ⟨e_x, e_y, he_xy⟩ := hedge
  have hexA : ∃ u0, u0 ∈ A := by
    rcases hcol01 e_x with hx0 | hx1
    · exact ⟨e_x, (hmemA e_x).mpr hx0⟩
    · exact ⟨e_y, (hmemA e_y).mpr ((hNB_sub_A ((hmemB e_x).mpr hx1) ((hmemN e_x e_y).mpr he_xy)) |> (hmemA e_y).mp)⟩
  obtain ⟨u0, hu0A⟩ := hexA
  -- Moore bound in B: N1 has 3 vertices, N3 has 6 * 2 = 12 vertices disjoint from N1
  let N1 : Finset (Fin n) := N u0
  have hN1_sub : N1 ⊆ B := hNA_sub_B hu0A
  have hN1_card : N1.card = 3 := hdegF u0
  let S2 : Fin n → Finset (Fin n) := fun b => (N b).erase u0
  have hS2_card : ∀ b ∈ N1, (S2 b).card = 2 := by
    intro b hb
    have hu0_mem : u0 ∈ N b := (hmemN b u0).mpr (SimpleGraph.adj_symm G ((hmemN u0 b).mp hb))
    rw [Finset.card_erase_of_mem hu0_mem, hdegF b]
  let P2 : Finset (Σ _ : Fin n, Fin n) := N1.sigma S2
  have hP2_card : P2.card = 6 := by
    rw [Finset.card_sigma, Finset.sum_congr rfl hS2_card, Finset.sum_const, hN1_card, smul_eq_mul]
  let S3 : (Σ _ : Fin n, Fin n) → Finset (Fin n) := fun p => (N p.2).erase p.1
  have hP2_facts : ∀ {p}, p ∈ P2 →
      p.1 ∈ N1 ∧ p.1 ∈ B ∧ p.2 ∈ A ∧ p.2 ≠ u0 ∧ G.Adj u0 p.1 ∧ G.Adj p.1 p.2 := by
    intro p hp
    obtain ⟨hb1, ha2⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hane, hab⟩ := Finset.mem_erase.mp ha2
    exact ⟨hb1, hN1_sub hb1, hNB_sub_A (hN1_sub hb1) hab, hane, (hmemN u0 p.1).mp hb1, (hmemN p.1 p.2).mp hab⟩
  have hS3_card : ∀ p ∈ P2, (S3 p).card = 2 := by
    intro p hp
    obtain ⟨_, _, _, _, _, e12⟩ := hP2_facts hp
    have hp1_mem : p.1 ∈ N p.2 := (hmemN p.2 p.1).mpr (SimpleGraph.adj_symm G e12)
    rw [Finset.card_erase_of_mem hp1_mem, hdegF p.2]
  have hS3_sub : ∀ {p}, p ∈ P2 → S3 p ⊆ B \ N1 := by
    intro p hp w hw
    obtain ⟨_, hbB, haA, hane, e01, e12⟩ := hP2_facts hp
    obtain ⟨hwne, hwa⟩ := Finset.mem_erase.mp hw
    have hwB : w ∈ B := hNA_sub_B haA hwa
    refine Finset.mem_sdiff.mpr ⟨hwB, fun hwN1 => ?_⟩
    exact four_cycle_false G hgirth
      (hneAB hu0A hbB) hane.symm (hneAB hu0A hwB)
      (hneAB haA hbB).symm hwne.symm (hneAB haA hwB)
      e01 e12 ((hmemN p.2 w).mp hwa) (SimpleGraph.adj_symm G ((hmemN u0 w).mp hwN1))
  have hS3_disj : (P2 : Set (Σ _ : Fin n, Fin n)).PairwiseDisjoint S3 := by
    intro p1 hp1 p2 hp2 hpne
    change Disjoint (S3 p1) (S3 p2)
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨hb1N1, hb1B, ha1A, ha1ne, e_u_b1, e_b1_a1⟩ := hP2_facts hp1
    obtain ⟨hb2N1, hb2B, ha2A, ha2ne, e_u_b2, e_b2_a2⟩ := hP2_facts hp2
    have hw_sdiff := hS3_sub hp1 hw1
    obtain ⟨hwB, hw_notN1⟩ := Finset.mem_sdiff.mp hw_sdiff
    obtain ⟨hw_neb1, hwa1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨hw_neb2, hwa2⟩ := Finset.mem_erase.mp hw2
    have e_a1_w : G.Adj p1.2 w := (hmemN p1.2 w).mp hwa1
    have e_a2_w : G.Adj p2.2 w := (hmemN p2.2 w).mp hwa2
    by_cases hb_eq : p1.1 = p2.1
    · have ha_ne : p1.2 ≠ p2.2 := by
        intro ha_eq
        apply hpne
        cases p1; cases p2
        simp only at hb_eq ha_eq
        subst hb_eq; subst ha_eq; rfl
      rw [← hb_eq] at e_b2_a2
      exact four_cycle_false G hgirth
        (hneAB ha1A hb1B).symm hw_neb1.symm (hneAB ha2A hb1B).symm
        (hneAB ha1A hwB) ha_ne (hneAB ha2A hwB).symm
        e_b1_a1 e_a1_w (SimpleGraph.adj_symm G e_a2_w) (SimpleGraph.adj_symm G e_b2_a2)
    · by_cases ha_eq : p1.2 = p2.2
      · rw [← ha_eq] at e_b2_a2
        exact four_cycle_false G hgirth
          (hneAB hu0A hb1B) ha1ne.symm (hneAB hu0A hb2B)
          (hneAB ha1A hb1B).symm hb_eq (hneAB ha1A hb2B)
          e_u_b1 e_b1_a1 (SimpleGraph.adj_symm G e_b2_a2) (SimpleGraph.adj_symm G e_u_b2)
      · exact six_cycle_false G hgirth
          (hneAB hu0A hb1B) ha1ne.symm (hneAB hu0A hwB) ha2ne.symm (hneAB hu0A hb2B)
          (hneAB ha1A hb1B).symm hw_neb1.symm (hneAB ha2A hb1B).symm hb_eq
          (hneAB ha1A hwB) ha_eq (hneAB ha1A hb2B)
          (hneAB ha2A hwB).symm hw_neb2 (hneAB ha2A hb2B)
          e_u_b1 e_b1_a1 e_a1_w (SimpleGraph.adj_symm G e_a2_w) (SimpleGraph.adj_symm G e_b2_a2) (SimpleGraph.adj_symm G e_u_b2)
  let N3 : Finset (Fin n) := P2.biUnion S3
  have hN3_card : N3.card = 12 := by
    rw [Finset.card_biUnion hS3_disj, Finset.sum_congr rfl hS3_card, Finset.sum_const, hP2_card, smul_eq_mul]
  have hN3_sub : N3 ⊆ B \ N1 := Finset.biUnion_subset.mpr fun p hp => hS3_sub hp
  have hN13_disj : Disjoint N1 N3 :=
    Finset.disjoint_left.mpr fun w hw1 hw3 => (Finset.mem_sdiff.mp (hN3_sub hw3)).2 hw1
  have hN13_sub : N1 ∪ N3 ⊆ B := Finset.union_subset hN1_sub (hN3_sub.trans Finset.sdiff_subset)
  have hB15 : 15 ≤ B.card := by
    have hc := Finset.card_le_card hN13_sub
    rw [Finset.card_union_of_disjoint hN13_disj, hN1_card, hN3_card] at hc
    exact hc
  have hn30 : 30 ≤ n := by omega
  have heven : Even n := ⟨A.card, by omega⟩
  -- Pick two distinct vertices u, w in A
  have hA_gt1 : 1 < A.card := by omega
  obtain ⟨u, huA, w, hwA, huw⟩ := Finset.one_lt_card.mp hA_gt1
  have hnotAdj : ¬ G.Adj u w := by
    intro hadj
    have hne := hvalid hadj
    rw [(hmemA u).mp huA, (hmemA w).mp hwA] at hne
    exact hne rfl
  let A' : Finset (Fin n) := (A.erase u).erase w
  have hw_er : w ∈ A.erase u := Finset.mem_erase.mpr ⟨huw.symm, hwA⟩
  have hA'_card : A'.card + 2 = A.card := by
    rw [Finset.card_erase_of_mem hw_er, Finset.card_erase_of_mem huA]
    omega
  have hA'_ne : A'.Nonempty := Finset.card_pos.mp (by omega)
  have hN_ok : ∀ a, (N a).Nonempty ∧ (N a).card ≤ 3 := by
    intro a
    refine ⟨Finset.card_pos.mp (by rw [hdegF a]; omega), by rw [hdegF a]⟩
  have hbld := bld_starFinset N hN_ok A' hA'_ne
  have hbld' := bld_congr hbld (H := fun x => f (Function.update (Function.update x u false) w false)) ?_
  · refine ⟨hn30, heven, u, w, huw, hnotAdj, 4 * A'.card - 1, by omega, bld_hasCircuitSize hbld'⟩
  · intro x
    let x' := Function.update (Function.update x u false) w false
    have hx'B : ∀ {b}, b ∈ B → x' b = x b := by
      intro b hb
      have hbw : b ≠ w := (hneAB hwA hb).symm
      have hbu : b ≠ u := (hneAB huA hb).symm
      simp [x', Function.update_of_ne hbw, Function.update_of_ne hbu]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hf x']
    constructor
    · rintro ⟨a, ha', hxa, b, hbN, hxb⟩
      obtain ⟨haw, ha_er⟩ := Finset.mem_erase.mp ha'
      obtain ⟨hau, haA⟩ := Finset.mem_erase.mp ha_er
      have hadj : G.Adj a b := (hmemN a b).mp hbN
      have hbB : b ∈ B := hNA_sub_B haA hbN
      refine ⟨a, b, hadj, ?_, ?_⟩
      · simp [x', Function.update_of_ne haw, Function.update_of_ne hau, hxa]
      · rw [hx'B hbB]; exact hxb
    · rintro ⟨p, q, hpq, hxp, hxq⟩
      rcases hcol01 p with hp0 | hp1
      · have hpA : p ∈ A := (hmemA p).mpr hp0
        have hqB : q ∈ B := hNA_sub_B hpA ((hmemN p q).mpr hpq)
        have hpw : p ≠ w := by intro rfl; simp [x'] at hxp
        have hpu : p ≠ u := by
          intro rfl
          simp [x', Function.update_of_ne hpw] at hxp
        refine ⟨p, Finset.mem_erase.mpr ⟨hpw, Finset.mem_erase.mpr ⟨hpu, hpA⟩⟩, ?_,
          q, (hmemN p q).mpr hpq, ?_⟩
        · simpa [x', Function.update_of_ne hpw, Function.update_of_ne hpu] using hxp
        · rwa [← hx'B hqB]
      · have hpB : p ∈ B := (hmemB p).mpr hp1
        have hqA : q ∈ A := hNB_sub_A hpB ((hmemN p q).mpr hpq)
        have hqw : q ≠ w := by intro rfl; simp [x'] at hxq
        have hqu : q ≠ u := by
          intro rfl
          simp [x', Function.update_of_ne hqw] at hxq
        refine ⟨q, Finset.mem_erase.mpr ⟨hqw, Finset.mem_erase.mpr ⟨hqu, hqA⟩⟩, ?_,
          p, (hmemN q p).mpr (SimpleGraph.adj_symm G hpq), ?_⟩
        · simpa [x', Function.update_of_ne hqw, Function.update_of_ne hqu] using hxq
        · rwa [← hx'B hpB]

end MooreAndCover

end PEqualNP.Outside.L_meta_3999

theorem PEqualNP.Outside.L_meta_3999 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → (30 : ℕ) ≤ x1 ∧ Even x1 ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), x9 ≠ x10 ∧ ¬x2.Adj x9 x10 ∧ ∃ (x11 : ℕ), x11 + (9 : ℕ) ≤ (2 : ℕ) * x1 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update (Function.update x12 x9 Bool.false) x10 Bool.false)) x11 :=
  PEqualNP.Outside.L_meta_3999.main
