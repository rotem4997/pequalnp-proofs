import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2050

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

def dstep (g : Gate) (d : List ℕ) : ℕ := g.lineDegree d

theorem dstep_or (a b : ℕ) (d : List ℕ) :
    dstep ⟨GateOp.or, [a, b]⟩ d = max (d.getD a 0) (d.getD b 0) := by
  simp [dstep, Gate.lineDegree]

theorem foldl_max_zero (g : ℕ → ℕ) : ∀ (l : List ℕ) (a : ℕ), a = 0 → (∀ i ∈ l, g i = 0) →
    l.foldl (fun v i => max v (g i)) a = 0
  | [], a, ha, _ => by simpa using ha
  | i :: is, a, ha, h => by
    rw [List.foldl_cons]
    exact foldl_max_zero g is _ (by rw [ha, h i (by simp)]; rfl)
      (fun k hk => h k (by simp [hk]))

theorem init_getD (N : ℕ) (marked : Finset ℕ) (i : ℕ) (hi : i < N) (hm : i ∉ marked) :
    ((List.range N).map fun i => if i ∈ marked then 1 else 0).getD i 0 = 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [hm]

theorem F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

theorem F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

def P (d : List ℕ) (b : List Gate) : Prop :=
  ∀ j < b.length, (∀ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, i < d.length + j) ∧
    ((b.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      ∃ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, (F dstep b d).getD i 0 = 0)

theorem P_app (d : List ℕ) (a b : List Gate) (ha : P d a) (hb : P (F dstep a d) b) :
    P d (a ++ b) := by
  intro j hj
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [List.getD_append _ _ _ _ h]
    obtain ⟨h1, h2⟩ := ha j h
    refine ⟨h1, fun hand => ?_⟩
    obtain ⟨i, hi, hz⟩ := h2 hand
    refine ⟨i, hi, ?_⟩
    have hlt := h1 i hi
    rw [F_append, F_pre dstep 0 b (F dstep a d) i (by rw [F_len]; omega)]
    exact hz
  · rw [List.getD_append_right _ _ _ _ h]
    have hj2 : j - a.length < b.length := by
      rw [List.length_append] at hj; omega
    obtain ⟨h1, h2⟩ := hb (j - a.length) hj2
    refine ⟨fun i hi => ?_, fun hand => ?_⟩
    · have := h1 i hi
      rw [F_len] at this; omega
    · obtain ⟨i, hi, hz⟩ := h2 hand
      exact ⟨i, hi, by rw [F_append]; exact hz⟩

theorem P_two (d : List ℕ) (op : GateOp) (a b : ℕ) (ha : a < d.length) (hb : b < d.length)
    (h2 : op = GateOp.and → d.getD a 0 = 0) : P d [⟨op, [a, b]⟩] := by
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  show (∀ i ∈ [a, b], i < d.length + 0) ∧
    (op = GateOp.and → ∃ i ∈ [a, b], (F dstep [⟨op, [a, b]⟩] d).getD i 0 = 0)
  refine ⟨fun i hi => ?_, fun hand => ⟨a, by simp, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi <;> omega
  · rw [F_one, List.getD_append _ _ _ _ ha]
    exact h2 hand

theorem P_chain : ∀ (ins : List ℕ) (acc w : ℕ) (d : List ℕ), d.length = w → acc < w →
    (∀ i ∈ ins, i < w) → P d (chain acc w ins)
  | [], _, _, _, _, _, _ => by
    intro j hj
    simp [chain] at hj
  | i :: is, acc, w, d, hw, hacc, hins => by
    have e : chain acc w (i :: is) = [⟨GateOp.or, [acc, i]⟩] ++ chain w (w + 1) is := rfl
    rw [e]
    apply P_app
    · exact P_two d GateOp.or acc i (by omega) (by have := hins i (by simp); omega)
        (fun h => by cases h)
    · exact P_chain is w (w + 1) _ (by simp [F_len, hw]) (by omega)
        (fun k hk => by have := hins k (by simp [hk]); omega)

def blk (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) : List Gate :=
  chain (hd l) w (tl l) ++ [⟨GateOp.and, [cfin (hd l) w (tl l), N + l]⟩]

theorem blk_len (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) :
    (blk N hd tl l w).length = (tl l).length + 1 := by
  simp [blk, chain_len]

theorem blk_shape (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) :
    ∀ g ∈ blk N hd tl l w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

theorem blk_P (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) (d : List ℕ)
    (hw : d.length = w) (h1 : hd l < w) (h2 : ∀ i ∈ tl l, i < w) (h3 : N + l < w)
    (z1 : d.getD (hd l) 0 = 0) (z2 : ∀ i ∈ tl l, d.getD i 0 = 0) :
    P d (blk N hd tl l w) := by
  obtain ⟨c1, c2, c3, c4⟩ := chain_spec dstep 0 max dstep_or (tl l) (hd l) w d hw h1 h2
  unfold blk
  apply P_app _ _ _ (P_chain (tl l) (hd l) w d hw h1 h2)
  exact P_two _ GateOp.and _ _ (by rw [c1]; exact c4) (by rw [c1]; omega)
    (fun _ => by rw [c3]; exact foldl_max_zero _ _ _ z1 z2)

theorem blk_val (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : hd l < w) (h2 : ∀ i ∈ tl l, i < w) (h3 : N + l < w) :
    (F wstep (blk N hd tl l w) d).getD (w + (tl l).length) false =
      ((d.getD (hd l) false || (tl l).any fun i => d.getD i false) && d.getD (N + l) false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or (tl l) (hd l) w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

theorem blk_iff (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (l w : ℕ) (d x : List Bool)
    (hw : d.length = w) (hpre : ∀ i < N + N, d.getD i false = x.getD i false)
    (h1 : hd l < N) (h2 : ∀ i ∈ tl l, i < N) (hl : l < N) (hNw : N + N ≤ w) :
    (F wstep (blk N hd tl l w) d).getD (w + (tl l).length) false = true ↔
      (x.getD (N + l) false = true ∧ ∃ i ∈ hd l :: tl l, x.getD i false = true) := by
  rw [blk_val N hd tl l w d hw (by omega) (fun i hi => by have := h2 i hi; omega) (by omega),
    Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, hpre (hd l) (by omega),
    hpre (N + l) (by omega)]
  constructor
  · rintro ⟨h | ⟨i, hi, h⟩, hy⟩
    · exact ⟨hy, hd l, by simp, h⟩
    · exact ⟨hy, i, by simp [hi], by rw [← hpre i (by have := h2 i hi; omega)]; exact h⟩
  · rintro ⟨hy, i, hi, h⟩
    refine ⟨?_, hy⟩
    rcases List.mem_cons.mp hi with e | hi2
    · rw [e] at h; exact Or.inl h
    · exact Or.inr ⟨i, hi2, by rw [hpre i (by have := h2 i hi2; omega)]; exact h⟩

def G (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) : ℕ → List Gate
  | 0 => blk N hd tl 0 (N + N)
  | k + 1 => G N hd tl k ++ blk N hd tl (k + 1) (N + N + (G N hd tl k).length) ++
      [⟨GateOp.or, [N + N + (G N hd tl k).length - 1,
        N + N + (G N hd tl k).length + (tl (k + 1)).length]⟩]

theorem G_len (N q : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (h3 : ∀ l, (tl l).length = q) :
    ∀ k, (G N hd tl k).length + 1 = (k + 1) * (q + 2)
  | 0 => by
    show (blk N hd tl 0 (N + N)).length + 1 = (0 + 1) * (q + 2)
    rw [blk_len, h3]
    omega
  | k + 1 => by
    have ih := G_len N q hd tl h3 k
    have e : (k + 1 + 1) * (q + 2) = (k + 1) * (q + 2) + (q + 2) := by ring
    rw [e]
    simp only [G, List.length_append, blk_len, h3, List.length_cons, List.length_nil]
    omega

theorem G_shape (N : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) :
    ∀ k, ∀ g ∈ G N hd tl k, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | 0 => by
    intro g hg
    simp only [G] at hg
    exact blk_shape N hd tl 0 (N + N) g hg
  | k + 1 => by
    intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact G_shape N hd tl k g hg
    · exact blk_shape _ _ _ _ _ g hg
    · exact ⟨Or.inr rfl, rfl⟩

def d0 (N : ℕ) : List ℕ :=
  (List.range (N + N)).map fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0

theorem d0_len (N : ℕ) : (d0 N).length = N + N := by
  simp [d0]

theorem d0_zero (N i : ℕ) (hi : i < N) : (d0 N).getD i 0 = 0 := by
  unfold d0
  exact init_getD (N + N) _ i (by omega) (by rw [Finset.mem_Ico]; omega)

theorem G_P (N q : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (h1 : ∀ l, hd l < N)
    (h2 : ∀ l, ∀ i ∈ tl l, i < N) (h3 : ∀ l, (tl l).length = q) :
    ∀ k, k < N → P (d0 N) (G N hd tl k)
  | 0, hk => by
    simp only [G]
    exact blk_P N hd tl 0 (N + N) (d0 N) (d0_len N) (by have := h1 0; omega)
      (fun i hi => by have := h2 0 i hi; omega) (by omega) (d0_zero N _ (h1 0))
      (fun i hi => d0_zero N i (h2 0 i hi))
  | k + 1, hk => by
    have ih := G_P N q hd tl h1 h2 h3 k (by omega)
    have hL : (F dstep (G N hd tl k) (d0 N)).length = N + N + (G N hd tl k).length := by
      rw [F_len, d0_len]
    have hz : ∀ i, i < N → (F dstep (G N hd tl k) (d0 N)).getD i 0 = 0 := by
      intro i hi
      rw [F_pre dstep 0 _ _ i (by rw [d0_len]; omega)]
      exact d0_zero N i hi
    simp only [G]
    apply P_app
    · apply P_app _ _ _ ih
      exact blk_P N hd tl (k + 1) _ _ hL (by have := h1 (k + 1); omega)
        (fun i hi => by have := h2 (k + 1) i hi; omega) (by omega) (hz _ (h1 (k + 1)))
        (fun i hi => hz i (h2 (k + 1) i hi))
    · exact P_two _ GateOp.or _ _
        (by rw [F_len, List.length_append, blk_len, d0_len]; omega)
        (by rw [F_len, List.length_append, blk_len, d0_len]; omega)
        (fun h => by cases h)

theorem G_val (N q : ℕ) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (h1 : ∀ l, hd l < N)
    (h2 : ∀ l, ∀ i ∈ tl l, i < N) (h3 : ∀ l, (tl l).length = q) (x : List Bool)
    (hx : x.length = N + N) :
    ∀ k, k < N →
      ((F wstep (G N hd tl k) x).getD (N + N + (G N hd tl k).length - 1) false = true ↔
        ∃ l, l ≤ k ∧ x.getD (N + l) false = true ∧ ∃ i ∈ hd l :: tl l, x.getD i false = true)
  | 0, hk => by
    have e : N + N + (G N hd tl 0).length - 1 = N + N + (tl 0).length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    rw [blk_iff N hd tl 0 (N + N) x x hx (fun i _ => rfl) (h1 0) (h2 0) hk (le_refl _)]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨0, le_refl _, a, b⟩
    · rintro ⟨l, hl, a, b⟩
      have hl0 : l = 0 := by omega
      subst hl0
      exact ⟨a, b⟩
  | k + 1, hk => by
    have ih := G_val N q hd tl h1 h2 h3 x hx k (by omega)
    have hL : (F wstep (G N hd tl k) x).length = N + N + (G N hd tl k).length := by
      rw [F_len, hx]
    have hpre : ∀ i < N + N, (F wstep (G N hd tl k) x).getD i false = x.getD i false :=
      fun i hi => F_pre wstep false _ _ i (by omega)
    have hb := blk_iff N hd tl (k + 1) (N + N + (G N hd tl k).length)
      (F wstep (G N hd tl k) x) x hL hpre (h1 (k + 1)) (h2 (k + 1)) hk (by omega)
    have hL2 : (F wstep (G N hd tl k ++ blk N hd tl (k + 1) (N + N + (G N hd tl k).length))
        x).length = N + N + (G N hd tl k).length + (tl (k + 1)).length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have e : N + N + (G N hd tl (k + 1)).length - 1 =
        N + N + (G N hd tl k).length + (tl (k + 1)).length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, wstep_or, Bool.or_eq_true]
    rw [F_append, F_pre wstep false _ _ (N + N + (G N hd tl k).length - 1)
      (by rw [hL]; omega), ih, hb]
    constructor
    · rintro (⟨l, hl2, a, b⟩ | ⟨a, b⟩)
      · exact ⟨l, by omega, a, b⟩
      · exact ⟨k + 1, le_refl _, a, b⟩
    · rintro ⟨l, hl2, a, b⟩
      rcases Nat.lt_or_ge l (k + 1) with h | h
      · exact Or.inl ⟨l, by omega, a, b⟩
      · have hl0 : l = k + 1 := by omega
        subst hl0
        exact Or.inr ⟨a, b⟩

theorem core (N q : ℕ) (hN : 0 < N) (hd : ℕ → ℕ) (tl : ℕ → List ℕ) (h1 : ∀ l, hd l < N)
    (h2 : ∀ l, ∀ i ∈ tl l, i < N) (h3 : ∀ l, (tl l).length = q) :
    ∃ C : Circuit,
      ((∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        NestedCover.ReadsBack (N + N) C) ∧
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
        (∃ i ∈ (NestedCover.gateAt C j).inputs,
          (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
        (∀ h ∈ (NestedCover.gateAt C j).inputs,
          (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0)) ∧
      C.size + 1 = (q + 2) * N ∧
      ∀ x : List Bool, x.length = N + N → (C.eval x = true ↔
        ∃ l, l < N ∧ x.getD (N + l) false = true ∧
          ∃ i ∈ hd l :: tl l, x.getD i false = true) := by
  have hP := G_P N q hd tl h1 h2 h3 (N - 1) (by omega)
  refine ⟨⟨G N hd tl (N - 1), N + N + (G N hd tl (N - 1)).length - 1⟩,
    ⟨G_shape N hd tl (N - 1), ?_⟩, ?_, ?_, ?_⟩
  · show ∀ j < (G N hd tl (N - 1)).length,
      ∀ i ∈ ((G N hd tl (N - 1)).getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j
    intro j hj i hi
    have := (hP j hj).1 i hi
    rw [d0_len] at this
    exact this
  · intro j hj hand
    exact Or.inl ((hP j hj).2 hand)
  · have := G_len N q hd tl h3 (N - 1)
    have e : N - 1 + 1 = N := by omega
    rw [e] at this
    show (G N hd tl (N - 1)).length + 1 = (q + 2) * N
    rw [this, Nat.mul_comm]
  · intro x hx
    have := G_val N q hd tl h1 h2 h3 x hx (N - 1) (by omega)
    show (F wstep (G N hd tl (N - 1)) x).getD (N + N + (G N hd tl (N - 1)).length - 1) false
      = true ↔ _
    rw [this]
    constructor
    · rintro ⟨l, hl, a⟩
      exact ⟨l, by omega, a⟩
    · rintro ⟨l, hl, a⟩
      exact ⟨l, by omega, a⟩

theorem main : ∀ (q271 N271 : ℕ) (I271 : Fin N271 → Fin N271 → Prop) [DecidableRel I271], 2 ≤ q271 → N271 = q271 ^ 2 + q271 + 1 → (∀ l271 : Fin N271, (Finset.univ.filter (fun p271 => I271 p271 l271)).card = q271 + 1) → (∀ pa271 pb271 : Fin N271, pa271 ≠ pb271 → ∃! lb271 : Fin N271, I271 pa271 lb271 ∧ I271 pb271 lb271) → ∃ C271 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g271 ∈ C271.gates, (g271.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g271.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g271.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N271 + N271) C271) ∧ (∀ j271 < C271.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.Ico N271 (N271 + N271))).getD i271 0 = 0) ∨ (∀ h271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.range N271)).getD h271 0 = 0)) ∧ C271.size + 1 = (q271 + 2) * N271 ∧ (∀ x271 y271 : Fin N271 → Bool, PEqualNP.MetaComplexity.circuitFun (N271 + N271) C271 (Fin.append x271 y271) = decide (∃ p271x1 w271 : Fin N271, I271 p271x1 w271 ∧ x271 p271x1 = true ∧ y271 w271 = true)) := by
  intro q N I _ _ hN hcard _
  have hNpos : 0 < N := by rw [hN]; exact Nat.succ_pos _
  have key : ∀ l : Fin N, ∃ (a : ℕ) (t : List ℕ), a < N ∧ (∀ i ∈ t, i < N) ∧ t.length = q ∧
      ∀ p : Fin N, I p l ↔ p.val ∈ a :: t := by
    intro l
    obtain ⟨L, hL⟩ : ∃ L : List ℕ,
      L = (Finset.univ.filter (fun p => I p l)).toList.map Fin.val := ⟨_, rfl⟩
    have hlen : L.length = q + 1 := by
      rw [hL, List.length_map, Finset.length_toList, hcard l]
    have hlt : ∀ i ∈ L, i < N := by
      intro i hi
      rw [hL] at hi
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hi
      rw [← hp]
      exact p.isLt
    have hmem : ∀ p : Fin N, I p l ↔ p.val ∈ L := by
      intro p
      rw [hL]
      constructor
      · intro h
        exact List.mem_map.mpr ⟨p, Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), rfl⟩
      · intro h
        obtain ⟨p2, hp2, e⟩ := List.mem_map.mp h
        have e2 : p2 = p := Fin.ext e
        rw [← e2]
        exact (Finset.mem_filter.mp (Finset.mem_toList.mp hp2)).2
    cases L with
    | nil => simp at hlen
    | cons a t =>
      exact ⟨a, t, hlt a (by simp), fun i hi => hlt i (by simp [hi]), by simpa using hlen, hmem⟩
  choose a t ha ht hlen hmem using key
  obtain ⟨hd, ehd, h1⟩ : ∃ hd : ℕ → ℕ, (∀ l (h : l < N), hd l = a ⟨l, h⟩) ∧ ∀ l, hd l < N := by
    refine ⟨fun l => if h : l < N then a ⟨l, h⟩ else 0, fun l h => dif_pos h, fun l => ?_⟩
    show (if h : l < N then a ⟨l, h⟩ else 0) < N
    split_ifs with h
    · exact ha _
    · exact hNpos
  obtain ⟨tl, etl, h2, h3⟩ : ∃ tl : ℕ → List ℕ, (∀ l (h : l < N), tl l = t ⟨l, h⟩) ∧
      (∀ l, ∀ i ∈ tl l, i < N) ∧ ∀ l, (tl l).length = q := by
    refine ⟨fun l => if h : l < N then t ⟨l, h⟩ else List.replicate q 0, fun l h => dif_pos h,
      fun l => ?_, fun l => ?_⟩
    · show ∀ i ∈ (if h : l < N then t ⟨l, h⟩ else List.replicate q 0), i < N
      split_ifs with h
      · exact ht _
      · intro i hi
        rw [List.eq_of_mem_replicate hi]
        exact hNpos
    · show (if h : l < N then t ⟨l, h⟩ else List.replicate q 0).length = q
      split_ifs with h
      · exact hlen _
      · simp
  obtain ⟨C, hA, hB, hC, hE⟩ := core N q hNpos hd tl h1 h2 h3
  refine ⟨C, hA, hB, hC, ?_⟩
  intro x y
  have gx : ∀ i (hi : i < N), (List.ofFn (Fin.append x y)).getD i false = x ⟨i, hi⟩ := by
    intro i hi
    rw [ofFn_getD _ i (by omega)]
    exact Fin.append_left x y ⟨i, hi⟩
  have gy : ∀ l (hl : l < N), (List.ofFn (Fin.append x y)).getD (N + l) false = y ⟨l, hl⟩ := by
    intro l hl
    rw [ofFn_getD _ (N + l) (by omega)]
    exact Fin.append_right x y ⟨l, hl⟩
  have hev := hE (List.ofFn (Fin.append x y)) (by simp)
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  show C.eval (List.ofFn (Fin.append x y)) = true ↔ _
  rw [hev]
  constructor
  · rintro ⟨l, hl, hy, i, hi, hx⟩
    rw [ehd l hl, etl l hl] at hi
    have hiN : i < N := by
      rcases List.mem_cons.mp hi with e | e
      · rw [e]; exact ha _
      · exact ht _ i e
    rw [gx i hiN] at hx
    rw [gy l hl] at hy
    exact ⟨⟨i, hiN⟩, ⟨l, hl⟩, (hmem ⟨l, hl⟩ ⟨i, hiN⟩).mpr hi, hx, hy⟩
  · rintro ⟨p, w, hI, hx, hy⟩
    refine ⟨w.val, w.isLt, ?_, p.val, ?_, ?_⟩
    · rw [gy w.val w.isLt]; exact hy
    · rw [ehd w.val w.isLt, etl w.val w.isLt]; exact (hmem w p).mp hI
    · rw [gx p.val p.isLt]; exact hx

end PEqualNP.Outside.L_meta_2050

theorem PEqualNP.Outside.L_meta_2050 : ∀ (q271 N271 : ℕ) (I271 : Fin N271 → Fin N271 → Prop) [DecidableRel I271], 2 ≤ q271 → N271 = q271 ^ 2 + q271 + 1 → (∀ l271 : Fin N271, (Finset.univ.filter (fun p271 => I271 p271 l271)).card = q271 + 1) → (∀ pa271 pb271 : Fin N271, pa271 ≠ pb271 → ∃! lb271 : Fin N271, I271 pa271 lb271 ∧ I271 pb271 lb271) → ∃ C271 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g271 ∈ C271.gates, (g271.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g271.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g271.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N271 + N271) C271) ∧ (∀ j271 < C271.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.Ico N271 (N271 + N271))).getD i271 0 = 0) ∨ (∀ h271 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C271 j271).inputs, (C271.lineDegrees (N271 + N271) (Finset.range N271)).getD h271 0 = 0)) ∧ C271.size + 1 = (q271 + 2) * N271 ∧ (∀ x271 y271 : Fin N271 → Bool, PEqualNP.MetaComplexity.circuitFun (N271 + N271) C271 (Fin.append x271 y271) = decide (∃ p271x1 w271 : Fin N271, I271 p271x1 w271 ∧ x271 p271x1 = true ∧ y271 w271 = true)) := by
  exact PEqualNP.Outside.L_meta_2050.main
