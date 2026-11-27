import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim

namespace PEqualNP.Outside.L_meta_659

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open SimpleGraph

/-! ### Part 1: Multi-output circuit predicate, relabeling, and 1-gate / 2-gate elimination -/

private def HasMulti (m k : ℕ) (f : (Fin m → Bool) → Bool)
    (G : Fin k → (Fin m → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
    ∃ (o1 : ℕ) (o : Fin k → ℕ), ∀ x : Fin m → Bool,
      (C.wires (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x

private def HasG (m k : ℕ) (G : Fin k → (Fin m → Bool) → Bool) (t : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ t ∧
    ∃ o : Fin k → ℕ, ∀ (x : Fin m → Bool) (j : Fin k),
      (C.wires (List.ofFn x)).getD (o j) false = G j x

private lemma hasMulti_mono {m k s s' : ℕ} {f : (Fin m → Bool) → Bool}
    {G : Fin k → (Fin m → Bool) → Bool} (h : HasMulti m k f G s) (hle : s ≤ s') :
    HasMulti m k f G s' := by
  obtain ⟨C, hC, hsz, o1, o, hev⟩ := h
  exact ⟨C, hC, le_trans hsz hle, o1, o, hev⟩

private lemma hasG_of_hasMulti {m k s : ℕ} {f : (Fin m → Bool) → Bool}
    {G : Fin k → (Fin m → Bool) → Bool} (h : HasMulti m k f G s) :
    HasG m k G s := by
  obtain ⟨C, hC, hsz, _, o, hev⟩ := h
  exact ⟨C, hC, hsz, o, fun x j => (hev x).2 j⟩

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (stepW W g) (stepW W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [stepW]; omega, by simp [stepW]; omega, ?_⟩
  intro w
  simp only [stepW, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    have hL : (W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD (wmap n m π w) false =
        W'.getD (wmap n m π w) false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    have hR : (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD w false =
        W.getD w false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, ← List.getD_eq_getElem?_getD]
    rw [hL, hR]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl stepW W) ((gs.map (relGate n m π)).foldl stepW W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · next h =>
    have hp := (π ⟨w, h⟩).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [h, hp]
  · next h =>
    have hL : (List.ofFn x).getD (w - n + m) false = false :=
      List.getD_eq_default _ _ (by simp)
    have hR : (List.ofFn (x ∘ π)).getD w false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [hL, hR]

private lemma relabel_multi {n m k s : ℕ} (π : Fin n → Fin m)
    {f : (Fin n → Bool) → Bool} {G : Fin k → (Fin n → Bool) → Bool}
    (h : HasMulti n k f G s) :
    HasMulti m k (fun x => f (x ∘ π)) (fun j x => G j (x ∘ π)) s := by
  obtain ⟨C, hC, hsz, o1, o, hev⟩ := h
  refine ⟨⟨C.gates.map (relGate n m π), 0⟩, ?_, ?_, wmap n m π o1, fun j => wmap n m π (o j), ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hop, hlen⟩ := hC g0 hg0
    exact ⟨hop, by simp [relGate, hlen]⟩
  · simpa [Circuit.size] using hsz
  · intro x
    have hr := rel_fold n m π C.gates (List.ofFn (x ∘ π)) (List.ofFn x) (rel_init n m π x)
    have h1 := hr.2.2 o1
    have h2 : ∀ j, ((C.gates.map (relGate n m π)).foldl stepW (List.ofFn x)).getD (wmap n m π (o j)) false =
        (C.gates.foldl stepW (List.ofFn (x ∘ π))).getD (o j) false := fun j => hr.2.2 (o j)
    refine ⟨?_, fun j => ?_⟩
    · change ((C.gates.map (relGate n m π)).foldl stepW (List.ofFn x)).getD (wmap n m π o1) false = _
      rw [h1]
      exact (hev (x ∘ π)).1
    · change ((C.gates.map (relGate n m π)).foldl stepW (List.ofFn x)).getD (wmap n m π (o j)) false = _
      rw [h2 j]
      exact (hev (x ∘ π)).2 j

private lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

private lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

private lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp [elimStep]
    omega

private lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

private lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hmem : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have hb := hand rfl; subst hb
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have hb := hor rfl; subst hb
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

private lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

private def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

private lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

private lemma suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

private lemma length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

private lemma two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj1 : j ≠ n := fun e => hj (Or.inl e)
      have hj2 : j ≠ n + 1 + pre.length := fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hL j hj1

private lemma multi_elim_one_last {n k s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {G : Fin k → (Fin (n + 1) → Bool) → Bool} (b : Bool)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hncf : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (hncG : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j (Fin.snoc y b) ≠ G j (Fin.snoc y' b))
    (h : HasMulti (n + 1) k f G s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasMulti n k (fun y => f (Fin.snoc y b)) (fun j y => G j (Fin.snoc y b)) s' := by
  classical
  obtain ⟨C, ok, hsz, o1, o, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg1 : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD o1 false = f x := by
    intro x; rw [hgs, wiresFrom_norm]; exact (hev x).1
  have hevgG : ∀ (j : Fin k) (x : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro j x; rw [hgs, wiresFrom_norm]; exact (hev x).2 j
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y; rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval1 : ∀ y : Fin n → Bool,
      (acc.1.getD o1 (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f (Fin.snoc y b) :=
    fun y => by rw [((hinv y).2 o1).2, hevg1]
  have hvalG : ∀ (j : Fin k) (y : Fin n → Bool),
      (acc.1.getD (o j) (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = G j (Fin.snoc y b) :=
    fun j y => by rw [((hinv y).2 (o j)).2, hevgG]
  cases hst1 : acc.1.getD o1 (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hncf
    apply hne; rw [← hval1 y, ← hval1 y', hst1]; rfl
  | wire w1 =>
    have hwG : ∀ j : Fin k, ∃ w : ℕ, acc.1.getD (o j) (Stat.const false) = Stat.wire w := by
      intro j
      cases hst : acc.1.getD (o j) (Stat.const false) with
      | const c =>
        exfalso
        obtain ⟨y, y', hne⟩ := hncG j
        apply hne; rw [← hvalG j y, ← hvalG j y', hst]; rfl
      | wire w => exact ⟨w, rfl⟩
    choose o' ho' using hwG
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        change C.gates.length ≤ s at hsz
        omega
      · exfalso
        push Not at hread
        have hout : o1 ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst1
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst1
          cases hst1
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o1 hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 o1 (by
            intro i hi
            have : i ≠ Fin.last n := fun e => hns (e ▸ hi)
            simp [Function.update_of_ne this])
        rw [← hevg1, ← hevg1]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, 0⟩, elim_ok n gs _ (by simp), le_rfl, w1, o', ?_⟩
    intro y
    refine ⟨?_, fun j => ?_⟩
    · have := hval1 y; rw [hst1] at this; exact this
    · have := hvalG j y; rw [ho' j] at this; exact this

private lemma multi_elim_two_last {n k s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {G : Fin k → (Fin (n + 1) → Bool) → Bool}
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hncf : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (hncG : ∀ (b : Bool) (j : Fin k), ∃ y y' : Fin n → Bool, G j (Fin.snoc y b) ≠ G j (Fin.snoc y' b))
    (h : HasMulti (n + 1) k f G s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMulti n k (fun y => f (Fin.snoc y b)) (fun j y => G j (Fin.snoc y b)) s' := by
  classical
  obtain ⟨C, ok, hsz, o1, o, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg1 : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD o1 false = f x := by
    intro x; rw [hgs, wiresFrom_norm]; exact (hev x).1
  have hevgG : ∀ (j : Fin k) (x : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro j x; rw [hgs, wiresFrom_norm]; exact (hev x).2 j
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y; rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval1 : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD o1 (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) :=
    fun b y => by rw [((hinv b y).2 o1).2, hevg1]
  have hvalG : ∀ (b : Bool) (j : Fin k) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD (o j) (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = G j (Fin.snoc y b) :=
    fun b j y => by rw [((hinv b y).2 (o j)).2, hevgG]
  have hout1 : ∀ b c, (elim n gs (initStats n b, [])).1.getD o1 (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hncf b
    apply hne; rw [← hval1 b y, ← hval1 b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o1 ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 o1 (by
        intro i hi
        have : i ≠ Fin.last n := fun e => hns (e ▸ hi)
        simp [Function.update_of_ne this])
    rw [← hevg1, ← hevg1]
    exact hag
  obtain ⟨b, hlen2⟩ := two_saved n gs hnok o1 hsupp hout1
  have hw1 : ∃ w1 : ℕ, (elim n gs (initStats n b, [])).1.getD o1 (Stat.const false) = Stat.wire w1 := by
    cases hst : (elim n gs (initStats n b, [])).1.getD o1 (Stat.const false) with
    | const c => exact absurd hst (hout1 b c)
    | wire w1 => exact ⟨w1, rfl⟩
  obtain ⟨w1, hw1⟩ := hw1
  have hwG : ∀ j : Fin k, ∃ w : ℕ,
      (elim n gs (initStats n b, [])).1.getD (o j) (Stat.const false) = Stat.wire w := by
    intro j
    cases hst : (elim n gs (initStats n b, [])).1.getD (o j) (Stat.const false) with
    | const c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hncG b j
      apply hne; rw [← hvalG b j y, ← hvalG b j y', hst]; rfl
    | wire w => exact ⟨w, rfl⟩
  choose o' ho' using hwG
  have hsz' : (elim n gs (initStats n b, [])).2.length + 2 ≤ s := by
    have hl : gs.length = C.gates.length := by simp [hgs]
    change C.gates.length ≤ s at hsz
    omega
  refine ⟨b, (elim n gs (initStats n b, [])).2.length, hsz',
    ⟨(elim n gs (initStats n b, [])).2, 0⟩, elim_ok n gs _ (by simp), le_rfl, w1, o', ?_⟩
  intro y
  refine ⟨?_, fun j => ?_⟩
  · have := hval1 b y; rw [hw1] at this; exact this
  · have := hvalG b j y; rw [ho' j] at this; exact this

private lemma snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b : Fin (n + 1) → Bool) ∘
      Equiv.swap p (Fin.last n) = Function.update x p b := by
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i = p
  · subst hi
    rw [Equiv.swap_apply_left, Function.update_self, Fin.snoc_last]
  · rw [Function.update_of_ne hi]
    have hne : Equiv.swap p (Fin.last n) i ≠ Fin.last n := by
      intro h
      apply hi
      have := (Equiv.swap p (Fin.last n)).injective (h.trans (Equiv.swap_apply_left p (Fin.last n)).symm)
      exact this
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.2 hne
    rw [← hj, Fin.snoc_castSucc, hj, Equiv.swap_apply_self]

private lemma multi_elim_one_at {n k s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {G : Fin k → (Fin (n + 1) → Bool) → Bool} (p : Fin (n + 1)) (b : Bool)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hncf : ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (hncG : ∀ j : Fin k, ∃ x y : Fin (n + 1) → Bool,
      G j (Function.update x p b) ≠ G j (Function.update y p b))
    (h : HasMulti (n + 1) k f G s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasMulti (n + 1) k (fun x => f (Function.update x p b))
        (fun j x => G j (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg := relabel_multi (⇑σ) h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n))) ≠
      (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hncf' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hncf
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only; rw [hσ, snoc_swap, snoc_swap]; exact hxy
  have hncG' : ∀ j : Fin k, ∃ y y' : Fin n → Bool,
      (fun x => G j (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => G j (x ∘ σ)) (Fin.snoc y' b) := by
    intro j
    obtain ⟨x, y, hxy⟩ := hncG j
    refine ⟨fun i => x (σ i.castSucc), fun i => y (σ i.castSucc), ?_⟩
    simp only; rw [hσ, snoc_swap, snoc_swap]; exact hxy
  obtain ⟨s', hle, h'⟩ := multi_elim_one_last b hdep' hncf' hncG' hg
  have h'' := relabel_multi (fun j : Fin n => σ j.castSucc) h'
  refine ⟨s', hle, ?_⟩
  have ef : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc)) = fun x => f (Function.update x p b) := by
    funext x; simp only; exact congrArg f (snoc_swap n p x b)
  have eG : (fun (j : Fin k) (x : Fin (n + 1) → Bool) =>
      (fun y : Fin n → Bool => (fun x => G j (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun i : Fin n => σ i.castSucc)) = fun j x => G j (Function.update x p b) := by
    funext j x; simp only; exact congrArg (G j) (snoc_swap n p x b)
  rwa [ef, eG] at h''

private lemma multi_elim_two_at {n k s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    {G : Fin k → (Fin (n + 1) → Bool) → Bool} (p : Fin (n + 1))
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hncf : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (hncG : ∀ (b : Bool) (j : Fin k), ∃ x y : Fin (n + 1) → Bool,
      G j (Function.update x p b) ≠ G j (Function.update y p b))
    (h : HasMulti (n + 1) k f G s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMulti (n + 1) k (fun x => f (Function.update x p b))
        (fun j x => G j (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg := relabel_multi (⇑σ) h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n))) ≠
      (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hncf' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hncf b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only; rw [hσ, snoc_swap, snoc_swap]; exact hxy
  have hncG' : ∀ (b : Bool) (j : Fin k), ∃ y y' : Fin n → Bool,
      (fun x => G j (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => G j (x ∘ σ)) (Fin.snoc y' b) := by
    intro b j
    obtain ⟨x, y, hxy⟩ := hncG b j
    refine ⟨fun i => x (σ i.castSucc), fun i => y (σ i.castSucc), ?_⟩
    simp only; rw [hσ, snoc_swap, snoc_swap]; exact hxy
  obtain ⟨b, s', hle, h'⟩ := multi_elim_two_last hdep' hncf' hncG' hg
  have h'' := relabel_multi (fun j : Fin n => σ j.castSucc) h'
  refine ⟨b, s', hle, ?_⟩
  have ef : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc)) = fun x => f (Function.update x p b) := by
    funext x; simp only; exact congrArg f (snoc_swap n p x b)
  have eG : (fun (j : Fin k) (x : Fin (n + 1) → Bool) =>
      (fun y : Fin n → Bool => (fun x => G j (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun i : Fin n => σ i.castSucc)) = fun j x => G j (Function.update x p b) := by
    funext j x; simp only; exact congrArg (G j) (snoc_swap n p x b)
  rwa [ef, eG] at h''

/-! ### Part 2: Forest good leaf avoiding one forbidden vertex -/

private lemma exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push Not at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

private lemma good_leaf_of_longest {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    {l z : V} (P : G.Walk l z) (hP : P.IsPath) (h1 : 1 ≤ P.length)
    (hmax : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length) :
    ∃ p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ; simpa using hmax c d Q hQ
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := fun h => hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

private lemma forest_good_leaf_avoid {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) (forb : V → Prop)
    (huniq : ∀ i i' : V, (∃ w, G.Adj i w) → (∃ w, G.Adj i' w) → forb i → forb i' → i = i') :
    ∃ l p : V, ¬ forb l ∧ G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  have : Nonempty V := ⟨u0⟩
  obtain ⟨a, b, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  have hab : a ≠ b := by
    intro h
    subst h
    cases P with
    | nil => simp at h1
    | cons hadj P' =>
      rw [Walk.cons_isPath_iff] at hP
      exact hP.2 (Walk.end_mem_support P')
  obtain ⟨pa, hapa, hleafa, hgooda⟩ := good_leaf_of_longest G hG P hP h1 hmax
  have hPrev : P.reverse.IsPath := hP.reverse
  have h1rev : 1 ≤ P.reverse.length := by simpa using h1
  have hmaxrev : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.reverse.length := by
    intro c d Q hQ; simpa using hmax c d Q hQ
  obtain ⟨pb, hbpb, hleafb, hgoodb⟩ := good_leaf_of_longest G hG P.reverse hPrev h1rev hmaxrev
  by_cases hfa : forb a
  · have hfb : ¬ forb b := fun hf => hab (huniq a b ⟨pa, hapa⟩ ⟨pb, hbpb⟩ hfa hf)
    exact ⟨b, pb, hfb, hbpb, hleafb, hgoodb⟩
  · exact ⟨a, pa, hfa, hapa, hleafa, hgooda⟩

/-! ### Part 3: Edge function, restrictions, and vertex covers -/

private noncomputable def F {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)
    (Classical.propDecidable _)

private lemma F_true {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F K A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

private lemma F_eq {n : ℕ} (K K' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, K.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, K'.Adj i j ∧ y i = true ∧ y j = true)) :
    F K A x = F K' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

private lemma F_zero {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F K A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

private lemma F_nc {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, K.Adj i j) :
    ∃ x y : Fin n → Bool, F K A x ≠ F K A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F K A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]; simp

private lemma F_dep_edge {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : K.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F K A (Function.update x u (!x u)) ≠ F K A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F K A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]; right
    exact ⟨u, v, huv, by simp [Function.update_of_ne hne], by simp [Function.update_of_ne hne.symm]⟩
  have h2 : F K A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]; simp

private lemma F_dep_A {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F K A (Function.update x a (!x a)) ≠ F K A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F K A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]; exact Or.inl ⟨a, ha, by simp⟩
  rw [this]; simp

private lemma restrict_A_false {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (haK : ∀ w, ¬ K.Adj a w) (x : Fin n → Bool) :
    F K A (Function.update x a false) = F K (A.erase a) x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨b, hb, hbx⟩
      have hba : b ≠ a := by rintro rfl; simp at hbx
      exact ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hbx⟩
    · rintro ⟨b, hb, hbx⟩
      obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      exact ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hia : i ≠ a := fun e => haK j (e ▸ hij)
      have hja : j ≠ a := fun e => haK i (e ▸ hij.symm)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hia] at hi,
        by rwa [Function.update_of_ne hja] at hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      have hia : i ≠ a := fun e => haK j (e ▸ hij)
      have hja : j ≠ a := fun e => haK i (e ▸ hij.symm)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hia], by rwa [Function.update_of_ne hja]⟩

private lemma restrict_false {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, K.Adj l w → w = p) (x : Fin n → Bool) :
    F K A (Function.update x l false) = F (K.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, (deleteEdges_adj).2 ⟨hij, by simp [hil, hjl]⟩,
        by rwa [Function.update_of_ne hil] at hi, by rwa [Function.update_of_ne hjl] at hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by rintro rfl; rw [hleaf j hij] at hne; exact hne rfl
      have hjl : j ≠ l := by rintro rfl; rw [hleaf i hij.symm] at hne; exact hne Sym2.eq_swap
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

private lemma restrict_true {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p)
    (hp : ∀ w, K.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F K A (Function.update x l true) = F (K.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hK1 : ∀ i j, (K.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl <;> exact hne (by simp)
    · rintro rfl
      rw [hleaf j hij] at hne
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := fun e => hjp (hleaf j (e ▸ hij))
      have hjl : j ≠ l := fun e => hip (hleaf i (e ▸ hij.symm))
      right
      exact ⟨i, j, (deleteEdges_adj).2 ⟨hij, by simp [hip, hjp]⟩,
        by rwa [Function.update_of_ne hil] at hi, by rwa [Function.update_of_ne hjl] at hj⟩
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right; exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hK1 i j hij
      have hj' := hK1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

private def Cov {n : ℕ} (K : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T

private lemma cov_insert {n : ℕ} (K : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (K.deleteEdges S) T) :
    Cov K (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · rcases Sym2.mem_iff.1 (hS _ he) with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

private lemma cov_swap_exists {n : ℕ} (K : SimpleGraph (Fin n)) (l p l' : Fin n)
    (hll' : l' ≠ l) (hpl' : K.Adj p l') (hleaf' : ∀ w, K.Adj l' w → w = p)
    (T0 : Finset (Fin n)) (hT0 : Cov (K.deleteEdges {s(l, p)}) T0) :
    ∃ T : Finset (Fin n), Cov K T ∧ T.card ≤ T0.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he; rw [Set.mem_singleton_iff] at he; subst he; exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T0
  · refine ⟨T0, ?_, le_rfl⟩
    have := cov_insert K _ p hS T0 hT0
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T0 := by
      have hpl'ne : p ≠ l' := hpl'.ne
      rcases hT0 p l' ((deleteEdges_adj).2 ⟨hpl', by simp [hll', hpl'ne.symm]⟩)
        with h | h
      · exact absurd h hpT
      · exact h
    refine ⟨insert p (T0.erase l'), ?_, ?_⟩
    · intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have hil' : i ≠ l' := fun e => hjp (hleaf' j (e ▸ hij))
      have hjl' : j ≠ l' := fun e => hip (hleaf' i (e ▸ hij.symm))
      have he : s(i, j) ≠ s(l, p) := by simp [hip, hjp]
      rcases hT0 i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    · have h1 := Finset.card_insert_le p (T0.erase l')
      have h2 := Finset.card_erase_add_one hl'T
      omega

private lemma ncard_del1 {n : ℕ} (K : SimpleGraph (Fin n)) (l p : Fin n) (hlp : K.Adj l p) :
    (K.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = K.edgeSet.ncard := by
  have hmem : s(l, p) ∈ K.edgeSet := hlp
  have hfin : K.edgeSet.Finite := Set.toFinite _
  rw [SimpleGraph.edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem hmem]
  have hpos : 1 ≤ K.edgeSet.ncard :=
    Nat.succ_le_of_lt ((Set.ncard_pos hfin).2 ⟨s(l, p), hmem⟩)
  omega

private lemma ncard_del2 {n : ℕ} (K : SimpleGraph (Fin n)) (l p q : Fin n) (hlp : K.Adj l p) :
    (K.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 1 ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard ≤ (K.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 := by
  have hfin : K.edgeSet.Finite := Set.toFinite _
  have hmem : s(p, l) ∈ K.edgeSet := hlp.symm
  have hsub : (K.deleteEdges {s(p, l), s(p, q)}).edgeSet = (K.edgeSet \ {s(p, l)}) \ {s(p, q)} := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    ext e; simp [and_assoc]
  rw [hsub]
  have h1 : (K.edgeSet \ {s(p, l)}).ncard + 1 = K.edgeSet.ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hmem]
    have hpos : 1 ≤ K.edgeSet.ncard :=
      Nat.succ_le_of_lt ((Set.ncard_pos hfin).2 ⟨s(p, l), hmem⟩)
    omega
  have hfin1 : (K.edgeSet \ {s(p, l)}).Finite := hfin.sdiff
  by_cases hm2 : s(p, q) ∈ K.edgeSet \ {s(p, l)}
  · rw [Set.ncard_sdiff_singleton_of_mem hm2]
    have hpos : 1 ≤ (K.edgeSet \ {s(p, l)}).ncard :=
      Nat.succ_le_of_lt ((Set.ncard_pos hfin1).2 ⟨s(p, q), hm2⟩)
    omega
  · rw [Set.sdiff_singleton_eq_self hm2]
    omega

private lemma noedge_ncard {n : ℕ} (K : SimpleGraph (Fin n)) (h : ∀ u v : Fin n, ¬ K.Adj u v) :
    K.edgeSet.ncard = 0 := by
  have he : K.edgeSet = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ u v => simp [h u v]
  rw [he, Set.ncard_empty]

/-! ### Part 4: Lower bound by induction on `2 * |E(K)| + |A|` -/

private def GDep {n k : ℕ} (G : Fin k → (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)

private lemma G_indep_update {n k : ℕ} {G : Fin k → (Fin n → Bool) → Bool} {i : Fin n}
    (h : ¬ GDep G i) (j : Fin k) (x : Fin n → Bool) (b : Bool) :
    G j (Function.update x i b) = G j x := by
  have hft : G j (Function.update x i false) = G j (Function.update x i true) := by
    by_contra hne
    exact h ⟨j, x, hne⟩
  cases hxi : x i <;> cases b
  · rw [← hxi, Function.update_eq_self]
  · rw [← hft, ← hxi, Function.update_eq_self]
  · rw [hft, ← hxi, Function.update_eq_self]
  · rw [← hxi, Function.update_eq_self]

private lemma lower_bound : ∀ (m n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (G : Fin k → (Fin n → Bool) → Bool),
    2 * K.edgeSet.ncard + A.card = m →
    K.IsAcyclic →
    (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) →
    (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
    (∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') →
    (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) →
      GDep G i → GDep G i' → i = i') →
    HasMulti n k (F K A) G s →
    ∃ (T : Finset (Fin n)) (t : ℕ),
      Cov K T ∧ A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧ HasG n k G t := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro n k s K A G hm hac hdisj hne hGnc hshared hM
    cases n with
    | zero =>
      exfalso
      rcases hne with ⟨a, _⟩ | ⟨u, _⟩
      · exact Fin.elim0 a
      · exact Fin.elim0 u
    | succ n' =>
      by_cases hedge : ∃ u v : Fin (n' + 1), K.Adj u v
      · -- K has at least one edge: pick a good leaf l avoiding GDep G
        obtain ⟨l, p, hl_indep, hlp, hleaf, hgood⟩ := forest_good_leaf_avoid K hac hedge (GDep G)
          (fun i i' hi hi' hdi hdi' => hshared i i' (Or.inr hi) (Or.inr hi') hdi hdi')
        have hlA : l ∉ A := fun hm => hdisj l hm p hlp
        have hpA : p ∉ A := fun hm => hdisj p hm l hlp.symm
        have hdepl : ∃ x : Fin (n' + 1) → Bool,
            F K A (Function.update x l (!x l)) ≠ F K A x := F_dep_edge K A l p hlp hpA
        have hGupd : ∀ b : Bool, (fun (j : Fin k) (x : Fin (n' + 1) → Bool) =>
            G j (Function.update x l b)) = G := by
          intro b; funext j x; exact G_indep_update hl_indep j x b
        have hGnc_l : ∀ (b : Bool) (j : Fin k), ∃ x y : Fin (n' + 1) → Bool,
            G j (Function.update x l b) ≠ G j (Function.update y l b) := by
          intro b j
          obtain ⟨x, y, hxy⟩ := hGnc j
          exact ⟨x, y, by rw [G_indep_update hl_indep, G_indep_update hl_indep]; exact hxy⟩
        set K0 := K.deleteEdges {s(l, p)} with hK0
        have hac0 : K0.IsAcyclic := hac.anti (deleteEdges_le _)
        have hdisj0 : ∀ a ∈ A, ∀ w, ¬ K0.Adj a w :=
          fun a ha w hw => hdisj a ha w ((deleteEdges_adj).1 hw).1
        have hshared0 : ∀ i i' : Fin (n' + 1), (i ∈ A ∨ ∃ w, K0.Adj i w) →
            (i' ∈ A ∨ ∃ w, K0.Adj i' w) → GDep G i → GDep G i' → i = i' := by
          intro i i' hi hi'
          apply hshared i i'
          · rcases hi with h | ⟨w, hw⟩
            · exact Or.inl h
            · exact Or.inr ⟨w, ((deleteEdges_adj).1 hw).1⟩
          · rcases hi' with h | ⟨w, hw⟩
            · exact Or.inl h
            · exact Or.inr ⟨w, ((deleteEdges_adj).1 hw).1⟩
        have hnc0_card : K0.edgeSet.ncard + 1 = K.edgeSet.ncard := ncard_del1 K l p hlp
        have hrf : (fun x : Fin (n' + 1) → Bool => F K A (Function.update x l false)) = F K0 A :=
          funext (restrict_false K A l p hlA hleaf)
        rcases hgood with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
        · -- Subcase: deg_K(p) <= 2 (all neighbors of p are l or q)
          set K1 := K.deleteEdges {s(p, l), s(p, q)} with hK1
          have hac1 : K1.IsAcyclic := hac.anti (deleteEdges_le _)
          have hdisj1 : ∀ a ∈ insert p A, ∀ w, ¬ K1.Adj a w := by
            intro a ha w hw
            rcases Finset.mem_insert.1 ha with rfl | haA
            · rw [hK1, deleteEdges_adj] at hw
              rcases hq w hw.1 with rfl | rfl <;> exact hw.2 (by simp)
            · exact hdisj a haA w ((deleteEdges_adj).1 hw).1
          have hshared1 : ∀ i i' : Fin (n' + 1), (i ∈ insert p A ∨ ∃ w, K1.Adj i w) →
              (i' ∈ insert p A ∨ ∃ w, K1.Adj i' w) → GDep G i → GDep G i' → i = i' := by
            intro i i' hi hi'
            apply hshared i i'
            · rcases hi with h | ⟨w, hw⟩
              · rcases Finset.mem_insert.1 h with rfl | haA
                · exact Or.inr ⟨l, hlp.symm⟩
                · exact Or.inl haA
              · exact Or.inr ⟨w, ((deleteEdges_adj).1 hw).1⟩
            · rcases hi' with h | ⟨w, hw⟩
              · rcases Finset.mem_insert.1 h with rfl | haA
                · exact Or.inr ⟨l, hlp.symm⟩
                · exact Or.inl haA
              · exact Or.inr ⟨w, ((deleteEdges_adj).1 hw).1⟩
          have hrt : (fun x : Fin (n' + 1) → Bool => F K A (Function.update x l true)) =
              F K1 (insert p A) := funext (restrict_true K A l p q hlA hlp hleaf hq)
          have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
            intro e he
            rcases he with rfl | he
            · exact Sym2.mem_mk_left _ _
            · rw [Set.mem_singleton_iff] at he; subst he; exact Sym2.mem_mk_left _ _
          obtain ⟨hd1, hd2⟩ := ncard_del2 K l p q hlp
          rw [← hK1] at hd1 hd2
          by_cases hne0 : A.Nonempty ∨ ∃ u v : Fin (n' + 1), K0.Adj u v
          · -- Both restrictions are non-constant: save 2 gates at l
            have hncf : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
                F K A (Function.update x l b) ≠ F K A (Function.update y l b) := by
              intro b
              cases b
              · obtain ⟨x, y, hxy⟩ := F_nc K0 A hne0
                refine ⟨x, y, ?_⟩
                rw [congrFun hrf x, congrFun hrf y]; exact hxy
              · obtain ⟨x, y, hxy⟩ := F_nc K1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
                refine ⟨x, y, ?_⟩
                rw [congrFun hrt x, congrFun hrt y]; exact hxy
            obtain ⟨b, s', hs', hM'⟩ := multi_elim_two_at l hdepl hncf hGnc_l hM
            cases b
            · rw [hrf, hGupd false] at hM'
              obtain ⟨T0, t, hT0, hbd0, hG0⟩ :=
                ih (2 * K0.edgeSet.ncard + A.card) (by omega) (n' + 1) k s' K0 A G rfl
                  hac0 hdisj0 hne0 hGnc hshared0 hM'
              have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
                intro e he; rw [Set.mem_singleton_iff] at he; subst he; exact Sym2.mem_mk_right _ _
              refine ⟨insert p T0, t, cov_insert K _ p hS0 T0 hT0, ?_, hG0⟩
              have := Finset.card_insert_le p T0
              omega
            · rw [hrt, hGupd true] at hM'
              have hcard_ins : (insert p A).card = A.card + 1 := Finset.card_insert_of_notMem hpA
              obtain ⟨T1, t, hT1, hbd1, hG1⟩ :=
                ih (2 * K1.edgeSet.ncard + (insert p A).card) (by omega) (n' + 1) k s' K1
                  (insert p A) G rfl hac1 hdisj1 (Or.inl (Finset.insert_nonempty _ _))
                  hGnc hshared1 hM'
              refine ⟨insert p T1, t, cov_insert K _ p hS1 T1 hT1, ?_, hG1⟩
              have := Finset.card_insert_le p T1
              omega
          · -- Only edge of K is s(l, p) and A = ∅: fix l = true to save 1 gate
            push Not at hne0
            obtain ⟨hA0, hK00⟩ := hne0
            have hE1 : K.edgeSet.ncard = 1 := by
              have := noedge_ncard K0 hK00
              omega
            have hncf_t : ∃ x y : Fin (n' + 1) → Bool,
                F K A (Function.update x l true) ≠ F K A (Function.update y l true) := by
              obtain ⟨x, y, hxy⟩ := F_nc K1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
              refine ⟨x, y, ?_⟩
              rw [congrFun hrt x, congrFun hrt y]; exact hxy
            obtain ⟨s', hs', hM'⟩ := multi_elim_one_at l true hdepl hncf_t (hGnc_l true) hM
            rw [hGupd true] at hM'
            have hcovp : Cov K {p} := by
              intro u v huv
              have h1 := hK00 u v
              rw [hK0, deleteEdges_adj] at h1
              push Not at h1
              have h2 := h1 huv
              rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
              rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
              · exact Or.inr (Finset.mem_singleton_self _)
              · exact Or.inl (Finset.mem_singleton_self _)
            refine ⟨{p}, s', hcovp, ?_, hasG_of_hasMulti hM'⟩
            subst hA0
            simp only [Finset.card_empty, Finset.card_singleton]
            omega
        · -- Subcase: p has a second leaf neighbor l' ≠ l
          have hpl'0 : K0.Adj p l' :=
            (deleteEdges_adj).2 ⟨hpl', by simp [hl'l, hpl'.ne.symm]⟩
          have hncf0 : ∃ x y : Fin (n' + 1) → Bool,
              F K A (Function.update x l false) ≠ F K A (Function.update y l false) := by
            obtain ⟨x, y, hxy⟩ := F_nc K0 A (Or.inr ⟨p, l', hpl'0⟩)
            refine ⟨x, y, ?_⟩
            rw [congrFun hrf x, congrFun hrf y]; exact hxy
          obtain ⟨s', hs', hM'⟩ := multi_elim_one_at l false hdepl hncf0 (hGnc_l false) hM
          rw [hrf, hGupd false] at hM'
          obtain ⟨T0, t, hT0, hbd0, hG0⟩ :=
            ih (2 * K0.edgeSet.ncard + A.card) (by omega) (n' + 1) k s' K0 A G rfl
              hac0 hdisj0 (Or.inr ⟨p, l', hpl'0⟩) hGnc hshared0 hM'
          obtain ⟨T, hTcov, hTle⟩ := cov_swap_exists K l p l' hl'l hpl' hleaf' T0 hT0
          exact ⟨T, t, hTcov, by omega, hG0⟩
      · -- K has no edges
        push Not at hedge
        have hE0 : K.edgeSet.ncard = 0 := noedge_ncard K hedge
        have hAne : A.Nonempty := by
          rcases hne with h | ⟨u, v, huv⟩
          · exact h
          · exact absurd huv (hedge u v)
        by_cases hA1 : A.card = 1
        · refine ⟨∅, s, fun u v huv => absurd huv (hedge u v), ?_, hasG_of_hasMulti hM⟩
          simp only [Finset.card_empty]
          omega
        · have hA2 : 2 ≤ A.card := by
            have := Finset.card_pos.2 hAne
            omega
          obtain ⟨a1, ha1, a2, ha2, ha12⟩ := Finset.one_lt_card.1 (by omega : 1 < A.card)
          obtain ⟨a, haA, ha_indep⟩ : ∃ a ∈ A, ¬ GDep G a := by
            by_cases h1 : GDep G a1
            · exact ⟨a2, ha2, fun h2 => ha12 (hshared a1 a2 (Or.inl ha1) (Or.inl ha2) h1 h2)⟩
            · exact ⟨a1, ha1, h1⟩
          have hdepa := F_dep_A K A a haA
          have hA'ne : (A.erase a).Nonempty := by
            have hc := Finset.card_erase_of_mem haA
            exact Finset.card_pos.1 (by omega)
          have hra : (fun x : Fin (n' + 1) → Bool => F K A (Function.update x a false)) =
              F K (A.erase a) := funext (restrict_A_false K A a (hedge a))
          have hncf0 : ∃ x y : Fin (n' + 1) → Bool,
              F K A (Function.update x a false) ≠ F K A (Function.update y a false) := by
            obtain ⟨x, y, hxy⟩ := F_nc K (A.erase a) (Or.inl hA'ne)
            refine ⟨x, y, ?_⟩
            rw [congrFun hra x, congrFun hra y]; exact hxy
          have hGupd : (fun (j : Fin k) (x : Fin (n' + 1) → Bool) =>
              G j (Function.update x a false)) = G := by
            funext j x; exact G_indep_update ha_indep j x false
          have hGnc_a : ∀ j : Fin k, ∃ x y : Fin (n' + 1) → Bool,
              G j (Function.update x a false) ≠ G j (Function.update y a false) := by
            intro j
            obtain ⟨x, y, hxy⟩ := hGnc j
            exact ⟨x, y, by rw [G_indep_update ha_indep, G_indep_update ha_indep]; exact hxy⟩
          obtain ⟨s', hs', hM'⟩ := multi_elim_one_at a false hdepa hncf0 hGnc_a hM
          rw [hra, hGupd] at hM'
          have hcard_er : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one haA
          have hdisj' : ∀ b ∈ A.erase a, ∀ w, ¬ K.Adj b w :=
            fun b hb => hdisj b (Finset.mem_of_mem_erase hb)
          have hshared' : ∀ i i' : Fin (n' + 1), (i ∈ A.erase a ∨ ∃ w, K.Adj i w) →
              (i' ∈ A.erase a ∨ ∃ w, K.Adj i' w) → GDep G i → GDep G i' → i = i' := by
            intro i i' hi hi'
            apply hshared i i'
            · rcases hi with h | h
              · exact Or.inl (Finset.mem_of_mem_erase h)
              · exact Or.inr h
            · rcases hi' with h | h
              · exact Or.inl (Finset.mem_of_mem_erase h)
              · exact Or.inr h
          obtain ⟨T, t, hTcov, hbd, hG0⟩ :=
            ih (2 * K.edgeSet.ncard + (A.erase a).card) (by omega) (n' + 1) k s' K (A.erase a) G
              rfl hac hdisj' (Or.inl hA'ne) hGnc hshared' hM'
          exact ⟨T, t, hTcov, by omega, hG0⟩

/-! ### Part 5: Upper bound construction (stars + OR-chain appended to C_G) -/

private lemma wiresFrom_append_gs (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_len (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]; simp; omega

private lemma wiresFrom_getD_lt_init (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).getD i false = _
    rw [ih (w ++ [_]) (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

private def orChainAux (base : ℕ) (cur : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], cur)
  | a :: rest =>
    let res := orChainAux (base + 1) base rest
    (⟨GateOp.or, [cur, a]⟩ :: res.1, res.2)

private lemma orChainAux_spec (base cur : ℕ) (rest : List ℕ) :
    (∀ g ∈ (orChainAux base cur rest).1, Ok g) ∧
    (orChainAux base cur rest).1.length = rest.length ∧
    (cur < base → (∀ a ∈ rest, a < base) →
      (orChainAux base cur rest).2 < base + rest.length ∧
      ∀ w : List Bool, w.length = base →
        (wiresFrom (orChainAux base cur rest).1 w).getD (orChainAux base cur rest).2 false =
          (w.getD cur false || rest.any (fun a => w.getD a false))) := by
  induction rest generalizing base cur with
  | nil =>
    refine ⟨by simp [orChainAux], rfl, fun hcur _ => ⟨by simpa [orChainAux] using hcur, ?_⟩⟩
    intro w _
    simp [orChainAux, wiresFrom]
  | cons a rest ih =>
    obtain ⟨hok, hlen, hrest⟩ := ih (base + 1) base
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [orChainAux, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · exact hok g hg
    · simp [orChainAux, hlen]
    · intro hcur hall
      have ha : a < base := hall a List.mem_cons_self
      have hrest' : ∀ b ∈ rest, b < base + 1 := fun b hb =>
        lt_trans (hall b (List.mem_cons_of_mem _ hb)) (Nat.lt_succ_self base)
      obtain ⟨hout, hev⟩ := hrest (Nat.lt_succ_self base) hrest'
      refine ⟨by simp only [orChainAux, List.length_cons]; omega, ?_⟩
      intro w hw
      simp only [orChainAux]
      change (wiresFrom (orChainAux (base + 1) base rest).1
          (w ++ [GateOp.or.eval ([cur, a].map fun i => w.getD i false)])).getD
        (orChainAux (base + 1) base rest).2 false = _
      set w1 := w ++ [GateOp.or.eval ([cur, a].map fun i => w.getD i false)]
      have hw1 : w1.length = base + 1 := by simp [w1, hw]
      rw [hev w1 hw1]
      have hbase_val : w1.getD base false = (w.getD cur false || w.getD a false) := by
        simp only [w1]
        rw [getD_snoc_len _ _ _ _ hw]
        simp [GateOp.eval]
      have hany : rest.any (fun b => w1.getD b false) = rest.any (fun b => w.getD b false) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        refine exists_congr fun b => and_congr_right fun hb => ?_
        have hblt : b < w.length := by rw [hw]; exact hall b (List.mem_cons_of_mem _ hb)
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hblt, ← List.getD_eq_getElem?_getD]
      rw [hbase_val, hany, List.any_cons, Bool.or_assoc]

private lemma build_orChain (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) (hlt : ∀ a ∈ ws, a < base) :
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 1 = ws.length ∧
      out < base + gs.length ∧
      ∀ w : List Bool, w.length = base →
        (wiresFrom gs w).getD out false = ws.any (fun a => w.getD a false) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons a rest =>
    obtain ⟨hok, hlen, hspec⟩ := orChainAux_spec base a rest
    obtain ⟨hout, hev⟩ := hspec (hlt a List.mem_cons_self)
      (fun b hb => hlt b (List.mem_cons_of_mem _ hb))
    refine ⟨(orChainAux base a rest).1, (orChainAux base a rest).2, hok,
      by simp [hlen], by omega, ?_⟩
    intro w hw
    rw [hev w hw, List.any_cons]

private lemma build_stars {n : ℕ} (L : List (Fin n × List (Fin n)))
    (hne : ∀ p ∈ L, p.2 ≠ []) :
    ∀ (base : ℕ), n ≤ base →
      ∃ (gs : List Gate) (outs : List ℕ),
        (∀ g ∈ gs, Ok g) ∧
        gs.length = (L.map fun p => p.2.length).sum ∧
        outs.length = L.length ∧
        (∀ a ∈ outs, a < base + gs.length) ∧
        ∀ (x : Fin n → Bool) (w : List Bool),
          w.length = base → (∀ i : Fin n, w.getD i.val false = x i) →
          (∀ (j : ℕ) (hj : j < L.length),
            (wiresFrom gs w).getD (outs.getD j 0) false =
              (x (L[j]'hj).1 && (L[j]'hj).2.any (fun u => x u))) := by
  induction L with
  | nil =>
    intro base _
    exact ⟨[], [], by simp, rfl, rfl, by simp, fun _ _ _ _ j hj => by simp at hj⟩
  | cons hd tl ih =>
    intro base hbase
    have hhd : hd.2 ≠ [] := hne hd List.mem_cons_self
    have htl : ∀ p ∈ tl, p.2 ≠ [] := fun p hp => hne p (List.mem_cons_of_mem _ hp)
    let ws := hd.2.map Fin.val
    have hws_ne : ws ≠ [] := by simp [ws, hhd]
    have hws_lt : ∀ a ∈ ws, a < base := by
      intro a ha
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 ha
      exact lt_of_lt_of_le u.isLt hbase
    obtain ⟨gs1, orOut, hok1, hlen1, hor_lt, hev1⟩ := build_orChain base ws hws_ne hws_lt
    let starGate : Gate := ⟨GateOp.and, [hd.1.val, orOut]⟩
    let gsHead := gs1 ++ [starGate]
    let starOut := base + gs1.length
    have hbase2 : n ≤ base + gsHead.length := by simp [gsHead]; omega
    obtain ⟨gs2, outs2, hok2, hlen2, houts2_len, houts2_lt, hev2⟩ := ih htl (base + gsHead.length) hbase2
    refine ⟨gsHead ++ gs2, starOut :: outs2, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg1 | hg2
      · rcases List.mem_append.1 hg1 with ha | hb
        · exact hok1 g ha
        · simp only [List.mem_singleton] at hb; subst hb
          exact ⟨Or.inl rfl, by simp [starGate]⟩
      · exact hok2 g hg2
    · simp only [gsHead, List.length_append, List.length_cons, List.length_nil,
        List.map_cons, List.sum_cons, hlen2]
      have hws_len : ws.length = hd.2.length := List.length_map _
      omega
    · simp [houts2_len]
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha2
      · simp only [starOut, gsHead, List.length_append, List.length_cons, List.length_nil]; omega
      · have := houts2_lt a ha2
        simp only [List.length_append]; omega
    · intro x w hw hwx j hj
      rw [wiresFrom_append_gs]
      set wHead := wiresFrom gsHead w
      have hwHead_len : wHead.length = base + gsHead.length := by
        rw [wiresFrom_len, hw]
      have hwHead_x : ∀ i : Fin n, wHead.getD i.val false = x i := by
        intro i
        rw [wiresFrom_getD_lt_init gsHead w i.val (by rw [hw]; exact lt_of_lt_of_le i.isLt hbase)]
        exact hwx i
      cases j with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [wiresFrom_getD_lt_init gs2 wHead starOut
          (by rw [hwHead_len]; simp [starOut, gsHead])]
        simp only [wHead, gsHead]
        rw [wiresFrom_append_gs]
        set w1 := wiresFrom gs1 w
        have hw1_len : w1.length = base + gs1.length := by rw [wiresFrom_len, hw]
        change (w1 ++ [starGate.op.eval (starGate.inputs.map fun i => w1.getD i false)]).getD
          starOut false = _
        rw [getD_snoc_len _ _ _ _ hw1_len]
        have hv1 : w1.getD hd.1.val false = x hd.1 := by
          rw [wiresFrom_getD_lt_init gs1 w hd.1.val (by rw [hw]; exact lt_of_lt_of_le hd.1.isLt hbase)]
          exact hwx hd.1
        have hv2 : w1.getD orOut false = hd.2.any (fun u => x u) := by
          rw [hev1 w hw]
          simp only [ws, List.any_map]
          exact List.any_congr rfl fun u => hwx u
        simp only [starGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, Bool.and_true, id_eq]
        rw [hv1, hv2]
      | succ j' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        exact hev2 x wHead hwHead_len hwHead_x j' (by simp at hj; omega)

private lemma upper_bound {n k s : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (G : Fin k → (Fin n → Bool) → Bool)
    (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v)
    (hGnc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (T : Finset (Fin n)) (t : ℕ) (hT : Cov K T)
    (hbd : A.card + K.edgeSet.ncard + T.card + t ≤ s + 1)
    (hG : HasG n k G t) :
    HasMulti n k (F K A) G s := by
  classical
  -- Shrink T to a minimal vertex cover T0 ⊆ T
  have hex_sz : ∃ m : ℕ, ∃ T0 : Finset (Fin n), T0 ⊆ T ∧ Cov K T0 ∧ T0.card = m :=
    ⟨T.card, T, Finset.Subset.rfl, hT, rfl⟩
  let m0 := Nat.find hex_sz
  obtain ⟨T0, hT0sub, hT0cov, hT0card⟩ := Nat.find_spec hex_sz
  have hT0le : T0.card ≤ T.card := hT0card ▸ Nat.find_min' hex_sz ⟨T, Finset.Subset.rfl, hT, rfl⟩
  have hT0min : ∀ v ∈ T0, ∃ w : Fin n, w ∉ T0 ∧ K.Adj v w := by
    intro v hv
    by_contra hno
    push Not at hno
    have hcov' : Cov K (T0.erase v) := by
      intro a b hab
      rcases hT0cov a b hab with ha | hb
      · by_cases hav : a = v
        · subst hav
          by_cases hbT : b ∈ T0
          · exact Or.inr (Finset.mem_erase.2 ⟨hab.ne.symm, hbT⟩)
          · exact absurd hab (hno b hbT)
        · exact Or.inl (Finset.mem_erase.2 ⟨hav, ha⟩)
      · by_cases hbv : b = v
        · subst hbv
          by_cases haT : a ∈ T0
          · exact Or.inl (Finset.mem_erase.2 ⟨hab.ne, haT⟩)
          · exact absurd hab.symm (hno a haT)
        · exact Or.inr (Finset.mem_erase.2 ⟨hbv, hb⟩)
    have hc : (T0.erase v).card < m0 := by
      have := Finset.card_erase_add_one hv; omega
    exact Nat.find_min hex_sz hc ⟨T0.erase v, (Finset.erase_subset v T0).trans hT0sub, hcov', rfl⟩
  -- Assign each edge to one endpoint in T0
  let nbrs : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter fun w : Fin n => K.Adj v w ∧ (w ∉ T0 ∨ v.val < w.val)
  have hnbrs_ne : ∀ v ∈ T0, (nbrs v).Nonempty := by
    intro v hv
    obtain ⟨w, hwT, hvw⟩ := hT0min v hv
    exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ w, hvw, Or.inl hwT⟩⟩
  -- Count edges: ∑ v ∈ T0, (nbrs v).card = K.edgeSet.ncard
  have hsum_edges : (∑ v ∈ T0, (nbrs v).card) = K.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hbij : (T0.sigma nbrs).card = K.edgeFinset.card := by
      apply Finset.card_bij (fun p _ => s(p.1, p.2))
      · intro p hp
        rw [Finset.mem_sigma] at hp
        rw [SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.1 hp.2).2.1
      · intro p1 hp1 p2 hp2 heq
        rw [Finset.mem_sigma] at hp1 hp2
        obtain ⟨_, hadj1, hord1⟩ := Finset.mem_filter.1 hp1.2
        obtain ⟨_, hadj2, hord2⟩ := Finset.mem_filter.1 hp2.2
        rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sigma.ext h1 (heq_of_eq h2)
        · exfalso
          rcases hord1 with h1' | h1' <;> rcases hord2 with h2' | h2'
          · exact h1' (h2 ▸ hp2.1)
          · exact h1' (h2 ▸ hp2.1)
          · exact h2' (h1 ▸ hp1.1)
          · rw [h1, h2] at h1'; omega
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          rw [SimpleGraph.mem_edgeFinset] at he
          have huv : K.Adj u v := he
          by_cases hu : u ∈ T0
          · by_cases hv : v ∈ T0
            · by_cases hlt : u.val < v.val
              · exact ⟨⟨u, v⟩, Finset.mem_sigma.2 ⟨hu, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, Or.inr hlt⟩⟩, rfl⟩
              · have hgt : v.val < u.val := by have := huv.ne; omega
                exact ⟨⟨v, u⟩, Finset.mem_sigma.2 ⟨hv, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩⟩, Sym2.eq_swap⟩
            · exact ⟨⟨u, v⟩, Finset.mem_sigma.2 ⟨hu, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, Or.inl hv⟩⟩, rfl⟩
          · have hv : v ∈ T0 := (hT0cov u v huv).resolve_left hu
            exact ⟨⟨v, u⟩, Finset.mem_sigma.2 ⟨hv, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, Or.inl hu⟩⟩, Sym2.eq_swap⟩
    rw [← hbij, Finset.card_sigma]
  -- Extract C_G and note every output o j < n + C_G.gates.length
  obtain ⟨CG, hCGfan, hCGsz, oG, hevG⟩ := hG
  have hoG_lt : ∀ j : Fin k, oG j < n + CG.gates.length := by
    intro j
    by_contra hge
    obtain ⟨y, y', hne'⟩ := hGnc j
    apply hne'
    rw [← hevG y j, ← hevG y' j]
    change (wiresFrom CG.gates (List.ofFn y)).getD (oG j) false =
      (wiresFrom CG.gates (List.ofFn y')).getD (oG j) false
    have hl1 : (wiresFrom CG.gates (List.ofFn y)).length = n + CG.gates.length := by
      rw [wiresFrom_len]; simp
    have hl2 : (wiresFrom CG.gates (List.ofFn y')).length = n + CG.gates.length := by
      rw [wiresFrom_len]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  -- Build star gadgets over T0.toList
  let starList : List (Fin n × List (Fin n)) := T0.toList.map fun v => (v, (nbrs v).toList)
  have hstar_ne : ∀ p ∈ starList, p.2 ≠ [] := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp
    have hv' : v ∈ T0 := Finset.mem_toList.1 hv
    obtain ⟨w, hw⟩ := hnbrs_ne v hv'
    intro heq
    dsimp only at heq
    have : w ∈ (nbrs v).toList := Finset.mem_toList.2 hw
    rw [heq] at this; simp at this
  let base1 := n + CG.gates.length
  obtain ⟨gsStars, starOuts, hokStars, hlenStars, houtsLen, houtsLt, hevStars⟩ :=
    build_stars starList hstar_ne base1 (by omega)
  have hstars_card : gsStars.length = K.edgeSet.ncard := by
    rw [hlenStars]
    simp only [starList, List.map_map]
    have h1 : (T0.toList.map (fun v => (nbrs v).toList.length)).sum = ∑ v ∈ T0, (nbrs v).card := by
      have h2 : (fun v => (nbrs v).toList.length) = (fun v => (nbrs v).card) := by
        funext v; exact Finset.length_toList _
      rw [h2, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    rw [← hsum_edges]
    exact h1
  -- Final OR chain over A.toList.map Fin.val ++ starOuts
  let topWs : List ℕ := A.toList.map Fin.val ++ starOuts
  have htop_len : topWs.length = A.card + T0.card := by
    simp [topWs, houtsLen, starList]
  have htop_ne : topWs ≠ [] := by
    intro heq
    have h0 : A.card + T0.card = 0 := by rw [← htop_len, heq]; rfl
    rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · have := Finset.card_pos.2 ⟨a, ha⟩; omega
    · rcases hT0cov u v huv with hu | hv
      · have := Finset.card_pos.2 ⟨u, hu⟩; omega
      · have := Finset.card_pos.2 ⟨v, hv⟩; omega
  have htop_lt : ∀ a ∈ topWs, a < base1 + gsStars.length := by
    intro a ha
    rcases List.mem_append.1 ha with ha1 | ha2
    · obtain ⟨u, _, rfl⟩ := List.mem_map.1 ha1
      have := u.isLt; omega
    · exact houtsLt a ha2
  obtain ⟨gsTop, topOut, hokTop, hlenTop, _, hevTop⟩ :=
    build_orChain (base1 + gsStars.length) topWs htop_ne htop_lt
  let allGs := CG.gates ++ (gsStars ++ gsTop)
  refine ⟨⟨allGs, 0⟩, ?_, ?_, topOut, oG, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg1 | hg2
    · exact hCGfan g hg1
    · rcases List.mem_append.1 hg2 with ha | hb
      · exact hokStars g ha
      · exact hokTop g hb
  · change allGs.length ≤ s
    have hszG : CG.gates.length ≤ t := hCGsz
    simp only [allGs, List.length_append]
    omega
  · intro x
    have hCG_len : (wiresFrom CG.gates (List.ofFn x)).length = base1 := by
      rw [wiresFrom_len]; simp [base1]
    have hCG_x : ∀ i : Fin n, (wiresFrom CG.gates (List.ofFn x)).getD i.val false = x i := by
      intro i
      rw [wiresFrom_getD_lt_init CG.gates (List.ofFn x) i.val (by simp)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [i.isLt]
    refine ⟨?_, fun j => ?_⟩
    · change (wiresFrom allGs (List.ofFn x)).getD topOut false = F K A x
      have h1 : wiresFrom allGs (List.ofFn x) =
          wiresFrom gsTop (wiresFrom gsStars (wiresFrom CG.gates (List.ofFn x))) := by
        simp [allGs, wiresFrom_append_gs]
      rw [h1]
      set wS := wiresFrom gsStars (wiresFrom CG.gates (List.ofFn x))
      have hwS_len : wS.length = base1 + gsStars.length := by
        rw [wiresFrom_len, hCG_len]
      rw [hevTop wS hwS_len, Bool.eq_iff_iff, F_true]
      simp only [topWs, List.any_append, Bool.or_eq_true, List.any_eq_true]
      apply or_congr
      · constructor
        · rintro ⟨a, ha, hval⟩
          obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
          refine ⟨u, Finset.mem_toList.1 hu, ?_⟩
          have hu' : wS.getD u.val false = x u := by
            rw [wiresFrom_getD_lt_init gsStars _ u.val (by rw [hCG_len]; have := u.isLt; omega)]
            exact hCG_x u
          rwa [hu'] at hval
        · rintro ⟨u, hu, hxu⟩
          refine ⟨u.val, List.mem_map.2 ⟨u, Finset.mem_toList.2 hu, rfl⟩, ?_⟩
          rw [wiresFrom_getD_lt_init gsStars _ u.val (by rw [hCG_len]; have := u.isLt; omega)]
          rw [hCG_x u]; exact hxu
      · constructor
        · rintro ⟨a, ha, hval⟩
          obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 ha
          have hidx' : idx < starList.length := by omega
          have hget : starOuts.getD idx 0 = starOuts[idx] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; rfl
          have hev := hevStars x (wiresFrom CG.gates (List.ofFn x)) hCG_len hCG_x idx hidx'
          rw [hget] at hev
          rw [hev, Bool.and_eq_true, List.any_eq_true] at hval
          obtain ⟨hxv, u, hu, hxu⟩ := hval
          have hvT : (starList[idx]'hidx').1 ∈ T0 := by
            have hmem : starList[idx]'hidx' ∈ starList := List.getElem_mem hidx'
            obtain ⟨v, hv, heqv⟩ := List.mem_map.1 hmem
            rw [← heqv]; exact Finset.mem_toList.1 hv
          have hu_nbr : u ∈ nbrs (starList[idx]'hidx').1 := by
            have hmem : starList[idx]'hidx' ∈ starList := List.getElem_mem hidx'
            obtain ⟨v, hv, heqv⟩ := List.mem_map.1 hmem
            rw [← heqv] at hu ⊢
            exact Finset.mem_toList.1 hu
          exact ⟨(starList[idx]'hidx').1, u, (Finset.mem_filter.1 hu_nbr).2.1, hxv, hxu⟩
        · rintro ⟨u, v, huv, hxu, hxv⟩
          obtain ⟨a, b, haT, hb_nbr, hxa, hxb⟩ :
              ∃ a b : Fin n, a ∈ T0 ∧ b ∈ nbrs a ∧ x a = true ∧ x b = true := by
            by_cases hu : u ∈ T0
            · by_cases hv : v ∈ T0
              · by_cases hlt : u.val < v.val
                · exact ⟨u, v, hu, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, Or.inr hlt⟩, hxu, hxv⟩
                · have hgt : v.val < u.val := by have := huv.ne; omega
                  exact ⟨v, u, hv, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩, hxv, hxu⟩
              · exact ⟨u, v, hu, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv, Or.inl hv⟩, hxu, hxv⟩
            · have hv : v ∈ T0 := (hT0cov u v huv).resolve_left hu
              exact ⟨v, u, hv, Finset.mem_filter.2 ⟨Finset.mem_univ _, huv.symm, Or.inl hu⟩, hxv, hxu⟩
          have ha_mem : (a, (nbrs a).toList) ∈ starList :=
            List.mem_map.2 ⟨a, Finset.mem_toList.2 haT, rfl⟩
          obtain ⟨idx, hidx, hidx_eq⟩ := List.mem_iff_getElem.1 ha_mem
          have hidx_o : idx < starOuts.length := by omega
          refine ⟨starOuts[idx]'hidx_o, List.getElem_mem hidx_o, ?_⟩
          have hget : starOuts.getD idx 0 = starOuts[idx]'hidx_o := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_o]; rfl
          have hev := hevStars x (wiresFrom CG.gates (List.ofFn x)) hCG_len hCG_x idx hidx
          rw [hget] at hev
          rw [hev, hidx_eq, Bool.and_eq_true, List.any_eq_true]
          exact ⟨hxa, b, Finset.mem_toList.2 hb_nbr, hxb⟩
    · change (wiresFrom allGs (List.ofFn x)).getD (oG j) false = G j x
      rw [show allGs = CG.gates ++ (gsStars ++ gsTop) from rfl, wiresFrom_append_gs]
      rw [wiresFrom_getD_lt_init (gsStars ++ gsTop) _ (oG j) (by rw [hCG_len]; exact hoG_lt j)]
      exact hevG x j

end PEqualNP.Outside.L_meta_659

theorem PEqualNP.Outside.L_meta_659 : ∀ (n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (G : Fin k → (Fin n → Bool) → Bool), (∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle) → (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) → (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) → (∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') → (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) → (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)) → (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i' false) ≠ G j (Function.update x i' true)) → i = i') → ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ (o1 : ℕ) (o : Fin k → ℕ), ∀ x : Fin n → Bool, ((C.wires (List.ofFn x)).getD o1 false = true ↔ ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) ∧ ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x) ↔ ∃ (T : Finset (Fin n)) (t : ℕ), (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) ∧ A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧ ∃ o : Fin k → ℕ, ∀ (x : Fin n → Bool) (j : Fin k), (C.wires (List.ofFn x)).getD (o j) false = G j x) := by
  intro n k s K A G hac hdisj hne hGnc hshared
  have hiff : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (o1 : ℕ) (o : Fin k → ℕ),
      (∀ x : Fin n → Bool,
      ((C.wires (List.ofFn x)).getD o1 false = true ↔
        ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) ∧
      ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x) ↔
      (∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD o1 false = PEqualNP.Outside.L_meta_659.F K A x ∧
        ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x) := by
    intro C o1 o
    constructor
    · intro h x
      refine ⟨?_, (h x).2⟩
      rw [Bool.eq_iff_iff, PEqualNP.Outside.L_meta_659.F_true]
      exact (h x).1
    · intro h x
      refine ⟨?_, (h x).2⟩
      rw [(h x).1, PEqualNP.Outside.L_meta_659.F_true]
  constructor
  · rintro ⟨C, hC, hsz, o1, o, hev⟩
    exact PEqualNP.Outside.L_meta_659.lower_bound (2 * K.edgeSet.ncard + A.card) n k s K A G rfl
      hac hdisj hne hGnc hshared ⟨C, hC, hsz, o1, o, (hiff C o1 o).1 hev⟩
  · rintro ⟨T, t, hT, hbd, hG⟩
    obtain ⟨C, hC, hsz, o1, o, hev⟩ :=
      PEqualNP.Outside.L_meta_659.upper_bound K A G hne hGnc T t hT hbd hG
    exact ⟨C, hC, hsz, o1, o, (hiff C o1 o).2 hev⟩
