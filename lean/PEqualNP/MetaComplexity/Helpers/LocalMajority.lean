import PEqualNP.MetaComplexity.Helpers.LocalPrivate
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# Every table of a 1-local reduction of parity to partial MCSP is easy

Helper for `L-meta-041`. In a 1-local reduction of parity to partial MCSP of fixed format, on at
least three input bits, EVERY input (odd or even) has a function of circuit size at most
`3 * s + 4` consistent with its table.

An odd input has a witness of size `s` (the reduction). For an even input `x`, flip one of
three positions: the three neighbours are odd and have witnesses of size `s`. A table entry
that is defined at `x` keeps its value at two of the three neighbours at least (`two_change`:
an entry cannot change along two different positions), so the majority of the three witnesses
is consistent with the table of `x`. The majority of three circuits is the three circuits put
one after the other, the later ones with their gate wires renumbered (`reloc_wires`), and four
more gates (`maj_size`).
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalMajority

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalPrivate

/-! ## Three circuits and a majority -/

/-- Renumber the wires a gate reads: the `m` input wires stay, every other wire moves up by
`d`. -/
def rel (m d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun a => if a < m then a else a + d⟩

/-- Gates renumbered by `rel` and run after `p.length` foreign wires compute what the original
gates compute. -/
theorem reloc_wires (x p : List Bool) (gs : List Gate) : ∀ t : List Bool,
    wiresFrom (gs.map (rel x.length p.length)) (x ++ p ++ t) =
      x ++ p ++ (wiresFrom gs (x ++ t)).drop x.length := by
  induction gs with
  | nil => intro t; simp [wiresFrom]
  | cons g gs ih =>
    intro t
    have key : ∀ a : ℕ, (x ++ p ++ t).getD (if a < x.length then a else a + p.length) false =
        (x ++ t).getD a false := by
      intro a
      by_cases h : a < x.length
      · rw [if_pos h, List.append_assoc, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
      · rw [if_neg h, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by omega)]
        congr 1
        simp
        omega
    have hval : (rel x.length p.length g).op.eval
        ((rel x.length p.length g).inputs.map fun i => (x ++ p ++ t).getD i false) =
        g.op.eval (g.inputs.map fun i => (x ++ t).getD i false) := by
      simp only [rel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact key a
    have e1 : wiresFrom ((g :: gs).map (rel x.length p.length)) (x ++ p ++ t) =
        wiresFrom (gs.map (rel x.length p.length)) (x ++ p ++ t ++
          [(rel x.length p.length g).op.eval
            ((rel x.length p.length g).inputs.map fun i => (x ++ p ++ t).getD i false)]) := rfl
    have e2 : wiresFrom (g :: gs) (x ++ t) =
        wiresFrom gs (x ++ t ++ [g.op.eval (g.inputs.map fun i => (x ++ t).getD i false)]) := rfl
    rw [e1, e2, hval, List.append_assoc (x ++ p), ih, List.append_assoc x t]

/-- Where the output wire `o` of a block of `l` gates goes when the block is put after `d`
foreign wires: an input wire stays, a gate wire moves up by `d`, and a wire that does not exist
goes to `B`, chosen beyond every wire. -/
def out (m d l B o : ℕ) : ℕ :=
  if o < m then o else if o < m + l then o + d else B

theorem out_range (m d l L B o : ℕ) (hL : m + d + l ≤ L) (hB : L + 4 ≤ B) :
    out m d l B o < L ∨ L + 4 ≤ out m d l B o := by
  unfold out
  split_ifs <;> omega

theorem getD_mid (v x p u q : List Bool) (d l B o : ℕ) (hv : v = x ++ p ++ u ++ q)
    (hB : v.length ≤ B) (hd : d = p.length) (hl : l = u.length) :
    v.getD (out x.length d l B o) false = (x ++ u).getD o false := by
  subst hv hd hl
  unfold out
  by_cases h1 : o < x.length
  · rw [if_pos h1, List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ h1,
      List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : o < x.length + u.length
    · rw [if_pos h2, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      simp
      omega
    · rw [if_neg h2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hB, List.getElem?_eq_none (by simp; omega)]

/-- The four gates of a majority of the wires `a`, `b`, `c`, appended after `L` wires. -/
def fin4 (L a b c : ℕ) : List Gate :=
  [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [a, b]⟩, ⟨GateOp.and, [c, L + 1]⟩,
    ⟨GateOp.or, [L, L + 2]⟩]

/-- The four gates compute the majority, when each of `a`, `b`, `c` is a wire of `v` or lies
beyond the four new wires (and so reads `false`). -/
theorem final_maj (v : List Bool) (a b c : ℕ) (ha : a < v.length ∨ v.length + 4 ≤ a)
    (hb : b < v.length ∨ v.length + 4 ≤ b) (hc : c < v.length ∨ v.length + 4 ≤ c) :
    (wiresFrom (fin4 v.length a b c) v).getD (v.length + 3) false =
      ((v.getD a false && v.getD b false) ||
        (v.getD c false && (v.getD a false || v.getD b false))) := by
  have A : ∀ (t : List Bool) (i : ℕ), t.length ≤ 4 → (i < v.length ∨ v.length + 4 ≤ i) →
      (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i ht h
    rcases h with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  have Aa := fun (t : List Bool) (ht : t.length ≤ 4) => A t a ht ha
  have Ab := fun (t : List Bool) (ht : t.length ≤ 4) => A t b ht hb
  have Ac := fun (t : List Bool) (ht : t.length ≤ 4) => A t c ht hc
  simp [fin4, wiresFrom, GateOp.eval, Aa, Ab, Ac, List.getD_eq_getElem?_getD]

/-- Three blocks of gates and the four majority gates, as one gate list on `m` inputs. -/
def glued (m : ℕ) (g1 g2 g3 : List Gate) (o1 o2 o3 : ℕ) : List Gate :=
  g1 ++ g2.map (rel m g1.length) ++ g3.map (rel m (g1.length + g2.length)) ++
    fin4 (m + (g1.length + g2.length + g3.length))
      (out m 0 g1.length (m + (g1.length + g2.length + g3.length) + 4) o1)
      (out m g1.length g2.length (m + (g1.length + g2.length + g3.length) + 4) o2)
      (out m (g1.length + g2.length) g3.length (m + (g1.length + g2.length + g3.length) + 4) o3)

theorem glue (x : List Bool) (g1 g2 g3 : List Gate) (o1 o2 o3 : ℕ) :
    (wiresFrom (glued x.length g1 g2 g3 o1 o2 o3) x).getD
        (x.length + (g1.length + g2.length + g3.length) + 3) false =
      (((wiresFrom g1 x).getD o1 false && (wiresFrom g2 x).getD o2 false) ||
        ((wiresFrom g3 x).getD o3 false &&
          ((wiresFrom g1 x).getD o1 false || (wiresFrom g2 x).getD o2 false))) := by
  obtain ⟨t1, ht1, hl1⟩ := wiresFrom_prefix g1 x
  obtain ⟨t2, ht2, hl2⟩ := wiresFrom_prefix g2 x
  obtain ⟨t3, ht3, hl3⟩ := wiresFrom_prefix g3 x
  have r2 : wiresFrom (g2.map (rel x.length g1.length)) (x ++ t1) = x ++ t1 ++ t2 := by
    have h := reloc_wires x t1 g2 []
    rw [List.append_nil, List.append_nil, ht2, List.drop_left, hl1] at h
    exact h
  have r3 : wiresFrom (g3.map (rel x.length (g1.length + g2.length))) (x ++ t1 ++ t2) =
      x ++ t1 ++ t2 ++ t3 := by
    have h := reloc_wires x (t1 ++ t2) g3 []
    rw [List.append_nil, List.append_nil, ht3, List.drop_left, List.length_append, hl1, hl2,
      ← List.append_assoc] at h
    exact h
  have hlen : (x ++ t1 ++ t2 ++ t3).length = x.length + (g1.length + g2.length + g3.length) := by
    simp [hl1, hl2, hl3]
    omega
  unfold glued
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_append, ht1, r2, r3, ← hlen,
    final_maj _ _ _ _ (out_range _ _ _ _ _ _ (by rw [hlen]; omega) le_rfl)
      (out_range _ _ _ _ _ _ (by rw [hlen]; omega) le_rfl)
      (out_range _ _ _ _ _ _ (by rw [hlen]; omega) le_rfl),
    getD_mid _ x [] t1 (t2 ++ t3) 0 g1.length _ o1 (by simp) (by omega) rfl hl1.symm,
    getD_mid _ x t1 t2 t3 g1.length g2.length _ o2 rfl (by omega) hl1.symm hl2.symm,
    getD_mid _ x (t1 ++ t2) t3 [] (g1.length + g2.length) g3.length _ o3 (by simp) (by omega)
      (by simp [hl1, hl2]) hl3.symm,
    ht2, ht3]

theorem ok_rel (m d : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rel m d g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (rel m d g).inputs.length ≤ 2 := by
  simpa [rel] using h

/-- The majority of three functions of circuit size `s` has circuit size `3 * s + 4`. -/
theorem maj_size (n s : ℕ) (f1 f2 f3 : (Fin n → Bool) → Bool) (h1 : HasCircuitSize n f1 s)
    (h2 : HasCircuitSize n f2 s) (h3 : HasCircuitSize n f3 s) :
    HasCircuitSize n (fun z => (f1 z && f2 z) || (f3 z && (f1 z || f2 z))) (3 * s + 4) := by
  obtain ⟨C1, F1, S1, E1⟩ := h1
  obtain ⟨C2, F2, S2, E2⟩ := h2
  obtain ⟨C3, F3, S3, E3⟩ := h3
  refine ⟨⟨glued n C1.gates C2.gates C3.gates C1.output C2.output C3.output,
    n + (C1.gates.length + C2.gates.length + C3.gates.length) + 3⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [glued, List.mem_append, List.mem_map] at hg
    rcases hg with ((hg | ⟨g', hg', rfl⟩) | ⟨g', hg', rfl⟩) | hg
    · exact F1 g hg
    · exact ok_rel _ _ _ (F2 g' hg')
    · exact ok_rel _ _ _ (F3 g' hg')
    · simp only [fin4, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp
  · simp only [Circuit.size] at S1 S2 S3 ⊢
    simp only [glued, fin4, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · intro z
    have h := glue (List.ofFn z) C1.gates C2.gates C3.gates C1.output C2.output C3.output
    simp only [List.length_ofFn] at h
    have e1 := E1 z
    have e2 := E2 z
    have e3 := E3 z
    simp only [Circuit.eval, wires_eq] at e1 e2 e3 ⊢
    rw [h, e1, e2, e3]

/-! ## A table entry changes along one position at most -/

/-- A function with certificates of size one cannot change under a flip at `i` and also under
a flip at another position `j`. -/
theorem same_two {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) (h : Cert1 g) (x : Fin n → Bool)
    (i j : Fin n) (hij : i ≠ j) (hi : g (Function.update x i (!x i)) ≠ g x)
    (hj : g (Function.update x j (!x j)) ≠ g x) : False :=
  hj (dep g h (Function.update x i (!x i)) x i
    (fun k hk => (Function.update_of_ne hk _ x).symm) (fun e => hi e.symm)
    (Function.update x j (!x j)) (Function.update_of_ne hij _ x))

/-- The entry cannot become undefined under a flip at `i` and change value under a flip at
another position `j`: flipping both would give the pair `false, true`, which is no code. -/
theorem mixed {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (b c : Bool) (hx : E x = some b)
    (hi : E (Function.update x i (!x i)) = none)
    (hj : E (Function.update x j (!x j)) = some c) (hcb : c ≠ b) : False := by
  have hDi := dep (fun u => (E u).isSome) hD x (Function.update x i (!x i)) i
    (fun k hk => Function.update_of_ne hk _ x) (by simp [hi, hx])
  have hVj := dep (fun u => (E u).getD false) hV x (Function.update x j (!x j)) j
    (fun k hk => Function.update_of_ne hk _ x) (by simpa [hj, hx] using hcb)
  have hb : b = false := by
    by_contra hb
    exact same_two (fun u => (E u).getD false) hV x i j hij (by simpa [hi, hx] using Ne.symm hb)
      (by simpa [hj, hx] using hcb)
  have h1 := hDi (Function.update (Function.update x i (!x i)) j (!x j))
    (Function.update_of_ne hij _ _)
  have h2 := hVj (Function.update (Function.update x i (!x i)) j (!x j)) (by simp)
  simp only [hi, hj] at h1 h2
  subst hb
  cases hu : E (Function.update (Function.update x i (!x i)) j (!x j)) with
  | none => rw [hu] at h2; cases c <;> simp_all
  | some d => rw [hu] at h1; simp at h1

/-- An entry defined at `x` keeps its value under a flip at `i` or under a flip at `j`. -/
theorem two_change {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (b : Bool) (hx : E x = some b) :
    E (Function.update x i (!x i)) = some b ∨ E (Function.update x j (!x j)) = some b := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hi, hj⟩ := hcon
  cases ei : E (Function.update x i (!x i)) with
  | none =>
    cases ej : E (Function.update x j (!x j)) with
    | none =>
      exact same_two (fun u => (E u).isSome) hD x i j hij (by simp [ei, hx]) (by simp [ej, hx])
    | some c =>
      exact mixed E hD hV x i j hij b c hx ei ej (fun e => hj (by rw [ej, e]))
  | some c =>
    have hc : c ≠ b := fun e => hi (by rw [ei, e])
    cases ej : E (Function.update x j (!x j)) with
    | none => exact mixed E hD hV x j i (Ne.symm hij) b c hx ej ei hc
    | some c' =>
      have hc' : c' ≠ b := fun e => hj (by rw [ej, e])
      exact same_two (fun u => (E u).getD false) hV x i j hij (by simpa [ei, hx] using hc)
        (by simpa [ej, hx] using hc')

/-! ## The statement -/

/-- Flipping one position of an input that is not of odd weight gives one of odd weight. -/
theorem flip_odd {n : ℕ} (x : Fin n → Bool) (i : Fin n)
    (hx : ¬ (Finset.univ.filter fun k : Fin n => x k = true).card % 2 = 1) :
    (Finset.univ.filter fun k : Fin n => Function.update x i (!x i) k = true).card % 2 = 1 := by
  cases hxi : x i with
  | false =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!false) k = true) =
        insert i (Finset.univ.filter fun k : Fin n => x k = true) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [hset, Finset.card_insert_of_notMem (by simp [hxi])]
    omega
  | true =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!true) k = true) =
        (Finset.univ.filter fun k : Fin n => x k = true).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hmem : i ∈ Finset.univ.filter fun k : Fin n => x k = true := by simp [hxi]
    have hpos := Finset.card_pos.2 ⟨i, hmem⟩
    rw [hset, Finset.card_erase_of_mem hmem]
    omega

/-- Every table is easy: the statement of `L-meta-041`. -/
theorem maj_witness (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hn : 3 ≤ n) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f (3 * s + 4) := by
  by_cases hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1
  · obtain ⟨f, hc, hs, _⟩ := private_witness n n' s w T hq hfmt hred x hx
    exact ⟨f, hc, hasCircuitSize_mono (by omega) hs⟩
  · have wit : ∀ l : Fin n, ∃ f : (Fin n' → Bool) → Bool,
        Consistent n' (T (Function.update x l (!x l))) f ∧ HasCircuitSize n' f s := by
      intro l
      obtain ⟨f, hc, hs, _⟩ := private_witness n n' s w T hq hfmt hred _ (flip_odd x l hx)
      exact ⟨f, hc, hs⟩
    obtain ⟨f1, c1, s1⟩ := wit ⟨0, by omega⟩
    obtain ⟨f2, c2, s2⟩ := wit ⟨1, by omega⟩
    obtain ⟨f3, c3, s3⟩ := wit ⟨2, by omega⟩
    refine ⟨fun z => (f1 z && f2 z) || (f3 z && (f1 z || f2 z)), ?_, maj_size n' s f1 f2 f3 s1 s2 s3⟩
    intro e b he
    by_cases hk : tableIndex e < 2 ^ n'
    · have hD : Cert1 fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).isSome := by
        intro u
        obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * tableIndex e) u
        refine ⟨S, c, fun v hv => ?_⟩
        have h := hS v hv
        rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).1,
          (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).1] at h
        exact Option.some.inj h
      have hV : Cert1 fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).getD false := by
        intro u
        obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * tableIndex e + 1) u
        refine ⟨S, c, fun v hv => ?_⟩
        have h := hS v hv
        rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).2,
          (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).2] at h
        exact Option.some.inj h
      have key : ∀ i j : Fin n, i ≠ j →
          (T (Function.update x i (!x i))).getD (tableIndex e) none = some b ∨
            (T (Function.update x j (!x j))).getD (tableIndex e) none = some b :=
        fun i j hij => two_change (fun u => (T u).getD (tableIndex e) none) hD hV x i j hij b he
      have ne01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      have ne02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
      have ne12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
      show ((f1 e && f2 e) || (f3 e && (f1 e || f2 e))) = b
      rcases key _ _ ne01 with h | h
      · rw [c1 e b h]
        rcases key _ _ ne12 with h' | h'
        · rw [c2 e b h']; cases b <;> cases f3 e <;> rfl
        · rw [c3 e b h']; cases b <;> cases f2 e <;> rfl
      · rw [c2 e b h]
        rcases key _ _ ne02 with h' | h'
        · rw [c1 e b h']; cases b <;> cases f3 e <;> rfl
        · rw [c3 e b h']; cases b <;> cases f1 e <;> rfl
    · exfalso
      have hl : (T x).length ≤ tableIndex e := by
        rw [(hfmt _).2]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at he
      simp at he

end PEqualNP.MetaComplexity.Helpers.LocalMajority
