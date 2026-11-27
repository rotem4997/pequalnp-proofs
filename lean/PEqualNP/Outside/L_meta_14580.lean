import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14580_aux

open PEqualNP.CircuitLowerBounds

def edges : List ℕ :=
  [0, 2, 0, 3, 1, 3, 2, 3, 0, 4, 2, 4]

def target (x : Fin 5 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

abbrev B := BitVec 60
abbrev Sig := B × B

def budget (_ : Fin 1) : ℕ := 7

def pairs (_ : Fin 1) : List (ℕ × ℕ) := [(5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 8), (5, 16), (5, 18), (5, 24), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 6), (9, 8), (9, 16), (9, 18), (9, 24), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 6), (10, 8), (10, 16), (10, 18), (10, 24), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 6), (12, 8), (12, 16), (12, 18), (12, 24), (17, 0), (17, 1), (17, 2), (17, 3), (17, 4), (17, 6), (17, 8), (17, 16), (17, 18), (17, 24), (20, 0), (20, 1), (20, 2), (20, 3), (20, 4), (20, 6), (20, 8), (20, 16), (20, 18), (20, 24)]

def maskFun (m : ℕ) : Fin 5 → Bool := fun i => m.testBit i.val

def pairA (t : Fin 1) (r : Fin 60) : Fin 5 → Bool := maskFun ((pairs t).getD r.val (0,0)).1
def pairB (t : Fin 1) (r : Fin 60) : Fin 5 → Bool := maskFun ((pairs t).getD r.val (0,0)).2

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 60 → Bool) : B :=
  BitVec.ofNat 60 (mkBVLoop 60 (fun i => if h : i < 60 then p ⟨i, h⟩ else false))

lemma testBit_mkBVLoop (n : ℕ) : ∀ (p : ℕ → Bool) (i : ℕ), i < n →
    (mkBVLoop n p).testBit i = p i := by
  induction n with
  | zero => intro p i hi; omega
  | succ n ih =>
    intro p i hi
    cases i with
    | zero =>
      simp only [mkBVLoop]
      cases p 0 <;> simp
    | succ i =>
      simp only [mkBVLoop]
      have hbit : (2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0).testBit (i + 1) =
          (mkBVLoop n (fun k => p (k + 1))).testBit i := by
        cases p 0 <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (fun k => p (k + 1)) i (by omega)]

lemma getElem_mkBV (p : Fin 60 → Bool) (i : ℕ) (hi : i < 60) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 60 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 60) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 60
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def goalSig : Sig := (top, 0)

def neg (a : Sig) : Sig := (~~~ a.1, ~~~ a.2)

def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~ a.2

def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a :: l => sep d a ||| unionSep d l

def before (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)

def dropped (del v : List Sig) : List Sig :=
  v.filter (fun x => !del.contains x)

def tryGate (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains goalSig
  | k + 1, t, v =>
    v.contains goalSig ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (search k t) v rest (bin false a b) keep ||
         tryGate k t (search k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 60 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

def initList (_ : Fin 1) : List Sig := [(BitVec.ofNat 60 1124800396263423, BitVec.ofNat 60 11270004932618250), (BitVec.ofNat 60 1072693248, BitVec.ofNat 60 338100147978547500), (BitVec.ofNat 60 1151796703137891327, BitVec.ofNat 60 54096023676567600), (BitVec.ofNat 60 1099511626752, BitVec.ofNat 60 649152284118811200), (BitVec.ofNat 60 1152920405095219200, BitVec.ofNat 60 1009792441962595200)]

def evalGateSig (g : Gate) (W : List Sig) : Sig :=
  match g.op, g.inputs with
  | GateOp.and, [] => one
  | GateOp.and, [p] => W.getD p zero
  | GateOp.and, [p, q] => bin false (W.getD p zero) (W.getD q zero)
  | GateOp.or, [] => zero
  | GateOp.or, [p] => W.getD p zero
  | GateOp.or, [p, q] => bin true (W.getD p zero) (W.getD q zero)
  | GateOp.not, [] => one
  | GateOp.not, p :: _ => neg (W.getD p zero)
  | _, _ => zero

def evalGates (gs : List Gate) (W : List Sig) : List Sig :=
  gs.foldl (fun W g => W ++ [evalGateSig g W]) W

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_cons (g : Gate) (rest : List Gate) (W : List Sig) :
    evalGates (g :: rest) W = evalGates rest (W ++ [evalGateSig g W]) := rfl

lemma evalWires_cons (g : Gate) (rest : List Gate) (w : List Bool) :
    evalWires (g :: rest) w =
      evalWires rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl


set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
lemma pairA_true : ∀ t (r : Fin 60), target (pairA t r) = true := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
lemma pairB_false : ∀ t (r : Fin 60), target (pairB t r) = false := by decide +kernel

lemma initList_nodup : ∀ t : Fin 1, (initList t).Nodup := by decide
lemma initList_len : ∀ t : Fin 1, (initList t).length = 5 := by decide
lemma target_ne_zero : goalSig ≠ zero := by decide
lemma target_ne_one : goalSig ≠ one := by decide

lemma all_init_needed_bool : ∀ t : Fin 1,
    (initList t).all (fun s => unionSep true ((initList t).erase s) != top) = true := by decide

lemma all_init_needed (t : Fin 1) : ∀ s ∈ initList t, unionSep true ((initList t).erase s) ≠ top := by
  intro s hs
  have h := List.all_eq_true.1 (all_init_needed_bool t) s hs
  exact bne_iff_ne.1 h

private def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private lemma isNot_iff (g : Gate) : isNot g = true ↔ g.op = .not := by
  obtain ⟨op,inputs⟩ := g
  cases op <;> simp [isNot]

private lemma not_count (l : List Gate)
    (unique : ∀ i j : Fin l.length, (l.get i).op = .not → (l.get j).op = .not → i = j) :
    l.countP isNot ≤ 1 := by
  have h := List.countP_ofFn l.get isNot
  rw [List.ofFn_get] at h
  rw [h]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact unique a b ((isNot_iff _).1 (Finset.mem_filter.mp ha).2)
    ((isNot_iff _).1 (Finset.mem_filter.mp hb).2)

-- The live-profile proof is adapted from L-meta-8707 and its cited predecessors.
lemma bin_comm (isOr : Bool) (a b : Sig) : bin isOr a b = bin isOr b a := by
  cases isOr <;> simp only [bin, BitVec.or_comm, BitVec.and_comm]

lemma bin_self (isOr : Bool) (a : Sig) : bin isOr a a = a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.and_self]
  · simp only [bin, ↓reduceIte, BitVec.or_self]

lemma bin_zero_left (isOr : Bool) (a : Sig) : bin isOr zero a = if isOr then a else zero := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, zero, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp
  · simp only [bin, zero, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp

lemma bin_zero_right (isOr : Bool) (a : Sig) : bin isOr a zero = if isOr then a else zero := by
  rw [bin_comm, bin_zero_left]

lemma bin_one_left (isOr : Bool) (a : Sig) : bin isOr one a = if isOr then one else a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, one, top, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
  · simp only [bin, one, top, ↓reduceIte, BitVec.allOnes_or]

lemma bin_one_right (isOr : Bool) (a : Sig) : bin isOr a one = if isOr then one else a := by
  rw [bin_comm, bin_one_left]

lemma neg_zero : neg zero = one := by decide
lemma neg_one : neg one = zero := by decide

lemma before_trichotomy {a b : Sig} (hne : a ≠ b) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases h1 : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h1 h)
    have h2n : a.2.toNat ≠ b.2.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = true := by rw [beq_iff_eq]; exact h1
    have hb2 : (b.1 == a.1) = true := by rw [beq_iff_eq]; exact h1.symm
    rw [hb1, hb2]
    simp only [↓reduceIte, decide_eq_true_eq]
    omega
  · have h1n : a.1.toNat ≠ b.1.toNat := fun h => h1 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = false := beq_false_of_ne h1
    have hb2 : (b.1 == a.1) = false := beq_false_of_ne (Ne.symm h1)
    rw [hb1, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

lemma unionSep_perm {d : Bool} {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    unionSep d v₁ = unionSep d v₂ := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [unionSep, ih]
  | swap a b l =>
    simp only [unionSep]
    rw [← BitVec.or_assoc, ← BitVec.or_assoc, BitVec.or_comm (sep d a) (sep d b)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma unionSep_append (d : Bool) (l₁ l₂ : List Sig) :
    unionSep d (l₁ ++ l₂) = unionSep d l₁ ||| unionSep d l₂ := by
  induction l₁ with
  | nil => simp [unionSep]
  | cons a t ih => simp only [List.cons_append, unionSep, ih, BitVec.or_assoc]

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 60) :
    (unionSep d v)[i] = true ↔ ∃ s ∈ v, (sep d s)[i] = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a t ih =>
    simp only [unionSep, BitVec.getElem_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, rfl | hs, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, h⟩

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 60), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 60) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 60) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 60) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 60) :
    (sep d (bin isOr a b))[i] = true → (sep d a)[i] = true ∨ (sep d b)[i] = true := by
  cases d <;> cases isOr <;>
    simp only [sep, bin, ↓reduceIte, Bool.false_eq_true, BitVec.getElem_and,
      BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not] <;>
    cases a.1[i] <;> cases a.2[i] <;> cases b.1[i] <;> cases b.2[i] <;> decide

lemma unionSep_target_eq_top : unionSep false [goalSig] = top := by decide

lemma dropped_perm {del v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    (dropped del v₁).Perm (dropped del v₂) :=
  hp.filter _

lemma contains_perm {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) (x : Sig) :
    v₁.contains x = v₂.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

lemma list_any_eq_of_eq {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma search_perm : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search k t v₁ = search k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp goalSig
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate k t' (search k t') v₁ rest₁ g keep =
          tryGate k t' (search k t') v₂ rest₂ g keep := by
      intro t' rest₁ rest₂ g keep hrest
      have hlen : rest₁.length = rest₂.length := hrest.length_eq
      have hcont : v₁.contains g = v₂.contains g := contains_perm hp g
      have husep : unionSep (decide (0 < t')) rest₁ = unionSep (decide (0 < t')) rest₂ :=
        unionSep_perm hrest
      simp only [tryGate, hcont, hlen, husep]
      congr 1
      refine list_any_eq_of_eq keep _ _ (fun h _ => ?_)
      have hp' : (g :: (h ++ rest₁)).Perm (g :: (h ++ rest₂)) :=
        List.Perm.cons g (List.Perm.append_left h hrest)
      rw [ih t' hp']
    have hcontT : v₁.contains goalSig = v₂.contains goalSig := contains_perm hp goalSig
    have hunary : v₁.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.1 ha, ?_⟩
        rw [← htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.2 ha, ?_⟩
        rw [htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
    have hbinary :
        v₁.any (fun a => v₁.any (fun b => before a b &&
          (let rest := dropped [a, b] v₁
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₁ rest (bin false a b) keep ||
           tryGate k t (search k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₂ rest (bin false a b) keep ||
           tryGate k t (search k t) v₂ rest (bin true a b) keep))) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.2 ha, b, hp.mem_iff.2 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
    simp only [search, hcontT, hunary, hbinary]

lemma getD_mem_of_ne {W : List Sig} {p : ℕ} (hne : W.getD p zero ≠ zero) :
    W.getD p zero ∈ W := by
  by_cases hp : p < W.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  · rw [List.getD_eq_default _ _ (by omega)] at hne
    exact absurd rfl hne

lemma perm_of_nodup_same_mem {l₁ l₂ : List Sig} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hmem

lemma mem_dropped_iff {del v : List Sig} {x : Sig} :
    x ∈ dropped del v ↔ x ∈ v ∧ x ∉ del := by
  simp only [dropped, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, fun hm => ?_⟩
    have hc : del.contains x = true := List.contains_iff_mem.2 hm
    rw [hc] at hnot
    cases hnot
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    cases hc : del.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot

lemma tryGate_eq_true {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search (k + 1) t V = true := by
  obtain ⟨a, b, hab_ord, haW, hbW, ha0, ha1, hb0, hb1, hab, hbin⟩ :
      ∃ a b : Sig, before a b = true ∧ a ∈ W ∧ b ∈ W ∧ a ≠ zero ∧ a ≠ one ∧
        b ≠ zero ∧ b ≠ one ∧ a ≠ b ∧ sg = bin isOr a b := by
    rcases before_trichotomy hab_ne with h | h
    · exact ⟨a0, b0, h, ha0W, hb0W, ha0_ne0, ha0_ne1, hb0_ne0, hb0_ne1, hab_ne, hsgeq⟩
    · exact ⟨b0, a0, h, hb0W, ha0W, hb0_ne0, hb0_ne1, ha0_ne0, ha0_ne1, hab_ne.symm,
        by rw [hsgeq, bin_comm]⟩
  let addA : List Sig := if a ∈ U then [] else [a]
  let addB : List Sig := if b ∈ U then [] else [b]
  let V : List Sig := addA ++ addB ++ U
  have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x = b ∨ x ∈ U := by
    intro x
    simp only [V, addA, addB, List.mem_append]
    constructor
    · intro hx
      rcases hx with (hx | hx) | hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inl hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · by_cases haU : x ∈ U
        · exact Or.inr haU
        · exact Or.inl (Or.inl (by simp [haU]))
      · by_cases hbU : x ∈ U
        · exact Or.inr hbU
        · exact Or.inl (Or.inr (by simp [hbU]))
      · exact Or.inr hx
  have hV_nd : V.Nodup := by
    simp only [V, addA, addB]
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU, hUnd, hab]
  have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
    intro s hs
    rw [hV_mem] at hs
    rcases hs with rfl | rfl | hsU
    · exact ⟨haW, ha0, ha1⟩
    · exact ⟨hbW, hb0, hb1⟩
    · exact hUsub s hsU
  have hV_len : V.length ≤ (k + 1) - t + 1 := by
    have hA : addA.length ≤ 1 := by simp only [addA]; split_ifs <;> simp
    have hB : addB.length ≤ 1 := by simp only [addB]; split_ifs <;> simp
    have hlenV : V.length = addA.length + addB.length + U.length := by
      simp only [V, List.length_append]
    omega
  have hV_sep : unionSep (decide (0 < t)) V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hsV', hsi⟩ := htop
    rw [hPermV'.mem_iff, List.mem_cons] at hsV'
    rcases hsV' with rfl | hsU
    · rw [hbin] at hsi
      rcases sep_bin_bit _ _ a b i hi hsi with ha_b | hb_b
      · exact ⟨a, (hV_mem a).2 (Or.inl rfl), ha_b⟩
      · exact ⟨b, (hV_mem b).2 (Or.inr (Or.inl rfl)), hb_b⟩
    · exact ⟨s, (hV_mem s).2 (Or.inr (Or.inr hsU)), hsi⟩
  let hkeep : List Sig :=
    if a ∈ U then (if b ∈ U then [a, b] else [a]) else (if b ∈ U then [b] else [])
  have hhkeep_mem : hkeep ∈ [[], [a], [b], [a, b]] := by
    simp only [hkeep]; split_ifs <;> simp
  have hdrop_nd : (dropped [a, b] V).Nodup := hV_nd.filter _
  have hperm_next : (sg :: (hkeep ++ dropped [a, b] V)).Perm V' := by
    refine perm_of_nodup_same_mem ?_ hVnd ?_
    · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
      have hkh_nd : hkeep.Nodup := by
        simp only [hkeep]; split_ifs <;> simp [hab]
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
      · intro hm
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · apply hsgU
          simp only [hkeep] at hm
          split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> assumption
        · exact hsgV_not (mem_dropped_iff.1 hm).1
      · intro x hx y hy hxy
        subst hxy
        have hynot := (mem_dropped_iff.1 hy).2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hynot
        simp only [hkeep] at hx
        split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
    · intro x
      rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro (rfl | hx | hx)
        · exact Or.inl rfl
        · right
          simp only [hkeep] at hx
          split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> assumption
        · right
          have hx' := mem_dropped_iff.1 hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
          rw [hV_mem] at hx'
          rcases hx'.1 with rfl | rfl | hxU
          · exact absurd rfl hx'.2.1
          · exact absurd rfl hx'.2.2
          · exact hxU
      · rintro (rfl | hxU)
        · exact Or.inl rfl
        · right
          by_cases hxa : x = a
          · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
          · by_cases hxb : x = b
            · subst hxb; left; simp only [hkeep]; split_ifs <;> simp
            · right
              rw [mem_dropped_iff]
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨(hV_mem x).2 (Or.inr (Or.inr hxU)), hxa, hxb⟩
  have htry_ok : tryGate k t (search k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm k t hperm_next]
      exact hVsearch
  have hsearch_new : search (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma extract_live (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, goalSig ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, t ≤ gs.countP isNot ∧ k + gs.countP isNot ≤ t + gs.length ∧ ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search k t V = true := by
  induction gs with
  | nil =>
    intro W hT
    refine ⟨0, le_rfl, 0, le_rfl, by simp, by simp, [goalSig], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self goalSig)
  | cons g rest ih =>
    intro W hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, htNot, hMono, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hT
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, by simp only [List.countP_cons]; omega,
        by simp only [List.length_cons, List.countP_cons]; split <;> omega, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
      intro s hs
      obtain ⟨hsmem, hs0, hs1⟩ := hVsub s hs
      rw [List.mem_append, List.mem_singleton] at hsmem
      rcases hsmem with hsmem | rfl
      · exact ⟨hsmem, hs0, hs1⟩
      · rcases hskip with hnot | hin
        · exact absurd hs hnot
        · exact ⟨hin, hs0, hs1⟩
    · push Not at hskip
      obtain ⟨hsgV, hsgW⟩ := hskip
      have hsg01 := hVsub sg hsgV
      have hsg0 : sg ≠ zero := hsg01.2.1
      have hsg1 : sg ≠ one := hsg01.2.2
      set U := V'.erase sg
      have hUnd : U.Nodup := hVnd.erase sg
      have hsgU : sg ∉ U := List.Nodup.not_mem_erase hVnd
      have hPermV' : V'.Perm (sg :: U) := List.perm_cons_erase hsgV
      have hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
        intro s hs
        have hsV : s ∈ V' := List.mem_of_mem_erase hs
        have hsne : s ≠ sg := fun h => hsgU (h ▸ hs)
        obtain ⟨hsm, hs0, hs1⟩ := hVsub s hsV
        rw [List.mem_append, List.mem_singleton] at hsm
        exact ⟨hsm.resolve_right hsne, hs0, hs1⟩
      have hUlen : U.length + 1 = V'.length := by
        have := hPermV'.length_eq
        simp at this
        omega
      rcases hg with ⟨hop, hinlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin false (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_left]; rfl
          have hb0_ne0 : b0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_right]; rfl
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_left]; simpa using hb0W
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_right]; simpa using ha0W
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, by simp only [List.countP_cons]; omega,
            by simp [isNot, hop]; omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg0; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin true (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h
            have hsgeq' : sg = b0 := by rw [hsgeq, h, bin_zero_left]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have hb0_ne0 : b0 ≠ zero := by
            intro h
            have hsgeq' : sg = a0 := by rw [hsgeq, h, bin_zero_right]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_left]; rfl
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_right]; rfl
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          exact ⟨k + 1, by simp; omega, t, by omega, by simp only [List.countP_cons]; omega,
            by simp [isNot, hop]; omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · have hsgeq : sg = neg (W.getD p zero) := by simp [sg, evalGateSig, hop, hin]
          set a := W.getD p zero
          have ha0 : a ≠ zero := by intro h; apply hsg1; rw [hsgeq, h, neg_zero]
          have ha1 : a ≠ one := by intro h; apply hsg0; rw [hsgeq, h, neg_one]
          have haW : a ∈ W := getD_mem_of_ne ha0
          let V : List Sig := if a ∈ U then U else a :: U
          have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x ∈ U := by
            intro x
            simp only [V]
            by_cases haU : a ∈ U
            · simp only [haU, ↓reduceIte]
              exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ haU) id⟩
            · simp only [haU, ↓reduceIte, List.mem_cons]
          have hV_nd : V.Nodup := by
            simp only [V]
            by_cases haU : a ∈ U <;> simp [haU, hUnd]
          have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
            intro s hs
            rw [hV_mem] at hs
            rcases hs with rfl | hsU
            · exact ⟨haW, ha0, ha1⟩
            · exact hUsub s hsU
          have hV_len : V.length ≤ (k + 1) - (t + 1) + 1 := by
            have : V.length ≤ U.length + 1 := by simp only [V]; split_ifs <;> simp
            omega
          have hV_sep : unionSep (decide (0 < t + 1)) V = top := by
            apply bv_eq_top_of_bits
            intro i hi
            rw [unionSep_bit_iff _ _ i hi]
            have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
            rw [unionSep_bit_iff _ _ i hi] at htop
            obtain ⟨s, hsV', hsi⟩ := htop
            have hsi' : (sep true s)[i] = true := sep_mono_true _ s i hi hsi
            rw [hPermV'.mem_iff, List.mem_cons] at hsV'
            rcases hsV' with rfl | hsU
            · rw [hsgeq, sep_neg_true a i hi] at hsi'
              exact ⟨a, (hV_mem a).2 (Or.inl rfl), by simpa using hsi'⟩
            · exact ⟨s, (hV_mem s).2 (Or.inr hsU), by simpa using hsi'⟩
          let hkeep : List Sig := if a ∈ U then [a] else []
          have hhkeep_mem : hkeep ∈ [[], [a]] := by simp only [hkeep]; split_ifs <;> simp
          have hdrop_nd : (dropped [a] V).Nodup := hV_nd.filter _
          have hperm_next : (sg :: (hkeep ++ dropped [a] V)).Perm V' := by
            refine perm_of_nodup_same_mem ?_ hVnd ?_
            · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
              have hkh_nd : hkeep.Nodup := by simp only [hkeep]; split_ifs <;> simp
              rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
              · intro hm
                rw [List.mem_append] at hm
                rcases hm with hm | hm
                · apply hsgU
                  simp only [hkeep] at hm
                  split_ifs at hm <;> simp at hm
                  rw [hm]; assumption
                · exact hsgV_not (mem_dropped_iff.1 hm).1
              · intro x hx y hy hxy
                subst hxy
                have hynot := (mem_dropped_iff.1 hy).2
                simp only [List.mem_singleton] at hynot
                simp only [hkeep] at hx
                split_ifs at hx <;> simp at hx
                exact hynot hx
            · intro x
              rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
              constructor
              · rintro (rfl | hx | hx)
                · exact Or.inl rfl
                · right
                  simp only [hkeep] at hx
                  split_ifs at hx <;> simp at hx
                  subst hx; assumption
                · right
                  have hx' := mem_dropped_iff.1 hx
                  simp only [List.mem_singleton] at hx'
                  rw [hV_mem] at hx'
                  exact hx'.1.resolve_left hx'.2
              · rintro (rfl | hxU)
                · exact Or.inl rfl
                · right
                  by_cases hxa : x = a
                  · subst hxa; left; simp only [hkeep]; split_ifs; simp
                  · right
                    rw [mem_dropped_iff]
                    simp only [List.mem_singleton]
                    exact ⟨(hV_mem x).2 (Or.inr hxU), hxa⟩
          have hsearch_new : search (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, by simp [isNot, hop]; omega,
            by simp [isNot, hop]; omega, V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
lemma excluded_4_0 : search 4 0 (initList 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
lemma excluded_5_0 : search 5 0 (initList 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
lemma excluded_6_0 : search 6 0 (initList 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
lemma excluded_5_1 : search 5 1 (initList 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
lemma excluded_6_1 : search 6 1 (initList 0) = false := by decide +kernel

lemma projected_check (k t : ℕ) (hk : k < budget 0) (hslots : 5 ≤ k - t + 1)
    (ht : t ≤ 1) : search k t (initList 0) = false := by
  change k < 7 at hk
  have hcases : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨
      (k = 6 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact excluded_4_0
  · exact excluded_5_0
  · exact excluded_6_0
  · exact excluded_5_1
  · exact excluded_6_1


def edges8 : List ℕ :=
  [0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7]

def target8 (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges8.length / 2,
    (List.ofFn x).getD (edges8.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges8.getD (2 * i + 1) 0) false = true)

def upperGates : List Gate :=
  [⟨.or, [0, 1]⟩,
   ⟨.or, [8, 5]⟩,
   ⟨.or, [9, 2]⟩,
   ⟨.or, [9, 3]⟩,
   ⟨.or, [11, 4]⟩,
   ⟨.and, [8, 5]⟩,
   ⟨.and, [10, 6]⟩,
   ⟨.and, [12, 7]⟩,
   ⟨.or, [13, 14]⟩,
   ⟨.or, [16, 15]⟩]

lemma upperShape : ∀ g ∈ upperGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [upperGates]

def upperDecidable : Decidable (∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates, 17⟩ (List.ofFn x) = target8 x) :=
  Fintype.decidableForallFintype

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma upperEval : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates, 17⟩ (List.ofFn x) = target8 x :=
  @of_decide_eq_true _ upperDecidable rfl

lemma replaceLarge (gates : List Gate) (h : 10 ≤ gates.length) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = target8 x :=
  ⟨upperGates, 17, upperShape, h, upperEval⟩


-- The first-use projection argument extends the L-meta-10318 reduction.
def ff {X : Type} : X → Bool := fun _ => false
def tt {X : Type} : X → Bool := fun _ => true
def combine {X : Type} (o : Bool) (a b : X → Bool) : X → Bool :=
  fun x => if o then a x || b x else a x && b x
def invert {X : Type} (a : X → Bool) : X → Bool := fun x => !(a x)

def Build {X : Type} (f : X → Bool) : ℕ → ℕ → Set (X → Bool) → Prop
  | 0, _, S => f ∈ S
  | k + 1, t, S =>
      f ∈ S ∨
      (∃ a ∈ S, ∃ b ∈ S, ∃ o : Bool, Build f k t (insert (combine o a b) S)) ∨
      (0 < t ∧ ∃ a ∈ S, Build f k (t - 1) (insert (invert a) S))

lemma build_weaken {X : Type} {f : X → Bool} {k t u : ℕ} {S T : Set (X → Bool)}
    (h : Build f k t S) (hST : S ⊆ T) (htu : t ≤ u) : Build f k u T := by
  induction k generalizing t u S T with
  | zero => exact hST h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨ht, a, ha, h⟩
    · exact Or.inl (hST h)
    · exact Or.inr (Or.inl ⟨a, hST ha, b, hST hb, o,
        ih h (Set.insert_subset_insert hST) htu⟩)
    · exact Or.inr (Or.inr ⟨by omega, a, hST ha,
        ih h (Set.insert_subset_insert hST) (by omega)⟩)

lemma build_step {X : Type} {f : X → Bool} {k t : ℕ} {S : Set (X → Bool)}
    (h : Build f k t S) : Build f (k + 1) t S := by
  induction k generalizing t S with
  | zero => exact Or.inl h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨ht, a, ha, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, o, ih h⟩)
    · exact Or.inr (Or.inr ⟨ht, a, ha, ih h⟩)

def pull {X Y : Type} (p : Y → X) (a : X → Bool) : Y → Bool := fun y => a (p y)

lemma pull_insert {X Y : Type} (p : Y → X) (a : X → Bool) (S : Set (X → Bool)) :
    pull p '' insert a S = insert (pull p a) (pull p '' S) := Set.image_insert_eq

lemma build_pull {X Y : Type} (p : Y → X) {f : X → Bool} {k t : ℕ}
    {S : Set (X → Bool)} (h : Build f k t S) : Build (pull p f) k t (pull p '' S) := by
  induction k generalizing S t with
  | zero => exact Set.mem_image_of_mem _ h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨ht, a, ha, h⟩
    · exact Or.inl (Set.mem_image_of_mem _ h)
    · have hh := ih h
      rw [pull_insert] at hh
      exact Or.inr (Or.inl ⟨pull p a, Set.mem_image_of_mem _ ha,
        pull p b, Set.mem_image_of_mem _ hb, o, hh⟩)
    · have hh := ih h
      rw [pull_insert] at hh
      exact Or.inr (Or.inr ⟨ht, pull p a, Set.mem_image_of_mem _ ha, hh⟩)

lemma build_agree {X : Type} {x y : X} {f : X → Bool} {k t : ℕ} {S : Set (X → Bool)}
    (h : Build f k t S) (he : ∀ a ∈ S, a x = a y) : f x = f y := by
  induction k generalizing t S with
  | zero => exact he f h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨_, a, ha, h⟩
    · exact he f h
    · apply ih h
      intro c hc
      rcases Set.mem_insert_iff.mp hc with rfl | hc
      · simp only [combine, he a ha, he b hb]
      · exact he c hc
    · apply ih h
      intro c hc
      rcases Set.mem_insert_iff.mp hc with rfl | hc
      · simp only [invert, he a ha]
      · exact he c hc

lemma combine_ff_left {X : Type} (o : Bool) (a : X → Bool) :
    combine o ff a = if o then a else ff := by
  cases o <;> funext x <;> simp [combine, ff]

lemma combine_ff_right {X : Type} (o : Bool) (a : X → Bool) :
    combine o a ff = if o then a else ff := by
  cases o <;> funext x <;> simp [combine, ff]

lemma cut_build {X : Type} (p : X → X) (w f : X → Bool) (k t : ℕ)
    (S : Set (X → Bool)) (hw : pull p w = ff) (hf : pull p f ≠ ff)
    (h0 : ff ∈ S) (h1 : tt ∈ S) (h : Build f k t (insert w S)) :
    Build f k t S ∨ Build (pull p f) (k - 1) t (pull p '' S) := by
  have remove (T : Set (X → Bool)) (hm : f ∈ insert w T) : f ∈ T :=
    (Set.mem_insert_iff.mp hm).resolve_left (fun e => hf (e ▸ hw))
  have image0 (T : Set (X → Bool)) (hT : ff ∈ T) : ff ∈ pull p '' T :=
    Set.mem_image_of_mem (pull p) hT
  have image_insert_w (T : Set (X → Bool)) (hT : ff ∈ T) :
      pull p '' insert w T = pull p '' T := by
    rw [pull_insert, hw, Set.insert_eq_of_mem (image0 T hT)]
  induction k generalizing S t with
  | zero => exact Or.inl (remove S h)
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨ht, a, ha, h⟩
    · exact Or.inl (Or.inl (remove S h))
    · let c := combine o a b
      have hc : insert c (insert w S) = insert w (insert c S) := Set.insert_comm _ _ _
      change Build f k t (insert c (insert w S)) at h
      by_cases hab : a = w ∨ b = w
      · right
        have hh := build_pull p h
        rw [pull_insert, image_insert_w S h0] at hh
        change Build (pull p f) k t (insert (combine o (pull p a) (pull p b)) (pull p '' S)) at hh
        have hm (d : X → Bool) (hd : d ∈ insert w S) : pull p d ∈ pull p '' S := by
          rw [← image_insert_w S h0]
          exact Set.mem_image_of_mem _ hd
        have hins : combine o (pull p a) (pull p b) ∈ pull p '' S := by
          rcases hab with ha' | hb'
          · rw [ha', hw, combine_ff_left]
            cases o
            · exact image0 S h0
            · exact hm b hb
          · rw [hb', hw, combine_ff_right]
            cases o
            · exact image0 S h0
            · exact hm a ha
        simpa only [Set.insert_eq_of_mem hins, Nat.add_sub_cancel] using hh
      · have haS := (Set.mem_insert_iff.mp ha).resolve_left (fun e => hab (Or.inl e))
        have hbS := (Set.mem_insert_iff.mp hb).resolve_left (fun e => hab (Or.inr e))
        rw [hc] at h
        have h0' : ff ∈ insert c S := Set.mem_insert_of_mem _ h0
        have h1' : tt ∈ insert c S := Set.mem_insert_of_mem _ h1
        cases k with
        | zero => exact Or.inl (Or.inr (Or.inl ⟨a, haS, b, hbS, o, remove _ h⟩))
        | succ k =>
          rcases ih t (insert c S) h0' h1' h with h' | h'
          · exact Or.inl (Or.inr (Or.inl ⟨a, haS, b, hbS, o, h'⟩))
          · rw [pull_insert] at h'
            exact Or.inr (Or.inr (Or.inl ⟨pull p a, Set.mem_image_of_mem _ haS,
              pull p b, Set.mem_image_of_mem _ hbS, o, h'⟩))
    · let c := invert a
      have hc : insert c (insert w S) = insert w (insert c S) := Set.insert_comm _ _ _
      change Build f k (t - 1) (insert c (insert w S)) at h
      by_cases ha' : a = w
      · right
        have hh := build_pull p h
        rw [pull_insert, image_insert_w S h0] at hh
        have hca : pull p c = tt := by
          change invert (pull p a) = tt
          rw [ha', hw]
          rfl
        have ho : tt ∈ pull p '' S := Set.mem_image_of_mem (pull p) h1
        rw [hca, Set.insert_eq_of_mem ho] at hh
        exact build_weaken hh (fun _ h => h) (by omega)
      · have haS := (Set.mem_insert_iff.mp ha).resolve_left ha'
        rw [hc] at h
        cases k with
        | zero => exact Or.inl (Or.inr (Or.inr ⟨ht, a, haS, remove _ h⟩))
        | succ k =>
          rcases ih (t - 1) (insert c S) (Set.mem_insert_of_mem _ h0)
              (Set.mem_insert_of_mem _ h1) h with h' | h'
          · exact Or.inl (Or.inr (Or.inr ⟨ht, a, haS, h'⟩))
          · rw [pull_insert] at h'
            exact Or.inr (Or.inr (Or.inr ⟨ht, pull p a, Set.mem_image_of_mem _ haS, h'⟩))

lemma cut_forced {X : Type} (p : X → X) (w f : X → Bool) (k t : ℕ)
    (S : Set (X → Bool)) (hw : pull p w = ff) (hf : pull p f ≠ ff)
    (h0 : ff ∈ S) (h1 : tt ∈ S) (x y : X) (hne : f x ≠ f y)
    (he : ∀ a ∈ S, a x = a y) (h : Build f k t (insert w S)) :
    Build (pull p f) (k - 1) t (pull p '' S) :=
  (cut_build p w f k t S hw hf h0 h1 h).resolve_left (fun h' => hne (build_agree h' he))



def readF {X : Type} (W : List (X → Bool)) (i : ℕ) : X → Bool := W.getD i ff

def gateF {X : Type} (W : List (X → Bool)) (g : Gate) : X → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => readF W i x)

def runF {X : Type} : List Gate → List (X → Bool) → List (X → Bool)
  | [], W => W
  | g :: gs, W => runF gs (W ++ [gateF W g])

lemma readF_point {X : Type} (W : List (X → Bool)) (i : ℕ) (x : X) :
    readF W i x = (W.map (fun a => a x)).getD i false := by
  simp only [readF, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

lemma runF_point {X : Type} (gs : List Gate) (W : List (X → Bool)) (x : X) :
    (runF gs W).map (fun a => a x) = evalWires gs (W.map fun a => a x) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    rw [runF, ih, evalWires_cons]
    simp only [List.map_append, List.map_singleton, gateF, readF_point]

lemma readF_mem {X : Type} {W : List (X → Bool)} {S : Set (X → Bool)}
    (hW : ∀ a ∈ W, a ∈ S) (h0 : ff ∈ S) (i : ℕ) : readF W i ∈ S := by
  by_cases hi : i < W.length
  · exact hW _ (by simpa [readF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        using List.getElem_mem (l := W) (i := i) hi)
  · simpa [readF, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : W.length ≤ i)] using h0

lemma gateF_shape {X : Type} {W : List (X → Bool)} {S : Set (X → Bool)} (g : Gate)
    (hW : ∀ a ∈ W, a ∈ S) (h0 : ff ∈ S) (h1 : tt ∈ S)
    (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    gateF W g ∈ S ∨
    (∃ a ∈ S, ∃ b ∈ S, ∃ o : Bool, gateF W g = combine o a b) ∨
    (isNot g = true ∧ ∃ a ∈ S, gateF W g = invert a) := by
  obtain ⟨op, ins⟩ := g
  have hr (i : ℕ) := readF_mem hW h0 i
  rcases hg with ⟨hop, hlen⟩
  change ins.length ≤ 2 at hlen
  rcases hop with hop | hop | hop
  all_goals change op = _ at hop; subst op
  · cases ins with
    | nil => exact Or.inl h1
    | cons a ins =>
      cases ins with
      | nil =>
        have he : gateF W ⟨.and, [a]⟩ = readF W a := by
          funext x
          simp [gateF, GateOp.eval]
        exact Or.inl (he ▸ hr a)
      | cons b ins =>
        have hn : ins = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst ins
        refine Or.inr (Or.inl ⟨_, hr a, _, hr b, false, ?_⟩)
        funext x
        simp [gateF, GateOp.eval, combine]
  · cases ins with
    | nil => exact Or.inl h0
    | cons a ins =>
      cases ins with
      | nil =>
        have he : gateF W ⟨.or, [a]⟩ = readF W a := by
          funext x
          simp [gateF, GateOp.eval]
        exact Or.inl (he ▸ hr a)
      | cons b ins =>
        have hn : ins = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
        subst ins
        refine Or.inr (Or.inl ⟨_, hr a, _, hr b, true, ?_⟩)
        funext x
        simp [gateF, GateOp.eval, combine]
  · cases ins with
    | nil => exact Or.inl h1
    | cons a ins => exact Or.inr (Or.inr ⟨rfl, _, hr a, rfl⟩)

lemma run_to_build {X : Type} (gs : List Gate) {f : X → Bool} {W : List (X → Bool)}
    {S : Set (X → Bool)} (hW : ∀ a ∈ W, a ∈ S) (h0 : ff ∈ S) (h1 : tt ∈ S)
    (hfan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hf : f ∈ runF gs W) {t : ℕ} (ht : gs.countP isNot ≤ t) : Build f gs.length t S := by
  induction gs generalizing W S t with
  | nil => exact hW _ hf
  | cons g gs ih =>
    have hrest := fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    have hstep : ∀ a ∈ W ++ [gateF W g], a ∈ insert (gateF W g) S := by
      intro a ha
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Set.mem_insert_of_mem _ (hW _ ha)
      · exact Set.mem_insert _ _
    have h0' := Set.mem_insert_of_mem (gateF W g) h0
    have h1' := Set.mem_insert_of_mem (gateF W g) h1
    have hle : gs.countP isNot ≤ t := by
      simp only [List.countP_cons] at ht
      split at ht <;> omega
    rw [runF] at hf
    rcases gateF_shape g hW h0 h1 (hfan g (by simp)) with hm | ⟨a, ha, b, hb, o, he⟩ |
        ⟨hnot, a, ha, he⟩
    · have hh := ih hstep h0' h1' hrest hf hle
      rw [Set.insert_eq_of_mem hm] at hh
      exact build_step hh
    · have hh := ih hstep h0' h1' hrest hf hle
      rw [he] at hh
      exact Or.inr (Or.inl ⟨a, ha, b, hb, o, hh⟩)
    · simp only [List.countP_cons, hnot, ↓reduceIte] at ht
      have hh := ih hstep h0' h1' hrest hf (show gs.countP isNot ≤ t - 1 by omega)
      rw [he] at hh
      exact Or.inr (Or.inr ⟨by omega, a, ha, hh⟩)

def var {n : ℕ} (i : Fin n) : (Fin n → Bool) → Bool := fun x => x i

lemma circuit_to_build {n : ℕ} (gs : List Gate) (o : ℕ) (f : (Fin n → Bool) → Bool)
    (hfan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hnot : gs.countP isNot ≤ 1) (he : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x)
    (hn : f ≠ ff) :
    Build f gs.length 1 (insert ff (insert tt (Set.range var))) := by
  let W := List.ofFn (var : Fin n → (Fin n → Bool) → Bool)
  have hm (a : (Fin n → Bool) → Bool) (ha : a ∈ W) :
      a ∈ insert ff (insert tt (Set.range var)) := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_range_self i))
  have hp (x : Fin n → Bool) : W.map (fun a => a x) = List.ofFn x := by
    rw [show W = List.ofFn var from rfl, List.map_ofFn]
    rfl
  have hval : readF (runF gs W) o = f := by
    funext x
    rw [readF_point, runF_point, hp]
    exact he x
  have hmem : f ∈ runF gs W := by
    by_cases ho : o < (runF gs W).length
    · rw [← hval]
      simpa [readF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho] using
        List.getElem_mem (l := runF gs W) (i := o) ho
    · have he' : readF (runF gs W) o = ff := by
        simp [readF, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (runF gs W).length ≤ o)]
      exact False.elim (hn (hval.symm.trans he'))
  exact run_to_build gs hm (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    hfan hmem hnot


def inputSet (V : Finset (Fin 8)) : Set ((Fin 8 → Bool) → Bool) :=
  insert ff (insert tt (var '' (↑V : Set (Fin 8))))

lemma inputSet_insert (v : Fin 8) (V : Finset (Fin 8)) :
    inputSet (insert v V) = insert (var v) (inputSet V) := by
  simp only [inputSet, Finset.coe_insert, Set.image_insert_eq]
  rw [Set.insert_comm tt (var v), Set.insert_comm ff (var v)]

lemma inputSet_univ : inputSet Finset.univ = insert ff (insert tt (Set.range var)) := by
  simp [inputSet]

def fix (v : Fin 8) (x : Fin 8 → Bool) (i : Fin 8) : Bool :=
  if i = v then false else x i

lemma inputSet_fix (v : Fin 8) (V : Finset (Fin 8)) (hv : v ∉ V) :
    pull (fix v) '' inputSet V = inputSet V := by
  have hi (i : Fin 8) (hm : i ∈ V) : pull (fix v) (var i) = var i := by
    have hn : i ≠ v := fun e => hv (e ▸ hm)
    funext x
    simp [pull, var, fix, hn]
  simp only [inputSet, pull_insert]
  change insert ff (insert tt (pull (fix v) '' (var '' (↑V : Set (Fin 8))))) = _
  congr 2
  rw [Set.image_image]
  exact Set.image_congr fun i h => hi i h

lemma cut_vertex (v : Fin 8) (V : Finset (Fin 8)) (hv : v ∉ V)
    (f : (Fin 8 → Bool) → Bool) {k t : ℕ} {x y z : Fin 8 → Bool}
    (hne : f x ≠ f y) (he : ∀ i ∈ V, x i = y i) (hz : f (fix v z) = true)
    (h : Build f k t (inputSet (insert v V))) :
    Build (pull (fix v) f) (k - 1) t (inputSet V) := by
  rw [inputSet_insert] at h
  have hw : pull (fix v) (var v) = ff := by
    funext a
    simp [pull, fix, var, ff]
  have hf : pull (fix v) f ≠ ff := by
    intro e
    have e' := congrFun e z
    change f (fix v z) = false at e'
    simp [hz] at e'
  have h0 : ff ∈ inputSet V := Set.mem_insert _ _
  have h1 : tt ∈ inputSet V := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have he' : ∀ a ∈ inputSet V, a x = a y := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rfl
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rfl
    obtain ⟨i, hi, rfl⟩ := ha
    exact he i hi
  have hc := cut_forced (fix v) (var v) f k t (inputSet V) hw hf h0 h1 x y hne he' h
  rwa [inputSet_fix v V hv] at hc

def cutInputs : Finset (Fin 8) := {0, 2, 5, 6, 7}
def mask8 (m : ℕ) (i : Fin 8) : Bool := m.testBit i.val

def after1 := pull (fix 1) target8
def after3 := pull (fix 3) after1
def after4 := pull (fix 4) after3

lemma three_cuts (k : ℕ) (h : Build target8 k 1 (inputSet Finset.univ)) :
    Build after4 (k - 1 - 1 - 1) 1 (inputSet cutInputs) := by
  have eqV : (Finset.univ : Finset (Fin 8)) = insert 1 (insert 3 (insert 4 cutInputs)) := by decide
  rw [eqV] at h
  have h1 : Build after1 (k - 1) 1 (inputSet (insert 3 (insert 4 cutInputs))) :=
    cut_vertex 1 _ (by decide) target8
      (x := mask8 34) (y := mask8 32) (z := mask8 33)
      (by decide) (by decide) (by decide) h
  have h3 : Build after3 (k - 1 - 1) 1 (inputSet (insert 4 cutInputs)) :=
    cut_vertex 3 _ (by decide) after1
      (x := mask8 136) (y := mask8 128) (z := mask8 33)
      (by decide) (by decide) (by decide) h1
  exact cut_vertex 4 _ (by decide) after3
    (x := mask8 144) (y := mask8 128) (z := mask8 33)
    (by decide) (by decide) (by decide) h3


def profile {X : Type} (pa pb : Fin 60 → X) (a : X → Bool) : Sig :=
  (mkBV (fun r => a (pa r)), mkBV (fun r => a (pb r)))

lemma profile_bin {X : Type} (pa pb : Fin 60 → X) (o : Bool) (a b : X → Bool) :
    profile pa pb (combine o a b) = bin o (profile pa pb a) (profile pa pb b) := by
  cases o <;> apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
    simp [profile, combine, bin, getElem_mkBV, BitVec.getElem_and, BitVec.getElem_or]

lemma profile_invert {X : Type} (pa pb : Fin 60 → X) (a : X → Bool) :
    profile pa pb (invert a) = neg (profile pa pb a) := by
  apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
    simp [profile, invert, neg, getElem_mkBV, BitVec.getElem_not]

lemma build_to_run {X : Type} (pa pb : Fin 60 → X) {f : X → Bool}
    {k t : ℕ} {S : Set (X → Bool)} {W : List Sig}
    (h : Build f k t S) (hW : ∀ a ∈ S, profile pa pb a ∈ W) :
    ∃ gs : List Gate, gs.length ≤ k ∧ gs.countP isNot ≤ t ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      profile pa pb f ∈ evalGates gs W := by
  induction k generalizing t S W with
  | zero => exact ⟨[], by simp, by simp, by simp, hW f h⟩
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, o, h⟩ | ⟨ht, a, ha, h⟩
    · exact ⟨[], by simp, by simp, by simp, hW f h⟩
    · let g : Gate := ⟨if o then .or else .and, [W.idxOf (profile pa pb a), W.idxOf (profile pa pb b)]⟩
      have hg : evalGateSig g W = profile pa pb (combine o a b) := by
        rw [profile_bin]
        cases o <;> simp [g, evalGateSig, List.getElem?_idxOf (hW a ha), List.getElem?_idxOf (hW b hb)]
      have h' : ∀ c ∈ insert (combine o a b) S, profile pa pb c ∈ W ++ [evalGateSig g W] := by
        intro c hc
        rcases Set.mem_insert_iff.mp hc with rfl | hc
        · simp [hg]
        · exact List.mem_append_left _ (hW c hc)
      obtain ⟨gs, hlen, hcount, hfan, he⟩ := ih h h'
      refine ⟨g :: gs, by simp; omega, ?_, ?_, he⟩
      · cases o <;> simpa [g, isNot] using hcount
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · cases o <;> simp [g]
        · exact hfan q hq
    · let g : Gate := ⟨.not, [W.idxOf (profile pa pb a)]⟩
      have hg : evalGateSig g W = profile pa pb (invert a) := by
        rw [profile_invert]
        simp [g, evalGateSig, List.getElem?_idxOf (hW a ha)]
      have h' : ∀ c ∈ insert (invert a) S, profile pa pb c ∈ W ++ [evalGateSig g W] := by
        intro c hc
        rcases Set.mem_insert_iff.mp hc with rfl | hc
        · simp [hg]
        · exact List.mem_append_left _ (hW c hc)
      obtain ⟨gs, hlen, hcount, hfan, he⟩ := ih h h'
      refine ⟨g :: gs, by simp; omega, ?_, ?_, he⟩
      · simp only [List.countP_cons, g, isNot, ↓reduceIte]
        omega
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [g]
        · exact hfan q hq

def projectedWires : List Sig := zero :: one :: initList 0

lemma search_excludes (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hcount : gs.countP isNot ≤ 1) (hs : goalSig ∈ evalGates gs projectedWires) :
    7 ≤ gs.length := by
  by_contra hn
  obtain ⟨k, hk, t, ht, htnot, _, V, hVnd, hVsub', hVlen, hVsep, hVsearch⟩ :=
    extract_live gs hfan projectedWires hs
  have hVsub : ∀ s ∈ V, s ∈ initList 0 := by
    intro s hs
    obtain ⟨hm, h0, h1⟩ := hVsub' s hs
    change s ∈ zero :: one :: initList 0 at hm
    simpa only [List.mem_cons, h0, h1, false_or] using hm
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ initList 0, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed 0 s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 (hVsub u huV), hui⟩
  have hp : V.Perm (initList 0) :=
    perm_of_nodup_same_mem hVnd (initList_nodup 0) (fun x => ⟨hVsub x, hall_in_V x⟩)
  rw [hp.length_eq, initList_len] at hVlen
  rw [search_perm k t hp, projected_check k t (by unfold budget; omega) hVlen
    (htnot.trans hcount)] at hVsearch
  cases hVsearch


def embed (x : Fin 5 → Bool) (i : Fin 8) : Bool :=
  match i.val with
  | 0 => x 0
  | 2 => x 1
  | 5 => x 2
  | 6 => x 3
  | 7 => x 4
  | _ => false

def projDecidable : Decidable (∀ x : Fin 5 → Bool, after4 (embed x) = target x) :=
  Fintype.decidableForallFintype

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma after4_embed : ∀ x : Fin 5 → Bool, after4 (embed x) = target x :=
  @of_decide_eq_true _ projDecidable rfl

def pa8 (r : Fin 60) : Fin 8 → Bool := embed (pairA 0 r)
def pb8 (r : Fin 60) : Fin 8 → Bool := embed (pairB 0 r)

lemma terminal_profile : profile pa8 pb8 after4 = goalSig := by
  apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
  · simp only [profile, goalSig, top, getElem_mkBV, BitVec.getElem_allOnes, pa8,
      after4_embed, pairA_true]
  · simp only [profile, goalSig, getElem_mkBV, zero_bit, pb8, after4_embed, pairB_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma terminal_vars : ∀ i ∈ cutInputs, profile pa8 pb8 (var i) ∈ projectedWires := by
  decide +kernel

lemma terminal_sources (a : (Fin 8 → Bool) → Bool) (ha : a ∈ inputSet cutInputs) :
    profile pa8 pb8 a ∈ projectedWires := by
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · have h : profile pa8 pb8 (ff : (Fin 8 → Bool) → Bool) = zero := by
      apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
        simp [profile, ff, zero, getElem_mkBV]
    rw [h]
    exact List.mem_cons_self
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · have h : profile pa8 pb8 (tt : (Fin 8 → Bool) → Bool) = one := by
      apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
      all_goals
        change (mkBV (fun _ => true))[i] = top[i]
        rw [getElem_mkBV]
        exact (top_bit i hi).symm
    rw [h]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨i, hi, rfl⟩ := ha
  exact terminal_vars i hi

lemma circuit_lower (gs : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target8 x) :
    10 ≤ gs.length := by
  have hnz : target8 ≠ ff := by
    intro e
    have h := congrFun e (mask8 33)
    exact (by decide : target8 (mask8 33) ≠ ff (mask8 33)) h
  have hbuild := circuit_to_build gs o target8 hfan (not_count _ hn) he hnz
  rw [← inputSet_univ] at hbuild
  obtain ⟨qs, hlen, hcount, hshape, hgoal⟩ :=
    build_to_run pa8 pb8 (three_cuts gs.length hbuild) terminal_sources
  rw [terminal_profile] at hgoal
  have hl := search_excludes qs hshape hcount hgoal
  omega


end PEqualNP.Outside.L_meta_14580_aux

theorem PEqualNP.Outside.L_meta_14580 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan hnot heval
  exact PEqualNP.Outside.L_meta_14580_aux.replaceLarge gates
    (PEqualNP.Outside.L_meta_14580_aux.circuit_lower gates o hfan hnot heval)
