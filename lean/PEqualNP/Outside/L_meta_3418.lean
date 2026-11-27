import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3418

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each wire is recorded as a word of 24 bits, bit i being its value on row i.
abbrev Word := BitVec 24

def inputs : List Word :=
  [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968]

def base : List Word := inputs ++ [5689661]

-- Fresh words for padding: each is an AND or OR of two words of the base.
def cand : List Word :=
  [1, 14053491, 1064960, 7684279, 262144, 16, 16605241, 32, 5634609, 278528, 6145137,
    4456448, 14566065, 5242880]

def F (x7 : Fin 9 → Bool) : Bool :=
  [(1 : ℕ), 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77].any fun x8 : ℕ =>
    x7 (Fin.ofNat (9 : ℕ) (x8 / (9 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (9 : ℕ)))

def bit (i : Fin 24) (v : Word) : Bool := v.getLsbD i.val

def xs (i : Fin 24) : Fin 9 → Bool := fun k => bit i (inputs.getD k.val 0)

lemma row_data : ∀ i : Fin 24, List.ofFn (xs i) = inputs.map (bit i) ∧
    F (xs i) = bit i 4095 := by decide +kernel

def gateWord (w : List Word) (g : Gate) : Word :=
  let args := g.inputs.map fun j => w.getD j 0
  match g.op with
  | .and => args.getD 0 (BitVec.allOnes 24) &&& args.getD 1 (BitVec.allOnes 24)
  | _ => args.getD 0 0 ||| args.getD 1 0

def wordStep (w : List Word) (g : Gate) := w ++ [gateWord w g]

def boolStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma zero_bit (i : Fin 24) : (0 : Word).getLsbD i.val = false :=
  BitVec.getLsbD_zero

lemma read_bit (w : List Word) (i : Fin 24) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
  simpa only [bit, zero_bit] using (List.getD_map w 0 (n := j) (bit i))

lemma step_bits (w : List Word) (i : Fin 24) (g : Gate)
    (hg : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    (wordStep w g).map (bit i) = boolStep (w.map (bit i)) g := by
  obtain ⟨op, args⟩ := g
  change op = .and ∨ op = .or at hg
  change args.length ≤ 2 at hlen
  have shapes : args = [] ∨ (∃ a, args = [a]) ∨ ∃ a b, args = [a, b] := by
    cases args with
    | nil => exact Or.inl rfl
    | cons a tail =>
      cases tail with
      | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
      | cons b tail =>
        cases tail with
        | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        | cons _ _ => simp at hlen
  rcases hg with rfl | rfl <;>
    rcases shapes with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
    simp only [wordStep, boolStep, gateWord, GateOp.eval, List.map_append, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, read_bit,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, bit,
      BitVec.getLsbD_and, BitVec.getLsbD_or, zero_bit, BitVec.getLsbD_allOnes,
      i.isLt, decide_true, Bool.and_true, Bool.or_false]

lemma run_bits (gs : List Gate) (w : List Word) (i : Fin 24)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hm g List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun k hk => hm k (List.mem_cons_of_mem g hk)),
      step_bits w i g hop hlen]

def Binary (pool : List Word) (v : Word) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

lemma binary_mono {P Q : List Word} (h : P ⊆ Q) {v : Word} (hv : Binary P v) :
    Binary Q v := by
  obtain ⟨a, ha, b, hb, e⟩ := hv
  exact ⟨a, h ha, b, h hb, e⟩

-- A good list: every entry is new (not zero, not in the base, not earlier) and is the
-- all-ones word or an AND or OR of two words before it.
def Good (l : List Word) : Prop :=
  ∀ j (hj : j < l.length), l[j] ∉ 0 :: (base ++ l.take j) ∧
    (l[j] = BitVec.allOnes 24 ∨ Binary (base ++ l.take j) l[j])

lemma good_nil : Good [] := by
  intro j hj
  simp at hj

lemma good_append {l : List Word} {v : Word} (h : Good l) (hfresh : v ∉ 0 :: (base ++ l))
    (hv : v = BitVec.allOnes 24 ∨ Binary (base ++ l) v) : Good (l ++ [v]) := by
  intro j hj
  by_cases hj' : j < l.length
  · simpa only [List.getElem_append_left hj',
      List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
  · have heq : j = l.length := by simp at hj; omega
    subst j
    simpa using And.intro hfresh hv

lemma good_take {l : List Word} (h : Good l) (k : Nat) : Good (l.take k) := by
  intro j hj
  have hjl : j < l.length := by simp at hj; omega
  have hjk : j < k := by simp at hj; omega
  have e1 : (l.take k)[j] = l[j] := by simp
  have e2 : (l.take k).take j = l.take j := by
    rw [List.take_take, Nat.min_eq_left hjk.le]
  rw [e1, e2]
  exact h j hjl

lemma good_nodup {l : List Word} (h : Good l) (hb : (0 :: base).Nodup) :
    ∀ n, n ≤ l.length → (0 :: (base ++ l.take n)).Nodup := by
  intro n
  induction n with
  | zero => intro _; simpa using hb
  | succ n ih =>
    intro hn
    have hlt : n < l.length := by omega
    have e : 0 :: (base ++ l.take (n + 1)) = (0 :: (base ++ l.take n)).concat l[n] := by
      rw [List.take_succ_eq_append_getElem hlt]
      simp
    rw [e]
    exact List.Nodup.concat (h n hlt).1 (ih (by omega))

lemma getD_cases {xs Q : List Word} (h : ∀ x ∈ xs, x ∈ Q) (d : Word) (i : Nat) :
    xs.getD i d = d ∨ xs.getD i d ∈ Q := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : xs[i]? with
  | none => left; rfl
  | some v => right; exact h v (List.mem_of_getElem? hv)

lemma gate_new {w P : List Word} (g : Gate) (hw : ∀ x ∈ w, x ∈ 0 :: P)
    (hnew : gateWord w g ∉ 0 :: P) :
    gateWord w g = BitVec.allOnes 24 ∨ Binary P (gateWord w g) := by
  have hargs : ∀ x ∈ g.inputs.map (fun j => w.getD j 0), x ∈ 0 :: P := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    rcases getD_cases hw 0 j with e | e
    · rw [e]
      exact List.mem_cons_self
    · exact e
  revert hnew
  unfold gateWord
  split
  · intro hnew
    dsimp only at hnew ⊢
    rcases getD_cases hargs (BitVec.allOnes 24) 0 with h0 | h0 <;>
      rcases getD_cases hargs (BitVec.allOnes 24) 1 with h1 | h1
    · left
      rw [h0, h1]
      simp
    · exfalso
      apply hnew
      rw [h0, BitVec.allOnes_and]
      exact h1
    · exfalso
      apply hnew
      rw [h1, BitVec.and_allOnes]
      exact h0
    · right
      rcases List.mem_cons.mp h0 with z0 | p0
      · exfalso
        apply hnew
        rw [z0]
        simp
      rcases List.mem_cons.mp h1 with z1 | p1
      · exfalso
        apply hnew
        rw [z1]
        simp
      exact ⟨_, p0, _, p1, Or.inl rfl⟩
  · intro hnew
    dsimp only at hnew ⊢
    have m0 : (g.inputs.map fun j => w.getD j 0).getD 0 0 ∈ 0 :: P := by
      rcases getD_cases hargs 0 0 with e | e
      · rw [e]
        exact List.mem_cons_self
      · exact e
    have m1 : (g.inputs.map fun j => w.getD j 0).getD 1 0 ∈ 0 :: P := by
      rcases getD_cases hargs 0 1 with e | e
      · rw [e]
        exact List.mem_cons_self
      · exact e
    right
    rcases List.mem_cons.mp m0 with z0 | p0
    · exfalso
      apply hnew
      rw [z0]
      simpa using m1
    rcases List.mem_cons.mp m1 with z1 | p1
    · exfalso
      apply hnew
      rw [z1]
      simpa using m0
    exact ⟨_, p0, _, p1, Or.inr rfl⟩

lemma record_step {trace w : List Word} (g : Gate) (h : Good trace)
    (hw : ∀ x ∈ w, x ∈ 0 :: (base ++ trace)) :
    ∃ next : List Word, next.length ≤ trace.length + 1 ∧ Good next ∧
      ∀ x ∈ wordStep w g, x ∈ 0 :: (base ++ next) := by
  by_cases hmem : gateWord w g ∈ 0 :: (base ++ trace)
  · refine ⟨trace, by omega, h, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw x hx
    · rw [List.mem_singleton.mp hx]
      exact hmem
  · refine ⟨trace ++ [gateWord w g], by simp, good_append h hmem (gate_new g hw hmem), ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' := hw x hx
      simp only [List.mem_cons, List.mem_append] at hx' ⊢
      tauto
    · rw [List.mem_singleton.mp hx]
      simp

lemma record_run (gs : List Gate) (trace w : List Word) (h : Good trace)
    (hw : ∀ x ∈ w, x ∈ 0 :: (base ++ trace)) :
    ∃ final : List Word, final.length ≤ trace.length + gs.length ∧ Good final ∧
      ∀ x ∈ gs.foldl wordStep w, x ∈ 0 :: (base ++ final) := by
  induction gs generalizing trace w with
  | nil => exact ⟨trace, by simp, h, hw⟩
  | cons g gs ih =>
    obtain ⟨next, hlen, hnext, hwires⟩ := record_step g h hw
    obtain ⟨final, hsize, hfinal, hout⟩ := ih next (wordStep w g) hnext hwires
    exact ⟨final, by simp; omega, hfinal, hout⟩

-- The same words as natural numbers: the kernel checks these facts fast.
def baseN : List Nat :=
  [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661]

def candN : List Nat :=
  [1, 14053491, 1064960, 7684279, 262144, 16, 16605241, 32, 5634609, 278528, 6145137,
    4456448, 14566065, 5242880]

lemma nat_facts : (0 :: baseN).Nodup ∧ 4095 ∉ 0 :: baseN ∧ candN.Nodup ∧
    ∀ c ∈ candN, c ∉ 0 :: baseN ∧ c ≠ 4095 ∧
      ∃ a ∈ baseN, ∃ b ∈ baseN, c = a &&& b ∨ c = a ||| b := by decide +kernel

lemma base_map : base.map BitVec.toNat = baseN := by decide +kernel

lemma cand_map : cand.map BitVec.toNat = candN := by decide +kernel

lemma base0_map : (0 :: base).map BitVec.toNat = 0 :: baseN := by
  rw [List.map_cons, base_map]
  rfl

lemma cand_facts : ∀ c ∈ cand, c ∉ 0 :: base ∧ c ≠ 4095 ∧ Binary base c := by
  intro c hc
  have hcn : c.toNat ∈ candN := by
    rw [← cand_map]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  obtain ⟨h0, h4, a', ha', b', hb', e⟩ := nat_facts.2.2.2 _ hcn
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    apply h0
    rw [← base0_map]
    exact List.mem_map.mpr ⟨c, hm, rfl⟩
  · intro e4
    apply h4
    rw [e4]
    rfl
  · rw [← base_map] at ha' hb'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    refine ⟨a, ha, b, hb, ?_⟩
    rcases e with e | e
    · left
      apply BitVec.eq_of_toNat_eq
      rw [e, BitVec.toNat_and]
    · right
      apply BitVec.eq_of_toNat_eq
      rw [e, BitVec.toNat_or]

lemma cand_nodup : cand.Nodup :=
  List.Nodup.of_map BitVec.toNat (by rw [cand_map]; exact nat_facts.2.2.1)

lemma cand_length : cand.length = 14 := rfl

lemma exists_fresh (l : List Word) (hl : l.length < cand.length) : ∃ c ∈ cand, c ∉ l := by
  by_contra hne
  have hsub : cand ⊆ l := fun c hc => by
    by_contra hcl
    exact hne ⟨c, hc, hcl⟩
  have := (cand_nodup.subperm hsub).length_le
  omega

lemma extend : ∀ n (l : List Word), Good l → (4095 : Word) ∉ l → l.length + n = 13 →
    ∃ l' : List Word, Good l' ∧ (4095 : Word) ∉ l' ∧ l'.length = 13 ∧ l ⊆ l' := by
  intro n
  induction n with
  | zero =>
    intro l h h4 hl
    exact ⟨l, h, h4, by omega, List.Subset.refl _⟩
  | succ n ih =>
    intro l h h4 hl
    obtain ⟨c, hc, hcl⟩ := exists_fresh l (by rw [cand_length]; omega)
    obtain ⟨hc0, hc4, hcb⟩ := cand_facts c hc
    have hfresh : c ∉ 0 :: (base ++ l) := by
      simp only [List.mem_cons, List.mem_append, not_or] at hc0 ⊢
      exact ⟨hc0.1, hc0.2, hcl⟩
    have hg := good_append h hfresh
      (Or.inr (binary_mono (List.subset_append_left _ _) hcb))
    have h4' : (4095 : Word) ∉ l ++ [c] := by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h4, fun e => hc4 e.symm⟩
    obtain ⟨l', h1, h2, h3, h5⟩ := ih (l ++ [c]) hg h4' (by simp; omega)
    exact ⟨l', h1, h2, h3, fun x hx => h5 (List.mem_append_left _ hx)⟩

lemma base_facts : (0 :: base).Nodup ∧ (4095 : Word) ∉ 0 :: base ∧
    (4095 : Word) ≠ BitVec.allOnes 24 ∧ (16777215 : Word) = BitVec.allOnes 24 ∧
    base.length = 10 := by
  refine ⟨List.Nodup.of_map BitVec.toNat (by rw [base0_map]; exact nat_facts.1), ?_,
    by decide +kernel, by decide +kernel, rfl⟩
  intro h
  apply nat_facts.2.1
  rw [← base0_map]
  exact List.mem_map.mpr ⟨_, h, rfl⟩

lemma start_word : wordStep inputs { op := GateOp.or, inputs := [0, 3] } = base := by
  have h : gateWord inputs { op := GateOp.or, inputs := [0, 3] } = 5689661 := by
    decide +kernel
  rw [wordStep, h]
  rfl

end PEqualNP.Outside.L_meta_3418

open PEqualNP.Outside.L_meta_3418 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3418 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (15 : ℕ) →     x1.output = (23 : ℕ) →       x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →         PEqualNP.MetaComplexity.Monotone2 x1 →           (∀ (x6 : ℕ) (x7 : x6 < x1.gates.length), ∀ x8 ∈ x1.gates[x6].inputs, x8 < (9 : ℕ) + x6 ∨ x8 = (24 : ℕ)) →             (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (9 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (9 : ℕ)))) →               ∃ (x8 : List (BitVec (24 : ℕ))),                 x8.length = (24 : ℕ) ∧                   List.take (10 : ℕ) x8 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧                     x8.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧                       ((0 : BitVec (24 : ℕ)) :: x8).Nodup ∧                         ∀ (x9 : ℕ),                           (0 : ℕ) < x9 →                             x9 < (15 : ℕ) →                               have x12 : BitVec (24 : ℕ) := x8.getD ((9 : ℕ) + x9) (0 : BitVec (24 : ℕ));                               x12 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x13 : BitVec (24 : ℕ)) (x14 : BitVec (24 : ℕ)), x13 ∈ List.take ((9 : ℕ) + x9) x8 ∧ x14 ∈ List.take ((9 : ℕ) + x9) x8 ∧ (x12 = x13 &&& x14 ∨ x12 = x13 ||| x14) := by
  intro C hlen _ hg0 hm _ hfun
  have hF : circuitFun 9 C = F := hfun
  obtain ⟨hb0, hnb4, h4ne, hall, hblen⟩ := base_facts
  -- the gates are the first gate OR(x0, x3) followed by 14 more
  obtain ⟨rest, hsplit⟩ : ∃ rest, C.gates = { op := GateOp.or, inputs := [0, 3] } :: rest := by
    cases hc : C.gates with
    | nil =>
      rw [hc] at hg0
      simp at hg0
    | cons a t =>
      rw [hc] at hg0
      simp at hg0
      exact ⟨t, by rw [hg0]⟩
  have hrest : rest.length = 14 := by
    rw [hsplit] at hlen
    simpa using hlen
  have hm' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hm g hg
    exact ⟨by simpa using h1, h2⟩
  -- the output wire carries 4095 on the 24 rows
  have houtput : (C.gates.foldl wordStep inputs).getD C.output 0 = 4095 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 24 := ⟨j, hj⟩
    obtain ⟨hin, hval⟩ := row_data i
    change bit i ((C.gates.foldl wordStep inputs).getD C.output 0) = bit i 4095
    rw [← read_bit, run_bits C.gates inputs i hm', ← hin, ← hval]
    exact congrFun hF (xs i)
  have hfold : C.gates.foldl wordStep inputs = rest.foldl wordStep base := by
    rw [hsplit, List.foldl_cons, start_word]
  obtain ⟨trace, htlen, htgood, htw⟩ := record_run rest [] base good_nil
    (fun x hx => List.mem_cons_of_mem _ (by simpa using hx))
  -- the word 4095 is recorded in the trace
  have h4mem : (4095 : Word) ∈ 0 :: (base ++ trace) := by
    have e := getD_cases htw 0 C.output
    rw [← hfold, houtput] at e
    rcases e with e | e
    · exact absurd e (by decide +kernel)
    · exact e
  have h4t : (4095 : Word) ∈ trace := by
    simp only [List.mem_cons, List.mem_append] at h4mem hnb4
    tauto
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem h4t
  obtain ⟨hfresh4, hbin4⟩ := htgood k hk
  rw [hget] at hfresh4 hbin4
  have hbin : Binary (base ++ trace.take k) 4095 := by
    rcases hbin4 with e | e
    · exact absurd e h4ne
    · exact e
  have h4p : (4095 : Word) ∉ trace.take k := fun hm4 =>
    hfresh4 (List.mem_cons_of_mem _ (List.mem_append_right _ hm4))
  have hklen : k ≤ 13 := by simp at htlen; omega
  obtain ⟨q, hqgood, hq4, hqlen, hpq⟩ :=
    extend (13 - k) (trace.take k) (good_take htgood k) h4p (by simp; omega)
  have hsub : base ++ trace.take k ⊆ base ++ q := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (hpq hx)
  have hfin : (4095 : Word) ∉ 0 :: (base ++ q) := by
    simp only [List.mem_cons, List.mem_append, not_or] at hnb4 ⊢
    exact ⟨hnb4.1, hnb4.2, hq4⟩
  have hgood : Good (q ++ [4095]) := good_append hqgood hfin (Or.inr (binary_mono hsub hbin))
  have hglen : (q ++ [(4095 : Word)]).length = 14 := by simp [hqlen]
  refine ⟨base ++ (q ++ [4095]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [hblen, hqlen]
  · rw [List.take_left' hblen]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by omega), hblen, List.getD_append_right _ _ _ _
      (by omega), hqlen]
    rfl
  · have hn := good_nodup hgood hb0 _ le_rfl
    rwa [List.take_length] at hn
  · intro x9 h1 h2
    dsimp only
    have hj : x9 - 1 < (q ++ [(4095 : Word)]).length := by omega
    obtain ⟨_, hbj⟩ := hgood (x9 - 1) hj
    have eget : (base ++ (q ++ [4095])).getD (9 + x9) 0 = (q ++ [(4095 : Word)])[x9 - 1] := by
      rw [List.getD_append_right _ _ _ _ (by omega), hblen, List.getD_eq_getElem _ _ (by omega)]
      congr 1
      omega
    have etake : (base ++ (q ++ [4095])).take (9 + x9) =
        base ++ (q ++ [(4095 : Word)]).take (x9 - 1) := by
      rw [List.take_append, List.take_of_length_le (by omega), hblen]
      congr 2
      omega
    rw [eget, etake, hall]
    rcases hbj with e | ⟨a, ha, b, hb, e⟩
    · exact Or.inl e
    · exact Or.inr ⟨a, b, ha, hb, e⟩
