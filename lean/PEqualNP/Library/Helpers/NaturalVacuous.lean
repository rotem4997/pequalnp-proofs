import PEqualNP.Defs
import Mathlib

/-!
# The hypothesis of the natural proofs lemma is false

The hypothesis asks for a function family whose truth tables fool every small circuit of the
model, where a circuit may use one MOD 2 gate of unbounded fan-in. There are `2^n` seeds and
the tables are vectors of length `2^n` over the field with two elements, so some nonempty set
of positions has the same parity on every table of the family. One MOD 2 gate on that set
accepts all of the tables or none of them, and exactly half of all strings.
-/

namespace PEqualNP.Library.Helpers.NaturalVacuous

open PEqualNP.CircuitLowerBounds

/-- The parity of `g` on the set `S`. -/
def par {N : ℕ} (S : Finset (Fin N)) (g : Fin N → Bool) : ZMod 2 :=
  ∑ i ∈ S, if g i = true then 1 else 0

/-- One MOD 2 gate reading the positions in `S`. -/
noncomputable def modCircuit {N : ℕ} (S : Finset (Fin N)) : Circuit :=
  ⟨[⟨GateOp.mod 2, S.toList.map Fin.val⟩], N⟩

theorem count_cast {α : Type} (l : List α) (g : α → Bool) :
    (((l.map g).count true : ℕ) : ZMod 2)
      = (l.map fun i => if g i = true then (1 : ZMod 2) else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : g a
    · simp [h, ih]
    · simp [h, ih, add_comm]

theorem exists_ofFn {α : Type} (s : List α) (n : ℕ) (hs : s.length = n) :
    ∃ g : Fin n → α, List.ofFn g = s := by
  subst hs
  exact ⟨s.get, List.ofFn_get s⟩

theorem eval_ofFn {N : ℕ} (S : Finset (Fin N)) (g : Fin N → Bool) :
    (modCircuit S).eval (List.ofFn g) = true ↔ par S g = 0 := by
  have h1 : (modCircuit S).eval (List.ofFn g)
      = decide (((S.toList.map g).count true) % 2 = 0) := by
    have h2 : (List.map (fun i => (List.ofFn g).getD i false) (S.toList.map Fin.val))
        = S.toList.map g := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simp [List.getD_eq_getElem?_getD]
    simp only [modCircuit, Circuit.eval, Circuit.wires, GateOp.eval, List.foldl_cons,
      List.foldl_nil, h2]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  rw [h1, decide_eq_true_iff, par, ← Finset.sum_map_toList, ← count_cast,
    ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem par_flip {N : ℕ} (S : Finset (Fin N)) (i0 : Fin N) (hi0 : i0 ∈ S)
    (g : Fin N → Bool) : par S (Function.update g i0 (!g i0)) = par S g + 1 := by
  have key : ∀ i ∈ S, (if Function.update g i0 (!g i0) i = true then (1 : ZMod 2) else 0)
      = (if g i = true then 1 else 0) + (if i = i0 then 1 else 0) := by
    intro i _
    by_cases h : i = i0
    · subst h
      cases hg : g i
      · simp
      · simp
        decide
    · simp [h]
  rw [par, Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq' S i0]
  simp [hi0, par]

theorem card_even {N : ℕ} (S : Finset (Fin N)) (i0 : Fin N) (hi0 : i0 ∈ S) :
    (Finset.univ.filter (fun g : Fin N → Bool => par S g = 0)).card * 2 = 2 ^ N := by
  have hflip : (Finset.univ.filter (fun g : Fin N → Bool => par S g = 0)).card
      = (Finset.univ.filter (fun g : Fin N → Bool => ¬ par S g = 0)).card := by
    apply Finset.card_bij' (fun g _ => Function.update g i0 (!g i0))
      (fun g _ => Function.update g i0 (!g i0))
    · intro g _
      simp
    · intro g _
      simp
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [par_flip S i0 hi0, hg]
      decide
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [par_flip S i0 hi0]
      revert hg
      generalize par S g = x
      revert x
      decide
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N → Bool))) (fun g => par S g = 0)
  rw [← hflip] at h
  simp at h
  omega

theorem ncard_len (m : ℕ) (p : List Bool → Prop) [DecidablePred p] :
    {T : List Bool | T.length = m ∧ p T}.ncard
      = (Finset.univ.filter (fun g : Fin m → Bool => p (List.ofFn g))).card := by
  have hset : {T : List Bool | T.length = m ∧ p T}
      = List.ofFn '' ((Finset.univ.filter (fun g : Fin m → Bool => p (List.ofFn g)) :
          Finset (Fin m → Bool)) : Set (Fin m → Bool)) := by
    ext T
    constructor
    · rintro ⟨hl, hp⟩
      obtain ⟨g, rfl⟩ := exists_ofFn T m hl
      exact ⟨g, by simpa using hp, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨List.length_ofFn, by simpa using hg⟩
  rw [hset, Set.ncard_image_of_injective _ List.ofFn_injective, Set.ncard_coe_finset]

/-- Some nonempty set of positions has the same parity on every table of the family. -/
theorem exists_kernel {n : ℕ} (τ : (Fin n → Bool) → Fin (2 ^ n) → ZMod 2) :
    ∃ (S : Finset (Fin (2 ^ n))) (b : ZMod 2), S.Nonempty ∧ ∀ s, ∑ i ∈ S, τ s i = b := by
  let φ : ((Fin (2 ^ n) → ZMod 2) × ZMod 2) → ((Fin n → Bool) → ZMod 2) :=
    fun x s => ∑ i, x.1 i * τ s i + x.2
  have hcard : Fintype.card ((Fin n → Bool) → ZMod 2)
      < Fintype.card ((Fin (2 ^ n) → ZMod 2) × ZMod 2) := by
    simp [ZMod.card]
  obtain ⟨x, y, hxy, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hcard
  have hker : ∀ s, ∑ i, (x.1 i - y.1 i) * τ s i + (x.2 - y.2) = 0 := by
    intro s
    have h := congrFun hφ s
    simp only [φ] at h
    simp only [sub_mul, Finset.sum_sub_distrib]
    linear_combination h
  refine ⟨Finset.univ.filter (fun i => x.1 i - y.1 i ≠ 0), x.2 - y.2, ?_, ?_⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hc : ∀ i, x.1 i - y.1 i = 0 := fun i => by simpa using hne (Finset.mem_univ i)
    have hb := hker (fun _ => false)
    simp [hc] at hb
    exact hxy (Prod.ext (funext fun i => sub_eq_zero.1 (hc i)) (sub_eq_zero.1 hb))
  · intro s
    have h := hker s
    rw [Finset.sum_filter]
    have e : ∀ u v : ZMod 2, (if u ≠ 0 then v else 0) = u * v := by decide
    simp only [e]
    have e2 : ∀ u v : ZMod 2, u + v = 0 → u = v := by decide
    exact e2 _ _ h

theorem arith (A B X P M : ℤ) (hA : A = X ∨ A = 0) (hB : B * 2 = P) (hX : 0 < X)
    (hM : 2 ≤ M) (hB0 : 0 ≤ B) : ¬ (|A * P - B * X| * M < X * P) := by
  subst hB
  have hXB : 0 ≤ X * B := mul_nonneg hX.le hB0
  have h2 : X * B * 2 ≤ X * B * M := mul_le_mul_of_nonneg_left hM hXB
  rcases hA with rfl | rfl
  · rw [show A * (B * 2) - B * A = A * B by ring, abs_of_nonneg hXB]
    intro h
    linarith
  · rw [show 0 * (B * 2) - B * X = -(X * B) by ring, abs_neg, abs_of_nonneg hXB]
    intro h
    linarith

/-- The seeds whose table the circuit accepts, as in the statement. -/
def seedSet (F : Language Bool) (n : ℕ) (D : Circuit) : Set (List Bool) :=
  {s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}

/-- The strings of length `2^n` the circuit accepts, as in the statement. -/
def tableSet (n : ℕ) (D : Circuit) : Set (List Bool) :=
  {T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}

open Classical in
/-- At every length `n` with `k ≤ n`, a one-gate circuit has advantage one half. -/
theorem core (F : Language Bool) (k n : ℕ) (hk : 0 < k) (hn : k ≤ n) :
    ∃ D : Circuit, D.size ≤ 2 ^ (n / k) ∧
      ¬ (|(((seedSet F n D).ncard : ℕ) : ℤ) * 2 ^ (2 ^ n)
          - (((tableSet n D).ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) := by
  let gs : List Bool → Fin (2 ^ n) → Bool := fun s i =>
    decide (s ++ (List.range n).map (fun j : ℕ => (i : ℕ).testBit j) ∈ F)
  obtain ⟨S, b, ⟨i0, hi0⟩, hS⟩ := exists_kernel (n := n)
    (fun s i => if gs (List.ofFn s) i = true then 1 else 0)
  have hpar : ∀ s : List Bool, s.length = n → par S (gs s) = b := by
    intro s hs
    obtain ⟨s', rfl⟩ := exists_ofFn s n hs
    exact hS s'
  have hev : ∀ T : List Bool, T.length = 2 ^ n →
      ((modCircuit S).eval T = true ↔ par S (fun i => T.getD i false) = 0) := by
    intro T hT
    obtain ⟨g, rfl⟩ := exists_ofFn T _ hT
    have hg : (fun i : Fin (2 ^ n) => (List.ofFn g).getD i false) = g := by
      funext i
      simp [List.getD_eq_getElem?_getD]
    rw [hg, eval_ofFn]
  have hA : seedSet F n (modCircuit S) = {s : List Bool | s.length = n ∧ b = 0} := by
    ext s
    simp only [seedSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hs, T, hT, hbits, hD⟩
      refine ⟨hs, ?_⟩
      rw [hev T hT] at hD
      have hg : (fun i : Fin (2 ^ n) => T.getD i false) = gs s := by
        funext i
        apply Bool.eq_iff_iff.2
        simpa [gs] using hbits i i.2
      rw [hg, hpar s hs] at hD
      exact hD
    · rintro ⟨hs, hb⟩
      refine ⟨hs, List.ofFn (gs s), List.length_ofFn, ?_, ?_⟩
      · intro i hi
        simp [List.getD_eq_getElem?_getD, hi, gs]
      · rw [eval_ofFn, hpar s hs, hb]
  have hB : (tableSet n (modCircuit S)).ncard * 2 = 2 ^ (2 ^ n) := by
    have h1 : (tableSet n (modCircuit S)).ncard
        = (Finset.univ.filter (fun g : Fin (2 ^ n) → Bool => par S g = 0)).card :=
      (ncard_len (2 ^ n) (fun T => (modCircuit S).eval T = true)).trans
        (congrArg Finset.card (Finset.filter_congr fun g _ => eval_ofFn S g))
    rw [h1]
    exact card_even S i0 hi0
  have hM : (2 : ℤ) ≤ 2 ^ (n / k) := by
    have h1 : 1 ≤ n / k := (Nat.one_le_div_iff hk).2 hn
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n / k) := pow_le_pow_right₀ (by norm_num) h1
  refine ⟨modCircuit S, ?_, arith _ _ _ _ _ ?_ (by exact_mod_cast hB) (by positivity) hM
    (by positivity)⟩
  · simp only [modCircuit, Circuit.size, List.length_singleton]
    exact Nat.one_le_two_pow
  · rw [hA]
    by_cases hb : b = 0
    · left
      have h2 : {s : List Bool | s.length = n ∧ b = 0}.ncard = 2 ^ n :=
        (ncard_len n (fun _ => b = 0)).trans (by simp [hb])
      rw [h2]
      norm_cast
    · right
      simp [hb]

/-- The hypothesis of the natural proofs lemma is false. -/
theorem hyp_false : ¬ (∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ PEqualNP.Library.P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ 2 ^ (n / k) → |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧ (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔ s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) - (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| * 2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n)) := by
  rintro ⟨F, k, hk, -, n₀, h⟩
  obtain ⟨D, hD, hnot⟩ := core F k (max n₀ k) hk (le_max_right _ _)
  exact hnot (h _ (le_max_left _ _) D hD)

end PEqualNP.Library.Helpers.NaturalVacuous
