import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8965

abbrev Gate := Bool × Fin 32 × Fin 32

def value (xs : List ℕ) (g : Gate) : ℕ :=
  if g.1 = true then xs.getD g.2.1.val 0 &&& xs.getD g.2.2.val 0
  else xs.getD g.2.1.val 0 ||| xs.getD g.2.2.val 0

def step (xs : List ℕ) (g : Gate) : List ℕ := xs ++ [value xs g]

def run (xs : List ℕ) (gs : List Gate) : List ℕ := gs.foldl step xs

lemma run_length (xs : List ℕ) (gs : List Gate) :
    (run xs gs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run (step xs g) gs).length = _
    rw [ih]
    simp [step]
    omega

lemma run_prefix (xs : List ℕ) (gs : List Gate) (i : ℕ) (hi : i < xs.length) :
    (run xs gs).getD i 0 = xs.getD i 0 := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run (step xs g) gs).getD i 0 = _
    rw [ih (step xs g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma run_output (xs : List ℕ) (gs : List Gate) (i : ℕ) (hi : i < gs.length)
    (h₁ : gs[i].2.1.val < xs.length) (h₂ : gs[i].2.2.val < xs.length) :
    (run xs gs).getD (xs.length + i) 0 = value xs gs[i] := by
  induction gs generalizing xs i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      change (run (step xs g) gs).getD (xs.length + 0) 0 = value xs g
      rw [Nat.add_zero, run_prefix _ _ _ (by simp [step])]
      unfold step
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
      rfl
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      change (run (step xs g) gs).getD (xs.length + (i + 1)) 0 = value xs gs[i]
      change gs[i].2.1.val < xs.length at h₁
      change gs[i].2.2.val < xs.length at h₂
      have shift : xs.length + (i + 1) = (step xs g).length + i := by
        simp [step]
        omega
      rw [shift, ih (step xs g) i hi'
        (by simp [step]; omega) (by simp [step]; omega)]
      unfold value step
      rw [List.getD_append _ _ _ _ h₁, List.getD_append _ _ _ _ h₂]

lemma proofCore (xs : List ℕ) (mask : ℕ) (before suffix : List Gate)
    (pairs : List (Fin 32 × Fin 32)) (f : Fin 21 → Gate)
    (hlen : xs.length = 11)
    (hshape : List.ofFn f = before ++ pairs.map (fun p => (true, p)) ++ suffix)
    (hsuffix : ∀ g ∈ suffix, g.1 = false)
    (hprefix : ∀ i : Fin before.length, (before.get i).1 = true →
      (run xs before).getD (11 + i.val) 0 &&& mask ≠ 0)
    (hpairs : ∀ p ∈ pairs, p.1.val < 11 + before.length ∧
      p.2.val < 11 + before.length ∧
      (run xs before).getD p.1.val 0 &&& (run xs before).getD p.2.val 0 &&& mask = 0) :
    List.count true (List.ofFn fun i =>
      decide ((f i).1 = true ∧ (run xs (List.ofFn f)).getD (11 + i.val) 0 &&& mask ≠ 0))
      = (before.filter fun g => g.1).length ∧
    ∀ i : Fin 21, (f i).1 = true →
      (run xs (List.ofFn f)).getD (11 + i.val) 0 &&& mask = 0 → before.length ≤ i.val := by
  let middle : List Gate := pairs.map (fun p => (true, p))
  let start := run xs before
  let full := run xs (List.ofFn f)
  have hstart : start.length = 11 + before.length := by
    simp [start, run_length, hlen]
  have full_eq : full = run (run start middle) suffix := by
    simp only [full, start, hshape, run, List.foldl_append, middle]
  have htotal : (before ++ middle ++ suffix).length = 21 := by
    change (before ++ pairs.map (fun p => (true, p)) ++ suffix).length = 21
    rw [← hshape, List.length_ofFn]
  have gate_at (i : Fin 21) :
      f i = (before ++ middle ++ suffix)[i.val]'(by rw [htotal]; exact i.isLt) := by
    have h := congrArg (fun l : List Gate => l[i.val]?) hshape
    change (List.ofFn f)[i.val]? = (before ++ middle ++ suffix)[i.val]? at h
    have hfin : i.val < (List.ofFn f).length := by simp
    have hlim : i.val < (before ++ middle ++ suffix).length := by
      rw [htotal]
      exact i.isLt
    rw [getElem?_pos (List.ofFn f) i.val hfin,
      getElem?_pos (before ++ middle ++ suffix) i.val hlim] at h
    simpa only [List.getElem_ofFn, Option.some.injEq, Fin.eta] using h
  have hleft (i : Fin 21) (hi : i.val < before.length) :
      f i = before[i.val] ∧ full.getD (11 + i.val) 0 = start.getD (11 + i.val) 0 := by
    constructor
    · rw [gate_at i, List.getElem_append_left, List.getElem_append_left hi]
      simp
      omega
    · have hn : 11 + i.val < start.length := by omega
      rw [full_eq, run_prefix _ _ _ (by rw [run_length]; omega), run_prefix _ _ _ hn]
  have hmiddle (i : Fin 21) (hi : before.length ≤ i.val)
      (hj : i.val < before.length + middle.length) :
      full.getD (11 + i.val) 0 &&& mask = 0 := by
    let j := i.val - before.length
    have hj' : j < middle.length := by dsimp [j]; omega
    have hp : j < pairs.length := by simpa [middle] using hj'
    have hg : middle[j] = (true, pairs[j]) := List.getElem_map _
    obtain ⟨h₁, h₂, hm⟩ := hpairs pairs[j] (List.getElem_mem hp)
    have hn : 11 + i.val = start.length + j := by dsimp [j]; omega
    have he₁ : middle[j].2.1.val < start.length := by rw [hg, hstart]; exact h₁
    have he₂ : middle[j].2.2.val < start.length := by rw [hg, hstart]; exact h₂
    have houtput : start.length + j < (run start middle).length := by
      rw [run_length start middle]
      exact Nat.add_lt_add_left hj' _
    rw [full_eq, hn, run_prefix _ _ _ houtput, run_output _ _ _ hj' he₁ he₂, hg]
    simpa [value, start] using hm
  have hright (i : Fin 21) (hi : before.length + middle.length ≤ i.val) :
      (f i).1 = false := by
    have hs : (before ++ middle).length ≤ i.val := by simpa using hi
    rw [gate_at i, List.getElem_append_right hs]
    exact hsuffix _ (List.getElem_mem _)
  constructor
  · let flags := List.ofFn fun i : Fin 21 => decide ((f i).1 = true ∧
        full.getD (11 + i.val) 0 &&& mask ≠ 0)
    have hflags : flags = before.map Prod.fst ++ List.replicate (middle.length + suffix.length) false := by
      apply List.ext_getElem
      · simpa only [flags, List.length_ofFn, List.length_append, List.length_map,
          List.length_replicate, Nat.add_assoc] using htotal.symm
      · intro i h₁ h₂
        let k : Fin 21 := ⟨i, by simpa [flags] using h₁⟩
        have hk : k.val = i := rfl
        dsimp [flags] at h₁ ⊢
        rw [List.getElem_ofFn]
        change decide ((f k).1 = true ∧ full.getD (11 + i) 0 &&& mask ≠ 0) = _
        by_cases hi : i < before.length
        · obtain ⟨hg, hv⟩ := hleft k (by simpa [hk] using hi)
          change f k = before[i] at hg
          change full.getD (11 + i) 0 = start.getD (11 + i) 0 at hv
          rw [hg, hv, List.getElem_append_left (by simpa using hi), List.getElem_map]
          cases hb : before[i].1 with
          | false => exact decide_eq_false fun h => Bool.false_ne_true h.1
          | true =>
            have hn := hprefix ⟨i, hi⟩ hb
            change start.getD (11 + i) 0 &&& mask ≠ 0 at hn
            exact decide_eq_true ⟨rfl, hn⟩
        · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi),
            List.getElem_replicate]
          by_cases hj : i < before.length + middle.length
          · have hz := hmiddle k (by simpa [hk] using Nat.le_of_not_gt hi) (by simpa [hk] using hj)
            change full.getD (11 + i) 0 &&& mask = 0 at hz
            exact decide_eq_false fun h => h.2 hz
          · have hb := hright k (by simpa [hk] using Nat.le_of_not_gt hj)
            simp [hb]
    change flags.count true = _
    rw [hflags, List.count_append, List.count_replicate, List.count_eq_countP,
      List.countP_map, List.countP_eq_length_filter]
    simp [Function.comp_def]
  · intro i hb hz
    by_contra! hi
    obtain ⟨hg, hv⟩ := hleft i hi
    have hp : (before.get ⟨i.val, hi⟩).1 = true := by rwa [hg] at hb
    apply hprefix ⟨i.val, hi⟩ hp
    change full.getD (11 + i.val) 0 &&& mask = 0 at hz
    rwa [hv] at hz

end PEqualNP.Outside.L_meta_8965

open PEqualNP.Outside.L_meta_8965 (proofCore)


theorem PEqualNP.Outside.L_meta_8965 :
∀ (x1 : List ℕ) (x2 : ℕ) (x3 x4 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x5 : List (Fin (32 : ℕ) × Fin (32 : ℕ))) (x6 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   have x7 : List ℕ → Bool × Fin (32 : ℕ) × Fin (32 : ℕ) → List ℕ := fun (x7 : List ℕ) (x8 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x7 ++ [if x8.1 = Bool.true then x7.getD ↑x8.2.1 (0 : ℕ) &&& x7.getD ↑x8.2.2 (0 : ℕ) else x7.getD ↑x8.2.1 (0 : ℕ) ||| x7.getD ↑x8.2.2 (0 : ℕ)];   have x8 : List ℕ := List.foldl x7 x1 x3;   have x9 : List ℕ := List.foldl x7 x1 (List.ofFn x6);   x1.length = (11 : ℕ) → List.ofFn x6 = x3 ++ List.map (fun (x11 : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.true, x11)) x5 ++ x4 → (∀ x12 ∈ x4, x12.1 = Bool.false) → (∀ (x13 : Fin x3.length), (x3.get x13).1 = Bool.true → x8.getD ((11 : ℕ) + ↑x13) (0 : ℕ) &&& x2 ≠ (0 : ℕ)) → (∀ x14 ∈ x5, ↑x14.1 < (11 : ℕ) + x3.length ∧ ↑x14.2 < (11 : ℕ) + x3.length ∧ x8.getD ↑x14.1 (0 : ℕ) &&& x8.getD ↑x14.2 (0 : ℕ) &&& x2 = (0 : ℕ)) → List.count Bool.true (List.ofFn fun (x15 : Fin (21 : ℕ)) => Decidable.decide ((x6 x15).1 = Bool.true ∧ x9.getD ((11 : ℕ) + ↑x15) (0 : ℕ) &&& x2 ≠ (0 : ℕ))) = (List.filter (fun (x15 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x15.1) x3).length ∧ ∀ (x15 : Fin (21 : ℕ)), (x6 x15).1 = Bool.true → x9.getD ((11 : ℕ) + ↑x15) (0 : ℕ) &&& x2 = (0 : ℕ) → x3.length ≤ ↑x15 := by
  exact proofCore
