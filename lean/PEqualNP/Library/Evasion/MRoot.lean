import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Evasion.Clock
import PEqualNP.Library.Evasion.Pure
import PEqualNP.Library.Machines.IterMeasure

/-!
# Evasion chain: a constructible bound of the order `n^(u/v)` (`rootDom : StmtRootDom`)

For `u = v` the bound is `g n = n`. For `u ≥ v + 1` it is `g n = 2^(u * k n) + 1` with
`k n = ⌈size n / v⌉`, `size n` the bit length of `n`. The clock:

0. `x ↦ ([], x)` in the pair encoding (two-pass machine);
1. `|x|` binary increments, least significant bit first, from the empty string (bounded
   iteration `iterM`, each increment a finite-state transducer): the bits of `|x|`;
2. a transducer writing one mark per `v` symbols, rounded up: `1^(k n)`;
3. the exponential clock `clk`.

The iteration costs `O(n * size n)`, which is `O(2^(u k))` because `u ≥ v + 1`.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-! ## Binary increment -/

/-- Binary increment, least significant bit first. -/
def binc : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: binc r

theorem binc_bits (n : ℕ) : binc (Nat.bits n) = Nat.bits (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with h0 | hm
      · subst h0; simp [binc, Nat.zero_bits]
      · rw [Nat.bit0_bits m (by omega), binc, ← Nat.bit1_bits]
    · rw [Nat.bit1_bits, binc, ih m (by omega),
        show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits (m + 1) (by omega)]

theorem binc_iter (n : ℕ) : binc^[n] [] = Nat.bits n := by
  induction n with
  | zero => simp [Nat.zero_bits]
  | succ n ih => rw [Function.iterate_succ_apply', ih, binc_bits]

/-- The increment transducer: the state is the carry. -/
def incδ (c a : Bool) : Bool × Option Bool × Option Bool := (c && a, some (xor c a), none)

def incFin (c : Bool) : Option Bool := if c then some true else none

theorem inc_run_false (l : List Bool) : fstRun2 incδ incFin false l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, incδ, ih]

theorem inc_run (l : List Bool) : fstRun2 incδ incFin true l = binc l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a
    · simp [fstRun2, incδ, binc, inc_run_false]
    · simp [fstRun2, incδ, binc, ih]

theorem binc_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) binc (fun n => 2 * n + 3) :=
  PEqualNP.Library.Helpers.fst2_time _ _ _ incδ incFin true (fun a => (inc_run a).symm)

/-! ## One mark per `v` symbols, rounded up -/

/-- State `q`: symbols still to skip before the next mark. -/
def divδ (v : ℕ) (hv : 1 ≤ v) (q : Fin v) (_ : Bool) : Fin v × Option Bool × Option Bool :=
  if q.val = 0 then (⟨v - 1, by omega⟩, some true, none) else (⟨q.val - 1, by omega⟩, none, none)

theorem div_run (v : ℕ) (hv : 1 ≤ v) : ∀ (l : List Bool) (q : Fin v),
    fstRun2 (divδ v hv) (fun _ => none) q l =
      List.replicate ((l.length + v - 1 - q.val) / v) true := by
  intro l
  induction l with
  | nil =>
    intro q
    have : (0 + v - 1 - q.val) / v = 0 := Nat.div_eq_of_lt (by omega)
    simp only [fstRun2, Option.toList_none, List.length_nil]
    rw [this]; rfl
  | cons a l ih =>
    intro q
    by_cases hq : q.val = 0
    · simp only [fstRun2, divδ, hq, ite_true, Option.toList_some, Option.toList_none,
        List.append_nil, ih, List.length_cons]
      have e : (l.length + 1 + v - 1 - 0) = l.length + v - 1 - (v - 1) + v := by omega
      rw [e, Nat.add_div_right _ (by omega)]
      rfl
    · simp only [fstRun2, divδ, hq, ite_false, Option.toList_none, List.append_nil,
        List.nil_append, ih, List.length_cons]
      congr 2
      omega

theorem div_time (v : ℕ) (hv : 1 ≤ v) : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => List.replicate ((y.length + v - 1) / v) true)
    (fun n => 2 * n + 3) :=
  PEqualNP.Library.Helpers.fst2_time _ _ _ (divδ v hv) (fun _ => none) ⟨0, by omega⟩
    (fun a => by rw [div_run]; rfl)

end PEqualNP.Library.Evasion

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-! ## Stage 1: the bits of the input length, by `|x|` increments -/

/-- The time of the iteration stage, as a function of the input length `m`. -/
def iterT (m : ℕ) : ℕ := m * (4 * Nat.size m + 6) + 2 * Nat.size m + m + 5

theorem iterT_mono : Monotone iterT := by
  intro a b hab
  have hs : Nat.size a ≤ Nat.size b := Nat.size_le_size hab
  unfold iterT
  have : a * (4 * Nat.size a + 6) ≤ b * (4 * Nat.size b + 6) :=
    Nat.mul_le_mul hab (by omega)
  omega

theorem iterBits_time : PEqualNP.Library.ComputableInTime
    (fun x : List Bool => PEqualNP.Library.encodePair ([], x)) (fun x : List Bool => x)
    (fun x : List Bool => Nat.bits x.length) iterT := by
  obtain ⟨c, hc⟩ := binc_time
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let p : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ p.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = binc z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (binc z),
      ?_, (c.outputsFun z).evals_in_steps, ?_⟩
    · have := (c.outputsFun z).steps_le_m.trans (hc _)
      simpa [p] using this
    · rw [List.map_map]
      conv_rhs => rw [← List.map_id (binc z)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ x : List Bool, ∃ n, n ≤ iterT (PEqualNP.Library.encodePair ([], x)).length ∧
      (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (Iter.iterM c.tm e₀ d₀ e₁) (PEqualNP.Library.encodePair ([], x)))) =
        some (haltList (Iter.iterM c.tm e₀ d₀ e₁) (Nat.bits x.length)) := by
    intro x
    have hL : ∀ j ≤ x.length, (binc^[j] ([] : List Bool)).length ≤ Nat.size x.length := by
      intro j hj
      rw [binc_iter, Nat.size_eq_bits_len]
      exact Nat.size_le_size hj
    obtain ⟨n, hn, hr⟩ := Iter.iter_run_bdd e₀ d₀ e₁ binc p hd hrun [] x _ hL
    rw [binc_iter] at hr
    refine ⟨n, ?_, hr⟩
    have hlen : (PEqualNP.Library.encodePair ([], x)).length = x.length := by
      simp [PEqualNP.Library.encodePair]
    rw [hlen]
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, List.length_nil] at hn
    unfold iterT
    have : x.length * (2 * Nat.size x.length + 3 + 2 * Nat.size x.length + 3) =
      x.length * (4 * Nat.size x.length + 6) := by ring_nf
    omega
  exact ⟨{
    tm := Iter.iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := iterT
    outputsFun := fun x =>
      { steps := Classical.choose (key x)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (Iter.iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key x)] (some (initList (Iter.iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (PEqualNP.Library.encodePair ([], x)))).trans
            ((Classical.choose_spec (key x)).2.trans
            (congrArg (fun l => some (haltList (Iter.iterM c.tm e₀ d₀ e₁) l))
              (hm _ (Nat.bits x.length)).symm))
        steps_le_m := (Classical.choose_spec (key x)).1 } }, fun _ => le_rfl⟩

end PEqualNP.Library.Evasion

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-! ## The bound and its pure facts -/

/-- `⌈size n / v⌉`. -/
def kRoot (v n : ℕ) : ℕ := (Nat.size n + v - 1) / v

/-- The bound for `u ≥ v + 1`. -/
def gRoot (u v n : ℕ) : ℕ := 2 ^ (u * kRoot v n) + 1

theorem kRoot_ge {v : ℕ} (hv : 1 ≤ v) (n : ℕ) : Nat.size n ≤ v * kRoot v n := by
  have h1 := Nat.div_add_mod (Nat.size n + v - 1) v
  have h2 := Nat.mod_lt (Nat.size n + v - 1) (by omega : v > 0)
  unfold kRoot
  omega

theorem kRoot_le {v : ℕ} (_hv : 1 ≤ v) (n : ℕ) : v * kRoot v n ≤ Nat.size n + v - 1 := by
  have h1 := Nat.div_add_mod (Nat.size n + v - 1) v
  unfold kRoot
  omega

theorem kRoot_mono (v : ℕ) : Monotone (kRoot v) := by
  intro a b hab
  have := Nat.size_le_size hab
  exact Nat.div_le_div_right (by omega)

theorem two_pow_size_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.size n ≤ 2 * n := by
  have hs : 0 < Nat.size n := Nat.size_pos.mpr hn
  have : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  calc 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * n := by omega

/-- `n < 2^(v k)`. -/
theorem lt_two_pow_vk {v : ℕ} (hv : 1 ≤ v) (n : ℕ) : n < 2 ^ (v * kRoot v n) :=
  (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by norm_num) (kRoot_ge hv n))

theorem gRoot_mono (u v : ℕ) : Monotone (gRoot u v) := by
  intro a b hab
  unfold gRoot
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2)
    (Nat.mul_le_mul_left u (kRoot_mono v hab))
  omega

theorem le_gRoot {u v : ℕ} (hv : 1 ≤ v) (hvu : v ≤ u) (n : ℕ) : n ≤ 2 ^ (u * kRoot v n) :=
  ((lt_two_pow_vk hv n).trans_le (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right _ hvu))).le

theorem pow_le_gRoot {u v : ℕ} (hv : 1 ≤ v) (n : ℕ) : n ^ u ≤ gRoot u v n ^ v := by
  have h1 : n ^ u ≤ (2 ^ (v * kRoot v n)) ^ u :=
    Nat.pow_le_pow_left (lt_two_pow_vk hv n).le u
  have h2 : (2 ^ (v * kRoot v n)) ^ u = (2 ^ (u * kRoot v n)) ^ v := by
    rw [← pow_mul, ← pow_mul]; ring_nf
  have h3 : (2 ^ (u * kRoot v n)) ^ v ≤ gRoot u v n ^ v :=
    Nat.pow_le_pow_left (by unfold gRoot; omega) v
  omega

theorem gRoot_pow_le {u v : ℕ} (hv : 1 ≤ v) (n : ℕ) :
    gRoot u v n ^ v ≤ (2 ^ v * 2 ^ (u * v)) * n ^ u + 2 ^ v := by
  have hX : (2 ^ (u * kRoot v n)) ^ v ≤ 2 ^ (u * v) * n ^ u + 1 := by
    rw [← pow_mul]
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have hk : kRoot v 0 = 0 := by
        have := kRoot_le hv 0
        simp only [Nat.size_zero] at this
        rcases Nat.eq_zero_or_pos (kRoot v 0) with h | h
        · exact h
        · exfalso
          have : v * 1 ≤ v * kRoot v 0 := Nat.mul_le_mul_left v h
          omega
      simp [hk]
    · have hle := kRoot_le hv n
      have hs := two_pow_size_le hn
      have hs1 : 0 < Nat.size n := Nat.size_pos.mpr hn
      have e1 : 2 ^ (u * kRoot v n * v) ≤ 2 ^ (u * (v - 1) + u * Nat.size n) :=
        Nat.pow_le_pow_right (by norm_num) (by
          have : kRoot v n * v ≤ (v - 1) + Nat.size n := by rw [Nat.mul_comm]; omega
          calc u * kRoot v n * v = u * (kRoot v n * v) := by ring
            _ ≤ u * ((v - 1) + Nat.size n) := Nat.mul_le_mul_left u this
            _ = _ := by ring)
      have e2 : 2 ^ (u * Nat.size n) ≤ 2 ^ u * n ^ u := by
        rw [Nat.mul_comm, pow_mul, ← mul_pow]
        exact Nat.pow_le_pow_left hs u
      have e3 : 2 ^ (u * (v - 1)) * 2 ^ u = 2 ^ (u * v) := by
        rw [← pow_add]; congr 1
        rcases v with _ | v
        · omega
        · simp only [Nat.add_sub_cancel]; ring
      calc 2 ^ (u * kRoot v n * v) ≤ 2 ^ (u * (v - 1) + u * Nat.size n) := e1
        _ = 2 ^ (u * (v - 1)) * 2 ^ (u * Nat.size n) := pow_add _ _ _
        _ ≤ 2 ^ (u * (v - 1)) * (2 ^ u * n ^ u) := Nat.mul_le_mul_left _ e2
        _ = 2 ^ (u * v) * n ^ u := by rw [← e3]; ring
        _ ≤ 2 ^ (u * v) * n ^ u + 1 := Nat.le_succ _
  have hg : gRoot u v n ≤ 2 * 2 ^ (u * kRoot v n) := by
    unfold gRoot; have := Nat.one_le_two_pow (n := u * kRoot v n); omega
  calc gRoot u v n ^ v ≤ (2 * 2 ^ (u * kRoot v n)) ^ v := Nat.pow_le_pow_left hg v
    _ = 2 ^ v * (2 ^ (u * kRoot v n)) ^ v := mul_pow _ _ _
    _ ≤ 2 ^ v * (2 ^ (u * v) * n ^ u + 1) := Nat.mul_le_mul_left _ hX
    _ = (2 ^ v * 2 ^ (u * v)) * n ^ u + 2 ^ v := by ring

/-- The iteration cost is paid by the clock when `u ≥ v + 1`. -/
theorem mul_size_le {u v : ℕ} (hv : 1 ≤ v) (hvu : v + 1 ≤ u) (n : ℕ) :
    n * Nat.size n ≤ v * 2 ^ (u * kRoot v n) := by
  set k := kRoot v n
  have h1 : n ≤ 2 ^ (v * k) := (lt_two_pow_vk hv n).le
  have h2 : Nat.size n ≤ v * 2 ^ k :=
    (kRoot_ge hv n).trans (Nat.mul_le_mul_left v Nat.lt_two_pow_self.le)
  have h3 : 2 ^ (v * k) * 2 ^ k ≤ 2 ^ (u * k) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc n * Nat.size n ≤ 2 ^ (v * k) * (v * 2 ^ k) := Nat.mul_le_mul h1 h2
    _ = v * (2 ^ (v * k) * 2 ^ k) := by ring
    _ ≤ v * 2 ^ (u * k) := Nat.mul_le_mul_left v h3

end PEqualNP.Library.Evasion

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-! ## The clock and the piece -/

/-- Stage 0: the input becomes the second component of a pair with an empty first one. -/
theorem toPair_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => PEqualNP.Library.encodePair ([], x)) (fun x : List Bool => x)
    (fun n => 4 * n + 4) :=
  tp_time _ _ _ (fun b => some (Sum.inr b)) (fun _ => none) (Sum.inl true) (fun a => by
    simp [PEqualNP.Library.encodePair])

theorem gRoot_constr {u v : ℕ} (hv : 1 ≤ v) (hvu : v + 1 ≤ u) : Constructible (gRoot u v) := by
  refine ⟨gRoot_mono u v, fun n => (le_gRoot (u := u) hv (by omega) n).trans (by unfold gRoot; omega), ?_⟩
  have h01 := comp_time (fun x : List Bool => x)
    (fun x : List Bool => PEqualNP.Library.encodePair ([], x)) (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => Nat.bits x.length) _ _ (fun n => n)
    toPair_time iterBits_time iterT_mono (fun a => by simp [PEqualNP.Library.encodePair])
  have h012 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) _ (fun y : List Bool => List.replicate ((y.length + v - 1) / v) true)
    _ _ (fun n => Nat.size n) h01 (div_time v hv)
    (fun a b hab => by show 2 * a + 3 ≤ 2 * b + 3; omega)
    (fun a => by simp [Nat.size_eq_bits_len])
  obtain ⟨-, -, c3, hc3⟩ := clk u 1 (by omega) le_rfl
  have h0123 := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => x) _ _ _ _ (fun n => kRoot v n) h012 hc3
    (fun a b hab => by
      show c3 * (1 * 2 ^ (u * a) + 1) + c3 ≤ c3 * (1 * 2 ^ (u * b) + 1) + c3
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.mul_le_mul_left u hab)
      exact Nat.add_le_add_right (Nat.mul_le_mul_left c3 (by omega)) c3)
    (fun a => by simp [Nat.size_eq_bits_len, kRoot])
  simp only [List.length_replicate, Nat.size_eq_bits_len, Nat.one_mul] at h0123
  refine ⟨4 * v + 3 * c3 + 40, time_mono h0123 fun n => ?_⟩
  have e1 := mul_size_le hv hvu n
  have e2 := le_gRoot hv (by omega : v ≤ u) n
  have e3 : Nat.size n ≤ 2 ^ (u * kRoot v n) :=
    ((kRoot_ge hv n).trans (Nat.mul_le_mul_right _ (by omega : v ≤ u))).trans
      Nat.lt_two_pow_self.le
  have e4 : kRoot v n ≤ 2 ^ (u * kRoot v n) :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < u)).trans Nat.lt_two_pow_self.le
  have e6 : n * (4 * Nat.size n + 6) = 4 * (n * Nat.size n) + 6 * n := by ring
  simp only [iterT, gRoot]
  rw [e6]
  generalize 2 ^ (u * kRoot v n) = E at *
  generalize n * Nat.size n = P at *
  generalize Nat.size n = s at *
  generalize kRoot v n = k at *
  nlinarith

/-- The piece: a constructible bound of the order `n^(u/v)`, from above. -/
theorem rootDom : StmtRootDom := by
  intro u v hv hvu
  rcases Nat.eq_or_lt_of_le hvu with h | h
  · subst h
    refine ⟨fun n => n, ⟨fun a b hab => hab, fun n => le_rfl, ?_⟩, fun n => ?_, 1, fun n => ?_⟩
    · obtain ⟨C, hC⟩ := t2a 1 0
      exact ⟨C, by simpa using hC⟩
    · exact (rootUp_spec v _ hv).2 n le_rfl
    · show n ^ v ≤ 1 * n ^ v + 1
      omega
  · refine ⟨gRoot u v, gRoot_constr hv h, fun n => (rootUp_spec v _ hv).2 _ (pow_le_gRoot hv n),
      2 ^ v * 2 ^ (u * v) + 2 ^ v, fun n => ?_⟩
    have := gRoot_pow_le (u := u) hv n
    have h1 : 2 ^ v ≤ 2 ^ v * 2 ^ (u * v) + 2 ^ v := Nat.le_add_left _ _
    have h2 : (2 ^ v * 2 ^ (u * v)) * n ^ u ≤ (2 ^ v * 2 ^ (u * v) + 2 ^ v) * n ^ u :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega

end PEqualNP.Library.Evasion
