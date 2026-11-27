import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- Live-wire compilation, projection, and monotonicity-fall lemmas adapted from
-- open-goat/pequalnp-proofs L_meta_671 (Apache-2.0, Lewis Watson / L-meta-515).
-- Exact-1-of-5 U_2 lower-bound DAG certificate generated and verified for L-meta-10405.

namespace PEqualNP.Outside.L_meta_10405_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- ============================================================================
-- 1. Abstract Live-Wire Calculus (adapted from L_meta_671)
-- ============================================================================
namespace Live

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

theorem live_mono_k {ops : α → α → Finset α} {goal : α} {m n : ℕ} (hmn : m ≤ n) {s : Finset α}
    (h : live ops goal m s) : live ops goal n s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {m n : ℕ} (hmn : m ≤ n) {s : Finset α}
    (h : build ops goal m s) : build ops goal n s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a, hs ha, b, hs hb, hab, z, hz, ih (Finset.insert_subset_insert _ hs) tail⟩

theorem map_live {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : α → Prop) (e : α → β)
    (hinj : ∀ x y, P x → P y → e x = e y → x = y)
    (hclosed : ∀ a b z, z ∈ ops a b → P z)
    (hmap : ∀ a b z, P a → P b → z ∈ ops a b → e z ∈ ops' (e a) (e b))
    {goal : α} {k : ℕ} {s : Finset α}
    (hsP : ∀ x ∈ s, P x) (h : live ops goal k s) :
    live ops' (e goal) k (s.image e) := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    subst h; simp [live]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih hsP skip)
    · have haP : P a := hsP a (by simp)
      have hbP : P b := hsP b (by simp)
      have hzP : P z := hclosed a b z hz
      have hne : e a ≠ e b := fun heq => hab (hinj a b haP hbP heq)
      have hzout : e z ∉ (insert a (insert b rest)).image e := by
        intro hm
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hm
        exact hout (hinj w z (hsP w hw) hzP hwe ▸ hw)
      have htailP : ∀ x ∈ insert z rest, P x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hzP
        · exact hsP x (by simp [hx])
      refine Or.inr ⟨e a, Finset.mem_image_of_mem e ha, e b, Finset.mem_image_of_mem e hb,
        hne, e z, hmap a b z haP hbP hz, hzout, rest.image e, ?_, ?_⟩
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih htailP tail

def kept (p : α → Option β) (s : Finset α) : Finset β :=
  s.biUnion (fun a => (p a).toFinset)

def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by simp [kept]

theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r) + 1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := fun h => fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hn, r, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    exact build_mono_k (Nat.zero_le n) mem
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hn, r, rfl, tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha | hb | ⟨u, w, hA, hB, hw, hop⟩
        · apply free; simp [kept_insert, hZ, ha]
        · apply free; simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert, hZ, hA, hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert, hA], w, by simp [kept_insert, hB],
              hw, v, hop, build_mono covers next⟩

end Live

-- ============================================================================
-- 2. Nat Truth-Table Algebra (uniform over N ∈ {1..5})
-- ============================================================================
def allMask (N : ℕ) : ℕ := 2 ^ (2 ^ N) - 1

def invN (N w : ℕ) : ℕ := (w &&& allMask N) ^^^ allMask N

def canonN (N w : ℕ) : ℕ :=
  let v := w &&& allMask N
  if v.testBit 0 then v ^^^ allMask N else v

def rawOps (N a b : ℕ) : List ℕ :=
  [a &&& b, a &&& invN N b, invN N a &&& b, invN N a &&& invN N b]

def opsN (N a b : ℕ) : List ℕ :=
  ((rawOps N a b).map (canonN N)).filter (· != 0)

def basicOps (N a b : ℕ) : Finset ℕ := (opsN N a b).toFinset

def target (N : ℕ) (isNor : Bool) : ℕ :=
  match N, isNor with
  | 1, false => 2
  | 1, true  => 2
  | 2, false => 6
  | 2, true  => 14
  | 3, false => 22
  | 3, true  => 254
  | 4, false => 278
  | 4, true  => 65534
  | 5, false => 65814
  | 5, true  => 4294967294
  | _, _     => 0

lemma testBit_allMask (N i : ℕ) : (allMask N).testBit i = decide (i < 2 ^ N) := by
  simp [allMask, Nat.testBit_two_pow_sub_one]

lemma testBit_invN (N w i : ℕ) :
    (invN N w).testBit i = (decide (i < 2 ^ N) && !w.testBit i) := by
  simp only [invN, Nat.testBit_xor, Nat.testBit_and, testBit_allMask]
  cases decide (i < 2 ^ N) <;> cases w.testBit i <;> rfl

lemma testBit_mask (N w i : ℕ) :
    (w &&& allMask N).testBit i = (w.testBit i && decide (i < 2 ^ N)) := by
  simp [Nat.testBit_and, testBit_allMask]

lemma invN_invN (N w : ℕ) : invN N (invN N w) = w &&& allMask N := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_invN, testBit_mask]
  cases decide (i < 2 ^ N) <;> cases w.testBit i <;> rfl

lemma invN_mask (N w : ℕ) : invN N (w &&& allMask N) = invN N w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_invN, testBit_mask]
  cases decide (i < 2 ^ N) <;> cases w.testBit i <;> rfl

lemma canonN_mask (N w : ℕ) : canonN N (w &&& allMask N) = canonN N w := by
  have hm : (w &&& allMask N) &&& allMask N = w &&& allMask N := by
    apply Nat.eq_of_testBit_eq; intro i; simp [testBit_mask]
  simp [canonN, hm]

lemma testBit_canonN (N w i : ℕ) :
    (canonN N w).testBit i =
      (decide (i < 2 ^ N) && (w.testBit i != w.testBit 0)) := by
  have h0 : 0 < 2 ^ N := Nat.two_pow_pos N
  dsimp only [canonN]
  have hbit0 : (w &&& allMask N).testBit 0 = w.testBit 0 := by
    rw [testBit_mask, decide_eq_true h0, Bool.and_true]
  rw [hbit0]
  cases hw0 : w.testBit 0 with
  | false =>
    simp only [Bool.false_eq_true, ite_false, testBit_mask, Bool.bne_false]
    exact Bool.and_comm _ _
  | true =>
    simp only [ite_true, Nat.testBit_xor, testBit_mask, testBit_allMask, Bool.bne_true]
    cases decide (i < 2 ^ N) <;> cases w.testBit i <;> rfl

lemma canonN_invN (N w : ℕ) : canonN N (invN N w) = canonN N w := by
  apply Nat.eq_of_testBit_eq; intro i
  have h0 : 0 < 2 ^ N := Nat.two_pow_pos N
  simp only [testBit_canonN, testBit_invN, h0, decide_true, Bool.true_and]
  cases decide (i < 2 ^ N) <;> cases w.testBit i <;> cases w.testBit 0 <;> rfl

lemma canonN_canonN (N w : ℕ) : canonN N (canonN N w) = canonN N w := by
  apply Nat.eq_of_testBit_eq; intro i
  have h0 : 0 < 2 ^ N := Nat.two_pow_pos N
  simp only [testBit_canonN, h0, decide_true, bne_self_eq_false, Bool.and_false, Bool.bne_false]
  cases decide (i < 2 ^ N) <;> cases w.testBit i <;> cases w.testBit 0 <;> rfl

lemma canonN_eq_zero_iff (N w : ℕ) :
    canonN N w = 0 ↔ (w &&& allMask N = 0 ∨ w &&& allMask N = allMask N) := by
  constructor
  · intro h
    cases hw0 : w.testBit 0 with
    | false =>
      left; apply Nat.eq_of_testBit_eq; intro i
      have hi := congrArg (fun n => n.testBit i) h
      simp only [testBit_canonN, hw0, Bool.bne_false, Nat.zero_testBit] at hi
      rw [testBit_mask, Nat.zero_testBit, Bool.and_comm]; exact hi
    | true =>
      right; apply Nat.eq_of_testBit_eq; intro i
      have hi := congrArg (fun n => n.testBit i) h
      simp only [testBit_canonN, hw0, Bool.bne_true, Nat.zero_testBit] at hi
      rw [testBit_mask, testBit_allMask]
      cases hm : decide (i < 2 ^ N) <;> cases hwi : w.testBit i <;> simp [hm, hwi] at hi ⊢
  · rintro (h | h) <;> apply Nat.eq_of_testBit_eq <;> intro i
    · have hi := congrArg (fun n => n.testBit i) h
      have h0 := congrArg (fun n => n.testBit 0) h
      have hp : 0 < 2 ^ N := Nat.two_pow_pos N
      simp only [testBit_mask, hp, decide_true, Bool.and_true, Nat.zero_testBit] at hi h0
      simp only [testBit_canonN, h0, Bool.bne_false, Nat.zero_testBit]
      rw [Bool.and_comm]; exact hi
    · have hi := congrArg (fun n => n.testBit i) h
      have h0 := congrArg (fun n => n.testBit 0) h
      have hp : 0 < 2 ^ N := Nat.two_pow_pos N
      simp only [testBit_mask, testBit_allMask, hp, decide_true, Bool.and_true] at hi h0
      simp only [testBit_canonN, h0, Bool.bne_true, Nat.zero_testBit]
      cases hm : decide (i < 2 ^ N) <;> cases hwi : w.testBit i <;> simp [hm, hwi] at hi ⊢

lemma signN (N w : ℕ) :
    w &&& allMask N = canonN N w ∨ w &&& allMask N = invN N (canonN N w) := by
  cases hw0 : w.testBit 0 with
  | false =>
    left; apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_mask, testBit_canonN, hw0, Bool.bne_false]
    exact Bool.and_comm _ _
  | true =>
    right; apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_mask, testBit_invN, testBit_canonN, hw0, Bool.bne_true]
    cases decide (i < 2 ^ N) <;> cases w.testBit i <;> rfl

lemma and_mask_canon (N x y : ℕ) :
    canonN N ((x &&& allMask N) &&& (y &&& allMask N)) = canonN N (x &&& y) := by
  apply Nat.eq_of_testBit_eq; intro i
  have h0 : 0 < 2 ^ N := Nat.two_pow_pos N
  simp only [testBit_canonN, Nat.testBit_and, testBit_mask, testBit_allMask, h0, decide_true, Bool.and_true]
  cases decide (i < 2 ^ N) <;> cases x.testBit i <;> cases y.testBit i <;>
    cases x.testBit 0 <;> cases y.testBit 0 <;> rfl

lemma signed_and_mem {N x y a b : ℕ}
    (hx : x &&& allMask N = a ∨ x &&& allMask N = invN N a)
    (hy : y &&& allMask N = b ∨ y &&& allMask N = invN N b)
    (h0 : canonN N (x &&& y) ≠ 0) :
    canonN N (x &&& y) ∈ basicOps N a b := by
  rw [← and_mask_canon]
  have h0' : canonN N ((x &&& allMask N) &&& (y &&& allMask N)) ≠ 0 := by
    rwa [and_mask_canon]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rw [hx, hy] at h0' ⊢ <;>
    simp [basicOps, opsN, rawOps, h0']

lemma same_and {N x y : ℕ} (heq : canonN N x = canonN N y) :
    canonN N (x &&& y) = canonN N x ∨ canonN N (x &&& y) = 0 := by
  have hx := signN N x
  have hy := signN N y
  rw [← heq] at hy
  rw [← and_mask_canon]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · left; rw [Nat.and_self, canonN_canonN]
  · right; apply (canonN_eq_zero_iff N _).mpr; left
    apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_mask, Nat.testBit_and, testBit_invN, Nat.zero_testBit]
    cases (canonN N x).testBit i <;> cases decide (i < 2 ^ N) <;> rfl
  · right; apply (canonN_eq_zero_iff N _).mpr; left
    apply Nat.eq_of_testBit_eq; intro i
    simp only [testBit_mask, Nat.testBit_and, testBit_invN, Nat.zero_testBit]
    cases (canonN N x).testBit i <;> cases decide (i < 2 ^ N) <;> rfl
  · left; rw [Nat.and_self, canonN_invN, canonN_canonN]

lemma basicOps_canon {N a b z : ℕ} (hz : z ∈ basicOps N a b) : canonN N z = z := by
  simp only [basicOps, opsN, rawOps, List.mem_toFinset, List.mem_filter, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨⟨u, _, rfl⟩, _⟩ := hz
  exact canonN_canonN N u

lemma basicOps_swap (N a b : ℕ) : basicOps N a b = basicOps N b a := by
  ext z
  simp only [basicOps, opsN, rawOps, List.mem_toFinset, List.mem_filter, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨u, rfl | rfl | rfl | rfl, rfl⟩, h0⟩
    · exact ⟨⟨b &&& a, Or.inl rfl, by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨invN N b &&& a, Or.inr (Or.inr (Or.inl rfl)), by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨b &&& invN N a, Or.inr (Or.inl rfl), by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨invN N b &&& invN N a, Or.inr (Or.inr (Or.inr rfl)), by rw [Nat.and_comm]⟩, h0⟩
  · rintro ⟨⟨u, rfl | rfl | rfl | rfl, rfl⟩, h0⟩
    · exact ⟨⟨a &&& b, Or.inl rfl, by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨invN N a &&& b, Or.inr (Or.inr (Or.inl rfl)), by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨a &&& invN N b, Or.inr (Or.inl rfl), by rw [Nat.and_comm]⟩, h0⟩
    · exact ⟨⟨invN N a &&& invN N b, Or.inr (Or.inr (Or.inr rfl)), by rw [Nat.and_comm]⟩, h0⟩

-- ============================================================================
-- 3. Row-Pullback Homomorphism (unified for SubMaps and S_N Permutations!)
-- ============================================================================
def mapRows (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | idx :: rest => Nat.bit (w.testBit idx) (mapRows w rest)

lemma mapRows_testBit (w : ℕ) : ∀ (f : List ℕ) (j : ℕ),
    (mapRows w f).testBit j = (if j < f.length then w.testBit (f.getD j 0) else false)
  | [], j => by simp [mapRows]
  | idx :: rest, 0 => by simp [mapRows, Nat.testBit_bit_zero]
  | idx :: rest, j + 1 => by
    simp only [mapRows, Nat.testBit_bit_succ, mapRows_testBit w rest j, List.length_cons,
      Nat.add_lt_add_iff_right, List.getD_cons_succ]

lemma mapRows_and (a b : ℕ) (f : List ℕ) :
    mapRows (a &&& b) f = mapRows a f &&& mapRows b f := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, mapRows_testBit, mapRows_testBit, mapRows_testBit]
  split <;> simp [Nat.testBit_and]

lemma mapRows_invN (N rem w : ℕ) (f : List ℕ) (hlen : f.length = 2 ^ rem)
    (hbnd : ∀ x ∈ f, x < 2 ^ N) :
    mapRows (invN N w) f = invN rem (mapRows w f) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_invN, mapRows_testBit, mapRows_testBit, hlen]
  by_cases hj : j < 2 ^ rem
  · have hmem : f.getD j 0 ∈ f := by
      have hj' : j < f.length := by omega
      rw [List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    have hx : f.getD j 0 < 2 ^ N := hbnd _ hmem
    simp only [hj, ite_true, decide_true, Bool.true_and, testBit_invN, hx]
  · simp only [hj, ite_false, decide_false, Bool.false_and]

lemma mapRows_mask (N w : ℕ) (f : List ℕ) (hbnd : ∀ x ∈ f, x < 2 ^ N) :
    mapRows (w &&& allMask N) f = mapRows w f := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [mapRows_testBit, mapRows_testBit]
  by_cases hj : j < f.length
  · have hmem : f.getD j 0 ∈ f := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    simp only [hj, ite_true, testBit_mask, hbnd _ hmem, decide_true, Bool.and_true]
  · simp only [hj, ite_false]

lemma mapRows_canon_zero (N w : ℕ) (f : List ℕ) (hlen : f.length = 2 ^ N)
    (hbnd : ∀ x ∈ f, x < 2 ^ N) (hf0 : f.getD 0 0 = 0) :
    mapRows (canonN N w) f = canonN N (mapRows w f) := by
  apply Nat.eq_of_testBit_eq; intro j
  have h0 : 0 < f.length := by rw [hlen]; exact Nat.two_pow_pos N
  rw [testBit_canonN, mapRows_testBit, mapRows_testBit, mapRows_testBit]
  rw [if_pos h0, hf0, hlen]
  by_cases hj : j < 2 ^ N
  · have hmem : f.getD j 0 ∈ f := by
      have hj' : j < f.length := by omega
      rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    simp only [hj, ite_true, decide_true, Bool.true_and, testBit_canonN, hbnd _ hmem]
  · simp only [hj, ite_false, decide_false, Bool.false_and]

lemma mapRows_inv_cancel (N w : ℕ) (fwd inv : List ℕ)
    (hf_len : fwd.length = 2 ^ N) (hi_len : inv.length = 2 ^ N)
    (hcancel : ∀ i < 2 ^ N, fwd.getD (inv.getD i 0) 0 = i)
    (hi_bnd : ∀ x ∈ inv, x < 2 ^ N) (hw : canonN N w = w) :
    mapRows (mapRows w fwd) inv = w := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [mapRows_testBit, hi_len]
  by_cases hj : j < 2 ^ N
  · have hmem : inv.getD j 0 ∈ inv := by
      have hj' : j < inv.length := by omega
      rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    have hlt : inv.getD j 0 < fwd.length := by rw [hf_len]; exact hi_bnd _ hmem
    rw [if_pos hj, mapRows_testBit, if_pos hlt, hcancel j hj]
  · rw [if_neg hj, ← hw, testBit_canonN]
    simp [hj]

def projMap (rem : ℕ) (rows : List ℕ) (w : ℕ) : Option ℕ :=
  let v := canonN rem (mapRows w rows)
  if v = 0 then none else some v

lemma projMap_invN (N rem : ℕ) (rows : List ℕ) (hlen : rows.length = 2 ^ rem)
    (hbnd : ∀ x ∈ rows, x < 2 ^ N) (w : ℕ) :
    projMap rem rows (invN N w) = projMap rem rows w := by
  simp only [projMap, mapRows_invN N rem w rows hlen hbnd, canonN_invN]

lemma projMap_canon (N rem : ℕ) (rows : List ℕ) (hlen : rows.length = 2 ^ rem)
    (hbnd : ∀ x ∈ rows, x < 2 ^ N) (w : ℕ) :
    projMap rem rows (canonN N w) = projMap rem rows w := by
  rcases signN N w with h | h
  · rw [← h]; simp only [projMap, mapRows_mask N w rows hbnd]
  · have h' : canonN N w = invN N (w &&& allMask N) := by
      have := congrArg (invN N) h
      rw [invN_invN] at this
      have hc : canonN N w &&& allMask N = canonN N w := by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [testBit_mask, testBit_canonN]
        cases decide (i < 2 ^ N) <;> cases w.testBit i <;> cases w.testBit 0 <;> rfl
      rw [hc] at this
      exact this.symm
    rw [h', invN_mask, projMap_invN N rem rows hlen hbnd]

def wrapN (rem x : ℕ) : Option ℕ :=
  let v := canonN rem x
  if v = 0 then none else some v

lemma projMap_eq_wrapN (rem : ℕ) (rows : List ℕ) (w : ℕ) :
    projMap rem rows w = wrapN rem (mapRows w rows) := rfl

lemma wrapN_invN (rem x : ℕ) : wrapN rem (invN rem x) = wrapN rem x := by
  simp only [wrapN, canonN_invN]

lemma mask_and_self_right (rem y : ℕ) : allMask rem &&& (y &&& allMask rem) = y &&& allMask rem := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, testBit_allMask]
  cases decide (i < 2 ^ rem) <;> cases y.testBit i <;> rfl

lemma mask_and_self_left (rem x : ℕ) : (x &&& allMask rem) &&& allMask rem = x &&& allMask rem := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, testBit_allMask]
  cases decide (i < 2 ^ rem) <;> cases x.testBit i <;> rfl

lemma binary_projectN {rem x y v : ℕ} (h : wrapN rem (x &&& y) = some v) :
    wrapN rem x = some v ∨ wrapN rem y = some v ∨
    ∃ u w, wrapN rem x = some u ∧ wrapN rem y = some w ∧ u ≠ w ∧ v ∈ basicOps rem u w := by
  by_cases hx : canonN rem x = 0
  · rcases (canonN_eq_zero_iff rem x).mp hx with hx0 | hx1
    · exfalso
      have hz : canonN rem (x &&& y) = 0 := by
        rw [← and_mask_canon, hx0, Nat.zero_and]
        simp [canonN]
      simp [wrapN, hz] at h
    · right; left
      have heq : canonN rem (x &&& y) = canonN rem y := by
        rw [← and_mask_canon, hx1, mask_and_self_right, canonN_mask]
      simpa [wrapN, heq] using h
  by_cases hy : canonN rem y = 0
  · rcases (canonN_eq_zero_iff rem y).mp hy with hy0 | hy1
    · exfalso
      have hz : canonN rem (x &&& y) = 0 := by
        rw [← and_mask_canon, hy0, Nat.and_zero]
        simp [canonN]
      simp [wrapN, hz] at h
    · left
      have heq : canonN rem (x &&& y) = canonN rem x := by
        rw [← and_mask_canon, hy1, mask_and_self_left, canonN_mask]
      simpa [wrapN, heq] using h
  have hnz : canonN rem (x &&& y) ≠ 0 := by intro hc; simp [wrapN, hc] at h
  have hval : canonN rem (x &&& y) = v := by simpa [wrapN, hnz] using h
  by_cases heq : canonN rem x = canonN rem y
  · rcases same_and heq with hsame | hbad
    · left; dsimp only [wrapN]; rw [if_neg hx, ← hval, hsame]
    · exact False.elim (hnz hbad)
  · refine Or.inr (Or.inr ⟨canonN rem x, canonN rem y, by dsimp only [wrapN]; rw [if_neg hx],
      by dsimp only [wrapN]; rw [if_neg hy], heq, ?_⟩)
    rw [← hval]
    exact signed_and_mem (signN rem x) (signN rem y) hnz

lemma projMap_projects (N rem : ℕ) (rows : List ℕ) (hlen : rows.length = 2 ^ rem)
    (hbnd : ∀ x ∈ rows, x < 2 ^ N) :
    Live.projects (projMap rem rows) (basicOps N) (basicOps rem) := by
  intro a b z hz v hv
  simp only [basicOps, opsN, rawOps, List.mem_toFinset, List.mem_filter, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨⟨u, rfl | rfl | rfl | rfl, rfl⟩, _⟩ := hz
  · rw [projMap_canon N rem rows hlen hbnd, projMap_eq_wrapN, mapRows_and] at hv
    simpa only [projMap_eq_wrapN] using binary_projectN hv
  · rw [projMap_canon N rem rows hlen hbnd, projMap_eq_wrapN, mapRows_and,
      mapRows_invN N rem b rows hlen hbnd] at hv
    simpa only [projMap_eq_wrapN, wrapN_invN] using binary_projectN hv
  · rw [projMap_canon N rem rows hlen hbnd, projMap_eq_wrapN, mapRows_and,
      mapRows_invN N rem a rows hlen hbnd] at hv
    simpa only [projMap_eq_wrapN, wrapN_invN] using binary_projectN hv
  · rw [projMap_canon N rem rows hlen hbnd, projMap_eq_wrapN, mapRows_and,
      mapRows_invN N rem a rows hlen hbnd, mapRows_invN N rem b rows hlen hbnd] at hv
    simpa only [projMap_eq_wrapN, wrapN_invN] using binary_projectN hv

-- ============================================================================
-- 4. Separation (`sepCheck`) & Small-k Soundness
-- ============================================================================
def differs (u v w : ℕ) : Prop := w.testBit u ≠ w.testBit v

instance (u v w : ℕ) : Decidable (differs u v w) :=
  inferInstanceAs (Decidable (w.testBit u ≠ w.testBit v))

lemma testBit_false_of_lt_two_pow {n k i : ℕ} (hn : n < 2 ^ k) (hi : k ≤ i) :
    n.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) hi))

lemma canonN_differs {N u v w : ℕ} (hu : u < 2 ^ N) (hv : v < 2 ^ N) :
    differs u v (canonN N w) ↔ differs u v w := by
  simp only [differs, testBit_canonN, hu, hv, decide_true, Bool.true_and]
  cases w.testBit u <;> cases w.testBit v <;> cases w.testBit 0 <;> simp

lemma basicOps_differs {N u v a b z : ℕ} (hu : u < 2 ^ N) (hv : v < 2 ^ N)
    (hz : z ∈ basicOps N a b) (hd : differs u v z) :
    differs u v a ∨ differs u v b := by
  by_contra h
  have ha : a.testBit u = a.testBit v := by
    by_contra hne; exact h (Or.inl hne)
  have hb : b.testBit u = b.testBit v := by
    by_contra hne; exact h (Or.inr hne)
  simp only [basicOps, opsN, rawOps, List.mem_toFinset, List.mem_filter, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨⟨w, rfl | rfl | rfl | rfl, rfl⟩, _⟩ := hz <;>
    rw [canonN_differs hu hv] at hd <;>
    simp only [differs, Nat.testBit_and, testBit_invN, hu, hv, decide_true, Bool.true_and, ha, hb] at hd <;>
    exact hd rfl

def agreeMask (N u : ℕ) (init : ℕ) (ws : List ℕ) : ℕ :=
  ws.foldl (fun acc w => acc &&& (if w.testBit u then w else invN N w)) init

lemma testBit_agreeMask (N u : ℕ) (ws : List ℕ) :
    ∀ (init v : ℕ), v < 2 ^ N →
      (agreeMask N u init ws).testBit v = true →
      init.testBit v = true ∧ ∀ w ∈ ws, w.testBit v = w.testBit u := by
  induction ws with
  | nil => intro init v _ h; exact ⟨h, by simp⟩
  | cons a rest ih =>
    intro init v hv h
    obtain ⟨h1, h2⟩ := ih _ v hv h
    simp only [Nat.testBit_and, Bool.and_eq_true] at h1
    refine ⟨h1.1, ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · have ha := h1.2
      cases hwu : w.testBit u <;> simp [hwu, testBit_invN, hv] at ha ⊢
      · exact ha
      · exact ha
    · exact h2 w hw

lemma exists_testBit_of_ne_zero {n : ℕ} (h : n ≠ 0) : ∃ v, n.testBit v = true := by
  by_contra hall
  apply h
  apply Nat.eq_of_testBit_eq; intro v
  simp only [Nat.zero_testBit]
  cases hv : n.testBit v
  · rfl
  · exfalso; exact hall ⟨v, hv⟩

def sepCheck (N : ℕ) (isNor : Bool) (ws : List ℕ) : Bool :=
  if isNor then
    agreeMask N 0 (allMask N ^^^ 1) ws == 0
  else
    let zeros := allMask N ^^^ target N false
    (List.range N).all (fun i => agreeMask N (1 <<< i) zeros ws == 0)

lemma target_bit_bounds (N : ℕ) (isNor : Bool) (hN : 1 ≤ N ∧ N ≤ 5) :
    (isNor = true → ∀ v < 2 ^ N, (allMask N ^^^ 1).testBit v = true →
      (target N true).testBit 0 ≠ (target N true).testBit v) ∧
    (isNor = false → ∀ i < N, 1 <<< i < 2 ^ N ∧
      ∀ v < 2 ^ N, (allMask N ^^^ target N false).testBit v = true →
        (target N false).testBit (1 <<< i) ≠ (target N false).testBit v) := by
  have hcase : ∀ N ∈ ([1, 2, 3, 4, 5] : List ℕ),
      (∀ v < 2 ^ N, (allMask N ^^^ 1).testBit v = true →
        (target N true).testBit 0 ≠ (target N true).testBit v) ∧
      (∀ i < N, 1 <<< i < 2 ^ N ∧
        ∀ v < 2 ^ N, (allMask N ^^^ target N false).testBit v = true →
          (target N false).testBit (1 <<< i) ≠ (target N false).testBit v) := by
    decide +kernel
  have hmem : N ∈ ([1, 2, 3, 4, 5] : List ℕ) := by
    rcases hN with ⟨h1, h2⟩
    interval_cases N <;> simp
  have ⟨ht, hf⟩ := hcase N hmem
  exact ⟨fun _ => ht, fun _ => hf⟩

lemma sepCheck_complete {N : ℕ} (hN : 1 ≤ N ∧ N ≤ 5) {isNor : Bool} {k : ℕ} {ws : List ℕ}
    (h : Live.live (basicOps N) (target N isNor) k ws.toFinset) :
    sepCheck N isNor ws = true := by
  have hb := target_bit_bounds N isNor hN
  unfold sepCheck
  cases isNor with
  | true =>
    simp only [ite_true, beq_iff_eq]
    by_contra hne
    obtain ⟨v, hv⟩ := exists_testBit_of_ne_zero hne
    have hvlt : v < 2 ^ N := by
      have : ∀ (xs : List ℕ) (init : ℕ), (∀ j, init.testBit j = true → j < 2 ^ N) →
          (agreeMask N 0 init xs).testBit v = true → v < 2 ^ N := by
        intro xs; induction xs with
        | nil => intro init hi h'; exact hi v h'
        | cons a r ih =>
          intro init hi h'
          exact ih _ (fun j hj => hi j (Bool.and_eq_true _ _ |>.mp (Nat.testBit_and _ _ _ ▸ hj)).1) h'
      exact this ws (allMask N ^^^ 1) (fun j hj => by
        rw [Nat.testBit_xor, testBit_allMask] at hj
        by_contra hge
        have hlt : decide (j < 2 ^ N) = false := decide_eq_false hge
        have h1 : (1 : ℕ).testBit j = false := by
          cases j with
          | zero => exact False.elim (hge (Nat.two_pow_pos N))
          | succ m => exact testBit_false_of_lt_two_pow (k := 1) (by omega) (by omega)
        simp [hlt, h1] at hj) hv
    obtain ⟨hinit, hall⟩ := testBit_agreeMask N 0 ws (allMask N ^^^ 1) v hvlt hv
    have htd : differs 0 v (target N true) := hb.1 rfl v hvlt hinit
    obtain ⟨w, hw, hdw⟩ := Live.live_separates (differs 0 v) htd
      (fun a b z hz => basicOps_differs (Nat.two_pow_pos N) hvlt hz) h
    exact hdw (hall w (List.mem_toFinset.mp hw)).symm
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi
    by_contra hne
    obtain ⟨v, hv⟩ := exists_testBit_of_ne_zero hne
    have htarget_lt : ∀ j, (target N false).testBit j = true → j < 2 ^ N := by
      have hc : ∀ N ∈ ([1, 2, 3, 4, 5] : List ℕ), target N false < 2 ^ (2 ^ N) := by decide +kernel
      have hmem : N ∈ ([1, 2, 3, 4, 5] : List ℕ) := by
        rcases hN with ⟨h1, h2⟩; interval_cases N <;> simp
      intro j hj
      by_contra hge
      have hf := testBit_false_of_lt_two_pow (hc N hmem) (Nat.le_of_not_lt hge)
      exact Bool.noConfusion (hj.symm.trans hf)
    have hvlt : v < 2 ^ N := by
      have : ∀ (xs : List ℕ) (init : ℕ), (∀ j, init.testBit j = true → j < 2 ^ N) →
          (agreeMask N (1 <<< i) init xs).testBit v = true → v < 2 ^ N := by
        intro xs; induction xs with
        | nil => intro init hi' h'; exact hi' v h'
        | cons a r ih =>
          intro init hi' h'
          exact ih _ (fun j hj => hi' j (Bool.and_eq_true _ _ |>.mp (Nat.testBit_and _ _ _ ▸ hj)).1) h'
      exact this ws (allMask N ^^^ target N false) (fun j hj => by
        rw [Nat.testBit_xor, testBit_allMask] at hj
        by_contra hge
        have h1 : decide (j < 2 ^ N) = false := decide_eq_false hge
        have h2 : (target N false).testBit j = false := by
          cases ht : (target N false).testBit j
          · rfl
          · exact False.elim (hge (htarget_lt j ht))
        simp [h1, h2] at hj) hv
    obtain ⟨hinit, hall⟩ := testBit_agreeMask N (1 <<< i) ws (allMask N ^^^ target N false) v hvlt hv
    have ⟨hult, htd⟩ := hb.2 rfl i hi
    have hdiff : differs (1 <<< i) v (target N false) := htd v hvlt hinit
    obtain ⟨w, hw, hdw⟩ := Live.live_separates (differs (1 <<< i) v) hdiff
      (fun a b z hz => basicOps_differs hult hvlt hz) h
    exact hdw (hall w (List.mem_toFinset.mp hw)).symm

-- ============================================================================
-- 5. Fast Binary Tree & Certificate Checker
-- ============================================================================
inductive BTree (α : Type) where
  | leaf (v : α)
  | node (l r : BTree α)

def BTree.getD {α : Type} (d : α) : BTree α → ℕ → α
  | .leaf v, _ => v
  | .node l r, n => if n % 2 == 0 then l.getD d (n / 2) else r.getD d (n / 2)

structure PermRec where
  N : ℕ
  fwd : List ℕ
  inv : List ℕ

def defaultPerm : PermRec := ⟨1, [0, 1], [0, 1]⟩

structure SMapRec where
  N : ℕ
  rem : ℕ
  isNor : Bool
  rows : List ℕ

def defaultSMap : SMapRec := ⟨1, 1, false, [0, 1]⟩

structure EntryHead where
  isBuild : Bool
  N : ℕ
  isNor : Bool
  k : ℕ
  ws : List ℕ
  deriving DecidableEq

def defaultEntry : EntryHead := ⟨false, 1, false, 0, []⟩

def checkPerm (p : PermRec) : Bool :=
  let M := 2 ^ p.N
  1 ≤ p.N && p.N ≤ 5 &&
  p.fwd.length == M && p.inv.length == M &&
  p.fwd.getD 0 1 == 0 &&
  p.fwd.all (· < M) && p.inv.all (· < M) &&
  (List.range M).all (fun i => p.fwd.getD (p.inv.getD i 0) 0 == i) &&
  mapRows (target p.N false) p.fwd == target p.N false &&
  mapRows (target p.N true) p.fwd == target p.N true

def checkSMap (s : SMapRec) : Bool :=
  let M := 2 ^ s.N
  let Mr := 2 ^ s.rem
  1 ≤ s.N && s.N ≤ 5 && 1 ≤ s.rem && s.rem ≤ 5 &&
  s.rows.length == Mr && s.rows.all (· < M) &&
  projMap s.rem s.rows (target s.N false) == some (target s.rem s.isNor)

def insertSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertSorted x (sortNat xs)

lemma insertSorted_perm (x : ℕ) (xs : List ℕ) : (insertSorted x xs).Perm (x :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons y ys ih =>
    unfold insertSorted
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap _ _ _)

lemma sortNat_perm (xs : List ℕ) : (sortNat xs).Perm xs := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (insertSorted_perm x _).trans (ih.cons x)

def isStrictSorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictSorted (b :: rest)

lemma isStrictSorted_nodup (xs : List ℕ) (h : isStrictSorted xs = true) : xs.Nodup := by
  have hlt : ∀ (a : ℕ) (ys : List ℕ), isStrictSorted (a :: ys) = true → ∀ y ∈ ys, a < y := by
    intro a ys
    induction ys generalizing a with
    | nil => intro _ _ hy; cases hy
    | cons b rs ih =>
      intro hs y hy
      simp only [isStrictSorted, Bool.and_eq_true, decide_eq_true_eq] at hs
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hs.1
      · exact Nat.lt_trans hs.1 (ih b hs.2 y hy)
  induction xs with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    refine List.nodup_cons.mpr ⟨fun ha => Nat.lt_irrefl a (hlt a rest h a ha), ?_⟩
    cases rest with
    | nil => exact List.nodup_nil
    | cons b rs =>
      simp only [isStrictSorted, Bool.and_eq_true] at h
      exact ih h.2

def dedupAdd (acc : List ℕ) (v : ℕ) : List ℕ :=
  if acc.contains v then acc else acc ++ [v]

def projScan (rem : ℕ) (rows : List ℕ) (ws : List ℕ) : ℕ × List ℕ :=
  ws.foldl (fun (z, acc) w =>
    match projMap rem rows w with
    | none => (z + 1, acc)
    | some v => (z, dedupAdd acc v)) (0, [])

def buildableLe1 (N tg : ℕ) (av : List ℕ) (k : ℕ) : Bool :=
  av.contains tg || (k ≥ 1 && av.any (fun a => av.any (fun b => (opsN N a b).contains tg)))

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: r => let s := subs r; s ++ s.map (a :: ·)

def zipAll {α β : Type} (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && zipAll p as bs
  | _, _ => false

def checkHint (entries : BTree EntryHead) (perms : BTree PermRec) (smaps : BTree SMapRec)
    (nP nS curId N : ℕ) (isNor : Bool) (k : ℕ) (ws : List ℕ) (h : ℕ) : Bool :=
  if h % 2 == 0 then
    let q := h / 2
    let tid := q % 512
    let pid := q / 512
    tid < curId && pid < nP &&
    let e := entries.getD defaultEntry tid
    let p := perms.getD defaultPerm pid
    !e.isBuild && e.N == N && e.isNor == isNor && k ≤ e.k &&
    ws.length == e.ws.length && p.N == N &&
    sortNat (ws.map (fun w => mapRows w p.fwd)) == e.ws
  else
    let q := h / 2
    let smIdx := q % 256
    let q1 := q / 256
    let tid1 := q1 % 512
    let pid := q1 / 512
    !isNor && smIdx < nS &&
    let sm := smaps.getD defaultSMap smIdx
    sm.N == N &&
    let (z, kept) := projScan sm.rem sm.rows ws
    if k < z then true
    else
      let rk := k - z
      if !sepCheck sm.rem sm.isNor kept then true
      else if rk ≤ 1 then !buildableLe1 sm.rem (target sm.rem sm.isNor) kept rk
      else
        tid1 ≥ 1 &&
        let tid := tid1 - 1
        tid < curId && pid < nP &&
        let e := entries.getD defaultEntry tid
        let p := perms.getD defaultPerm pid
        e.isBuild && e.N == sm.rem && e.isNor == sm.isNor && rk ≤ e.k && p.N == sm.rem &&
        kept.all (fun w => e.ws.contains (mapRows w p.fwd))

def checkEntry (entries : BTree EntryHead) (perms : BTree PermRec) (smaps : BTree SMapRec)
    (nP nS id : ℕ) (hs : List ℕ) : Bool :=
  let e := entries.getD defaultEntry id
  let tg := target e.N e.isNor
  1 ≤ e.N && e.N ≤ 5 && isStrictSorted e.ws && e.ws.all (fun w => canonN e.N w == w) &&
  if e.isBuild then
    !(e.ws.contains tg) &&
    let children := (subs e.ws).filter (fun s => 2 ≤ s.length && s.length ≤ e.k + 1 && sepCheck e.N e.isNor s)
    if e.k ≤ 1 then
      hs.isEmpty && children.all (fun s => !(s == [tg]) && !(e.k == 1 && s.length == 2 && buildableLe1 e.N tg s 1))
    else
      zipAll (checkHint entries perms smaps nP nS id e.N e.isNor e.k) children hs
  else
    !(e.ws == [tg]) &&
    if e.k == 0 then hs.isEmpty
    else
      let k' := e.k - 1
      let allNext := (pairs e.ws).flatMap fun (a, b, r) =>
        (opsN e.N a b).flatMap fun z =>
          if e.ws.contains z then []
          else (keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ k' then some (z :: kept) else none
      let children := allNext.filter (sepCheck e.N e.isNor)
      if k' ≤ 1 then
        hs.isEmpty && children.all (fun s => !(s == [tg]) && !(k' == 1 && s.length == 2 && buildableLe1 e.N tg s 1))
      else
        zipAll (checkHint entries perms smaps nP nS id e.N e.isNor k') children hs

-- ============================================================================
-- 6. Soundness of the Certificate Checker
-- ============================================================================
lemma agreeMask_testBit (N u : ℕ) (ws : List ℕ) : ∀ (init v : ℕ),
    (agreeMask N u init ws).testBit v =
      (init.testBit v && ws.all (fun w => (if w.testBit u then w else invN N w).testBit v)) := by
  induction ws with
  | nil => intro init v; simp [agreeMask]
  | cons a rest ih =>
    intro init v
    simp only [agreeMask, List.foldl_cons, List.all_cons]
    rw [← agreeMask, ih, Nat.testBit_and, Bool.and_assoc]

lemma agreeMask_mono {N u init : ℕ} {xs ys : List ℕ} (hsub : ∀ w ∈ xs, w ∈ ys)
    (h0 : agreeMask N u init xs = 0) : agreeMask N u init ys = 0 := by
  apply Nat.eq_of_testBit_eq; intro v
  rw [Nat.zero_testBit, agreeMask_testBit]
  have hv := congrArg (fun n => n.testBit v) h0
  rw [Nat.zero_testBit, agreeMask_testBit] at hv
  cases hi : init.testBit v with
  | false => rfl
  | true =>
    simp only [hi, Bool.true_and] at hv ⊢
    cases hy : ys.all (fun w => (if w.testBit u then w else invN N w).testBit v) with
    | false => rfl
    | true =>
      exfalso
      have hxt : xs.all (fun w => (if w.testBit u then w else invN N w).testBit v) = true :=
        List.all_eq_true.mpr (fun w hw => List.all_eq_true.mp hy w (hsub w hw))
      exact Bool.noConfusion (hxt.symm.trans hv)

lemma sepCheck_mono {N : ℕ} {isNor : Bool} {xs ys : List ℕ} (hsub : ∀ w ∈ xs, w ∈ ys)
    (h : sepCheck N isNor xs = true) : sepCheck N isNor ys = true := by
  unfold sepCheck at h ⊢
  cases isNor with
  | true =>
    simp only [ite_true, beq_iff_eq] at h ⊢
    exact agreeMask_mono hsub h
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.all_eq_true, beq_iff_eq] at h ⊢
    intro i hi
    exact agreeMask_mono hsub (h i hi)

lemma zipAll_sound {α β : Type} {p : α → β → Bool} {xs : List α} {ys : List β}
    (h : zipAll p xs ys = true) : ∀ x ∈ xs, ∃ y, p x y = true := by
  induction xs generalizing ys with
  | nil => intro _ hx; cases hx
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipAll] at h
    | cons y ys =>
      simp only [zipAll, Bool.and_eq_true] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨y, h.1⟩
      · exact ih h.2 a ha

lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with hax | ha'
    · subst hax
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with hbx | hb'
      · subst hbx
        obtain ⟨r, hm, hp⟩ := pick_one ha'
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha' hb'
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

lemma recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, henne]
    by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, not_or] at habr ⊢
      exact ⟨habr.1.2, habr.2.2⟩
    · ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, henne]
      by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, henne]
    by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp only [List.mem_toFinset, henne]
    by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all

lemma filter_mem_subs {α : Type} (p : α → Bool) : ∀ xs : List α, xs.filter p ∈ subs xs
  | [] => by simp [subs]
  | a :: rest => by
    unfold subs
    cases hp : p a
    · simp [List.filter_cons, hp, filter_mem_subs p rest]
    · simp only [List.filter_cons, hp, ite_true, List.mem_append, List.mem_map]
      right; exact ⟨rest.filter p, filter_mem_subs p rest, rfl⟩

lemma singleton_list {α : Type} [DecidableEq α] {ws : List α} {g : α}
    (hn : ws.Nodup) (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

lemma live_singleton {α : Type} [DecidableEq α] {ops : α → α → Finset α} {g w : α} {k : ℕ}
    (h : Live.live ops g k {w}) : w = g := by
  induction k with
  | zero =>
    change ({w} : Finset α) = {g} at h
    exact Finset.singleton_injective h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, _⟩
    · exact ih skip
    · simp at ha hb; exact False.elim (hab (ha.trans hb.symm))

lemma live_zero_or_one {N tg k : ℕ} {ws : List ℕ} (hn : ws.Nodup)
    (hk : k ≤ 1) (h : Live.live (basicOps N) tg k ws.toFinset) :
    ws = [tg] ∨ (k = 1 ∧ ws.length = 2 ∧ buildableLe1 N tg ws 1 = true) := by
  cases k with
  | zero => left; exact singleton_list hn h
  | succ k' =>
    have hk' : k' = 0 := by omega
    subst hk'
    rcases Live.first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, tail⟩
    · left; exact singleton_list hn done
    · change insert z rest = {tg} at tail
      have hztg : z = tg := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
      have hrempty : rest = ∅ := by
        ext x; simp only [Finset.notMem_empty, iff_false]
        intro hx
        have hxtg : x = tg := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_of_mem hx)
        rw [← hztg] at hxtg; subst hxtg
        exact hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      rw [hrempty] at hs
      have hlen : ws.length = 2 := by
        have hc := List.toFinset_card_of_nodup hn
        rw [hs, Finset.card_insert_of_notMem (by simp [hab]),
          Finset.card_insert_of_notMem (by simp), Finset.card_empty] at hc
        omega
      right; refine ⟨rfl, hlen, ?_⟩
      simp only [buildableLe1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.contains_eq_mem]
      right; refine ⟨by omega, a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, ?_⟩
      rw [← hztg]
      exact List.mem_toFinset.mp hz

lemma build_zero_or_one {N tg k : ℕ} {av : List ℕ} (hk : k ≤ 1)
    (h : Live.build (basicOps N) tg k av.toFinset) :
    buildableLe1 N tg av k = true := by
  cases k with
  | zero =>
    simp only [buildableLe1, List.contains_eq_mem, Bool.or_eq_true, decide_eq_true_eq]
    left; exact List.mem_toFinset.mp h
  | succ k' =>
    have hk' : k' = 0 := by omega
    subst hk'
    simp only [buildableLe1, List.contains_eq_mem, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    rcases h with skip | ⟨a, ha, b, hb, _, z, hz, tail⟩
    · left; exact List.mem_toFinset.mp skip
    · rcases Finset.mem_insert.mp tail with rfl | hmem
      · right; exact ⟨by omega, a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb,
          List.mem_toFinset.mp hz⟩
      · left; exact List.mem_toFinset.mp hmem

lemma projScan_spec (rem : ℕ) (rows : List ℕ) (ws : List ℕ) (hn : ws.Nodup) :
    let sc := projScan rem rows ws
    sc.1 = Live.zeros (projMap rem rows) ws.toFinset ∧
    sc.2.toFinset = Live.kept (projMap rem rows) ws.toFinset ∧
    ∀ w ∈ sc.2, canonN rem w = w := by
  have aux : ∀ (l : List ℕ) (z0 : ℕ) (acc0 : List ℕ), l.Nodup →
      (∀ w ∈ acc0, canonN rem w = w) →
      let r := l.foldl (fun (z, acc) w =>
        match projMap rem rows w with
        | none => (z + 1, acc)
        | some v => (z, dedupAdd acc v)) (z0, acc0)
      r.1 = z0 + Live.zeros (projMap rem rows) l.toFinset ∧
      r.2.toFinset = acc0.toFinset ∪ Live.kept (projMap rem rows) l.toFinset ∧
      ∀ w ∈ r.2, canonN rem w = w := by
    intro l
    induction l with
    | nil =>
      intro z0 acc0 _ hacc
      exact ⟨by simp [Live.zeros], by simp [Live.kept], hacc⟩
    | cons a rest ih =>
      intro z0 acc0 hnd hacc
      obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
      have ha' : a ∉ rest.toFinset := by simpa using ha
      simp only [List.foldl_cons, List.toFinset_cons]
      cases hp : projMap rem rows a with
      | none =>
        have hres := ih (z0 + 1) acc0 hnd' hacc
        refine ⟨?_, ?_, hres.2.2⟩
        · rw [hres.1, Live.zeros_none hp ha']; omega
        · rw [hres.2.1, Live.kept_insert, hp]; simp
      | some v =>
        have hv : canonN rem v = v := by
          dsimp only [projMap] at hp
          split at hp
          · cases hp
          · injection hp with hv'
            rw [← hv', canonN_canonN]
        have hda_mem : ∀ x, x ∈ dedupAdd acc0 v ↔ x = v ∨ x ∈ acc0 := by
          intro x; unfold dedupAdd
          split
          · rename_i hc
            have hvm : v ∈ acc0 := List.contains_iff_mem.mp hc
            constructor
            · intro hx; exact Or.inr hx
            · rintro (rfl | hx); exact hvm; exact hx
          · simp [or_comm]
        have hda_fin : (dedupAdd acc0 v).toFinset = insert v acc0.toFinset := by
          ext x; simp [hda_mem]
        have hda_can : ∀ w ∈ dedupAdd acc0 v, canonN rem w = w := by
          intro w hw
          rcases (hda_mem w).mp hw with rfl | hw
          · exact hv
          · exact hacc w hw
        have hres := ih z0 (dedupAdd acc0 v) hnd' hda_can
        refine ⟨?_, ?_, hres.2.2⟩
        · rw [hres.1, Live.zeros_some hp]
        · rw [hres.2.1, hda_fin, Live.kept_insert, hp]
          ext x; simp
  have h := aux ws 0 [] hn (by simp)
  simpa [projScan] using h

lemma perm_map_live {p : PermRec} (hp : checkPerm p = true) {isNor : Bool} {k : ℕ} {s : Finset ℕ}
    (hcan : ∀ w ∈ s, canonN p.N w = w)
    (h : Live.live (basicOps p.N) (target p.N isNor) k s) :
    Live.live (basicOps p.N) (target p.N isNor) k (s.image (fun w => mapRows w p.fwd)) := by
  simp only [checkPerm, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN1, hN5⟩, hflen⟩, hilen⟩, hf0⟩, hfbnd⟩, hibnd⟩, hcancel⟩, htf⟩, htt⟩ := hp
  have hf0' : p.fwd.getD 0 0 = 0 := by
    have hpos : 0 < p.fwd.length := by rw [hflen]; exact Nat.two_pow_pos p.N
    rw [List.getD_eq_getElem _ _ hpos] at hf0 ⊢; exact hf0
  have htg : mapRows (target p.N isNor) p.fwd = target p.N isNor := by
    cases isNor <;> assumption
  rw [← htg]
  apply Live.map_live (ops := basicOps p.N) (ops' := basicOps p.N) (fun w => canonN p.N w = w) (fun w => mapRows w p.fwd)
  · intro x y hx hy heq
    have hx' := mapRows_inv_cancel p.N x p.fwd p.inv hflen hilen hcancel hibnd hx
    have hy' := mapRows_inv_cancel p.N y p.fwd p.inv hflen hilen hcancel hibnd hy
    rw [← hx', ← hy', heq]
  · intro a b z hz; exact basicOps_canon hz
  · intro a b z _ _ hz
    simp only [basicOps, opsN, rawOps, List.mem_toFinset, List.mem_filter, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq] at hz ⊢
    obtain ⟨⟨u, hu, rfl⟩, hnz⟩ := hz
    have hne0 : mapRows (canonN p.N u) p.fwd ≠ 0 := by
      intro hc
      have h0 := mapRows_inv_cancel p.N (canonN p.N u) p.fwd p.inv hflen hilen hcancel hibnd (canonN_canonN p.N u)
      rw [hc] at h0
      have hmr0 : ∀ f : List ℕ, mapRows 0 f = 0 := by
        intro f; induction f with
        | nil => rfl
        | cons _ r ih => simp [mapRows, ih]
      rw [hmr0] at h0
      exact hnz h0.symm
    refine ⟨?_, hne0⟩
    rw [mapRows_canon_zero p.N u p.fwd hflen hfbnd hf0']
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨mapRows a p.fwd &&& mapRows b p.fwd, Or.inl rfl, by rw [mapRows_and]⟩
    · exact ⟨mapRows a p.fwd &&& invN p.N (mapRows b p.fwd), Or.inr (Or.inl rfl),
        by rw [mapRows_and, mapRows_invN p.N p.N b p.fwd hflen hfbnd]⟩
    · exact ⟨invN p.N (mapRows a p.fwd) &&& mapRows b p.fwd, Or.inr (Or.inr (Or.inl rfl)),
        by rw [mapRows_and, mapRows_invN p.N p.N a p.fwd hflen hfbnd]⟩
    · exact ⟨invN p.N (mapRows a p.fwd) &&& invN p.N (mapRows b p.fwd), Or.inr (Or.inr (Or.inr rfl)),
        by rw [mapRows_and, mapRows_invN p.N p.N a p.fwd hflen hfbnd, mapRows_invN p.N p.N b p.fwd hflen hfbnd]⟩
  · exact hcan
  · exact h

lemma perm_map_build {p : PermRec} (hp : checkPerm p = true) {isNor : Bool} {k : ℕ} {av : Finset ℕ}
    (hcan : ∀ w ∈ av, canonN p.N w = w)
    (h : Live.build (basicOps p.N) (target p.N isNor) k av) :
    Live.build (basicOps p.N) (target p.N isNor) k (av.image (fun w => mapRows w p.fwd)) := by
  obtain ⟨s, hs, hl⟩ := Live.compress h
  have hml := perm_map_live hp (fun w hw => hcan w (hs hw)) hl
  have live_to_build : ∀ {m : ℕ} {t : Finset ℕ},
      Live.live (basicOps p.N) (target p.N isNor) m t →
      Live.build (basicOps p.N) (target p.N isNor) m t := by
    intro m; induction m with
    | zero => intro t ht; change t = {_} at ht; rw [ht]; simp [Live.build]
    | succ m ih =>
      intro t ht
      rcases ht with skip | ⟨a, ha, b, hb, hab, z, hz, _, rest, rfl, tail⟩
      · exact Or.inl (ih skip)
      · refine Or.inr ⟨a, ha, b, hb, hab, z, hz, Live.build_mono ?_ (ih tail)⟩
        intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto
  exact Live.build_mono (Finset.image_subset_image hs) (live_to_build hml)

def EntryClaim (e : EntryHead) : Prop :=
  if e.isBuild then
    ¬ Live.build (basicOps e.N) (target e.N e.isNor) e.k e.ws.toFinset
  else
    ¬ Live.live (basicOps e.N) (target e.N e.isNor) e.k e.ws.toFinset

lemma checkHint_sound (entries : BTree EntryHead) (perms : BTree PermRec) (smaps : BTree SMapRec)
    (nP nS curId N : ℕ) (isNor : Bool) (k : ℕ) (ws : List ℕ) (h : ℕ)
    (hP : ∀ i < nP, checkPerm (perms.getD defaultPerm i) = true)
    (hS : ∀ i < nS, checkSMap (smaps.getD defaultSMap i) = true)
    (hIH : ∀ j < curId, EntryClaim (entries.getD defaultEntry j))
    (hnd : ws.Nodup) (hcan : ∀ w ∈ ws, canonN N w = w)
    (hok : checkHint entries perms smaps nP nS curId N isNor k ws h = true) :
    ¬ Live.live (basicOps N) (target N isNor) k ws.toFinset := by
  intro hlive
  unfold checkHint at hok
  split at hok
  · -- REF hint
    dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨htid, hpid⟩, ⟨⟨⟨⟨⟨⟨hnb, heN⟩, heNor⟩, hkle⟩, _⟩, hpN⟩, hsort⟩⟩ := hok
    set e := entries.getD defaultEntry ((h / 2) % 512)
    set p := perms.getD defaultPerm ((h / 2) / 512)
    have hpc : checkPerm p = true := hP _ hpid
    have hcl : EntryClaim e := hIH _ htid
    simp only [EntryClaim, hnb, Bool.false_eq_true, ite_false] at hcl
    rw [← hpN] at hlive hcan
    have hml := perm_map_live hpc (fun w hw => hcan w (List.mem_toFinset.mp hw)) hlive
    have himg : ws.toFinset.image (fun w => mapRows w p.fwd) = e.ws.toFinset := by
      ext x
      simp only [Finset.mem_image, List.mem_toFinset, ← hsort, (sortNat_perm _).mem_iff, List.mem_map]
    rw [himg, hpN, ← heN, ← heNor] at hml
    exact hcl (Live.live_mono_k hkle hml)
  · -- PROJ hint
    dsimp only at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨hisNor, hsmIdx⟩, hsmN, hrest⟩ := hok
    set sm := smaps.getD defaultSMap ((h / 2) % 256)
    have hsmc : checkSMap sm = true := hS _ hsmIdx
    simp only [checkSMap, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hsmc
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hrem1⟩, hrem5⟩, hlen⟩, hbnd⟩, htg⟩ := hsmc
    have hproj := projMap_projects sm.N sm.rem sm.rows hlen hbnd
    have hps := projScan_spec sm.rem sm.rows ws hnd
    set sc := projScan sm.rem sm.rows ws
    have hz : sc.1 = Live.zeros (projMap sm.rem sm.rows) ws.toFinset := hps.1
    have hkept : sc.2.toFinset = Live.kept (projMap sm.rem sm.rows) ws.toFinset := hps.2.1
    have hkcan : ∀ w ∈ sc.2, canonN sm.rem w = w := hps.2.2
    rw [hisNor, ← hsmN] at hlive
    have hzb := Live.zeros_budget htg hproj hlive
    rw [← hz] at hzb
    by_cases hkz : k < sc.1
    · omega
    · simp only [hkz, ite_false] at hrest
      have hbuild : Live.build (basicOps sm.rem) (target sm.rem sm.isNor) (k - sc.1) sc.2.toFinset := by
        rw [hkept]
        exact Live.project_live htg hproj hlive (k - sc.1) (by omega)
      cases hsep : sepCheck sm.rem sm.isNor sc.2 with
      | false =>
        obtain ⟨sub, hsub, hlsub⟩ := Live.compress hbuild
        have hsep_sub := sepCheck_complete ⟨hrem1, hrem5⟩ (ws := sub.toList) (by simpa using hlsub)
        have hsep_sc := sepCheck_mono (fun w hw => List.mem_toFinset.mp (hsub (Finset.mem_toList.mp hw))) hsep_sub
        exact Bool.noConfusion (hsep.symm.trans hsep_sc)
      | true =>
        simp only [hsep, Bool.true_eq_false, ite_false] at hrest
        by_cases hrk1 : k - sc.1 ≤ 1
        · simp only [hrk1, ite_true, Bool.not_eq_true'] at hrest
          have hb1 := build_zero_or_one hrk1 hbuild
          exact Bool.noConfusion (hrest.symm.trans hb1)
        · simp only [hrk1, ite_false, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
            List.all_eq_true, List.contains_eq_mem] at hrest
          obtain ⟨_, ⟨htid, hpid⟩, ⟨⟨⟨⟨⟨heB, heN⟩, heNor⟩, hrkle⟩, hpN⟩, hall⟩⟩ := hrest
          set tid := ((h / 2) / 256) % 512 - 1
          set pid := ((h / 2) / 256) / 512
          set e := entries.getD defaultEntry tid
          set p := perms.getD defaultPerm pid
          have hpc : checkPerm p = true := hP _ hpid
          have hcl : EntryClaim e := hIH _ htid
          simp only [EntryClaim, heB, ite_true] at hcl
          rw [← hpN] at hbuild hkcan
          have hmb := perm_map_build hpc (fun w hw => hkcan w (List.mem_toFinset.mp hw)) hbuild
          have hsub : sc.2.toFinset.image (fun w => mapRows w p.fwd) ⊆ e.ws.toFinset := by
            intro x hx
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
            exact List.mem_toFinset.mpr (hall w (List.mem_toFinset.mp hw))
          have hbe := Live.build_mono hsub hmb
          rw [hpN, ← heN, ← heNor] at hbe
          exact hcl (Live.build_mono_k hrkle hbe)

lemma checkEntry_sound (entries : BTree EntryHead) (perms : BTree PermRec) (smaps : BTree SMapRec)
    (nP nS id : ℕ) (hs : List ℕ)
    (hP : ∀ i < nP, checkPerm (perms.getD defaultPerm i) = true)
    (hS : ∀ i < nS, checkSMap (smaps.getD defaultSMap i) = true)
    (hIH : ∀ j < id, EntryClaim (entries.getD defaultEntry j))
    (hok : checkEntry entries perms smaps nP nS id hs = true) :
    EntryClaim (entries.getD defaultEntry id) := by
  unfold checkEntry at hok
  dsimp only at hok
  generalize entries.getD defaultEntry id = e at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hN1, hN5⟩, hsort⟩, hcan⟩, hbody⟩ := hok
  have hnd : e.ws.Nodup := isStrictSorted_nodup e.ws hsort
  unfold EntryClaim
  cases hB : e.isBuild with
  | true =>
    simp only [hB, ite_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem] at hbody ⊢
    obtain ⟨hntg, hch⟩ := hbody
    intro hbuild
    obtain ⟨s, hs_sub, hlive⟩ := Live.compress hbuild
    let sub := e.ws.filter (fun a => decide (a ∈ s))
    have hsub_sub : sub.Sublist e.ws := List.filter_sublist
    have hsub_nd : sub.Nodup := hnd.sublist hsub_sub
    have hsub_fin : sub.toFinset = s := by
      ext a; simp only [sub, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs_sub ha), ha⟩⟩
    rw [← hsub_fin] at hlive
    have hlen_le : sub.length ≤ e.k + 1 := by
      have hc := Live.live_card hlive
      rwa [List.toFinset_card_of_nodup hsub_nd] at hc
    have hsep : sepCheck e.N e.isNor sub = true := sepCheck_complete ⟨hN1, hN5⟩ hlive
    have hlen_ge2 : 2 ≤ sub.length := by
      by_contra hlt
      cases hsub_eq : sub with
      | nil =>
        rw [hsub_eq] at hsep
        have hsep0 : sepCheck e.N e.isNor [] = false := by
          have : ∀ N ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ b : Bool, sepCheck N b [] = false := by decide +kernel
          have hmem : e.N ∈ ([1, 2, 3, 4, 5] : List ℕ) := by interval_cases e.N <;> simp
          exact this e.N hmem e.isNor
        exact Bool.noConfusion (hsep0.symm.trans hsep)
      | cons w rest =>
        cases hrest_eq : rest with
        | nil =>
          rw [hsub_eq, hrest_eq] at hlive hsub_sub
          have heq := live_singleton (by simpa using hlive)
          have hwmem : w ∈ e.ws := hsub_sub.subset List.mem_cons_self
          exact absurd (heq ▸ hwmem) (of_decide_eq_false hntg)
        | cons _ _ =>
          rw [hsub_eq, hrest_eq] at hlt
          simp at hlt
    have hmem_ch : sub ∈ (subs e.ws).filter
        (fun s => 2 ≤ s.length && s.length ≤ e.k + 1 && sepCheck e.N e.isNor s) := by
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨filter_mem_subs _ e.ws, ⟨hlen_ge2, hlen_le⟩, hsep⟩
    by_cases hk1 : e.k ≤ 1
    · simp only [hk1, ite_true, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hch
      have hsub_ok := hch.2 sub hmem_ch
      rcases live_zero_or_one hsub_nd hk1 hlive with h1 | ⟨hk, hl2, hb1⟩
      · simp [h1] at hsub_ok
      · simp [hk, hl2, hb1] at hsub_ok
    · simp only [hk1, ite_false] at hch
      obtain ⟨hint, hhint⟩ := zipAll_sound hch sub hmem_ch
      exact checkHint_sound entries perms smaps nP nS id e.N e.isNor e.k sub hint hP hS hIH
        hsub_nd (fun w hw => hcan w (hsub_sub.subset hw)) hhint hlive
  | false =>
    simp only [hB, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.not_eq_true'] at hbody ⊢
    obtain ⟨hneq, hrest⟩ := hbody
    intro hlive
    cases hk0 : e.k with
    | zero =>
      rw [hk0] at hlive
      have hs := singleton_list hnd hlive
      simp [hs] at hneq
    | succ k' =>
      rw [hk0] at hlive hrest
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] at hrest
      rcases Live.first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
      · have hs := singleton_list hnd done
        simp [hs] at hneq
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go : ∀ {a b : ℕ}, (a, b, r) ∈ pairs e.ws → e.ws.Perm (a :: b :: r) →
            e.ws.toFinset = insert a (insert b needed) → z ∈ basicOps e.N a b → False := by
          intro a b hpair hperm hset hop
          obtain ⟨kept, hk_mem, hnk, hfin⟩ := recover_kept hperm hnd hset
          have hznot : z ∉ e.ws := fun hu => hout (List.mem_toFinset.mpr hu)
          have hzkept : z ∉ kept := fun hu =>
            hznot (List.mem_toFinset.mp (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))))
          have hnd_next : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzkept, hnk⟩
          have hl_next : Live.live (basicOps e.N) (target e.N e.isNor) k' (z :: kept).toFinset := by
            simpa [hfin] using tail
          have hcard := Live.live_card hl_next
          rw [List.toFinset_card_of_nodup hnd_next, List.length_cons] at hcard
          have hklen : kept.length ≤ k' := by omega
          have hsep : sepCheck e.N e.isNor (z :: kept) = true := sepCheck_complete ⟨hN1, hN5⟩ hl_next
          have hmem_all : (z :: kept) ∈ ((pairs e.ws).flatMap fun (a, b, r) =>
              (opsN e.N a b).flatMap fun z =>
                if e.ws.contains z then []
                else (keepChoices a b r).filterMap fun kept =>
                  if kept.length ≤ k' then some (z :: kept) else none).filter
              (sepCheck e.N e.isNor) := by
            rw [List.mem_filter]
            refine ⟨?_, hsep⟩
            rw [List.mem_flatMap]
            refine ⟨(a, b, r), hpair, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨z, List.mem_toFinset.mp hop, ?_⟩
            have hnc : e.ws.contains z = false := Bool.eq_false_iff.mpr (fun hc => hznot (List.contains_iff_mem.mp hc))
            rw [hnc]; simp only [Bool.false_eq_true, ite_false, List.mem_filterMap]
            exact ⟨kept, hk_mem, by simp [hklen]⟩
          have hcan_next : ∀ w ∈ z :: kept, canonN e.N w = w := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact basicOps_canon hop
            · exact hcan w (List.mem_toFinset.mp (hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw))))
          by_cases hk1 : k' ≤ 1
          · simp only [hk1, ite_true, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hrest
            have hok_n := hrest.2 (z :: kept) hmem_all
            rcases live_zero_or_one hnd_next hk1 hl_next with h1 | ⟨hk, hl2, hb1⟩
            · simp [h1] at hok_n
            · simp [hk, hl2, hb1] at hok_n
          · simp only [hk1, ite_false] at hrest
            obtain ⟨hint, hhint⟩ := zipAll_sound hrest (z :: kept) hmem_all
            exact checkHint_sound entries perms smaps nP nS id e.N e.isNor k' (z :: kept) hint
              hP hS hIH hnd_next hcan_next hhint hl_next
        rcases hm with direct | swap
        · exact go direct hp hs_eq hz
        · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm])
            (basicOps_swap e.N a b ▸ hz)

lemma cert_all_sound (entries : BTree EntryHead) (perms : BTree PermRec) (smaps : BTree SMapRec)
    (nE nP nS : ℕ) (chunks : List (ℕ × List ℕ))
    (hP : (List.range nP).all (fun i => checkPerm (perms.getD defaultPerm i)) = true)
    (hS : (List.range nS).all (fun i => checkSMap (smaps.getD defaultSMap i)) = true)
    (hids : chunks.map Prod.fst = List.range nE)
    (hok : chunks.all (fun p => checkEntry entries perms smaps nP nS p.1 p.2) = true) :
    ∀ i < nE, EntryClaim (entries.getD defaultEntry i) := by
  have hP' : ∀ i < nP, checkPerm (perms.getD defaultPerm i) = true := fun i hi =>
    List.all_eq_true.mp hP i (List.mem_range.mpr hi)
  have hS' : ∀ i < nS, checkSMap (smaps.getD defaultSMap i) = true := fun i hi =>
    List.all_eq_true.mp hS i (List.mem_range.mpr hi)
  have hex : ∀ i < nE, ∃ hs, checkEntry entries perms smaps nP nS i hs = true := by
    intro i hi
    have hmem : i ∈ chunks.map Prod.fst := hids ▸ List.mem_range.mpr hi
    obtain ⟨⟨j, hs⟩, hjmem, hj⟩ := List.mem_map.mp hmem
    simp only at hj; subst hj
    exact ⟨hs, List.all_eq_true.mp hok (j, hs) hjmem⟩
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    obtain ⟨hs, hchk⟩ := hex i hi
    exact checkEntry_sound entries perms smaps nP nS i hs hP' hS'
      (fun j hj => ih j hj (lt_trans hj hi)) hchk

-- ============================================================================
-- 7. Circuit Compilation & 1-NOT-Gate Lower Bound (adapted from L_meta_671)
-- ============================================================================
def ex1_5 (x : Fin 5 → Bool) : Bool := decide (((List.ofFn x).count true) = 1)

def rawInputs5 : List ℕ := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def negGate (g : Gate) : Bool := match g.op with | GateOp.not => true | _ => false

def binaries : List Gate → ℕ
  | [] => 0
  | g :: gs => if negGate g then binaries gs else binaries gs + 1

def ordered (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i : Fin u.length, u.getD i.val false = true → v.getD i.val false = true

lemma getOrdered {u v : List Bool} (h : ordered u v) (i : ℕ) :
    u.getD i false = true → v.getD i false = true := by
  by_cases hi : i < u.length
  · exact h.2 ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by omega : u.length ≤ i)]; simp

lemma appendOrdered {u v : List Bool} {a b : Bool} (h : ordered u v) (hab : a = true → b = true) :
    ordered (u ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i.val < u.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact getOrdered h _
  · have len := i.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at len
    have e : i.val = u.length := by omega
    rw [e]; simpa [h.1] using hab

lemma stepOrdered {u v : List Bool} (h : ordered u v) (g : Gate) (ok : legal g)
    (hn : negGate g = false) : ordered (step u g) (step v g) := by
  apply appendOrdered h
  obtain ⟨op, args⟩ := g
  have ops := ok.1
  change op = .and ∨ op = .or ∨ op = .not at ops
  rcases ops with rfl | rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.forall_mem_map, id_eq]
    intro hall i hi; exact getOrdered h i (hall i hi)
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨v₀, hm, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact ⟨_, List.mem_map_of_mem hi, getOrdered h i hv⟩
  · simp [negGate] at hn

lemma binaries_le : ∀ gs : List Gate, binaries gs ≤ gs.length
  | [] => by decide
  | g :: gs => by
    have h := binaries_le gs
    cases hn : negGate g <;> simp [binaries, hn] <;> omega

lemma oneFall (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (u v : List Bool)
    (h : ordered u v) (fall : ¬ ordered (gs.foldl step u) (gs.foldl step v)) :
    binaries gs + 1 ≤ gs.length := by
  induction gs generalizing u v with
  | nil => exact False.elim (fall h)
  | cons g gs ih =>
    have ht : ∀ g' ∈ gs, legal g' := fun g' hm => hg g' (List.mem_cons_of_mem _ hm)
    cases hn : negGate g with
    | false =>
      have hh := ih ht _ _ (stepOrdered h g (hg g List.mem_cons_self) hn) fall
      simp [binaries, hn]; omega
    | true => simpa [binaries, hn] using binaries_le gs

def row5 (v : ℕ) (i : Fin 5) : Bool := v.testBit i.val

lemma ex1_5_fall (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = ex1_5 x) :
    binaries C.gates + 1 ≤ C.gates.length := by
  apply oneFall C.gates hg (List.ofFn (row5 1)) (List.ofFn (row5 3))
  · unfold ordered; decide
  · intro h
    have h' := getOrdered h C.output
    change (C.eval (List.ofFn (row5 1)) = true → C.eval (List.ofFn (row5 3)) = true) at h'
    rw [he, he] at h'
    have h1 : ex1_5 (row5 1) = true := by decide
    have h3 : ex1_5 (row5 3) = false := by decide
    rw [h1, h3] at h'
    exact Bool.noConfusion (h' rfl)

def bit5 (k : Fin 32) (z : ℕ) : Bool := z.testBit k.val

def possible5 (w : List ℕ) (z : ℕ) : Prop :=
  z = 0 ∨ z = allMask 5 ∨
  ∃ u ∈ w, z = u ∨ z = invN 5 u ∨ ∃ v ∈ w, z = (u &&& v) ∨ z = (u ||| v)

lemma read_bit5 (w : List ℕ) (i : ℕ) (k : Fin 32) :
    (w.map (bit5 k)).getD i false = bit5 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit5]

lemma read_wire5 (w : List ℕ) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

lemma atom5 {ws : List ℕ} {x : ℕ} (hx : x = 0 ∨ x ∈ ws) :
    possible5 ws x ∧ possible5 ws (invN 5 x) := by
  rcases hx with rfl | hx
  · exact ⟨Or.inl rfl, Or.inr (Or.inl (by decide))⟩
  · exact ⟨Or.inr (Or.inr ⟨x, hx, Or.inl rfl⟩), Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inl rfl)⟩)⟩

lemma pair5 {ws : List ℕ} {x y : ℕ} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible5 ws (x &&& y) ∧ possible5 ws (x ||| y) := by
  rcases hx with rfl | hx
  · simp only [Nat.zero_and, Nat.zero_or]
    exact ⟨Or.inl rfl, (atom5 hy).1⟩
  rcases hy with rfl | hy
  · simp only [Nat.and_zero, Nat.or_zero]
    exact ⟨Or.inl rfl, (atom5 (Or.inr hx)).1⟩
  · exact ⟨Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inr ⟨y, hy, Or.inl rfl⟩)⟩),
           Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inr ⟨y, hy, Or.inr rfl⟩)⟩)⟩

lemma gate_table5 (w : List ℕ) (g : Gate) (hg : legal g) :
    ∃ z, possible5 w z ∧ ∀ k : Fin 32, step (w.map (bit5 k)) g = (w ++ [z]).map (bit5 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨allMask 5, Or.inr (Or.inl rfl), fun k => ?_⟩
      simp [step, GateOp.eval, bit5, testBit_allMask, k.isLt]
    · refine ⟨0, Or.inl rfl, fun k => ?_⟩
      simp [step, GateOp.eval, bit5]
    · refine ⟨allMask 5, Or.inr (Or.inl rfl), fun k => ?_⟩
      simp [step, GateOp.eval, bit5, testBit_allMask, k.isLt]
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · refine ⟨_, (atom5 (read_wire5 w i)).1, fun k => ?_⟩
        simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval]
      · refine ⟨_, (atom5 (read_wire5 w i)).1, fun k => ?_⟩
        simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval]
      · refine ⟨_, (atom5 (read_wire5 w i)).2, fun k => ?_⟩
        simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval, bit5, testBit_invN, k.isLt]
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · refine ⟨_, (pair5 (read_wire5 w i) (read_wire5 w j)).1, fun k => ?_⟩
          simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval, bit5, Nat.testBit_and]
        · refine ⟨_, (pair5 (read_wire5 w i) (read_wire5 w j)).2, fun k => ?_⟩
          simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval, bit5, Nat.testBit_or]
        · refine ⟨_, (atom5 (read_wire5 w i)).2, fun k => ?_⟩
          simp only [step, List.map_cons, List.map_nil, read_bit5]; simp [GateOp.eval, bit5, testBit_invN, k.isLt]

def represents5 (av : Finset ℕ) (w : List ℕ) : Prop :=
  ∀ u ∈ w, canonN 5 u = 0 ∨ canonN 5 u ∈ av

lemma not_step5 (w : List ℕ) (g : Gate) (hn : negGate g = true) (av : Finset ℕ)
    (hw : represents5 av w) :
    ∃ z, (canonN 5 z = 0 ∨ canonN 5 z ∈ av) ∧
      ∀ k : Fin 32, step (w.map (bit5 k)) g = (w ++ [z]).map (bit5 k) := by
  obtain ⟨op, args⟩ := g
  cases op <;> simp [negGate] at hn
  cases args with
  | nil =>
    refine ⟨allMask 5, Or.inl (by decide), fun k => ?_⟩
    simp [step, GateOp.eval, bit5, testBit_allMask, k.isLt]
  | cons i _ =>
    refine ⟨invN 5 (w.getD i 0), ?_, fun k => ?_⟩
    · rw [canonN_invN]
      rcases read_wire5 w i with h0 | hm
      · left; rw [h0]; rfl
      · exact hw _ hm
    · simp only [step, List.map_cons, read_bit5]; simp [GateOp.eval, bit5, testBit_invN, k.isLt]

lemma classify5 {av : Finset ℕ} {ws : List ℕ} (hw : represents5 av ws) {z : ℕ} (hz : possible5 ws z) :
    canonN 5 z = 0 ∨ canonN 5 z ∈ av ∨
      ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ canonN 5 z ∈ basicOps 5 a b := by
  have andCase (u v : ℕ) (hu : canonN 5 u = 0 ∨ canonN 5 u ∈ av)
      (hv : canonN 5 v = 0 ∨ canonN 5 v ∈ av) :
      canonN 5 (u &&& v) = 0 ∨ canonN 5 (u &&& v) ∈ av ∨
      ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ canonN 5 (u &&& v) ∈ basicOps 5 a b := by
    by_cases hz0 : canonN 5 (u &&& v) = 0
    · exact Or.inl hz0
    · rcases hu with hu0 | hu
      · rcases (canonN_eq_zero_iff 5 u).mp hu0 with h0 | h1
        · exfalso; apply hz0; rw [← and_mask_canon, h0, Nat.zero_and]; rfl
        · have heq : canonN 5 (u &&& v) = canonN 5 v := by
            rw [← and_mask_canon, h1, mask_and_self_right, canonN_mask]
          rw [heq]; rcases hv with hv0 | hv; exact Or.inl hv0; exact Or.inr (Or.inl hv)
      · rcases hv with hv0 | hv
        · rcases (canonN_eq_zero_iff 5 v).mp hv0 with h0 | h1
          · exfalso; apply hz0; rw [← and_mask_canon, h0, Nat.and_zero]; rfl
          · have heq : canonN 5 (u &&& v) = canonN 5 u := by
              rw [← and_mask_canon, h1, mask_and_self_left, canonN_mask]
            rw [heq]; exact Or.inr (Or.inl hu)
        · by_cases heq : canonN 5 u = canonN 5 v
          · rcases same_and heq with hsame | h0
            · exact Or.inr (Or.inl (hsame ▸ hu))
            · exact Or.inl h0
          · exact Or.inr (Or.inr ⟨canonN 5 u, hu, canonN 5 v, hv, heq,
              signed_and_mem (signN 5 u) (signN 5 v) hz0⟩)
  rcases hz with h0 | h1 | ⟨u, hu, hzu⟩
  · subst h0; left; rfl
  · subst h1; left; decide
  · rcases hzu with h2 | h3 | ⟨v, hv, hzv⟩
    · rw [h2]; exact (hw u hu).imp_right Or.inl
    · rw [h3, canonN_invN]; exact (hw u hu).imp_right Or.inl
    · rcases hzv with h4 | h5
      · rw [h4]; exact andCase u v (hw u hu) (hw v hv)
      · rw [h5]
        have hor : canonN 5 (u ||| v) = canonN 5 (invN 5 u &&& invN 5 v) := by
          rw [← canonN_invN 5 (u ||| v)]
          apply congrArg (canonN 5); apply Nat.eq_of_testBit_eq; intro i
          simp only [testBit_invN, Nat.testBit_or, Nat.testBit_and]
          cases decide (i < 2 ^ 5) <;> cases u.testBit i <;> cases v.testBit i <;> rfl
        rw [hor]
        have hu' : canonN 5 (invN 5 u) = 0 ∨ canonN 5 (invN 5 u) ∈ av := by
          rw [canonN_invN]; exact hw u hu
        have hv' : canonN 5 (invN 5 v) = 0 ∨ canonN 5 (invN 5 v) ∈ av := by
          rw [canonN_invN]; exact hw v hv
        exact andCase (invN 5 u) (invN 5 v) hu' hv'

lemma compile5 (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g) (w : List ℕ) (av : Finset ℕ)
    (hw : represents5 av w)
    (he : ∀ k : Fin 32, (gs.foldl step (w.map (bit5 k))).getD out false = bit5 k (target 5 false)) :
    Live.build (basicOps 5) (target 5 false) (binaries gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hval : (w.getD out 0) &&& allMask 5 = target 5 false := by
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 32
      · have hk := he ⟨i, hi⟩
        simp only [List.foldl_nil, read_bit5, bit5] at hk
        have hi' : i < 2 ^ 5 := hi
        rw [testBit_mask, decide_eq_true hi', Bool.and_true]
        exact hk
      · have ht : (target 5 false).testBit i = false :=
          testBit_false_of_lt_two_pow (k := 32) (by decide) (Nat.le_of_not_lt hi)
        have hi' : ¬ i < 2 ^ 5 := hi
        rw [testBit_mask, decide_eq_false hi', Bool.and_false, ht]
    have hcan : canonN 5 (w.getD out 0) = target 5 false := by
      rw [← canonN_mask 5 (w.getD out 0), hval]; decide
    rcases read_wire5 w out with hz | hm
    · rw [hz] at hcan; exact False.elim ((by decide : canonN 5 0 ≠ target 5 false) hcan)
    · rw [← hcan]; exact (hw _ hm).resolve_left (by rw [hcan]; decide)
  | cons g gs ih =>
    by_cases ng : negGate g = true
    · obtain ⟨z, hz, hstep⟩ := not_step5 w g ng av hw
      rw [binaries, if_pos ng]
      apply ih (fun g' h => hg g' (List.mem_cons_of_mem _ h)) (w ++ [z]) av
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · exact hw u old
        · exact (List.mem_singleton.mp fresh) ▸ hz
      · intro k; simpa only [List.foldl_cons, hstep] using he k
    · rw [binaries, if_neg ng]
      obtain ⟨z, hz, hstep⟩ := gate_table5 w g (hg g List.mem_cons_self)
      have fn := ih (fun g' h => hg g' (List.mem_cons_of_mem _ h)) (w ++ [z])
      have he' : ∀ k : Fin 32, (gs.foldl step ((w ++ [z]).map (bit5 k))).getD out false =
          bit5 k (target 5 false) := by
        intro k; simpa only [List.foldl_cons, hstep] using he k
      have appendOK (h : canonN 5 z = 0 ∨ canonN 5 z ∈ av) : represents5 av (w ++ [z]) := by
        intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · exact hw u old
        · exact (List.mem_singleton.mp fresh) ▸ h
      rcases classify5 hw hz with h | h | ⟨a, ha, b, hb, hab, hop⟩
      · exact Or.inl (fn av (appendOK (.inl h)) he')
      · exact Or.inl (fn av (appendOK (.inr h)) he')
      · refine Or.inr ⟨a, ha, b, hb, hab, canonN 5 z, hop, fn (insert (canonN 5 z) av) ?_ he'⟩
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact (hw u hu).imp_right (Finset.mem_insert_of_mem ·)
        · rw [List.mem_singleton.mp hu]; exact Or.inr (Finset.mem_insert_self _ _)

lemma input_rows5 (k : Fin 32) : List.ofFn (row5 k.val) = rawInputs5.map (bit5 k) := by
  fin_cases k <;> decide

lemma target_rows5 (k : Fin 32) : ex1_5 (row5 k.val) = bit5 k (target 5 false) := by
  fin_cases k <;> decide

lemma initial_rep5 : represents5 rawInputs5.toFinset rawInputs5 := by
  intro u hu
  have hc : rawInputs5.all (fun w => canonN 5 w == w) = true := by decide
  have heq : canonN 5 u = u := beq_iff_eq.mp (List.all_eq_true.mp hc u hu)
  right; rw [heq]; exact List.mem_toFinset.mpr hu

lemma full_inputs5 {s : Finset ℕ} {k : ℕ} (hs : s ⊆ rawInputs5.toFinset)
    (hr : Live.live (basicOps 5) (target 5 false) k s) : s = rawInputs5.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  have hall : ∀ a ∈ rawInputs5, ∃ u ∈ ([1, 2, 4, 8, 16] : List ℕ),
      u < 32 ∧ differs 0 u (target 5 false) ∧
      ∀ b ∈ rawInputs5, differs 0 u b → b = a := by decide +kernel
  obtain ⟨u, _, hult, htd, huniq⟩ := hall a (List.mem_toFinset.mp ha)
  obtain ⟨b, hb, hdb⟩ := Live.live_separates (differs 0 u) htd
    (fun x y z hz => basicOps_differs (by omega) hult hz) hr
  exact (huniq b (List.mem_toFinset.mp (hs hb)) hdb) ▸ hb

def perm_0 : PermRec := ⟨2, [0,1,2,3], [0,1,2,3]⟩
def perm_1 : PermRec := ⟨3, [0,1,2,3,4,5,6,7], [0,1,2,3,4,5,6,7]⟩
def perm_2 : PermRec := ⟨3, [0,2,4,6,1,3,5,7], [0,4,1,5,2,6,3,7]⟩
def perm_3 : PermRec := ⟨3, [0,1,4,5,2,3,6,7], [0,1,4,5,2,3,6,7]⟩
def perm_4 : PermRec := ⟨3, [0,2,1,3,4,6,5,7], [0,2,1,3,4,6,5,7]⟩
def perm_5 : PermRec := ⟨4, [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15], [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15]⟩
def perm_6 : PermRec := ⟨3, [0,4,2,6,1,5,3,7], [0,4,2,6,1,5,3,7]⟩
def perm_7 : PermRec := ⟨3, [0,4,1,5,2,6,3,7], [0,2,4,6,1,3,5,7]⟩
def perm_8 : PermRec := ⟨4, [0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15], [0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15]⟩
def perm_9 : PermRec := ⟨4, [0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15], [0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15]⟩
def perm_10 : PermRec := ⟨4, [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15], [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]⟩
def perm_11 : PermRec := ⟨4, [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15], [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]⟩
def perm_12 : PermRec := ⟨4, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15], [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]⟩
def perm_13 : PermRec := ⟨4, [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15], [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]⟩
def perm_14 : PermRec := ⟨4, [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15], [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]⟩
def perm_15 : PermRec := ⟨4, [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15], [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]⟩
def perm_16 : PermRec := ⟨4, [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15], [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15]⟩
def perm_17 : PermRec := ⟨4, [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15], [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15]⟩
def perm_18 : PermRec := ⟨4, [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15], [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]⟩
def perm_19 : PermRec := ⟨4, [0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15], [0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15]⟩
def perm_20 : PermRec := ⟨4, [0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15], [0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15]⟩
def perm_21 : PermRec := ⟨4, [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15], [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]⟩
def perm_22 : PermRec := ⟨4, [0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15], [0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15]⟩
def perm_23 : PermRec := ⟨4, [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15], [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15]⟩
def perm_24 : PermRec := ⟨4, [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15], [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]⟩
def perm_25 : PermRec := ⟨4, [0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15], [0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15]⟩
def perm_26 : PermRec := ⟨4, [0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15], [0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15]⟩
def perm_27 : PermRec := ⟨4, [0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15], [0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15]⟩
def perm_28 : PermRec := ⟨5, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31], [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]⟩
def perm_29 : PermRec := ⟨5, [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31], [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31]⟩
def perm_30 : PermRec := ⟨5, [0,2,4,6,16,18,20,22,1,3,5,7,17,19,21,23,8,10,12,14,24,26,28,30,9,11,13,15,25,27,29,31], [0,8,1,9,2,10,3,11,16,24,17,25,18,26,19,27,4,12,5,13,6,14,7,15,20,28,21,29,22,30,23,31]⟩
def perm_31 : PermRec := ⟨5, [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31], [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31]⟩
def perm_32 : PermRec := ⟨4, [0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15], [0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15]⟩
def perm_33 : PermRec := ⟨5, [0,2,8,10,1,3,9,11,16,18,24,26,17,19,25,27,4,6,12,14,5,7,13,15,20,22,28,30,21,23,29,31], [0,4,1,5,16,20,17,21,2,6,3,7,18,22,19,23,8,12,9,13,24,28,25,29,10,14,11,15,26,30,27,31]⟩
def perm_34 : PermRec := ⟨5, [0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23,8,10,12,14,9,11,13,15,24,26,28,30,25,27,29,31], [0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31]⟩
def perm_35 : PermRec := ⟨5, [0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31], [0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31]⟩
def perm_36 : PermRec := ⟨5, [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31], [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31]⟩
def perm_37 : PermRec := ⟨4, [0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15], [0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15]⟩
def perm_38 : PermRec := ⟨4, [0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15], [0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15]⟩
def perm_39 : PermRec := ⟨5, [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31], [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31]⟩
def perm_40 : PermRec := ⟨5, [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31], [0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31]⟩
def perm_41 : PermRec := ⟨5, [0,2,8,10,4,6,12,14,16,18,24,26,20,22,28,30,1,3,9,11,5,7,13,15,17,19,25,27,21,23,29,31], [0,16,1,17,4,20,5,21,2,18,3,19,6,22,7,23,8,24,9,25,12,28,13,29,10,26,11,27,14,30,15,31]⟩
def perm_42 : PermRec := ⟨5, [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31], [0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31]⟩
def perm_43 : PermRec := ⟨5, [0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31], [0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31]⟩
def perm_44 : PermRec := ⟨5, [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31], [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31]⟩
def perm_45 : PermRec := ⟨5, [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31], [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]⟩
def perm_46 : PermRec := ⟨5, [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31], [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]⟩
def perm_47 : PermRec := ⟨5, [0,2,16,18,4,6,20,22,8,10,24,26,12,14,28,30,1,3,17,19,5,7,21,23,9,11,25,27,13,15,29,31], [0,16,1,17,4,20,5,21,8,24,9,25,12,28,13,29,2,18,3,19,6,22,7,23,10,26,11,27,14,30,15,31]⟩
def perm_48 : PermRec := ⟨5, [0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31], [0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31]⟩
def perm_49 : PermRec := ⟨5, [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31], [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]⟩
def perm_50 : PermRec := ⟨5, [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31], [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]⟩
def perm_51 : PermRec := ⟨5, [0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31], [0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]⟩
def perm_52 : PermRec := ⟨5, [0,2,8,10,16,18,24,26,1,3,9,11,17,19,25,27,4,6,12,14,20,22,28,30,5,7,13,15,21,23,29,31], [0,8,1,9,16,24,17,25,2,10,3,11,18,26,19,27,4,12,5,13,20,28,21,29,6,14,7,15,22,30,23,31]⟩
def perm_53 : PermRec := ⟨5, [0,4,8,12,2,6,10,14,16,20,24,28,18,22,26,30,1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31], [0,16,4,20,1,17,5,21,2,18,6,22,3,19,7,23,8,24,12,28,9,25,13,29,10,26,14,30,11,27,15,31]⟩
def perm_54 : PermRec := ⟨5, [0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31], [0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31]⟩
def perm_55 : PermRec := ⟨5, [0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31], [0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31]⟩
def perm_56 : PermRec := ⟨5, [0,4,8,12,1,5,9,13,16,20,24,28,17,21,25,29,2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31], [0,4,16,20,1,5,17,21,2,6,18,22,3,7,19,23,8,12,24,28,9,13,25,29,10,14,26,30,11,15,27,31]⟩
def perm_57 : PermRec := ⟨5, [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31], [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]⟩
def perm_58 : PermRec := ⟨5, [0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31], [0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31]⟩
def perm_59 : PermRec := ⟨5, [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31], [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31]⟩
def perm_60 : PermRec := ⟨5, [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31], [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31]⟩
def perm_61 : PermRec := ⟨5, [0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31], [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]⟩
def perm_62 : PermRec := ⟨5, [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31], [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31]⟩
def perm_63 : PermRec := ⟨5, [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15,16,18,24,26,17,19,25,27,20,22,28,30,21,23,29,31], [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15,16,20,17,21,24,28,25,29,18,22,19,23,26,30,27,31]⟩
def perm_64 : PermRec := ⟨5, [0,2,16,18,1,3,17,19,4,6,20,22,5,7,21,23,8,10,24,26,9,11,25,27,12,14,28,30,13,15,29,31], [0,4,1,5,8,12,9,13,16,20,17,21,24,28,25,29,2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]⟩
def perm_65 : PermRec := ⟨5, [0,4,16,20,1,5,17,21,2,6,18,22,3,7,19,23,8,12,24,28,9,13,25,29,10,14,26,30,11,15,27,31], [0,4,8,12,1,5,9,13,16,20,24,28,17,21,25,29,2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31]⟩
def perm_66 : PermRec := ⟨5, [0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31], [0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31]⟩
def permsTree : BTree PermRec := (.node (.node (.node (.node (.node (.node (.node (.leaf perm_0) (.leaf perm_64)) (.leaf perm_32)) (.node (.leaf perm_16) (.leaf perm_48))) (.node (.node (.leaf perm_8) (.leaf perm_40)) (.node (.leaf perm_24) (.leaf perm_56)))) (.node (.node (.node (.leaf perm_4) (.leaf perm_36)) (.node (.leaf perm_20) (.leaf perm_52))) (.node (.node (.leaf perm_12) (.leaf perm_44)) (.node (.leaf perm_28) (.leaf perm_60))))) (.node (.node (.node (.node (.node (.leaf perm_2) (.leaf perm_66)) (.leaf perm_34)) (.node (.leaf perm_18) (.leaf perm_50))) (.node (.node (.leaf perm_10) (.leaf perm_42)) (.node (.leaf perm_26) (.leaf perm_58)))) (.node (.node (.node (.leaf perm_6) (.leaf perm_38)) (.node (.leaf perm_22) (.leaf perm_54))) (.node (.node (.leaf perm_14) (.leaf perm_46)) (.node (.leaf perm_30) (.leaf perm_62)))))) (.node (.node (.node (.node (.node (.node (.leaf perm_1) (.leaf perm_65)) (.leaf perm_33)) (.node (.leaf perm_17) (.leaf perm_49))) (.node (.node (.leaf perm_9) (.leaf perm_41)) (.node (.leaf perm_25) (.leaf perm_57)))) (.node (.node (.node (.leaf perm_5) (.leaf perm_37)) (.node (.leaf perm_21) (.leaf perm_53))) (.node (.node (.leaf perm_13) (.leaf perm_45)) (.node (.leaf perm_29) (.leaf perm_61))))) (.node (.node (.node (.node (.leaf perm_3) (.leaf perm_35)) (.node (.leaf perm_19) (.leaf perm_51))) (.node (.node (.leaf perm_11) (.leaf perm_43)) (.node (.leaf perm_27) (.leaf perm_59)))) (.node (.node (.node (.leaf perm_7) (.leaf perm_39)) (.node (.leaf perm_23) (.leaf perm_55))) (.node (.node (.leaf perm_15) (.leaf perm_47)) (.node (.leaf perm_31) (.leaf perm_63)))))))

def smap_0 : SMapRec := ⟨3, 2, false, [0,2,4,6]⟩
def smap_1 : SMapRec := ⟨3, 2, false, [0,1,4,5]⟩
def smap_2 : SMapRec := ⟨3, 2, false, [0,1,2,3]⟩
def smap_3 : SMapRec := ⟨4, 2, false, [0,1,8,9]⟩
def smap_4 : SMapRec := ⟨4, 3, false, [0,2,4,6,8,10,12,14]⟩
def smap_5 : SMapRec := ⟨4, 3, false, [0,1,2,3,8,9,10,11]⟩
def smap_6 : SMapRec := ⟨4, 3, false, [0,1,2,3,4,5,6,7]⟩
def smap_7 : SMapRec := ⟨4, 3, false, [0,1,4,5,8,9,12,13]⟩
def smap_8 : SMapRec := ⟨4, 2, false, [0,4,8,12]⟩
def smap_9 : SMapRec := ⟨4, 2, false, [0,1,4,5]⟩
def smap_10 : SMapRec := ⟨4, 2, false, [0,2,4,6]⟩
def smap_11 : SMapRec := ⟨4, 2, false, [0,2,8,10]⟩
def smap_12 : SMapRec := ⟨4, 2, false, [0,1,2,3]⟩
def smap_13 : SMapRec := ⟨5, 4, false, [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]⟩
def smap_14 : SMapRec := ⟨5, 4, false, [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29]⟩
def smap_15 : SMapRec := ⟨5, 4, false, [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]⟩
def smap_16 : SMapRec := ⟨5, 4, false, [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]⟩
def smap_17 : SMapRec := ⟨5, 4, false, [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]⟩
def smap_18 : SMapRec := ⟨5, 3, false, [0,4,8,12,16,20,24,28]⟩
def smap_19 : SMapRec := ⟨5, 3, false, [0,1,8,9,16,17,24,25]⟩
def smap_20 : SMapRec := ⟨5, 3, false, [0,1,4,5,16,17,20,21]⟩
def smap_21 : SMapRec := ⟨5, 3, false, [0,1,2,3,8,9,10,11]⟩
def smap_22 : SMapRec := ⟨5, 3, false, [0,1,2,3,4,5,6,7]⟩
def smap_23 : SMapRec := ⟨5, 3, false, [0,2,8,10,16,18,24,26]⟩
def smap_24 : SMapRec := ⟨5, 3, false, [0,2,4,6,16,18,20,22]⟩
def smap_25 : SMapRec := ⟨5, 3, false, [0,1,4,5,8,9,12,13]⟩
def smap_26 : SMapRec := ⟨5, 3, false, [0,2,4,6,8,10,12,14]⟩
def smap_27 : SMapRec := ⟨5, 2, false, [0,2,8,10]⟩
def smap_28 : SMapRec := ⟨5, 3, false, [0,1,2,3,16,17,18,19]⟩
def smap_29 : SMapRec := ⟨5, 2, false, [0,4,16,20]⟩
def smap_30 : SMapRec := ⟨5, 2, false, [0,8,16,24]⟩
def smap_31 : SMapRec := ⟨5, 2, false, [0,4,8,12]⟩
def smap_32 : SMapRec := ⟨5, 2, false, [0,1,16,17]⟩
def smap_33 : SMapRec := ⟨5, 2, false, [0,2,16,18]⟩
def smapsTree : BTree SMapRec := (.node (.node (.node (.node (.node (.node (.leaf smap_0) (.leaf smap_32)) (.leaf smap_16)) (.node (.leaf smap_8) (.leaf smap_24))) (.node (.node (.leaf smap_4) (.leaf smap_20)) (.node (.leaf smap_12) (.leaf smap_28)))) (.node (.node (.node (.leaf smap_2) (.leaf smap_18)) (.node (.leaf smap_10) (.leaf smap_26))) (.node (.node (.leaf smap_6) (.leaf smap_22)) (.node (.leaf smap_14) (.leaf smap_30))))) (.node (.node (.node (.node (.node (.leaf smap_1) (.leaf smap_33)) (.leaf smap_17)) (.node (.leaf smap_9) (.leaf smap_25))) (.node (.node (.leaf smap_5) (.leaf smap_21)) (.node (.leaf smap_13) (.leaf smap_29)))) (.node (.node (.node (.leaf smap_3) (.leaf smap_19)) (.node (.leaf smap_11) (.leaf smap_27))) (.node (.node (.leaf smap_7) (.leaf smap_23)) (.node (.leaf smap_15) (.leaf smap_31))))))

def ent_0 : EntryHead := ⟨false, 2, false, 2, [10,12]⟩
def ent_1 : EntryHead := ⟨true, 2, false, 2, [10,12]⟩
def ent_2 : EntryHead := ⟨false, 3, false, 2, [238,250,252]⟩
def ent_3 : EntryHead := ⟨false, 3, false, 3, [170,204,250,252]⟩
def ent_4 : EntryHead := ⟨false, 3, false, 3, [14,170,204,240]⟩
def ent_5 : EntryHead := ⟨false, 3, false, 3, [170,204,240,254]⟩
def ent_6 : EntryHead := ⟨false, 3, false, 4, [170,204,238,240]⟩
def ent_7 : EntryHead := ⟨false, 3, false, 5, [170,204,240]⟩
def ent_8 : EntryHead := ⟨true, 3, false, 5, [170,204,240]⟩
def ent_9 : EntryHead := ⟨true, 3, false, 4, [170,204,238,240]⟩
def ent_10 : EntryHead := ⟨true, 3, false, 2, [238,250,252]⟩
def ent_11 : EntryHead := ⟨false, 3, false, 3, [238,250,252]⟩
def ent_12 : EntryHead := ⟨true, 3, false, 3, [238,250,252]⟩
def ent_13 : EntryHead := ⟨false, 4, false, 5, [43690,64764,65484,65520]⟩
def ent_14 : EntryHead := ⟨false, 3, false, 3, [10,238,240,252]⟩
def ent_15 : EntryHead := ⟨false, 3, false, 3, [170,238,250,252]⟩
def ent_16 : EntryHead := ⟨false, 3, false, 3, [168,204,250,252]⟩
def ent_17 : EntryHead := ⟨false, 3, false, 3, [14,170,238,252]⟩
def ent_18 : EntryHead := ⟨false, 3, false, 4, [170,204,250,252]⟩
def ent_19 : EntryHead := ⟨true, 3, false, 4, [170,204,250,252]⟩
def ent_20 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65450,65484]⟩
def ent_21 : EntryHead := ⟨false, 3, false, 3, [10,174,204,240]⟩
def ent_22 : EntryHead := ⟨false, 3, false, 3, [170,204,242,252]⟩
def ent_23 : EntryHead := ⟨false, 3, false, 4, [170,174,204,240]⟩
def ent_24 : EntryHead := ⟨false, 3, false, 3, [170,172,204,252]⟩
def ent_25 : EntryHead := ⟨false, 3, false, 3, [10,12,238,240]⟩
def ent_26 : EntryHead := ⟨false, 3, false, 4, [10,204,238,240]⟩
def ent_27 : EntryHead := ⟨false, 3, false, 4, [10,12,170,204,240]⟩
def ent_28 : EntryHead := ⟨false, 3, false, 3, [10,84,204,240]⟩
def ent_29 : EntryHead := ⟨false, 3, false, 4, [10,170,204,240,252]⟩
def ent_30 : EntryHead := ⟨false, 3, false, 5, [10,170,204,240]⟩
def ent_31 : EntryHead := ⟨true, 3, false, 5, [10,170,204,240]⟩
def ent_32 : EntryHead := ⟨true, 3, false, 3, [170,204,240,254]⟩
def ent_33 : EntryHead := ⟨false, 3, false, 2, [14,50,170]⟩
def ent_34 : EntryHead := ⟨false, 3, false, 3, [14,170,204,254]⟩
def ent_35 : EntryHead := ⟨false, 3, false, 3, [14,170,204,250]⟩
def ent_36 : EntryHead := ⟨false, 3, false, 4, [14,170,204,240]⟩
def ent_37 : EntryHead := ⟨true, 3, false, 4, [14,170,204,240]⟩
def ent_38 : EntryHead := ⟨false, 3, false, 4, [170,204,240,254]⟩
def ent_39 : EntryHead := ⟨true, 3, false, 4, [170,204,240,254]⟩
def ent_40 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65278,65280]⟩
def ent_41 : EntryHead := ⟨false, 3, false, 4, [170,204,238,240,250]⟩
def ent_42 : EntryHead := ⟨true, 3, false, 4, [170,204,238,240,250]⟩
def ent_43 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65278,65280]⟩
def ent_44 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65280,65520]⟩
def ent_45 : EntryHead := ⟨false, 4, false, 7, [43690,52428,61166,61680,65280]⟩
def ent_46 : EntryHead := ⟨false, 4, false, 8, [43690,52428,61680,65280]⟩
def ent_47 : EntryHead := ⟨true, 4, false, 8, [43690,52428,61680,65280]⟩
def ent_48 : EntryHead := ⟨true, 4, false, 7, [43690,52428,61166,61680,65280]⟩
def ent_49 : EntryHead := ⟨true, 4, false, 5, [43690,64764,65484,65520]⟩
def ent_50 : EntryHead := ⟨false, 3, false, 4, [10,196,204,238,240]⟩
def ent_51 : EntryHead := ⟨true, 3, false, 4, [10,196,204,238,240]⟩
def ent_52 : EntryHead := ⟨false, 3, false, 3, [170,172,204,220]⟩
def ent_53 : EntryHead := ⟨false, 3, false, 3, [170,174,238,252]⟩
def ent_54 : EntryHead := ⟨false, 3, false, 4, [10,204,206,238,240]⟩
def ent_55 : EntryHead := ⟨true, 3, false, 4, [10,204,206,238,240]⟩
def ent_56 : EntryHead := ⟨false, 3, false, 2, [168,202,252]⟩
def ent_57 : EntryHead := ⟨false, 3, false, 2, [14,184,238]⟩
def ent_58 : EntryHead := ⟨false, 3, false, 3, [170,202,252]⟩
def ent_59 : EntryHead := ⟨false, 3, false, 3, [170,202,250,252]⟩
def ent_60 : EntryHead := ⟨false, 3, false, 3, [10,200,238,250]⟩
def ent_61 : EntryHead := ⟨false, 3, false, 3, [10,50,238,250]⟩
def ent_62 : EntryHead := ⟨false, 3, false, 3, [10,204,234,250]⟩
def ent_63 : EntryHead := ⟨false, 3, false, 4, [10,204,238,250]⟩
def ent_64 : EntryHead := ⟨true, 3, false, 4, [10,204,238,250]⟩
def ent_65 : EntryHead := ⟨true, 3, false, 4, [10,204,238,240]⟩
def ent_66 : EntryHead := ⟨false, 4, false, 5, [238,64250,64764,65280]⟩
def ent_67 : EntryHead := ⟨false, 4, false, 5, [238,61166,64250,64764,65280]⟩
def ent_68 : EntryHead := ⟨false, 3, false, 3, [14,50,170]⟩
def ent_69 : EntryHead := ⟨false, 3, false, 3, [14,50,170,204]⟩
def ent_70 : EntryHead := ⟨false, 3, false, 2, [14,50,84]⟩
def ent_71 : EntryHead := ⟨false, 3, false, 3, [14,50,170,254]⟩
def ent_72 : EntryHead := ⟨false, 3, false, 4, [14,170,204,254]⟩
def ent_73 : EntryHead := ⟨false, 3, false, 4, [14,170,204,240,254]⟩
def ent_74 : EntryHead := ⟨true, 3, false, 4, [14,170,204,240,254]⟩
def ent_75 : EntryHead := ⟨false, 4, false, 5, [43690,64764,65484,65530]⟩
def ent_76 : EntryHead := ⟨true, 3, false, 3, [10,200,238,250]⟩
def ent_77 : EntryHead := ⟨false, 4, false, 4, [43690,64748,65484,65518,65520]⟩
def ent_78 : EntryHead := ⟨false, 4, false, 4, [14,43690,64764,65484,65520]⟩
def ent_79 : EntryHead := ⟨false, 4, false, 4, [43690,64764,65484,65520,65534]⟩
def ent_80 : EntryHead := ⟨false, 4, false, 5, [43690,64764,65278,65484,65520]⟩
def ent_81 : EntryHead := ⟨false, 4, false, 5, [43690,64716,64764,65484,65520]⟩
def ent_82 : EntryHead := ⟨true, 3, false, 3, [14,170,238,252]⟩
def ent_83 : EntryHead := ⟨false, 4, false, 4, [254,61166,64250,64764,65280]⟩
def ent_84 : EntryHead := ⟨false, 4, false, 5, [43690,64764,65484,65520,65532]⟩
def ent_85 : EntryHead := ⟨false, 4, false, 6, [43690,64764,65484,65520]⟩
def ent_86 : EntryHead := ⟨true, 4, false, 6, [43690,64764,65484,65520]⟩
def ent_87 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4293984240,4294963440,4294967040]⟩
def ent_88 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61680,65450,65484]⟩
def ent_89 : EntryHead := ⟨false, 4, false, 5, [43690,56540,65484,65520]⟩
def ent_90 : EntryHead := ⟨false, 4, false, 6, [170,52428,64250,64764,65280]⟩
def ent_91 : EntryHead := ⟨true, 4, false, 6, [170,52428,64250,64764,65280]⟩
def ent_92 : EntryHead := ⟨false, 3, false, 2, [14,234,252]⟩
def ent_93 : EntryHead := ⟨false, 3, false, 2, [14,238,248]⟩
def ent_94 : EntryHead := ⟨false, 3, false, 3, [2,14,238,250]⟩
def ent_95 : EntryHead := ⟨true, 3, false, 3, [2,14,238,250]⟩
def ent_96 : EntryHead := ⟨true, 3, false, 3, [10,50,238,250]⟩
def ent_97 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,65278,65520]⟩
def ent_98 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65450,65532]⟩
def ent_99 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61680,65450,65532]⟩
def ent_100 : EntryHead := ⟨false, 4, false, 4, [61166,64250,64764,65450,65532]⟩
def ent_101 : EntryHead := ⟨false, 3, false, 3, [14,238,250,252]⟩
def ent_102 : EntryHead := ⟨true, 3, false, 3, [14,238,250,252]⟩
def ent_103 : EntryHead := ⟨true, 3, false, 3, [170,238,250,252]⟩
def ent_104 : EntryHead := ⟨false, 4, false, 5, [43690,52428,64250,65450,65520,65532]⟩
def ent_105 : EntryHead := ⟨false, 3, false, 3, [10,228,240,252]⟩
def ent_106 : EntryHead := ⟨false, 3, false, 2, [14,226,250]⟩
def ent_107 : EntryHead := ⟨false, 3, false, 2, [24,238,240]⟩
def ent_108 : EntryHead := ⟨false, 3, false, 3, [170,172,238,252]⟩
def ent_109 : EntryHead := ⟨false, 3, false, 3, [10,238,250,252]⟩
def ent_110 : EntryHead := ⟨false, 3, false, 2, [10,28,238]⟩
def ent_111 : EntryHead := ⟨false, 3, false, 3, [10,224,238,252]⟩
def ent_112 : EntryHead := ⟨false, 3, false, 3, [10,14,238,252]⟩
def ent_113 : EntryHead := ⟨false, 3, false, 2, [10,226,252]⟩
def ent_114 : EntryHead := ⟨false, 3, false, 3, [10,12,238,250]⟩
def ent_115 : EntryHead := ⟨false, 3, false, 4, [10,238,240,252]⟩
def ent_116 : EntryHead := ⟨false, 3, false, 3, [170,172,238,240]⟩
def ent_117 : EntryHead := ⟨false, 3, false, 4, [10,170,238,240,252]⟩
def ent_118 : EntryHead := ⟨true, 3, false, 4, [10,170,238,240,252]⟩
def ent_119 : EntryHead := ⟨false, 3, false, 2, [14,50,234]⟩
def ent_120 : EntryHead := ⟨false, 3, false, 3, [14,50,238,250]⟩
def ent_121 : EntryHead := ⟨true, 3, false, 3, [14,50,238,250]⟩
def ent_122 : EntryHead := ⟨false, 4, false, 4, [14,13104,43690,61680,65484]⟩
def ent_123 : EntryHead := ⟨false, 4, false, 5, [238,43690,61166,61680,65484,65532]⟩
def ent_124 : EntryHead := ⟨false, 3, false, 2, [168,234,252]⟩
def ent_125 : EntryHead := ⟨false, 3, false, 3, [168,238,250,252]⟩
def ent_126 : EntryHead := ⟨true, 3, false, 3, [168,238,250,252]⟩
def ent_127 : EntryHead := ⟨false, 4, false, 4, [61166,64250,65484,65530,65532]⟩
def ent_128 : EntryHead := ⟨false, 3, false, 3, [10,200,238,240]⟩
def ent_129 : EntryHead := ⟨true, 3, false, 3, [10,200,238,240]⟩
def ent_130 : EntryHead := ⟨false, 4, false, 4, [43690,61166,64748,65518,65520]⟩
def ent_131 : EntryHead := ⟨false, 4, false, 5, [43690,61166,64764,65518,65520]⟩
def ent_132 : EntryHead := ⟨false, 4, false, 5, [43690,52428,64250,64764,65450,65532]⟩
def ent_133 : EntryHead := ⟨false, 3, false, 2, [14,170,184]⟩
def ent_134 : EntryHead := ⟨false, 3, false, 3, [170,172,204,250]⟩
def ent_135 : EntryHead := ⟨false, 3, false, 3, [10,50,238,240]⟩
def ent_136 : EntryHead := ⟨false, 3, false, 4, [10,204,238,240,250]⟩
def ent_137 : EntryHead := ⟨true, 3, false, 4, [10,204,238,240,250]⟩
def ent_138 : EntryHead := ⟨true, 3, false, 3, [168,204,250,252]⟩
def ent_139 : EntryHead := ⟨false, 4, false, 5, [43688,52428,61680,65450,65484,65532]⟩
def ent_140 : EntryHead := ⟨true, 3, false, 3, [14,170,204,250]⟩
def ent_141 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,64250,65520]⟩
def ent_142 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,64250,65280,65520]⟩
def ent_143 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,64250,65278,65520]⟩
def ent_144 : EntryHead := ⟨false, 4, false, 5, [43690,52428,61680,65450,65484,65534]⟩
def ent_145 : EntryHead := ⟨true, 3, false, 3, [14,170,204,254]⟩
def ent_146 : EntryHead := ⟨false, 4, false, 5, [43690,52428,61680,65448,65484,65532]⟩
def ent_147 : EntryHead := ⟨false, 4, false, 5, [14,43690,52428,61680,65450,65520]⟩
def ent_148 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65450,65484,65530]⟩
def ent_149 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61680,65450,65484,65530]⟩
def ent_150 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,64250,64764,65280]⟩
def ent_151 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65450,65484,65518]⟩
def ent_152 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61680,65450,65484,65518]⟩
def ent_153 : EntryHead := ⟨false, 5, false, 7, [2863311530,4244438268,4291624908,4294963440,4294967040]⟩
def ent_154 : EntryHead := ⟨false, 5, false, 6, [4008636142,4210752250,4291624908,4294963440,4294967040]⟩
def ent_155 : EntryHead := ⟨false, 5, false, 7, [2863311530,3435973836,4210752250,4291624908,4294963440,4294967040]⟩
def ent_156 : EntryHead := ⟨false, 4, false, 5, [43690,61166,64764,65484,65520]⟩
def ent_157 : EntryHead := ⟨false, 4, false, 5, [238,61166,61680,65450,65484]⟩
def ent_158 : EntryHead := ⟨false, 3, false, 4, [170,174,204,238,240]⟩
def ent_159 : EntryHead := ⟨true, 3, false, 4, [170,174,204,238,240]⟩
def ent_160 : EntryHead := ⟨false, 4, false, 5, [238,61166,61680,64250,64764,65280]⟩
def ent_161 : EntryHead := ⟨false, 4, false, 6, [43690,52428,64250,65450,65520]⟩
def ent_162 : EntryHead := ⟨true, 4, false, 6, [43690,52428,64250,65450,65520]⟩
def ent_163 : EntryHead := ⟨false, 3, false, 2, [170,172,184]⟩
def ent_164 : EntryHead := ⟨false, 3, false, 2, [10,226,254]⟩
def ent_165 : EntryHead := ⟨false, 3, false, 3, [10,226,238,240]⟩
def ent_166 : EntryHead := ⟨false, 3, false, 3, [14,170,226,240]⟩
def ent_167 : EntryHead := ⟨false, 3, false, 3, [170,172,204,254]⟩
def ent_168 : EntryHead := ⟨false, 3, false, 3, [170,172,236,252]⟩
def ent_169 : EntryHead := ⟨false, 3, false, 4, [170,172,204,252]⟩
def ent_170 : EntryHead := ⟨false, 3, false, 3, [10,12,226,240]⟩
def ent_171 : EntryHead := ⟨false, 3, false, 4, [10,204,228,240]⟩
def ent_172 : EntryHead := ⟨false, 3, false, 4, [10,204,228,238,240]⟩
def ent_173 : EntryHead := ⟨true, 3, false, 4, [10,204,228,238,240]⟩
def ent_174 : EntryHead := ⟨false, 4, false, 6, [238,43690,61680,64764,65280]⟩
def ent_175 : EntryHead := ⟨true, 4, false, 6, [238,43690,61680,64764,65280]⟩
def ent_176 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4042322160,4289396650,4294954188,4294967040]⟩
def ent_177 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65280,65520]⟩
def ent_178 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4008636142,4042322160,4278255360,4294963440,4294967040]⟩
def ent_179 : EntryHead := ⟨true, 3, false, 4, [170,172,204,252]⟩
def ent_180 : EntryHead := ⟨false, 4, false, 6, [43690,43724,52428,61680,65484]⟩
def ent_181 : EntryHead := ⟨true, 3, false, 4, [170,174,204,240]⟩
def ent_182 : EntryHead := ⟨false, 4, false, 6, [43690,43758,61680,64764,65280]⟩
def ent_183 : EntryHead := ⟨true, 3, false, 4, [10,170,204,240,252]⟩
def ent_184 : EntryHead := ⟨false, 4, false, 6, [170,52428,64250,65280,65520]⟩
def ent_185 : EntryHead := ⟨false, 4, false, 6, [170,52428,61680,65278,65280]⟩
def ent_186 : EntryHead := ⟨false, 4, false, 6, [170,52428,61166,61680,65278,65280]⟩
def ent_187 : EntryHead := ⟨false, 4, false, 6, [170,52428,61166,61680,65280,65518]⟩
def ent_188 : EntryHead := ⟨false, 4, false, 6, [170,52428,61166,61680,65280,65520]⟩
def ent_189 : EntryHead := ⟨false, 4, false, 7, [170,52428,61166,61680,65280]⟩
def ent_190 : EntryHead := ⟨true, 4, false, 7, [170,52428,61166,61680,65280]⟩
def ent_191 : EntryHead := ⟨true, 3, false, 4, [14,170,204,254]⟩
def ent_192 : EntryHead := ⟨true, 3, false, 3, [14,50,170,254]⟩
def ent_193 : EntryHead := ⟨false, 3, false, 3, [14,50,84]⟩
def ent_194 : EntryHead := ⟨false, 3, false, 3, [14,50,84,254]⟩
def ent_195 : EntryHead := ⟨true, 3, false, 3, [14,50,84,254]⟩
def ent_196 : EntryHead := ⟨true, 3, false, 2, [14,50,170]⟩
def ent_197 : EntryHead := ⟨false, 4, false, 5, [238,13090,43690,61680,65518]⟩
def ent_198 : EntryHead := ⟨false, 4, false, 6, [238,43690,52428,61680,65518]⟩
def ent_199 : EntryHead := ⟨false, 4, false, 6, [238,43690,52428,61680,65280,65518]⟩
def ent_200 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,61680,65278,65450]⟩
def ent_201 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65280,65530]⟩
def ent_202 : EntryHead := ⟨false, 4, false, 6, [254,43690,52428,61680,65280]⟩
def ent_203 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,61680,65278,65534]⟩
def ent_204 : EntryHead := ⟨false, 4, false, 6, [254,43690,52428,61680,65278,65280]⟩
def ent_205 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65280,65534]⟩
def ent_206 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65278,65280,65534]⟩
def ent_207 : EntryHead := ⟨false, 4, false, 7, [43690,52428,61680,65278,65280]⟩
def ent_208 : EntryHead := ⟨true, 4, false, 7, [43690,52428,61680,65278,65280]⟩
def ent_209 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65450,65484]⟩
def ent_210 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65450,65484]⟩
def ent_211 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4042322160,4278255360,4294945450,4294954188,4294966010]⟩
def ent_212 : EntryHead := ⟨false, 5, false, 9, [2863311530,3435973836,4042322160,4278255360,4294945450,4294954188]⟩
def ent_213 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65290,65484]⟩
def ent_214 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61680,65290,65520]⟩
def ent_215 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61182,61680,65280]⟩
def ent_216 : EntryHead := ⟨false, 4, false, 6, [43690,43758,52428,61680,64254,65280]⟩
def ent_217 : EntryHead := ⟨false, 4, false, 6, [43690,43758,52428,61680,65280,65518]⟩
def ent_218 : EntryHead := ⟨false, 4, false, 6, [43690,43758,52428,61680,65280,65520]⟩
def ent_219 : EntryHead := ⟨false, 4, false, 7, [43690,43758,52428,61680,65280]⟩
def ent_220 : EntryHead := ⟨false, 4, false, 6, [43260,43690,52428,61680,65280]⟩
def ent_221 : EntryHead := ⟨false, 3, false, 2, [152,238,240]⟩
def ent_222 : EntryHead := ⟨false, 3, false, 3, [10,164,204,240]⟩
def ent_223 : EntryHead := ⟨false, 3, false, 3, [152,170,220,240]⟩
def ent_224 : EntryHead := ⟨false, 3, false, 3, [10,174,204,250]⟩
def ent_225 : EntryHead := ⟨false, 3, false, 4, [10,174,204,240]⟩
def ent_226 : EntryHead := ⟨false, 3, false, 3, [152,170,204,240]⟩
def ent_227 : EntryHead := ⟨false, 3, false, 4, [10,170,174,204,240]⟩
def ent_228 : EntryHead := ⟨true, 3, false, 4, [10,170,174,204,240]⟩
def ent_229 : EntryHead := ⟨false, 3, false, 3, [10,220,238,240]⟩
def ent_230 : EntryHead := ⟨false, 3, false, 3, [170,206,250,252]⟩
def ent_231 : EntryHead := ⟨false, 3, false, 3, [168,204,242,252]⟩
def ent_232 : EntryHead := ⟨false, 3, false, 3, [14,170,220,238]⟩
def ent_233 : EntryHead := ⟨false, 3, false, 2, [174,236,250]⟩
def ent_234 : EntryHead := ⟨false, 3, false, 3, [136,186,238,240]⟩
def ent_235 : EntryHead := ⟨false, 3, false, 3, [14,170,206,252]⟩
def ent_236 : EntryHead := ⟨false, 3, false, 4, [170,204,242,252]⟩
def ent_237 : EntryHead := ⟨false, 3, false, 3, [14,170,186,204]⟩
def ent_238 : EntryHead := ⟨false, 3, false, 4, [170,174,204,240,250]⟩
def ent_239 : EntryHead := ⟨true, 3, false, 4, [170,174,204,240,250]⟩
def ent_240 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61182,61680,65280]⟩
def ent_241 : EntryHead := ⟨false, 3, false, 3, [2,68,80,252]⟩
def ent_242 : EntryHead := ⟨false, 3, false, 3, [10,12,238,254]⟩
def ent_243 : EntryHead := ⟨false, 3, false, 4, [10,12,238,240]⟩
def ent_244 : EntryHead := ⟨false, 3, false, 3, [10,204,226,240]⟩
def ent_245 : EntryHead := ⟨false, 3, false, 3, [10,12,48,238]⟩
def ent_246 : EntryHead := ⟨false, 3, false, 4, [10,12,170,238,240]⟩
def ent_247 : EntryHead := ⟨true, 3, false, 4, [10,12,170,238,240]⟩
def ent_248 : EntryHead := ⟨false, 3, false, 4, [10,204,238,240,252]⟩
def ent_249 : EntryHead := ⟨true, 3, false, 4, [10,204,238,240,252]⟩
def ent_250 : EntryHead := ⟨false, 4, false, 6, [170,52428,61680,64764,65278,65280]⟩
def ent_251 : EntryHead := ⟨true, 3, false, 4, [10,174,204,240]⟩
def ent_252 : EntryHead := ⟨true, 3, false, 4, [10,12,170,204,240]⟩
def ent_253 : EntryHead := ⟨false, 4, false, 6, [170,252,43690,52428,61680,64764,65280]⟩
def ent_254 : EntryHead := ⟨true, 3, false, 3, [10,84,204,240]⟩
def ent_255 : EntryHead := ⟨false, 4, false, 5, [170,21844,52428,61680,64764,65280]⟩
def ent_256 : EntryHead := ⟨false, 4, false, 6, [170,43690,52428,61680,64764,65280,65532]⟩
def ent_257 : EntryHead := ⟨false, 4, false, 7, [170,43690,52428,61680,64764,65280]⟩
def ent_258 : EntryHead := ⟨false, 4, false, 6, [170,43690,52428,61680,65280,65484,65532]⟩
def ent_259 : EntryHead := ⟨false, 4, false, 7, [170,43690,52428,61680,65280,65484]⟩
def ent_260 : EntryHead := ⟨false, 4, false, 8, [170,43690,52428,61680,65280]⟩
def ent_261 : EntryHead := ⟨true, 4, false, 8, [170,43690,52428,61680,65280]⟩
def ent_262 : EntryHead := ⟨false, 5, false, 9, [2863311530,3435973836,4042322160,4278124286,4278255360,4294901760]⟩
def ent_263 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,64250,65278,65280]⟩
def ent_264 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,64250,65278,65280]⟩
def ent_265 : EntryHead := ⟨false, 4, false, 3, [65278,65518,65530,65532]⟩
def ent_266 : EntryHead := ⟨false, 4, false, 4, [43690,64764,65518,65530,65532]⟩
def ent_267 : EntryHead := ⟨false, 4, false, 4, [43690,52428,64200,65530,65532]⟩
def ent_268 : EntryHead := ⟨false, 4, false, 5, [43690,52428,64250,65484,65530,65532]⟩
def ent_269 : EntryHead := ⟨true, 3, false, 4, [10,238,240,252]⟩
def ent_270 : EntryHead := ⟨true, 3, false, 3, [10,238,250,252]⟩
def ent_271 : EntryHead := ⟨false, 4, false, 5, [43690,52428,65278,65518,65520]⟩
def ent_272 : EntryHead := ⟨false, 4, false, 5, [43690,52428,61166,65278,65518,65520]⟩
def ent_273 : EntryHead := ⟨false, 4, false, 5, [43690,52428,61680,65278,65450,65532]⟩
def ent_274 : EntryHead := ⟨false, 4, false, 5, [43690,52428,61152,61680,65518,65520]⟩
def ent_275 : EntryHead := ⟨false, 4, false, 5, [14,43690,61166,61680,65280,65532]⟩
def ent_276 : EntryHead := ⟨false, 4, false, 5, [43688,52428,61680,64764,65450,65532]⟩
def ent_277 : EntryHead := ⟨true, 3, false, 3, [10,50,238,240]⟩
def ent_278 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,61166,65278,65520]⟩
def ent_279 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65518,65520]⟩
def ent_280 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65518,65520]⟩
def ent_281 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65278,65280]⟩
def ent_282 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65280,65530]⟩
def ent_283 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,64250,65280,65518]⟩
def ent_284 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,64250,65280,65518]⟩
def ent_285 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4042322160,4278124286,4278255360,4293853166,4294901760]⟩
def ent_286 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4008636142,4042322160,4278255360,4294962926,4294963440]⟩
def ent_287 : EntryHead := ⟨false, 3, false, 4, [10,170,204,240,254]⟩
def ent_288 : EntryHead := ⟨true, 3, false, 4, [10,170,204,240,254]⟩
def ent_289 : EntryHead := ⟨false, 4, false, 5, [43690,43774,52428,61680,65484,65532]⟩
def ent_290 : EntryHead := ⟨false, 4, false, 5, [238,13090,43690,61680,65484]⟩
def ent_291 : EntryHead := ⟨false, 4, false, 5, [238,13090,43690,61680,65484,65518]⟩
def ent_292 : EntryHead := ⟨false, 3, false, 4, [10,48,170,204,250]⟩
def ent_293 : EntryHead := ⟨true, 3, false, 4, [10,48,170,204,250]⟩
def ent_294 : EntryHead := ⟨false, 4, false, 5, [238,43690,52428,61680,65518,65530]⟩
def ent_295 : EntryHead := ⟨false, 3, false, 3, [14,170,176,204]⟩
def ent_296 : EntryHead := ⟨false, 3, false, 3, [14,170,204,242]⟩
def ent_297 : EntryHead := ⟨false, 3, false, 3, [10,12,50,170]⟩
def ent_298 : EntryHead := ⟨false, 3, false, 4, [10,50,170,204,240]⟩
def ent_299 : EntryHead := ⟨true, 3, false, 4, [10,50,170,204,240]⟩
def ent_300 : EntryHead := ⟨false, 4, false, 6, [238,43690,52428,61680,65450,65518]⟩
def ent_301 : EntryHead := ⟨false, 4, false, 6, [238,43690,52428,61680,65280,65450,65518]⟩
def ent_302 : EntryHead := ⟨true, 4, false, 6, [238,43690,52428,61680,65280,65450,65518]⟩
def ent_303 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901758,4294901760]⟩
def ent_304 : EntryHead := ⟨true, 3, false, 3, [14,50,170,204]⟩
def ent_305 : EntryHead := ⟨false, 4, false, 5, [14,43690,52428,61680,65280,65530]⟩
def ent_306 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,61166,61680,65520]⟩
def ent_307 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65278,65280,65520]⟩
def ent_308 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65278,65280,65520]⟩
def ent_309 : EntryHead := ⟨false, 4, false, 6, [14,43690,52428,61680,65280]⟩
def ent_310 : EntryHead := ⟨false, 4, false, 5, [14,13104,43690,52428,61680,65280]⟩
def ent_311 : EntryHead := ⟨false, 4, false, 6, [14,43690,52428,61680,65280,65520]⟩
def ent_312 : EntryHead := ⟨true, 4, false, 6, [14,43690,52428,61680,65280,65520]⟩
def ent_313 : EntryHead := ⟨false, 4, false, 6, [43690,52428,61166,61680,65280,65534]⟩
def ent_314 : EntryHead := ⟨true, 4, false, 6, [43690,52428,61166,61680,65280,65534]⟩
def ent_315 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760,4294967040]⟩
def ent_316 : EntryHead := ⟨false, 5, false, 9, [2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760]⟩
def ent_317 : EntryHead := ⟨true, 3, false, 4, [170,204,242,252]⟩
def ent_318 : EntryHead := ⟨false, 4, false, 6, [43690,43694,52428,61680,65280,65520]⟩
def ent_319 : EntryHead := ⟨true, 3, false, 4, [10,12,238,240]⟩
def ent_320 : EntryHead := ⟨false, 4, false, 6, [10,52428,61166,61680,65280,65520]⟩
def ent_321 : EntryHead := ⟨false, 4, false, 4, [680,1020,43690,52428,61680]⟩
def ent_322 : EntryHead := ⟨false, 4, false, 3, [30,43690,52428,57600]⟩
def ent_323 : EntryHead := ⟨false, 4, false, 4, [30,7710,43690,52428,65280]⟩
def ent_324 : EntryHead := ⟨false, 4, false, 4, [1020,43010,43690,52428,61680]⟩
def ent_325 : EntryHead := ⟨false, 4, false, 4, [1020,43690,44030,52428,61680]⟩
def ent_326 : EntryHead := ⟨false, 4, false, 5, [1020,43690,52428,61680]⟩
def ent_327 : EntryHead := ⟨false, 4, false, 6, [10,21840,52428,61680,65280]⟩
def ent_328 : EntryHead := ⟨false, 4, false, 6, [10,12,43690,52428,61680,65280,65520]⟩
def ent_329 : EntryHead := ⟨false, 4, false, 5, [10,21844,52428,61680,65280,65520]⟩
def ent_330 : EntryHead := ⟨false, 4, false, 6, [10,43690,52428,61680,65280,65520,65532]⟩
def ent_331 : EntryHead := ⟨false, 4, false, 7, [10,43690,52428,61680,65280,65520]⟩
def ent_332 : EntryHead := ⟨true, 4, false, 7, [10,43690,52428,61680,65280,65520]⟩
def ent_333 : EntryHead := ⟨false, 4, false, 4, [14,50,43690,64764,65280]⟩
def ent_334 : EntryHead := ⟨false, 4, false, 5, [14,254,43690,52428,64250,65280]⟩
def ent_335 : EntryHead := ⟨true, 3, false, 3, [14,50,170]⟩
def ent_336 : EntryHead := ⟨false, 4, false, 5, [254,43690,52428,61166,61680,65518]⟩
def ent_337 : EntryHead := ⟨false, 4, false, 6, [254,43690,52428,61166,61680,65280]⟩
def ent_338 : EntryHead := ⟨true, 4, false, 6, [254,43690,52428,61166,61680,65280]⟩
def ent_339 : EntryHead := ⟨false, 5, false, 8, [2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901758,4294901760]⟩
def ent_340 : EntryHead := ⟨true, 4, false, 7, [170,43690,52428,61680,64764,65280]⟩
def ent_341 : EntryHead := ⟨false, 5, false, 9, [2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760]⟩
def ent_342 : EntryHead := ⟨false, 5, false, 10, [2863311530,3435973836,4008636142,4042322160,4278255360,4294901760]⟩
def ent_343 : EntryHead := ⟨false, 5, false, 11, [2863311530,3435973836,4042322160,4278255360,4294901760]⟩
def entriesTree : BTree EntryHead := (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ent_0) (.leaf ent_256)) (.leaf ent_128)) (.node (.node (.leaf ent_64) (.leaf ent_320)) (.leaf ent_192))) (.node (.node (.node (.leaf ent_32) (.leaf ent_288)) (.leaf ent_160)) (.node (.leaf ent_96) (.leaf ent_224)))) (.node (.node (.node (.node (.leaf ent_16) (.leaf ent_272)) (.leaf ent_144)) (.node (.node (.leaf ent_80) (.leaf ent_336)) (.leaf ent_208))) (.node (.node (.node (.leaf ent_48) (.leaf ent_304)) (.leaf ent_176)) (.node (.leaf ent_112) (.leaf ent_240))))) (.node (.node (.node (.node (.node (.leaf ent_8) (.leaf ent_264)) (.leaf ent_136)) (.node (.node (.leaf ent_72) (.leaf ent_328)) (.leaf ent_200))) (.node (.node (.node (.leaf ent_40) (.leaf ent_296)) (.leaf ent_168)) (.node (.leaf ent_104) (.leaf ent_232)))) (.node (.node (.node (.node (.leaf ent_24) (.leaf ent_280)) (.leaf ent_152)) (.node (.leaf ent_88) (.leaf ent_216))) (.node (.node (.node (.leaf ent_56) (.leaf ent_312)) (.leaf ent_184)) (.node (.leaf ent_120) (.leaf ent_248)))))) (.node (.node (.node (.node (.node (.node (.leaf ent_4) (.leaf ent_260)) (.leaf ent_132)) (.node (.node (.leaf ent_68) (.leaf ent_324)) (.leaf ent_196))) (.node (.node (.node (.leaf ent_36) (.leaf ent_292)) (.leaf ent_164)) (.node (.leaf ent_100) (.leaf ent_228)))) (.node (.node (.node (.node (.leaf ent_20) (.leaf ent_276)) (.leaf ent_148)) (.node (.node (.leaf ent_84) (.leaf ent_340)) (.leaf ent_212))) (.node (.node (.node (.leaf ent_52) (.leaf ent_308)) (.leaf ent_180)) (.node (.leaf ent_116) (.leaf ent_244))))) (.node (.node (.node (.node (.node (.leaf ent_12) (.leaf ent_268)) (.leaf ent_140)) (.node (.node (.leaf ent_76) (.leaf ent_332)) (.leaf ent_204))) (.node (.node (.node (.leaf ent_44) (.leaf ent_300)) (.leaf ent_172)) (.node (.leaf ent_108) (.leaf ent_236)))) (.node (.node (.node (.node (.leaf ent_28) (.leaf ent_284)) (.leaf ent_156)) (.node (.leaf ent_92) (.leaf ent_220))) (.node (.node (.node (.leaf ent_60) (.leaf ent_316)) (.leaf ent_188)) (.node (.leaf ent_124) (.leaf ent_252))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ent_2) (.leaf ent_258)) (.leaf ent_130)) (.node (.node (.leaf ent_66) (.leaf ent_322)) (.leaf ent_194))) (.node (.node (.node (.leaf ent_34) (.leaf ent_290)) (.leaf ent_162)) (.node (.leaf ent_98) (.leaf ent_226)))) (.node (.node (.node (.node (.leaf ent_18) (.leaf ent_274)) (.leaf ent_146)) (.node (.node (.leaf ent_82) (.leaf ent_338)) (.leaf ent_210))) (.node (.node (.node (.leaf ent_50) (.leaf ent_306)) (.leaf ent_178)) (.node (.leaf ent_114) (.leaf ent_242))))) (.node (.node (.node (.node (.node (.leaf ent_10) (.leaf ent_266)) (.leaf ent_138)) (.node (.node (.leaf ent_74) (.leaf ent_330)) (.leaf ent_202))) (.node (.node (.node (.leaf ent_42) (.leaf ent_298)) (.leaf ent_170)) (.node (.leaf ent_106) (.leaf ent_234)))) (.node (.node (.node (.node (.leaf ent_26) (.leaf ent_282)) (.leaf ent_154)) (.node (.leaf ent_90) (.leaf ent_218))) (.node (.node (.node (.leaf ent_58) (.leaf ent_314)) (.leaf ent_186)) (.node (.leaf ent_122) (.leaf ent_250)))))) (.node (.node (.node (.node (.node (.node (.leaf ent_6) (.leaf ent_262)) (.leaf ent_134)) (.node (.node (.leaf ent_70) (.leaf ent_326)) (.leaf ent_198))) (.node (.node (.node (.leaf ent_38) (.leaf ent_294)) (.leaf ent_166)) (.node (.leaf ent_102) (.leaf ent_230)))) (.node (.node (.node (.node (.leaf ent_22) (.leaf ent_278)) (.leaf ent_150)) (.node (.node (.leaf ent_86) (.leaf ent_342)) (.leaf ent_214))) (.node (.node (.node (.leaf ent_54) (.leaf ent_310)) (.leaf ent_182)) (.node (.leaf ent_118) (.leaf ent_246))))) (.node (.node (.node (.node (.node (.leaf ent_14) (.leaf ent_270)) (.leaf ent_142)) (.node (.node (.leaf ent_78) (.leaf ent_334)) (.leaf ent_206))) (.node (.node (.node (.leaf ent_46) (.leaf ent_302)) (.leaf ent_174)) (.node (.leaf ent_110) (.leaf ent_238)))) (.node (.node (.node (.node (.leaf ent_30) (.leaf ent_286)) (.leaf ent_158)) (.node (.leaf ent_94) (.leaf ent_222))) (.node (.node (.node (.leaf ent_62) (.leaf ent_318)) (.leaf ent_190)) (.node (.leaf ent_126) (.leaf ent_254)))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf ent_1) (.leaf ent_257)) (.leaf ent_129)) (.node (.node (.leaf ent_65) (.leaf ent_321)) (.leaf ent_193))) (.node (.node (.node (.leaf ent_33) (.leaf ent_289)) (.leaf ent_161)) (.node (.leaf ent_97) (.leaf ent_225)))) (.node (.node (.node (.node (.leaf ent_17) (.leaf ent_273)) (.leaf ent_145)) (.node (.node (.leaf ent_81) (.leaf ent_337)) (.leaf ent_209))) (.node (.node (.node (.leaf ent_49) (.leaf ent_305)) (.leaf ent_177)) (.node (.leaf ent_113) (.leaf ent_241))))) (.node (.node (.node (.node (.node (.leaf ent_9) (.leaf ent_265)) (.leaf ent_137)) (.node (.node (.leaf ent_73) (.leaf ent_329)) (.leaf ent_201))) (.node (.node (.node (.leaf ent_41) (.leaf ent_297)) (.leaf ent_169)) (.node (.leaf ent_105) (.leaf ent_233)))) (.node (.node (.node (.node (.leaf ent_25) (.leaf ent_281)) (.leaf ent_153)) (.node (.leaf ent_89) (.leaf ent_217))) (.node (.node (.node (.leaf ent_57) (.leaf ent_313)) (.leaf ent_185)) (.node (.leaf ent_121) (.leaf ent_249)))))) (.node (.node (.node (.node (.node (.node (.leaf ent_5) (.leaf ent_261)) (.leaf ent_133)) (.node (.node (.leaf ent_69) (.leaf ent_325)) (.leaf ent_197))) (.node (.node (.node (.leaf ent_37) (.leaf ent_293)) (.leaf ent_165)) (.node (.leaf ent_101) (.leaf ent_229)))) (.node (.node (.node (.node (.leaf ent_21) (.leaf ent_277)) (.leaf ent_149)) (.node (.node (.leaf ent_85) (.leaf ent_341)) (.leaf ent_213))) (.node (.node (.node (.leaf ent_53) (.leaf ent_309)) (.leaf ent_181)) (.node (.leaf ent_117) (.leaf ent_245))))) (.node (.node (.node (.node (.node (.leaf ent_13) (.leaf ent_269)) (.leaf ent_141)) (.node (.node (.leaf ent_77) (.leaf ent_333)) (.leaf ent_205))) (.node (.node (.node (.leaf ent_45) (.leaf ent_301)) (.leaf ent_173)) (.node (.leaf ent_109) (.leaf ent_237)))) (.node (.node (.node (.node (.leaf ent_29) (.leaf ent_285)) (.leaf ent_157)) (.node (.leaf ent_93) (.leaf ent_221))) (.node (.node (.node (.leaf ent_61) (.leaf ent_317)) (.leaf ent_189)) (.node (.leaf ent_125) (.leaf ent_253))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf ent_3) (.leaf ent_259)) (.leaf ent_131)) (.node (.node (.leaf ent_67) (.leaf ent_323)) (.leaf ent_195))) (.node (.node (.node (.leaf ent_35) (.leaf ent_291)) (.leaf ent_163)) (.node (.leaf ent_99) (.leaf ent_227)))) (.node (.node (.node (.node (.leaf ent_19) (.leaf ent_275)) (.leaf ent_147)) (.node (.node (.leaf ent_83) (.leaf ent_339)) (.leaf ent_211))) (.node (.node (.node (.leaf ent_51) (.leaf ent_307)) (.leaf ent_179)) (.node (.leaf ent_115) (.leaf ent_243))))) (.node (.node (.node (.node (.node (.leaf ent_11) (.leaf ent_267)) (.leaf ent_139)) (.node (.node (.leaf ent_75) (.leaf ent_331)) (.leaf ent_203))) (.node (.node (.node (.leaf ent_43) (.leaf ent_299)) (.leaf ent_171)) (.node (.leaf ent_107) (.leaf ent_235)))) (.node (.node (.node (.node (.leaf ent_27) (.leaf ent_283)) (.leaf ent_155)) (.node (.leaf ent_91) (.leaf ent_219))) (.node (.node (.node (.leaf ent_59) (.leaf ent_315)) (.leaf ent_187)) (.node (.leaf ent_123) (.leaf ent_251)))))) (.node (.node (.node (.node (.node (.node (.leaf ent_7) (.leaf ent_263)) (.leaf ent_135)) (.node (.node (.leaf ent_71) (.leaf ent_327)) (.leaf ent_199))) (.node (.node (.node (.leaf ent_39) (.leaf ent_295)) (.leaf ent_167)) (.node (.leaf ent_103) (.leaf ent_231)))) (.node (.node (.node (.node (.leaf ent_23) (.leaf ent_279)) (.leaf ent_151)) (.node (.node (.leaf ent_87) (.leaf ent_343)) (.leaf ent_215))) (.node (.node (.node (.leaf ent_55) (.leaf ent_311)) (.leaf ent_183)) (.node (.leaf ent_119) (.leaf ent_247))))) (.node (.node (.node (.node (.node (.leaf ent_15) (.leaf ent_271)) (.leaf ent_143)) (.node (.node (.leaf ent_79) (.leaf ent_335)) (.leaf ent_207))) (.node (.node (.node (.leaf ent_47) (.leaf ent_303)) (.leaf ent_175)) (.node (.leaf ent_111) (.leaf ent_239)))) (.node (.node (.node (.node (.leaf ent_31) (.leaf ent_287)) (.leaf ent_159)) (.node (.leaf ent_95) (.leaf ent_223))) (.node (.node (.node (.leaf ent_63) (.leaf ent_319)) (.leaf ent_191)) (.node (.leaf ent_127) (.leaf ent_255)))))))))

def chunk_0 : List (ℕ × List ℕ) := [
  (0, []),
  (1, [0]),
  (2, []),
  (3, [1028,1,3,1]),
  (4, []),
  (5, []),
  (6, [1025,1,3,1,3,3,3,1025,2054,1,1,1027,3078,5,1032,5,1034]),
  (7, [1025,1025,1027,1036,1025,1025,1029,3084,1027,1027,1029,2060]),
  (8, [1038]),
  (9, [1038,1036]),
  (10, [1028]),
  (11, [1027,1027,1029,3,5,1025,1025,1029,1,5,1025,1025,1027,1,3]),
  (12, [1046]),
  (13, [1031,267785,268809,268809,268809,268809,267785,267785,268809,268809,268809,268809,267785,267785,268809,268809,268809,268809,266763,266763,529419,529419,266763,529419,266765,529421,529423,266767,266767,529423,529423,266767,529423,266765,529421,529423,266767,266767,529423,529423,266767,529423,266763,529419,529423]),
  (14, [1028,1,5,1]),
  (15, [1,1027,1,1])
]
def chunk_1 : List (ℕ × List ℕ) := [
  (16, [1029]),
  (17, [3,5]),
  (18, [3100,2076,1046,1054,4126,1029,1029,1025,1,1056,1,2082,1027,3,4128,3,3106,1029,1029,1025,1025,1027,1,3]),
  (19, [1060]),
  (20, [1041,791561,791561,791561,791561,5146,791561,791567,791561,791561,791561,791561,791561,534543,791561,791561,266765,791561,266761,266761,791561,791561,266761,791561,1043,791561,791561,791567,791567,791567,791567,534537,791567,266767,266767,791567,791567,266767,791567,1045,791567,791561,791567,266765,791567,272395,272395,272395,272395,272393,272395,272395,272395,272395,272395,272399,272395,266761,266761,791561,791561,266761,791561,266767,791567,791561]),
  (21, []),
  (22, [1,3,1]),
  (23, [3,3,3,3,1066,2092,3,1,3,1025,1,1032,5,1034,1027,1027]),
  (24, [3,5]),
  (25, [1,5]),
  (26, [1025,1,3,1,3,1025,6192,1025,2054,1,1,1074,1052,5,5]),
  (27, [1,1,3,1032,3,4138,1,1066,1074,1029,1029]),
  (28, []),
  (29, [1027,3116,1030,1,1,1027,1034,1052,1,1080,1029]),
  (30, [1025,1025,1,1025,1,1025,1,1027,1025,4142,1025,1025,3084,1025,1,1025,1,1025,1076,1025,1025,1,1025,1029,1025,1025,1025,1029,1078,1029,1082]),
  (31, [1038,1084])
]
def chunk_2 : List (ℕ × List ℕ) := [
  (32, [1025,1034]),
  (33, []),
  (34, [1,4162,1090]),
  (35, [1,1,1090]),
  (36, [1,3,1,1027,3,1,3,1025,1092,1034,6200,1094,7224,4166]),
  (37, [1038,1096]),
  (38, [2056,2116,3080,3140,1032,1092]),
  (39, [1038,1100]),
  (40, [267273,267273,267273,267273,267273,267273,267273,267273,267273,1031,267273,267273,267273,267273,267273,534543,267273,267279,267279,267279,267273,540681,1047,267279,267279,267279,267279,267279,534537,267279,802825,1041,1041,267275,267275,267275,267275,796681,267275,266765,279053,281609,282637,266765,279053,282633,282637]),
  (41, [1025,1025,1025,1025,1054,1027,3142,1029,1094,1027,3,5,1034]),
  (42, [2084,1038,3084,1036,1106]),
  (43, [267273,267273,267273,267273,267279,267273,267279,267273,267279,540687,267273,1031,267273,534539,267273,267273,267279,267273,540681,540681,1047,267279,796683,1041,17,1041,1041,17,1041,267275,540681,540681,267275,1041,1041,279053,284169,17,17,267275,796681,267277,281609,267277,282633]),
  (44, [529417,529417,529417,529417,529423,529417,529423,529417,529417,796687,529417,1070607,529417,529417,272399,529417,1857039,17,266761,17,529417,529417,282639,529417,534539,529417,529417,529423,529423,796681,796681,1070601,529423,529423,272393,272393,1857033,17,266767,17,529423,543753,282633,282633,796683,25,267275,266763,267275,25,796681,796681,1070601,25,281611,266765,267277,25,272393,272393,1857033,1041,17,25,1041,17,281611,543753,543753,25,282633,282633,282635,267275,267275,267275,267275,267277,1851401,267277,1064969,267275]),
  (45, [266761,266761,266761,266761,266761,266761,266767,266761,266761,266767,266761,266761,266761,266761,266761,8232,266761,266761,266761,266761,266761,9256,266761,266761,266761,266761,266767,266767,266767,266767,10280,266767,266767,266767,266767,266767,11304,266767,266763,1041,802825,802825,540681,540681,12368,12374,266765,1041,278537,278537,1589257,1589257,13392,13398,267275,1064969,1851401,12376]),
  (46, [266761,266761,266767,12378,266761,266761,266763,14426,266761,266761,266765,15450,266767,266767,266763,16474,266767,266767,266765,17498,266763,266763,266765,18522]),
  (47, [12380])
]
def chunk_3 : List (ℕ × List ℕ) := [
  (48, [12380,12378]),
  (49, [12314]),
  (50, [3,1025,1,1,1]),
  (51, [1027,1076,1124]),
  (52, [5]),
  (53, [3,3,3]),
  (54, [1025,3,6248,4202,1,1,1]),
  (55, [1076,1132]),
  (56, []),
  (57, []),
  (58, [5,3,1027,1027,1029,1136,2162,3,1027]),
  (59, [1029]),
  (60, [1,2160,3]),
  (61, [1,7282]),
  (62, [5,3]),
  (63, [1,1025,1,1025,4202,2164,1025,2166,1025,2054,1,1,1144,1146,1148,1029])
]
def chunk_4 : List (ℕ × List ℕ) := [
  (64, [1150]),
  (65, [1076]),
  (66, [278539,1041,1041,1047,288777,290825,1064971,1041,1041,1031,288783,290831,295433,534537,268813,295945,295945,295951,295945,267789,268813,267789,268813,267789,268813,267789,268813]),
  (67, [1041,1041,278543,17,1041,266767,17,267279,1047,267279,278537,17,1041,266761,17,267273,1031,267273,1041,284169,278543,17,1041,17,295951,281611,295945,278537,17,1041,17,295945,281611,295945,1041,1041,267789,295433,1041,268813,278537,278537,278543,17,17,268813,268813,268813,268813]),
  (68, []),
  (69, []),
  (70, []),
  (71, [1164]),
  (72, [1025,1032,1034,4232,4234,4238,1160,1162,1166]),
  (73, [2186,3210]),
  (74, [1038,1100,1168,1096,1170]),
  (75, [267785,267785,268809,268809,267785,267785,268809,268809,268809,1606155,268809,272395,272395,272397,272395,266767,266767,282639,282639,266767,279055,1045,824847,282639,266767,266767,282639,282639,266767,279055,1047,300559,282639]),
  (76, [1144]),
  (77, [1045,1612303,279051,21,9]),
  (78, [25,267785,25,267785,281611,17,17]),
  (79, [279051,279055,21,279055,23,17])
]
def chunk_5 : List (ℕ × List ℕ) := [
  (80, [268809,267785,268809,267785,557583,268809,1031,268809,1031,268809,268809,268809,268809,267785,267785,267275,267275,1070603,267275,796683,279053,796687,267279,267279,1070607,267279,796687,279053,796687,529421,13466,529421,1047,1047,14492,529421,12446,529421,10394,529421,1041,1041,12444,529421,12446,267279,267279,1070607,267279,267275]),
  (81, [267785,267785,1031,1070603,1031,1045,1031,1070603,1047,1047,543755,282635,1606667,272395,529419,529419,1851403,529421,1031,7,1031,266767,7,529423,1049,529423,266763,7,529419,1851403,1851403,19,529419,529419,529419,1031,7,1031,7,19,19,529419,266763,19,266763,7,7,7,529419]),
  (82, [1058]),
  (83, [295945,23,1082377,17,281609,17,281615,281609,1091081,281609,304649,304655]),
  (84, [558095,796687,1606671,272399,1606667,272395,267785,267785,8358,12446,529419,529419,529419,529419,529421,529423,529423,529423,529423,529421,266765,529421,529421,529423,529423,529423,529423,529419,266763,529419,529419,266767,529423,529423]),
  (85, [268809,268809,8324,8326,15510,12448,268809,268809,9348,9350,14486,13472,268809,268809,19588,19590,12438,10400,266763,266763,266765,12450,266763,529419,266765,529421,12456,266767,266767,266765,14498,266767,529423,266765,529421,12456,266767,266767,266763,15522,266767,529423,266763,529419,12456]),
  (86, [12458]),
  (87, [3171355,3171355,3171357,3190299,3171355,3171355,3190299,3190299,3190299,3190299,3171355,3171355,3190299,3190299,3190299,3190299,3171355,3171355,3190299,3190299,3190299,3190299,3171357,3171357,3190301,3190301,3190301,3190301,3171357,3171357,3190301,3190301,3190301,3190301,3171357,3171357,3190301,3190301,3190301,3190301,3170335,3170335,4743711,4743711,3170335,4743711,3170337,4743713,4743715,3170339,3170339,4743715,4743715,3170339,4743715,3170337,4743713,4743715,3170339,3170339,4743715,4743715,3170339,4743715,3170335,4743711,4743715]),
  (88, [12328]),
  (89, [267785,267785,268809,268809,268809,268809,267785,267785,268809,268809,268809,268809,267785,267785,268809,268809,266763,266763,529419,529419,266763,529419,266765,550927,552975,558095,558095,558095,1045,1049,558095,558095,558095,558095,266763,529419,558095]),
  (90, [267273,267273,267273,267273,267273,20658,267273,295951,267273,267273,1606157,267273,266761,266761,267273,267273,266761,267273,1031,267273,267273,267273,534543,267273,295951,295951,295951,1047,295951,267273,540681,278539,295951,295951,295945,295951,295951,534537,284169,266761,267273,266761,267273,295951,267273,1047,278539,272397,1070601,272397,281609,272397,272397,282633,272397]),
  (91, [12468]),
  (92, []),
  (93, []),
  (94, [4280,1210]),
  (95, [1025,1212])
]
def chunk_6 : List (ℕ × List ℕ) := [
  (96, [1146]),
  (97, [304649,1031,1097743,304649,304649,304655,1047,1097737,304655,304655,266765,279053,279053,1081865,796681,304649,573967,304655,573961,282637,279053]),
  (98, [279049,282633,279049,282633,282633,5270,282633,272399,282633,279049,282633,279049,282633,282633,21654,282633,272395,282633,282633,1606159,282633,266761,266761,282633,279049,266761,279049,8386,282633,282633,272399,272399,272399,272399,272399,272399,272399,272399,543753,1868299,562697,272395,272395,272395,272395,805897,1868303,824841,266761,266761,282633,282633,266761,279049,1031,300553,282633]),
  (99, [12484]),
  (100, [272399,279049,267273,279049,267273,1031,1031,267273]),
  (101, [3,1,1208,4280,1210]),
  (102, [1046,1226]),
  (103, [1046,1054]),
  (104, [268815,10440,279049,279049,577039,272395,529417,529417,577039,21662,315407,1868299,529419,279049,529417,1043,279049,529417,1031]),
  (105, [1,5]),
  (106, []),
  (107, []),
  (108, [3,2260,2262,5]),
  (109, [1,1029,1,1]),
  (110, []),
  (111, [1027,1244])
]
def chunk_7 : List (ℕ × List ℕ) := [
  (112, [3,4308,5]),
  (113, []),
  (114, [1,4322,1,5]),
  (115, [1234,6360,1046,1242,7198,1025,1,1027,1,6250,1029,1246,5,1248,5,1025,1025,1029,1,5,1074,4324]),
  (116, [1,5]),
  (117, [6376,1054,1,1,1242,1,1,1029,1]),
  (118, [3108,1254,1258]),
  (119, []),
  (120, [1,1262]),
  (121, [1264]),
  (122, [279055]),
  (123, [529423,529421,279049,17,796683,323087,557581,17,1111051,17,18676,304651]),
  (124, []),
  (125, [1272,1,1]),
  (126, [1046,1274]),
  (127, [796687,272393,327179,272393,796687,272393])
]
def chunk_8 : List (ℕ × List ℕ) := [
  (128, [1,1]),
  (129, [1027,1280]),
  (130, [1639439,21]),
  (131, [315401,272399,315401,585231,1606671,315401,557581,315401,16638,315401,267785,585231,268809,1606671,796685,17,327177,1041,17,300555,577033,282635,267275,267275,12548,267275,1045,1041,1041,267275,17,267275]),
  (132, [1101839,12488,279049,279049,585227,268815,267273,267273,272399,1868811,279049,267273,1031,1031,267273]),
  (133, []),
  (134, [1,2274,1,1,3338]),
  (135, [1,7434,1]),
  (136, [1025,1025,6412,1252,1242,1280,1294,1029,1029,1029,5]),
  (137, [2084,1150,1076,1296]),
  (138, [1025,1056]),
  (139, [22682,1043,279049,1606159,566795,1874443,333323,1874447,23]),
  (140, [1094]),
  (141, [1120777,1031,1097743,1120777,1120777,23,304655,23,1047,279053,23,304655,23,529417,1120777,304655,1120777,573967,1120777,1111055,304655,304649,304655,304655,1120777,279053]),
  (142, [529417,1031,21,796687,23,17,1120777,314895,281609,279053,279053,281609]),
  (143, [1031,23,1081865,1906191,1906191,573967,304655,573961])
]
def chunk_9 : List (ℕ × List ℕ) := [
  (144, [5278,279049,1645071,279055,1645065,279049,7,23]),
  (145, [1092]),
  (146, [18586,17668,529423,1645065,1031,861193,279049,7,23]),
  (147, [25,272399,282637,25,272399,21660,17,21748,281611,17]),
  (148, [1857033,1857033,23712,1857033,16592,1857033,272395,1857033,1606155,529417,529417,1857033,529417,9462,1606155,1857033,1606155,272395,272395,15622,24840,272395,282639,279055,1045,279055,1606153,1643529,1045,272393,1868811,1868299,791567,791567,21782,791567,10522,10524,10526,12576,272395,272395,272395,272395,1868297,1905673,1045,272395,272395,272395,1045,529417,529417,1857033,529417,272393,279055,272393,272395,272395,791567,791567,21796,791567,1047,14630,1047,12576]),
  (149, [21700,12328,12584]),
  (150, [267273,7,295945,23,1082377,17,281609,17,12454,281609,1091087,281615,1091081,281609,304649,336905]),
  (151, [791561,791561,5288,791561,791567,791561,534543,791561,267277,791561,791561,791561,791561,1043,540685,791561,1043,820233,534537,791567,791567,791567,791567,1045,791567,267277,802829,791567,1045,1868809,272393,1868815,272399,272395,272395,13612,12576,791561,791561,791561,791561,791567,266767,791567,791567,266761,791561,791561]),
  (152, [12328,12590]),
  (153, [272421,272421,2144285,529447,6604831,4533279,272421,272421,6862877,529449,6604835,4533283,272421,272421,7125027,529451,1361949,4271133,272421,272421,7125023,529453,5556253,5843997,4502051,4502051,4502047,4502051,4239901,4239901,4764193,4239901,266791,266791,266797,529447,266791,529447,266797,529453,4272669,266793,266793,266795,529449,266793,529449,266795,529451,4272669,4239901,4239901,4764193,4239901,4502051,4502051,4502047,4272669]),
  (154, [272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,272421,796719,847397,585253,796719,272421,272421,1643557,272421,796719,796719,796719,796719,796713,796713,796713,796713,272421,272421,1905701,272421,796719,796719,1119279,796719]),
  (155, [272421,272421,272421,272421,272421,28980,272421,272421,272421,2144285,4502051,272421,272421,272421,272421,272421,272421,6604835,272421,4533283,272421,272421,272421,272421,529451,272421,272421,272421,272421,272421,272421,272421,6342691,272421,5319715,272421,272421,272421,272421,272421,272421,6604831,272421,796719,272421,6862875,557615,272421,272421,272421,272421,272421,272421,3190307,272421,6630431,272421,272421,272421,272421,791597,272421,272421,796719,796719,847397,796719,585253,6604835,6604835,4533283,4533283,272421,272421,272421,1606181,1643557,272421,796719,796719,796719,266797,796719,5319715,796713,796713,796713,266795,796713,4534819,272421,272421,272421,1868325,1905701,272421,4502051,4502051,1119279,4502051]),
  (156, [315401,529423,315401,558095,315401,1031,315401,315401,1606671,315401,1043,315401,315401,315401,282639,315401,8392,315401,267785,558095,529419,268809,315401,268809,315401,267785,1606671,529421,268809,315401,268809,17,327177,1041,17,12444,577033,12446,267275,267275,1070603,267275,267277,266767,266767,529423,17,267277,266767,266767,529423,17,267275]),
  (157, [1041,1041,1041,1041,267787,314891,17,791561,266767,17,791567,791561,791561,17,791567,266761,17,791561,791561,791561,1041,332809,278543,17,1041,17,267277,278537,17,1041,17,267277,314891,314891,314891,314891,278537,278537,278543,17,17]),
  (158, [3,1027,3,1027,1,3,1130]),
  (159, [1038,1036,1070,1340])
]
def chunk_10 : List (ℕ × List ℕ) := [
  (160, [1041,1041,267275,1130505,278543,7,278537,23,1041,1041,281611,295945,278543,278537,295433,278537]),
  (161, [529417,529417,529417,529417,268815,529417,21816,529417,529417,791563,529417,529417,791565,529417,266761,529417,529417,266761,266761,529417,529417,19770,529417,21672,529417,315407,315407,558089,1047,796681,1070601,315407,315407,1606665,1045,272393,1857033,315407,315407,543753,18752,282633,12496,266763,266763,266765,1047,266763,791563,266765,791565,529417,266761,266761,529417,529417,266761,529417,266765,791565,529417,266761,266761,529417,529417,266761,529417,266763,791563,529417]),
  (162, [21674,12610]),
  (163, []),
  (164, []),
  (165, [1,7494,1,1352]),
  (166, [3,1236]),
  (167, [2376,1,3338]),
  (168, [3,1,5]),
  (169, [3,1027,2378,1240,2380,1358,3,1027,1029,3,1360,1029,1029,1029,1029,1029]),
  (170, [3,3,1250,5]),
  (171, [1,1025,1,1025,6248,1025,6192,2164,1025,6412,1,1,1025,1025,1025,4436,1234,5,5]),
  (172, [1025,1025,2166,1,1025,1]),
  (173, [6482,1076,1366,1368]),
  (174, [295945,295945,295945,295945,295945,295945,266763,1041,266763,1041,1041,1041,266763,288777,290825,295945,295945,295945,1031,351241,295945,295433,534537,332809,295945,295945,295945,295945,295945,12420,295945,281611,295945,295945,295945,295945,295945,295945,295945,295945,295945,295945,295945,278543,278543,278543,281611,281611,281611,281611,796685,281611,796685,796685,796685,796685]),
  (175, [12636])
]
def chunk_11 : List (ℕ × List ℕ) := [
  (176, [529445,3715611,3715611,3715611,3715611,30002,3715611,3977757,3715611,3715611,3715611,3715611,3715611,31030,3715611,3715611,4481567,3715611,3715611,3715611,3715611,3715611,3715611,5549597,3715611,5326365,3715611,3715611,3715611,3715611,266797,3715611,3715611,3977757,2668571,3977757,3977757,32054,3977757,3977757,3977757,3977757,3977757,3977757,5549595,3229211,5850651,3977757,3977757,3957281,3977757,3977757,3977757,3977757,266797,3977757,3748379,272431,272431,6076443,791601,6604829,4008989,272431,272431,8435741,791603,1361947,3746843,272431,272431,4808731,266797,3196955,1387547,266801,266801,266803,791601,266801,791601,266803,791603,3748379,3715611,3715611,3715611,3170337,3957281,3715611,3977757,3977757,3977757,3170335,4481567,3748379]),
  (177, [266761,266763,266761,12376]),
  (178, [4239899,4239899,4239899,4239899,4239899,4239899,4239901,4239899,4239899,4239901,4239899,4239899,4239899,4239899,4239899,4239899,34102,4239899,3236899,4239899,4239899,4239899,4239899,4239899,4239899,35126,4239899,3236895,4239899,4239899,4239899,4239899,4239899,4239899,1361949,4239899,4271133,4239899,4239899,4239899,4239899,4239899,4239899,5556253,4239899,5843997,4239899,4239899,4239899,4239899,4239901,4239901,4239901,2144283,4239901,36150,4239901,3236899,4239901,4239901,4239901,4239901,6862875,4239901,37174,4239901,3236895,4239901,4239901,4239901,4239901,2449435,4239901,1361947,1361947,4271131,4271131,4239901,4239901,4239901,5070875,4239901,5556251,5556251,5843995,5843995,272421,272421,272421,272421,2144283,2144283,4743715,272421,6604831,272421,3236899,272421,272421,272421,272421,272421,6862875,6862875,4743711,272421,6604835,272421,3236895,272421,272421,272421,272421,272421,2449435,2449435,266795,272421,1361947,1361947,4271131,4271131,272421,272421,272421,272421,5070875,5070875,266797,272421,5556251,5556251,5843995,5843995,3236899,3236899,847397,3236899,585253,3190299,5588507,1394203,3236899,1606693,1606181,1643557,3170851,3170851,3236899,3236899,3170851,3236899,267309,3236899,4272667,3170847,3170847,3236895,3236895,3170847,3236895,267307,3236895,4272667,1868837,1868325,1905701,3170851,3170851,3236899,3236899,3170851,3236899,3170847,3236895,4272667]),
  (179, [1362]),
  (180, [17,17,266767,17,266767,17,17,17,1041,17,1041,17,17,17,1041,1041,17,17,1041,19,1041,1041,266767,17,17,266767,1041,266767,17,1041,17,17,1041,17,1041,354315,1041,278537,791561,19,17,1041,17,1041,295433,1041,1041,266765,19,19,354315,19,354315]),
  (181, [1038,1070]),
  (182, [295945,266767,295945,295945,295945,295945,295945,295945,25778,295945,355339,295945,295945,295945,295945,540687,295945,295945,295945,295945,295945,295945,796685,295945,266763,1041,266763,1041,802831,802831,540687,288777,290825,295945,295945,295945,1665033,351241,295945,295945,295945,295945,295945,534537,332809,266767,266767,266767,355339,1064975,1064975,1851407,796685,355339,1031,1064975,1851407,796685]),
  (183, [1038,2060,1025,1082]),
  (184, [529417,529417,529417,529417,534541,529417,529417,1049,529417,21530,529417,791565,529417,266761,266761,529417,529417,266761,529417,266763,529417,529417,1047,880649,558089,1047,796681,1070601,791565,356361,1606665,791565,272393,1857033,1049,1142797,543753,1049,282633,1857037,266765,1047,266765,1047,278539,278539,266765,791565,529417,266761,266761,529417,529417,266761,529417,266765,791565,529417,1064969,278539,278539]),
  (185, [267273,267273,267273,267273,267273,267273,267273,267273,267273,1665039,267273,267273,534543,267273,295951,295951,295951,267273,540681,1047,295951,295951,295945,295951,1667081,534537,284169,802825,1041,1041,295947,1082377,295947,1929225,796681,1070601,266765,279053,282637,266765,279053,282637]),
  (186, [267273,267273,267273,267273,267279,267273,1041,267273,1130511,1665035,267273,1665035,267273,284175,267273,267273,1041,267273,540681,540681,1047,1041,284169,1041,17,1041,1041,17,1041,295947,540681,295947,1041,295951,1667081,284169,17,17,1082377,796681,267277,281609,267277,282633]),
  (187, [791561,791561,791561,791561,791567,1043,791561,1041,791561,534541,791561,791567,266767,791561,791567,791561,791561,1041,284169,17,1041,17,1041,791561,1589257,1589257,1045,1041,284169,1041,17,1041,17,267277,1589257,1589257,267277,1868809,272393,295947,295947,805897,282633,17,17]),
  (188, [529417,529417,529417,529417,529423,529417,1665035,529417,529417,534541,529417,295947,272399,529417,1857039,17,266761,17,529417,529417,282639,529417,534539,529417,529417,880649,558089,796681,796681,1070601,356361,1606665,272393,272393,1857033,17,278543,17,356367,543753,282633,282633,796685,880649,558089,796681,796681,1070601,25,1606665,25,272393,1041,17,25,17,543753,543753,25,282633,295947,295947,295947,295947,267277,1851401,267277,1064969,295947]),
  (189, [266761,266761,266761,266761,266761,266761,266767,266761,266761,266761,28008,266761,266761,266761,266761,266761,5484,266761,266761,9256,266761,266761,266761,266761,278543,802825,802825,540681,14516,278543,278543,278537,278537,1589257,14704,278543,1041,802825,802825,540681,12658,12660,266765,1041,278537,1589257,1589257,12662,295947,1064969,1851401,12664]),
  (190, [12666]),
  (191, [1168])
]
def chunk_12 : List (ℕ × List ℕ) := [
  (192, [1160,1166]),
  (193, []),
  (194, [7234,4162,1090]),
  (195, [1410,1412]),
  (196, [1090]),
  (197, [1041,360971,21,21,360971,360971,17,17,1041,295439,1041,362507,363019,363019]),
  (198, [17,17,17,17,17,17,17,17,17,1041,17,1041,360459,1041,266761,278537,791561,1041,17,17,17,17,17,1041,17,1041,295439,1041,1041,21898,1041,17,1041,17,1041,295433,1041,1041,12682,1041,336907,336907,360459,360459]),
  (199, [791561,791567,791561,791567,791567,791561,791567,791561,1041,1041,279051,300555,1041,332815,17,17,1041,1041,1043,1041,1043,1041,332809,17,17,1041,1041,1045,1041,1045,336907,336907,300555,300555,281611,281611,300555,300555]),
  (200, [267273,267273,23,17,21,267273,279053,336905]),
  (201, [529417,529417,529417,529417,529417,529417,279055,529417,279055,529417,529417,534539,284171,529417,529417,534541,534539,529417,562703,529417,529417,880649,558089,796681,796681,1070601,356361,1606665,272393,272393,1857033,266767,17,282639,17,543753,543753,10640,282633,791563,880649,791563,1070601,791565,356361,791565,1857033,266767,17,282639,266767,17,279055,543753,543753,562703,282633,282633,282639,1851401,884751,1064969,360463]),
  (202, [266761,281609,281609,281609,266761,281609,281609,281609,278537,281615,281615,281615,266767,281615,355337,281615,1064969,281611,1041,281611,266763,281611,1141769,281611,360457,282633,300553,281609,281609,281609,281609,281609,281609,281609,281609,281609,281609,281609,281609,281609,281609,281615,281615,281615,281615,281615,281615,281615,281615,281615,281615,281611,281611,281611,281611,281611,281611]),
  (203, [279053,267273,622605,884749,360461,279053]),
  (204, [267273,282637,267273,1031,622605,1031,267273,344079,295945,282637,267279,1047,884749,1047,267279,344073,1082377,282637,267275,1041,360461,1041,267275,1130505,266765,279053,279053,12694,282637,562701,622605,282637,282637,16578,12688,282637,824845,884749,282637,282637,14530,21904,282637,300557,360461,282637,282637,12482,5520,282637,279053,282637,282637,279053,360457,12694,300553]),
  (205, [279049,279049,282633,282633,279049,279049,282633,282633,279049,279049,282633,282633,282633,622607,282633,279055,279055,282639,282639,279055,279055,282639,282639,543753,622601,562697,279051,279051,282635,282635,805897,884745,824841,281609,360457,300553]),
  (206, [562701,622605,282637,282637,622605,562701,622605,824845,884749,282637,282637,884749,824845,884749,300557,360461,282637,282637,360461,300557,360461,282637,282637,279053,360457,12694,300553,279053,266765,279053,279053,282637,12694]),
  (207, [267273,267273,267279,12374,267273,267273,267275,14422,540687,8588,8590,267273,12658,267273,282637,27844,15762,267279,267279,267275,16470,540681,10636,10638,267279,21874,267279,282637,32964,17810,802825,13708,13710,267275,5490,267275,282637,25796,18834,266765,282637,12692,12696,266765,282637,12698,12700])
]
def chunk_13 : List (ℕ × List ℕ) := [
  (208, [12380,12702]),
  (209, [791561,791561,791561,791561,791561,791561,791567,791561,791567,791561,791567,791561,791561,618511,284175,791561,267277,266761,17,791561,266761,17,791561,1043,791567,791561,791561,791567,791567,618505,284169,266767,17,791567,266767,17,791567,1045,791561,1589257,267277,1041,1041,618505,284169,266767,17,791567,266767,17,791567,266765,791561,266761,17,791561,266761,17,791561,266765,791561,1868809,272393,805897,282633,266761,266761,791561,17,17]),
  (210, [5290,16706,14658,12328,12706]),
  (211, [791589,266805,791589,266805,791589,1355299,3753507,4277795,791589,791589,3191331,791589,3191331,2437661,3191331,791589,3455011,791589,3222559,9776157,3222559,3695137,3695137,3695137,4481563,4481563,266805,791589,4481563,791589,267315,266805,3224099,540723,266805,266795,266805,791589,3191331,791589,3191331,3191331,10044955,2991643,2467355,3191331,791589,6338595,791589,3222559,3222559,3222559,3514909,3514909,266805,791589,3514909,791589,266805,266805,266805,266805,3191323,3224099,8486435,3695137,3695137,3957277,3957277,1079,791589,3957277,791589,540725,540725,540725,540725,3224099,3224099,3191331,3191331,3191331,3191331,3222559,3191331,3191331,3191331,3191331,3191331,3191331,3191331,266805,3191331,266805,3191331,3191331,3191331,3191331,3191331,3224093,3191331,1589285,266805,3191331,5556255,3222559,5556255,3222559,3222559,3222559,3222563,3222563,3222559,3222559,4546595,3222559,3746845,5581859,3191327,3222559,3191327,3222559,3222559,3222559,3222563,3222563,4481563,4481563,3514909,266805,4481563,3191323,791589,3514909,791589,3191323,3224099,278565,3191331,3191331,3957277,3957277,266799,267315,3957277,791589,278565,278565,266799,791599,3224099,3224099]),
  (212, [266789,3957275,3957275,3957275,3957275,40110,3957275,3957277,3957275,3957275,3957275,3957275,3957275,41312,3957275,3957275,3957275,3957275,3957275,42336,3957275,3957275,3170337,3957275,3170331,3170331,3957275,3957275,3170331,3957275,266803,3957275,3957275,3957277,3957277,3957277,3957277,43360,3957277,3957277,3957277,3957277,3957277,44384,3957277,3170333,3170333,3957277,3957277,3170333,3957277,266805,3957277,3957275,3957277,3170337,3957277,3191331,3191331,3191327,40292,3191331,3191331,8486427,266805,3514909,29094,3191331,3191331,8486429,266803,3514907,45478,3191327,3191327,6651419,266805,2728477,46502,3191327,3191327,6651421,266803,2728475,47526,3170331,3170331,3957275,3957275,3170331,3957275,3170333,3957277,3957275]),
  (213, [791561,791561,791561,791561,791561,18610,791561,1928207,791561,791561,791561,791561,791561,791561,791561,791561,791561,791561,791561,791561,791561,266761,791561,266761,791561,791561,791561,1928207,820233,1928207,618505,534537,284169,266767,266767,1928207,1928207,266767,1928207,1045,1928207,791561,1589257,1868299,1928207,272395,1142793,1868809,272395,272393,1857033,272395,272395,805897,272395,282633,272395,266761,266761,791561,791561,266761,791561,266767,1928207,791561]),
  (214, [529417,529417,529417,529417,534539,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,266761,266761,529417,529417,266761,529417,1049,529417,529417,791563,880649,558089,791563,796681,1070601,1045,356361,1606665,1045,272393,1857033,1049,1142795,543753,1049,282633,1857035,266763,266763,791563,791563,266763,791563,278541,791563,529417,1851401,278541,791563,266761,266761,529417,529417,266761,529417,266763,791563,529417]),
  (215, [355337,355337,355337,355337,355337,1031,355337,355337,355337,355337,355337,355337,355337,355337,355337,534539,355337,355343,1047,355343,355343,355343,355343,344073,355343,355343,355343,355343,796683,355343,266763,267275,802825,267275,266763,267275,267273,344073,1041,279053,281609,282637,1589257,279053,282633,282637,267275,267275,267275,267275,267275,267275]),
  (216, [267279,267279,267279,267279,1041,267279,540687,540687,1031,1041,284175,267279,1141769,267279,1141769,1041,17,1041,1041,17,1041,355339,540687,540687,355339,1141769,1041,1141769,284175,267279,290825,17,17,267279,267279,267279,267279,17,17,1082383,796687,267277,281615,267277,282639]),
  (217, [791567,791567,791567,791567,1041,284175,17,17,1041,791567,1589263,1589263,1043,791567,791561,791567,791561,1041,1041,618511,284175,17,791561,1041,17,1041,791561,266761,278537,791561,791567,332809,791567,791567,1045,791567,1045,1868815,272399,355339,355339,805903,282639,17,17]),
  (218, [356361,529423,356361,529423,356361,356361,796687,356361,1070607,356361,356361,272399,356361,1857039,17,278537,17,356361,356361,282639,356361,534541,356361,529417,25,529417,25,880655,558095,558095,25,796687,796687,1070607,25,356361,529417,356361,25,272393,272399,1857033,1041,17,25,1041,17,281611,1666057,543759,25,282633,282639,282635,529423,529423,796685,323081,355339,529423,529423,17,17,529423,529423,355339,355339,355339,355339,267277,1851407,267277,1064975,355339]),
  (219, [278537,266767,278537,278537,278537,278537,266767,278537,278537,278537,278537,278537,278537,8618,278537,278537,278537,278537,278537,8620,278537,278537,278537,266761,278537,266767,266767,266761,278537,266763,1041,802831,802831,540687,540687,14766,12720,266761,278537,278537,278537,266761,278537,13392,12722,266767,266767,266767,266767,12652,266767,266767,278537,266767,266767,266767,266767,355339,1064975,1851407,12724]),
  (220, [266761,7,281609,7,266761,281609,281609,281609,278537,7,266763,7,266767,7,355337,7,1064969,7,266767,7,266763,7,1141769,7,266761,7,281609,7,266761,281609,266761,281609,360457,282633,300553,7,281609,281609,7,281609,281609,7,281609,281609,7,281609,281609,281609,281609,281609,281609,7,7,7,7,7,7,1031,1031,1031,1031,7,7,1031,1031,1031,1031]),
  (221, []),
  (222, [3514,1]),
  (223, [5])
]
def chunk_14 : List (ℕ × List ℕ) := [
  (224, [3514]),
  (225, [1468,7614,3,3,1472,2092,1,1025,1,5]),
  (226, [1,1466]),
  (227, [3524,1472,1]),
  (228, [1038,1070,1474,1025,1478]),
  (229, [1,5]),
  (230, [1028,1029,1]),
  (231, []),
  (232, [5]),
  (233, []),
  (234, [3538]),
  (235, [3]),
  (236, [2506,3532,1029,1030,1025,1,1486,1,2512,1027,3,6612,3,3542,7210,7616,1025,1025,1027,1,3]),
  (237, [1090]),
  (238, [3540,1472,1,1094,3,5,1034,1027,3546]),
  (239, [2520,1038,3084,1070,1500])
]
def chunk_15 : List (ℕ × List ℕ) := [
  (240, [355337,355337,355337,355337,355343,355337,355343,1031,355337,1031,355337,344079,355337,534539,355337,355337,1047,355343,1047,355343,344073,355343,796683,266763,267275,267275,267275,267275,267275,344073,279053,379401,279053,385033,267275,17,267275,267273,17,281609,1589257,282633,267275,267275]),
  (241, [6364,2268]),
  (242, [4424,3,1352,1,5]),
  (243, [1025,1,3,1,3,4436,4426,1252,4124,1364,1354,4324,1052,5,1029,7650,5,1508]),
  (244, [3,3,1250]),
  (245, [5]),
  (246, [1,1,4584,1,1,4586,1252,1029]),
  (247, [4148,1510,1516]),
  (248, [1027,1027,4126,3,1027,4324,1029,1025,5]),
  (249, [1254,1076,1520]),
  (250, [267273,267273,267273,267273,267273,267273,7,267273,1031,267273,7,267273,267273,1665039,267273,534543,295951,295951,295951,295951,295947,295951,295947,1047,295951,1047,295945,534537,295951,295951,1041,1041,1041,1082377,796681,266761,267273,267273,279053,1175567,279053,390159,529421,529421]),
  (251, [1474]),
  (252, [1038,1027,1025,1078]),
  (253, [7,267273,7,281615,7,1165835,7,1165839,7,281609,7,1165839,267273,391183,295945,23,1082377,17,21,1175563,1175567,281609,1175567,529421,391695,1091081,304649,529421,336905]),
  (254, [1080]),
  (255, [1615373,566797,279049,599053,25,19,21,279049,392719,543757,336905])
]
def chunk_16 : List (ℕ × List ℕ) := [
  (256, [529423,1171467,529419,1171471,279049,279049,1031,1171471,272399,7,267273,1666063,282639,390155,390159,279049,390159,267273,12798,356367,596489,858633,529421,336905,21]),
  (257, [267273,267273,267273,267273,267273,267273,267273,266767,267273,266767,267273,10666,267273,278543,267273,267273,267273,267273,267273,266763,267273,266763,267273,13738,267273,278539,267273,266761,266761,267273,267273,266761,266761,267273,267273,28088,267273,1031,267273,16814,267273,16864,267273,267273,15448,267273,267273,267273,267273,267273,267273,14516,267273,278543,267273,267273,267273,267273,267273,267273,12468,267273,278539,267273,266761,267273,266761,266761,267273,267273,267273,267273,12658,267273,12788,267273,267273,267273,267273,529421,267273,267273,267273,278543,278543,278543,278543,278543,278543,278539,278543,540681,278539,278543,278543,295945,278543,1667081,534537,284169,802825,278543,278543,278539,1082377,278539,1929225,796681,1070601,266765,529421,281609,12794,266765,529421,282633,12800]),
  (258, [529423,1070605,529419,272397,1857039,279049,279049,529423,1857039,791561,791561,1666063,282639,1070605,272397,279049,1043,791561,543757,356367,1645065,356363,861193,334345,23]),
  (259, [791561,791561,791561,791561,791561,791561,791561,266767,791561,266767,791561,10668,791561,278543,791561,791561,791561,791561,791561,529419,791561,5556,791561,12328,791561,266765,791561,266761,266761,791561,791561,266761,266761,791561,791561,266767,791561,266767,791561,13392,791561,17494,791561,791561,791561,791561,791561,791561,14704,791561,278543,791561,791561,791561,791561,791561,14712,791561,791561,791561,791561,266765,791561,791561,791561,266761,266761,791561,791561,266761,791561,540685,791561,540685,791561,791561,791561,278543,820233,278543,618505,534537,284169,278543,278543,278543,278543,278543,278543,266765,278543,1589257,266765,278543,356363,1142793,1868809,266765,272393,1857033,278539,356363,278539,356363,805897,1064973,282633,12804,278537,278543,278543]),
  (260, [266761,266761,266761,266761,266761,266761,266761,266767,266761,21942,266761,266761,266761,266761,266761,266763,266761,5558,266761,266761,15450,266761,266761,266761,266761,266761,12666,266761,266761,266761,266761,266761,14714,266761,266761,266761,266761,266765,266761,266761,266761,278543,802825,540681,12802,278543,278537,1589257,12806,278539,1064969,1851401,14854]),
  (261, [12380,12808]),
  (262, [3170843,3170843,3170843,3170843,3170843,3170843,3170843,3170843,3170843,266791,3170843,3170843,3170843,3170843,3170843,3252767,3170843,3170843,3170843,3170843,3170843,3252769,3170843,3170845,3170845,3170845,3170843,2231323,266799,3170845,3170845,3505691,3170845,3170845,3252767,3170845,3170845,3243547,3170845,3170845,3252769,3170845,2755611,266789,266789,3170851,6389275,3170851,3170851,3252767,3170851,3170851,5602843,3170851,3170851,3252769,3170851,3170335,3252767,3252767,3252767,3170335,3252767,3252763,3252767,3170337,3252769,3252769,3252769,3170337,3252769,3514907,3252769,3252767,3252767,3252767,3252767]),
  (263, [267273,267273,267273,267273,1031,267273,267279,1047,23,1041,1041,267279,267279,267275,23,17,17]),
  (264, [8232,8494,266761,12368,266761,14422,266761,12374,266761,12814]),
  (265, [267787,267791,267785,267791,267785,267785]),
  (266, [12818,267785,272395,272399,272399,267785,267785]),
  (267, [327179,272395,23,272397,19,23]),
  (268, [12542,22036,1615375,272393,13844,796687,566793,12822,272393,796687,272393]),
  (269, [1254]),
  (270, [1046,1242]),
  (271, [268809,267785,315401,267785,267791,315401,663055,315401,1711631,315401,8724,662537,663049,1711113,1711625,315407,10772,267275,267275,267277,267275,267277,1041,1041,267277,17,267277,1041,1041,267275,17,267275])
]
def chunk_17 : List (ℕ × List ℕ) := [
  (272, [315401,267791,662543,1711119,267785,662537,1711113,662537,1711113,17,17,267275,17,17]),
  (273, [1101839,268811,663055,268815,267273,267273,315407,1031,7,267273,17,267273]),
  (274, [333321,272399,327183,17,16918,272393,327177,17,14870,662537,267277,281613,25,17]),
  (275, [279049,529423,25,17,17,314893,314891,17,17,304651]),
  (276, [22788,16644,279049,529421,333327,596489,858633,21]),
  (277, [1294]),
  (278, [1031,1047,267275,267275,267277,304649,666639,666633,666633]),
  (279, [272393,272393,272393,272393,272399,272393,272399,272393,272393,21766,272393,22792,1606671,272393,1643535,272393,16920,272393,272393,847369,272399,12550,272399,5384,1606665,1606665,1643529,272399,14872,279051,847369,282635,662537,585225,12830,12832,5666,1606665,1606665,1643529,1041,17,12836,1041,17,300555,18982,282635,267275,267275,5672,267275,13868,1868809,1868297,1041,1041,267275,17,267275]),
  (280, [5316,12846]),
  (281, [266761,12368,266761,12374]),
  (282, [8388,266761,10320,266761,12690]),
  (283, [791561,791561,534543,791561,791561,1667087,284169,791567,618505,1589257,1041,1041,791567,791567,618505,284169,1041,1041,1589257,272393,267275,805897,267275,267275,805897,282633]),
  (284, [26820,8232,8488,266761,13392,266761,14738,266761,13398,266761,12854]),
  (285, [2142747,2142747,2142749,266789,2142747,266789,2142749,266789,266789,266789,266789,266789,266789,2142749,266789,266789,267303,266789,266789,266789,266789,266789,2142749,266789,266789,267305,266789,266789,266789,266789,266789,2436131,266789,266789,266789,266789,266789,2142747,266789,266789,267311,266789,266789,266789,266789,266789,2142747,266789,266789,267313,266789,266789,266789,266789,266789,2960419,266789,266789,266789,266789,267311,802853,802853,540709,540709,4015643,3515931,2729499,267321,3170851,3170851,1083,267311,802853,802853,540709,540709,540709,540709,3252767,3281435,267311,278565,278565,1589285,3551775,3290147,3170847,1085,3170847,1085,802853,802853,802853,802853,540709,540709,3814427,3281435,3170851,3170851,3290147,3290147,802853,802853,802853,802853,540709,540709,540709,540709,3252763,3290139,3814427,3281435,3514913,1085,278565,278565,1589285,1589285,3814939,3291675,266789,266789,266789,3290143,1064997,1064997,1851429,3551779,3290143,3252769,1083,1064997,1064997,1851429,1851429,3290651,3815963]),
  (286, [3191323,3191323,3191323,3191323,3191323,3191323,3191325,3191323,3191323,3191325,3191323,3191323,3191323,3191323,3191323,3191323,3753501,3191323,3253789,3191323,3191323,3191323,3191323,3191323,2173987,3191323,7175709,3191323,266803,3191323,3191323,3191323,3191323,3191323,3224093,3191323,3191323,3191323,3191323,3191325,3191325,3191325,3191325,3191325,3753499,3753499,3253787,3253787,3191325,3191325,3191325,3191325,2698275,3191325,7175707,7175707,266805,3191325,3191325,3191325,3191325,3191325,3224091,3224091,791589,791589,791589,791589,3514915,791589,3514915,791589,3753499,3753499,3253787,3253787,791589,791589,791589,791589,1361951,791589,3289631,791589,7175707,7175707,3170849,791589,266789,266789,791589,791589,266789,266789,791589,791589,267307,791589,3224091,3224091,3552291,6338587,3552291,618533,534565,284197,3170851,3170851,3552291,3552291,3170851,3552291,1087,3552291,3224091,8486427,3170849,3552291,3289631,1142821,4022299,3289631,5556251,3222555,3289631,3289631,4546587,3289631,3196955,5581851,266789,266789,791589,791589,266789,791589,3170851,3552291,3224091]),
  (287, [1027,1080])
]
def chunk_18 : List (ℕ × List ℕ) := [
  (288, [1038,1100,1025,1598]),
  (289, [334345,622605,529423,279049,334345,19,1982989,1031,360969]),
  (290, [791567,278543,791567,1041,791567,791567,791567,1041,934413,791567,21,21,1041,1041,1041,1045,410127,278543,17,17,1041,1041,332815,1041,1041,1043,1041,363019,363019]),
  (291, [791567,21,21,17,17,1041,362507,1043]),
  (292, [5,5,1,1029]),
  (293, [7220,1025,1608]),
  (294, [272393,529417,279051,400905,17,360971,334347,17]),
  (295, [3]),
  (296, [1,1090]),
  (297, [1090,5]),
  (298, [1,1,5,1029,7758,3664,1,5,1,1294,1618]),
  (299, [1038,3144,1025,1620]),
  (300, [791561,791561,1041,791561,1041,791561,791561,1041,5698,17,791561,17,791561,1041,791561,266761,278537,791561,1041,1041,1041,295439,1041,267277,22084,1041,22086,1041,332809,1041,17,1041,17,12682,1041,1045,1045,1041,1045,336907,336907,412681,12876,334347,334347,415753,410121,17,17]),
  (301, [791561,791567,791561,791567,1041,267277,1043,1041,1045,21,17,17]),
  (302, [266761,13392,266761,15446,12684,278537,12888,278537,12686,278537,12890]),
  (303, [3290139,3290139,3290139,3290139,3290141,3290139,3290141,3290139,3290141,267303,3290139,267303,3290139,3281437,540711,3290139,2252317,3290139,3553821,3290139,3290139,3290141,3290139,267311,3290141,267311,3290141,3281435,540719,3290141,2252315,3290141,3553819,267301,267301,267301,267301,267301,267301,3290147,3252771,267301,3290147,267301,267301,3252767,3281435,540719,267301,2252315,267301,267301,282669,3553819,267301,267301,3290147,2699803,540709,540709,1083,3290147,2960411,1085,61,1085,1085,61,1085,3290143,540709,540709,3290143,1085,1085,1667109,284197,61,61,1082405,3551771,3290145,281637,3290145,282661])
]
def chunk_19 : List (ℕ × List ℕ) := [
  (304, [1160,1162]),
  (305, [25,279055,17,17,25,279049,17,942603,334347]),
  (306, [7,23,23,267275,267275,17,1120777,304655,336911,304649,336905,666633,304649,1204745,336905]),
  (307, [1070601,796681,796687,1031,534539,267273,534539,796687,796681,1047,796683,267279,796683,267275,300557,594953,25,1700873,5666,1041,1041,19042,282637,267275,1081865,267277,12900,1041,17,267277,282633]),
  (308, [25796,266761,266763,12368,18834,13870,266761,12376,12374,12902]),
  (309, [266761,17,266767,17,266761,17,266767,17,266767,17,266761,17,266767,17,266761,17,1041,1141769,1041,1041,1928201,1041,17,17,17,17,17,17,1041,1041,1041,1041,17,17,1041,1041,1041,1041,17,17,1041,1041,1041,1041,17,17,1041,1041,1041,1041,281611,281611,281611,281611]),
  (310, [279055,25,17,17,13556,12532,1965579]),
  (311, [529417,529423,25,529423,529423,529417,25,529417,282637,300557,1171465,282635,300555,1957897,282633,300555,282635,281611,13606,281613,12582,17,17,22124,12898,281611,24870,281613,21798,17,17,12908,22114,281611,281611,281611,281611,281613,281611,281613,281611,281611]),
  (312, [266761,266763,12906,12910]),
  (313, [282633,279049,282633,279049,279055,282633,279055,282633,8480,282633,9504,543759,282633,562703,279049,279049,934409,10528,410121,11552,543753,543753,562697,279051,934409,672265,282637,279053,410121,1720841,282635,543753,543753,562697,805897,884745,281609,360457]),
  (314, [266761,12698,266761,12914]),
  (315, [3236891,3236891,3236891,3236891,3236893,3236891,3236893,3236891,3236893,529447,3236891,529447,3236891,3236891,2436129,3236891,3290143,3236891,3236891,2436127,3236891,2436127,61,3170843,61,3236891,3236891,3290653,3236891,5124643,3236891,3236891,3236893,3236891,529455,3236893,529455,3236893,3236893,2960417,3236893,3290143,3236893,3236893,2960415,3236893,2960415,61,3170845,61,3236893,3236893,3290651,3290651,4862499,529445,529445,529445,529445,529445,529445,3236899,4743715,529445,3236899,529445,529445,3252767,529445,3252767,3551779,529445,3290143,529445,529445,3252769,529445,3252769,3289635,529445,3290145,266789,61,529445,266789,61,529445,282669,529445,279085,3290651,3290651,4876827,529445,529445,880677,558117,796709,796709,1070629,356389,1606693,272421,272421,1857061,61,3170851,61,3236899,543781,2672667,5649947,4862491,3170847,880677,558117,558117,3170847,6604827,3551771,4863515,3170849,356389,1606693,1606693,3170849,1361947,3289627,10106395,1085,61,267309,1085,61,3306011,543781,4878875,267309,282661,282661,4879899,3290143,3290143,3290143,3290143,3290145,1851429,3290145,1064997,3290143]),
  (316, [3170843,3170843,3170843,3170843,3170843,3170843,3170845,3170843,3170843,3170845,3170843,3170843,3170843,3170843,3170843,3170845,3170843,2231325,3170843,266791,3170843,3170843,3170843,3170843,3170843,42406,3170843,3170843,3170843,3170843,3170843,48550,3170843,3170843,3170843,3170843,3170845,3170845,3170845,3170845,3170843,3170843,2231323,2231323,266799,3170845,3170845,3170845,3170845,3170845,44454,3170845,3170845,3170845,3170845,3170845,49574,3170845,266789,266789,266789,266789,266789,266789,266789,266789,3170851,266789,2231323,2231323,3170851,266789,266789,266789,266789,266789,3252767,266789,29242,266789,266789,266789,266789,266789,3252769,266789,50746,266789,2755611,266789,266789,3170851,6389275,802853,540709,51772,3170851,3170851,5602843,278565,1589285,52796,3170851,3170847,1085,802853,802853,540709,540709,3252763,29278,3170849,1085,278565,278565,1589285,1589285,3514907,50782,3290143,1064997,1851429,29302]),
  (317, [1496]),
  (318, [529423,529423,529423,529423,880655,558095,796687,796687,1070607,356367,1606671,272399,272399,1857039,17,1041,17,391179,543759,282639,282639,687115,529423,529417,25,529417,25,880655,529417,558095,25,949257,796687,1171465,25,356367,529417,1606671,25,424969,272399,1957897,266761,17,25,1041,17,281611,529417,543759,25,282633,282639,282635,529423,529423,529423,529423,17,17,529423,529423,355339,355339,355339,355339,355341,1851407,355341,1064975,355339]),
  (319, [1510])
]
def chunk_20 : List (ℕ × List ℕ) := [
  (320, [529417,529417,529417,529417,529423,529417,1665035,949263,529417,1171471,424975,529417,1957903,282639,529417,534539,529417,529417,880649,558089,796681,796681,1070601,356361,1606665,272393,272393,1857033,17,1041,17,425995,543753,282633,282633,400395,558089,796681,1606665,272393,1041,17,25,17,543753,543753,25,282633,295947,295947,295947,295947,295949,1851401,295949,1064969,295947]),
  (321, [7,1049,7,1043]),
  (322, []),
  (323, [12932]),
  (324, [8836]),
  (325, [7,1907213,7,1120781]),
  (326, [12930,8838,12936,12938,7,1031,7,1031,7,1031,7,1031,7,1031,7,1031,7,1031,7,1031,7,7,7,7]),
  (327, [8844,529417,1049,529417,529417,529417,529417,529417,529417,1049,529417,529417,1049,529417,25,543753,25,1049,282633,1049,25,25,25,25,25,25,25,25,25,880649,25,1070601,25,356361,25,1857033,25,25,25,25]),
  (328, [529417,529417,529423,281611,529423,1177611,949263,424975,279055,529417,391179,949257,424969,279049,425995,17,1049,17,1049,391691]),
  (329, [1645069,1645067,599055,25,17,392715]),
  (330, [529423,949259,949263,424975,1857035,529417,529417,529423,282635,400395,279049,1049,529417,12946,1049,599049,356363,1907209,1120777,17]),
  (331, [529417,529417,529417,529417,529417,529417,529417,529423,529417,22140,529417,13740,529417,278539,529417,12716,529417,278541,529417,10320,529417,18518,529417,529417,529417,529417,529417,12928,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,529417,266761,266761,529417,529417,12942,529417,1049,529417,529417,529417,278539,880649,558089,278539,796681,1070601,278541,356361,1606665,278541,272393,1857033,1041,1049,1041,12944,543753,1049,282633,12948,278539,278539,278539,278539,278539,278539,278541,278539,1851401,278541,278539,1064969,278539,278539]),
  (332, [12380,18522,266761,12950]),
  (333, [281615,363021]),
  (334, [23,281609,281609,360459,17,22170,17,311311,336909]),
  (335, [1160])
]
def chunk_21 : List (ℕ × List ℕ) := [
  (336, [17,17,17,334345,1703439,1703433,1703433,434185]),
  (337, [266761,281609,17,1031,17052,281609,17,281609,278537,281615,17,1047,15004,281615,17,355337,278537,281611,17,266763,281611,267275,1041,279053,17,355337,282637,355337,1064969,17,267275,1141769,360457,282633,281609,281609,281609,281609,281615,281609,281615,281609,16684,281609,281609,16666,281609,16668,281609,281609,940041,14636,281615,281615,14618,281615,14620,281611,940041,677897,282637,279053,281611,282637,39570,279053,360459,12960,300555,26110,12900]),
  (338, [266761,266761,12692,12962]),
  (339, [4338715,4338715,4338715,4338715,4338717,4338715,4338717,4338715,4338715,2699805,4338715,5640733,4338715,4338715,3486237,4338715,1446429,3252763,3252763,3252763,4338715,4338715,3252765,4338715,4338717,540711,4338715,1089,4338715,4352541,4338715,4338715,4338717,4338717,2699803,2699803,5640731,4338717,4338717,3486235,3486235,1446427,3252765,3252765,3252765,4338717,4338717,3252763,3252763,4338715,540719,4338717,1091,4338717,4352539,267301,267301,3252771,267301,3252771,2699803,2699803,5640731,267301,267301,3252767,267301,3252767,3486235,3486235,1446427,267301,267301,267301,267301,267301,267301,267321,267301,267321,540719,267301,267321,267301,267301,4879905,4352539,3290147,3290147,3290147,3290147,3290143,3290147,3290143,802865,3290147,1083,295973,4795419,3290147,3290147,802863,802863,1085,1082405,4533275,266789,4102683,267301,267321,267321,3307041,3303971,3236897,4367899,3236897,4355611]),
  (340, [12380,16474,266761,12802]),
  (341, [4219419,4219419,4219419,4219419,4219419,4219419,4219421,4219419,4219419,4219421,4219419,4219419,4219419,4219419,4219419,4219419,53600,4219419,3170851,4219419,4219419,4219419,4219419,4219419,4219419,31072,4219419,3170847,4219419,3170331,4219419,3170331,3170331,4219419,4219419,4219419,4219419,3252765,4219419,54844,4219419,4219419,4219419,4219419,4219419,54628,4219419,4219419,4219419,4219419,4219421,4219421,4219421,2194971,4219421,55648,4219421,3170851,4219421,4219421,4219421,4219421,6913563,4219421,56672,4219421,3170847,4219421,3170333,4219421,3170333,3170333,4219421,4219421,4219421,4219421,3252763,3252763,57916,4219421,4219421,4219421,4219421,4219421,57700,4219421,3170339,267301,3170851,267301,2194971,2194971,3170339,3170851,3252767,51772,3170851,3170851,3170335,267301,3170847,267301,6913563,6913563,3170335,3170847,3252771,50748,3252771,3170847,266789,266789,266809,267301,266789,266789,4102683,4102683,266809,4889123,266809,4889123,3252763,3252763,3252771,29350,4743713,267301,3320347,3320347,7252507,7252507,3514915,58998,3170851,3170851,3170851,3170851,3170851,3170851,3170847,3170851,6163483,3170847,3170851,3170851,4292123,3170851,3170851,51556,3170851,6425627,3170851,3170851,3170847,5864987,1485347,6728227,50532,3170847,3170849,267321,1485347,1485347,6728227,6724123,2204187,60022]),
  (342, [3170331,3170331,3170331,3170331,3170331,3170331,3170333,3170331,3170331,3170333,3170331,3170331,3170331,3170331,3170331,41384,3170331,3170331,3170331,3170331,3170331,42408,3170331,3170331,3170331,3170331,3170331,48552,3170331,3170331,3170331,3170331,3170333,3170333,3170333,3170333,43432,3170333,3170333,3170333,3170333,3170333,44456,3170333,3170333,3170333,3170333,3170333,49576,3170333,3170339,266789,2755611,2755611,2231323,2231323,29196,29304,3170335,266789,3542043,3542043,6949915,6949915,46604,46712,3170337,266789,3279899,3279899,7212059,7212059,58892,59000,3170851,6425627,6163483,29354,3170851,5639195,8522779,50858,3170847,1444891,6687771,51882]),
  (343, [3170331,3170331,3170333,29356,3170331,3170331,3170339,61100,3170331,3170331,3170335,62124,3170331,3170331,3170337,63148,3170333,3170333,3170339,64172,3170333,3170333,3170335,65196,3170333,3170333,3170337,66220,3170339,3170339,3170335,40620,3170339,3170339,3170337,67244,3170335,3170335,3170337,68268])
]

def nEntries : ℕ := 344
def nPerms : ℕ := 67
def nSMaps : ℕ := 34
def nChunks : ℕ := 22

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_0 : chunk_0.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_1 : chunk_1.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_2 : chunk_2.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_3 : chunk_3.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_4 : chunk_4.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_5 : chunk_5.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_6 : chunk_6.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_7 : chunk_7.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_8 : chunk_8.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_9 : chunk_9.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_10 : chunk_10.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_11 : chunk_11.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_12 : chunk_12.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_13 : chunk_13.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_14 : chunk_14.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_15 : chunk_15.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_16 : chunk_16.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_17 : chunk_17.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_18 : chunk_18.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_19 : chunk_19.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_20 : chunk_20.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chk_21 : chunk_21.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem perms_ok : (List.range 67).all (fun i => checkPerm (permsTree.getD defaultPerm i)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem smaps_ok : (List.range 34).all (fun i => checkSMap (smapsTree.getD defaultSMap i)) = true := by decide +kernel
def allChunks : List (ℕ × List ℕ) :=
  chunk_0 ++ chunk_1 ++ chunk_2 ++ chunk_3 ++ chunk_4 ++ chunk_5 ++ chunk_6 ++ chunk_7 ++ chunk_8 ++ chunk_9 ++ chunk_10 ++ chunk_11 ++ chunk_12 ++ chunk_13 ++ chunk_14 ++ chunk_15 ++ chunk_16 ++ chunk_17 ++ chunk_18 ++ chunk_19 ++ chunk_20 ++ chunk_21
theorem allChunks_ids : allChunks.map Prod.fst = List.range 344 := by decide +kernel
theorem allChunks_ok : allChunks.all (fun p => checkEntry entriesTree permsTree smapsTree nPerms nSMaps p.1 p.2) = true := by
  simp only [allChunks, List.all_append, Bool.and_eq_true, chk_0, chk_1, chk_2, chk_3, chk_4, chk_5, chk_6, chk_7, chk_8, chk_9, chk_10, chk_11, chk_12, chk_13, chk_14, chk_15, chk_16, chk_17, chk_18, chk_19, chk_20, chk_21]
  trivial
theorem root_entry_eq : entriesTree.getD defaultEntry 343 = ⟨false, 5, false, 11, rawInputs5⟩ := by decide +kernel

theorem no_u2_11 : ¬ Live.live (basicOps 5) (target 5 false) 11 rawInputs5.toFinset := by
  have hall := cert_all_sound entriesTree permsTree smapsTree nEntries nPerms nSMaps allChunks
    perms_ok smaps_ok allChunks_ids allChunks_ok
  have hroot := hall 343 (by decide)
  rw [root_entry_eq] at hroot
  simpa [EntryClaim] using hroot

theorem main : ¬ HasCircuitSize 5 ex1_5 12 := by
  rintro ⟨C, hfan, hsize, heval⟩
  have hfall := ex1_5_fall C hfan heval
  have hlen : C.gates.length ≤ 12 := hsize
  have hbin : binaries C.gates ≤ 11 := by omega
  have hrows : ∀ k : Fin 32,
      (C.gates.foldl step (rawInputs5.map (bit5 k))).getD C.output false = bit5 k (target 5 false) := by
    intro k
    rw [← input_rows5, ← target_rows5]
    exact heval (row5 k.val)
  have hbuild := compile5 C.gates C.output hfan rawInputs5 rawInputs5.toFinset initial_rep5 hrows
  obtain ⟨s, hs, hlive⟩ := Live.compress hbuild
  have hseq := full_inputs5 hs hlive
  rw [hseq] at hlive
  exact no_u2_11 (Live.live_mono_k hbin hlive)

end PEqualNP.Outside.L_meta_10405_aux

theorem PEqualNP.Outside.L_meta_10405 : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (((List.ofFn x).count true) = 1)) 12) :=
  PEqualNP.Outside.L_meta_10405_aux.main
