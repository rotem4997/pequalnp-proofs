import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3696

theorem two_mul_le_sq_add_sq (x y : ℕ) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  by_cases h : x ≤ y
  · obtain ⟨k, rfl⟩ : ∃ k, y = x + k := ⟨y - x, by omega⟩
    have h1 : x ^ 2 + (x + k) ^ 2 = 2 * (x * (x + k)) + k ^ 2 := by ring
    rw [h1]
    exact Nat.le_add_right _ _
  · obtain ⟨k, rfl⟩ : ∃ k, x = y + k := ⟨x - y, by omega⟩
    have h1 : (y + k) ^ 2 + y ^ 2 = 2 * ((y + k) * y) + k ^ 2 := by ring
    rw [h1]
    exact Nat.le_add_right _ _

theorem sum_const_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ℕ) :
    ∑ _x ∈ s, c = s.card * c := by
  refine Finset.induction_on s (by simp) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, ih]
  simp [ha]
  ring

theorem sq_sum_le_card_mul_sum_sq_nat {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h1 : 2 * (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * f j) := by
    rw [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have h2 : ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * f j) ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum fun j _ => ?_
    exact two_mul_le_sq_add_sq (f i) (f j)
  have h3 : ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) = 2 * (s.card * ∑ i ∈ s, f i ^ 2) := by
    have h3a : ∀ i, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) = s.card * f i ^ 2 + ∑ j ∈ s, f j ^ 2 := by
      intro i
      rw [Finset.sum_add_distrib, sum_const_nat]
    simp_rw [h3a]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_const_nat]
    ring
  rw [← h1] at h2
  rw [h3] at h2
  exact Nat.le_of_mul_le_mul_left h2 (by omega)

theorem mul_self_sub_self (n : ℕ) : n * n - n = n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.add_sub_cancel]

theorem offDiag_card_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  exact mul_self_sub_self s.card

theorem sq_eq_add_mul_pred (n : ℕ) : n ^ 2 = n + n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

theorem card_filter_product_eq_sum {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) :
    ((X ×ˢ Y).filter (fun p => p ∈ E)).card =
      ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card := by
  have hS : (X ×ˢ Y).filter (fun p => p ∈ E) =
      X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨a', ha', b', ⟨hb', hab'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ha', hb'⟩, hab'⟩
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
    obtain ⟨b₁, _, h₁⟩ := hp₁
    obtain ⟨b₂, _, h₂⟩ := hp₂
    exact hne (Prod.mk.inj (h₁.trans h₂.symm)).1
  rw [hS, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_image_of_injective]
  exact fun b₁ b₂ h => (Prod.mk.inj h).2

theorem sum_pairs_le_offDiag {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B))
    (hE : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (X : Finset A) (Y : Finset B) :
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) ≤
      Y.card * (Y.card - 1) := by
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq₁ hq₂
    have hqne : q.1 ≠ q.2 := by tauto
    have h11 : (a₁, q.1) ∈ E := by tauto
    have h12 : (a₁, q.2) ∈ E := by tauto
    have h21 : (a₂, q.1) ∈ E := by tauto
    have h22 : (a₂, q.2) ∈ E := by tauto
    exact hE a₁ a₂ q.1 q.2 hne hqne ⟨h11, h12, h21, h22⟩
  have hsub : X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) ⊆ Y.offDiag := by
    rw [Finset.biUnion_subset]
    intro a _ q hq
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq ⊢
    tauto
  calc
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) =
      ∑ a ∈ X, ((Y.filter (fun b => (a, b) ∈ E)).offDiag).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (offDiag_card_eq (Y.filter (fun b => (a, b) ∈ E))).symm
    _ = (X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Y.offDiag.card := Finset.card_le_card hsub
    _ = Y.card * (Y.card - 1) := offDiag_card_eq Y

theorem c4sq : ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (E : Finset (A × B)), (∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → ∀ (X : Finset A) (Y : Finset B), (((X ×ˢ Y).filter (fun p => p ∈ E)).card) ^ 2 ≤ X.card * (((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1)) := by
  intro A B _ _ _ _ E hE X Y
  let N : A → Finset B := fun a => Y.filter (fun b => (a, b) ∈ E)
  have he : ((X ×ˢ Y).filter (fun p => p ∈ E)).card = ∑ a ∈ X, (N a).card :=
    card_filter_product_eq_sum E X Y
  have hpairs : ∑ a ∈ X, (N a).card * ((N a).card - 1) ≤ Y.card * (Y.card - 1) :=
    sum_pairs_le_offDiag E hE X Y
  have hsum_sq : ∑ a ∈ X, (N a).card ^ 2 ≤
      ((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1) := by
    calc
      ∑ a ∈ X, (N a).card ^ 2 = ∑ a ∈ X, ((N a).card + (N a).card * ((N a).card - 1)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact sq_eq_add_mul_pred _
      _ = (∑ a ∈ X, (N a).card) + ∑ a ∈ X, (N a).card * ((N a).card - 1) :=
        Finset.sum_add_distrib
      _ = ((X ×ˢ Y).filter (fun p => p ∈ E)).card +
          ∑ a ∈ X, (N a).card * ((N a).card - 1) := by rw [← he]
      _ ≤ ((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1) :=
        Nat.add_le_add (Nat.le_refl _) hpairs
  calc
    (((X ×ˢ Y).filter (fun p => p ∈ E)).card) ^ 2 = (∑ a ∈ X, (N a).card) ^ 2 := by rw [he]
    _ ≤ X.card * ∑ a ∈ X, (N a).card ^ 2 :=
      sq_sum_le_card_mul_sum_sq_nat X (fun a => (N a).card)
    _ ≤ X.card * (((X ×ˢ Y).filter (fun p => p ∈ E)).card + Y.card * (Y.card - 1)) :=
      Nat.mul_le_mul (Nat.le_refl _) hsum_sq

open PEqualNP.CircuitLowerBounds

theorem arith (a b s e : ℕ) (hs : s ≤ 4512) (hab : a + b ≤ s + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    (he : e ^ 2 ≤ a * (e + b * (b - 1))) : e ≤ 24 * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hc : 1 + c - 1 = c := by omega
  rw [hc] at he
  have h0 : 24 * (1 + c + d + c + 1) ≤ e + 23 := by omega
  zify at he h0 hab hs
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hlim : 2 * (1 + (c : ℤ)) + d ≤ 4513 := by linarith
  set B : ℤ := 1 + c with hB
  have hB1 : 1 ≤ B := by linarith
  have hcB : (c : ℤ) = B - 1 := by linarith
  rw [hcB] at he h0
  have h1 : 48 * B + 24 * d - 23 ≤ (e : ℤ) := by linarith
  have h2 : (48 * B + 24 * d - 23) * (47 * B + 23 * d - 23) ≤ (e : ℤ) * (e - (B + d)) := by
    have p1 : 0 ≤ 48 * B + 24 * (d : ℤ) - 23 := by linarith
    have p2 : 0 ≤ 47 * B + 23 * (d : ℤ) - 23 := by linarith
    exact mul_le_mul h1 (by linarith) p2 (by linarith)
  have h3 : (48 * B + 24 * d - 23) * (47 * B + 23 * d - 23) ≤ (B + d) * (B * (B - 1)) := by
    nlinarith [he, h2]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    push_cast at h3 hlim
    have hB2 : B ≤ 2256 := by linarith
    have k1 : 0 ≤ (B - 1) * (2256 - B) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ B * ((B - 1) * (2256 - B)) := mul_nonneg (by linarith) k1
    nlinarith [h3, k2]
  · have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hB2 : B ≤ 2256 := by linarith
    have k1 : 0 ≤ B * (B * (4513 - 2 * B - d)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k2 : 0 ≤ B * ((d - 1) * (2256 - B)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k3 : 0 ≤ (d - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have k4 : 0 ≤ (B - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h3, k1, k2, k3, k4]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dep (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ S : Finset ℕ, S.card ≤ gs.length + T.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ t ∈ T, (run gs x).getD t false = (run gs y).getD t false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun T => ⟨T, by simp, fun x y _ _ h t ht => by simpa [run] using h t ht⟩
  | append_singleton gs g ih =>
    intro T
    have ih' := ih (fun g' h' => hg g' (by simp [h']))
    have hlen := hg g (by simp)
    by_cases hk : n + gs.length ∈ T
    · obtain ⟨S, hS, hdet⟩ := ih' (T.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, ?_⟩
      · have h1 := Finset.card_union_le (T.erase (n + gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one hk
        have h3 := List.toFinset_card_le g.inputs
        rw [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy t ht
        have hd := hdet x y hx hy hxy
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy]
        by_cases htk : t = n + gs.length
        · rw [if_pos htk, if_pos htk]
          congr 1
          exact List.map_congr_left fun i hi => hd i (by simp [hi])
        · rw [if_neg htk, if_neg htk]
          exact hd t (by simp [htk, ht])
    · obtain ⟨S, hS, hdet⟩ := ih' T
      refine ⟨S, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]; omega
      · intro x y hx hy hxy t ht
        have htk : t ≠ n + gs.length := fun h => hk (h ▸ ht)
        rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy,
          if_neg htk, if_neg htk]
        exact hdet x y hx hy hxy t ht

variable {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def Acc (C : Circuit) : Finset (Fin N × Fin N) :=
  {x8 : Fin N × Fin N | I x8.1 x8.2 ∧
    (PEqualNP.MetaComplexity.circuitFun (N + N) C fun (x9 : Fin (N + N)) =>
      decide (x9 = Fin.castAdd N x8.1 ∨ x9 = Fin.natAdd N x8.2)) = true}

def Snd (q : ℕ) (C : Circuit) : Prop := ∀ (x9 : Fin (N + N) → Bool),
  Fintype.card { x10 : Fin N // x9 (Fin.natAdd N x10) = true } ≤ q →
  (¬ ∃ (x11 : Fin N) (x12 : Fin N), I x11 x12 ∧ x9 (Fin.castAdd N x11) = true ∧
    x9 (Fin.natAdd N x12) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C x9 = false

theorem single_false {C : Circuit} (hq : 1 ≤ q) (hS : Snd I q C) (v : Fin (N + N)) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C (fun x => decide (x = v)) = false := by
  refine hS _ ?_ ?_
  · refine le_trans ?_ hq
    rw [Fintype.card_subtype]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have h1 := of_decide_eq_true (Finset.mem_filter.1 ha).2
    have h2 := of_decide_eq_true (Finset.mem_filter.1 hb).2
    have h3 := congrArg Fin.val (h1.trans h2.symm)
    simp at h3
    exact Fin.ext h3
  · rintro ⟨a, b, -, ha, hb⟩
    have h3 := congrArg Fin.val ((of_decide_eq_true ha).trans (of_decide_eq_true hb).symm)
    simp at h3
    have := a.2
    omega

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (v : Fin n) : (List.ofFn f).getD v false = f v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem main (hq : 1 ≤ q) (hI : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hS : Snd I q C) (hsz : C.size ≤ 4512) :
    (Acc I C).card ≤ 24 * C.size := by
  classical
  obtain ⟨S, hScard, hdet⟩ := dep (N + N) C.gates hlen {C.output}
  have hfun : ∀ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x =
      (run C.gates (List.ofFn x)).getD C.output false := fun x => rfl
  have agree : ∀ x y : Fin (N + N) → Bool, (∀ v : Fin (N + N), (v : ℕ) ∈ S → x v = y v) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x =
        PEqualNP.MetaComplexity.circuitFun (N + N) C y := by
    intro x y h
    rw [hfun, hfun]
    refine hdet _ _ (by simp) (by simp) (fun i hi => ?_) _ (by simp)
    by_cases hin : i < N + N
    · rw [ofFn_getD x ⟨i, hin⟩, ofFn_getD y ⟨i, hin⟩]
      exact h ⟨i, hin⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  set X : Finset (Fin N) := Finset.univ.filter fun p => (p : ℕ) ∈ S with hX
  set Y : Finset (Fin N) := Finset.univ.filter fun l => N + (l : ℕ) ∈ S with hY
  have hXY : X.card + Y.card ≤ C.size + 1 := by
    have e1 : (X.image fun p : Fin N => (p : ℕ)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have e2 : (Y.image fun l : Fin N => N + (l : ℕ)).card = Y.card :=
      Finset.card_image_of_injective _ fun a b h => Fin.ext (by simpa using h)
    have hdis : Disjoint (X.image fun p : Fin N => (p : ℕ)) (Y.image fun l : Fin N => N + (l : ℕ)) := by
      rw [Finset.disjoint_left]
      rintro i hi hj
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨l, -, h⟩ := Finset.mem_image.1 hj
      have := p.2
      omega
    have hsub : (X.image fun p : Fin N => (p : ℕ)) ∪ (Y.image fun l : Fin N => N + (l : ℕ)) ⊆ S := by
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hp).2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hl).2
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, e1, e2] at h
    simp only [Finset.card_singleton] at hScard
    exact h.trans hScard
  have hmem : ∀ e ∈ Acc I C, e.1 ∈ X ∧ e.2 ∈ Y := by
    intro e he
    obtain ⟨-, -, ht⟩ := Finset.mem_filter.1 he
    constructor
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.natAdd N e.2)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.castAdd N e.1 := fun hc => hn (by rw [hc] at hv; simpa using hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_left hne, Or.inr⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.castAdd N e.1)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.natAdd N e.2 := fun hc => hn (by rw [hc] at hv; exact hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_right hne, Or.inl⟩
  have hc4 : ∀ a a' : Fin N, ∀ b b' : Fin N, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ Acc I C ∧ (a, b') ∈ Acc I C ∧ (a', b) ∈ Acc I C ∧ (a', b') ∈ Acc I C) := by
    rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
    have g1 := (Finset.mem_filter.1 h1).2.1
    have g2 := (Finset.mem_filter.1 h2).2.1
    have g3 := (Finset.mem_filter.1 h3).2.1
    have g4 := (Finset.mem_filter.1 h4).2.1
    exact hb ((hI a a' ha).unique ⟨g1, g3⟩ ⟨g2, g4⟩)
  rcases (Acc I C).eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he]; simp
  have hXp : 1 ≤ X.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).1⟩
  have hYp : 1 ≤ Y.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).2⟩
  have f1 : ((X ×ˢ Y).filter fun p => p ∈ Acc I C) = Acc I C := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => h.2, fun h => ⟨hmem p h, h⟩⟩
  rcases le_total Y.card X.card with hle | hle
  · have h := c4sq (Fin N) (Fin N) (Acc I C) hc4 X Y
    rw [f1] at h
    exact arith X.card Y.card C.size _ hsz hXY hYp hle h
  · have h := c4sq (Fin N) (Fin N) ((Acc I C).image Prod.swap) (by
      rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
      have sw : ∀ p q : Fin N, (p, q) ∈ (Acc I C).image Prod.swap → (q, p) ∈ Acc I C := by
        intro p q h
        obtain ⟨r, hr, hrs⟩ := Finset.mem_image.1 h
        have : r = (q, p) := by rw [← Prod.swap_swap r, hrs]; rfl
        rwa [← this]
      exact hc4 b b' a a' hb ha ⟨sw _ _ h1, sw _ _ h3, sw _ _ h2, sw _ _ h4⟩) Y X
    have f2 : ((Y ×ˢ X).filter fun p => p ∈ (Acc I C).image Prod.swap) =
        (Acc I C).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hmem r hr).2, (hmem r hr).1⟩
    rw [f2, Finset.card_image_of_injective _ Prod.swap_injective] at h
    exact arith Y.card X.card C.size _ hsz (by omega) hXp hle h

end PEqualNP.Outside.L_meta_3696

theorem PEqualNP.Outside.L_meta_3696 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) → x8 x9 → x9.size ≤ (4512 : ℕ) → (x7 x9).card ≤ (24 : ℕ) * x9.size := by
  intro q N I _ hq hI _ _ C hlen hS hsz
  exact PEqualNP.Outside.L_meta_3696.main I hq hI C hlen hS hsz
