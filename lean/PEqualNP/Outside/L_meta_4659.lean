import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4659_aux

open PEqualNP.CircuitLowerBounds

-- Circuit toolkit, copied from extra/L_meta_1406.lean (lines 8 to 162).
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h


-- Part A: counting on a rectangle-free family of finsets.

lemma offd {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card + s.card = s.card * s.card := by
  rw [Finset.offDiag_card]
  have := Nat.le_mul_self s.card
  omega

lemma partA {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : β → Finset α)
    (hrf : ∀ b b' a a', b ≠ b' → a ≠ a' → a ∈ F b → a' ∈ F b → a ∈ F b' → a' ∈ F b' → False)
    (hL : (Finset.univ.filter (fun b => (F b).Nonempty)).card ≤ 1893)
    (he : 1 ≤ ∑ b, (F b).card) :
    ∑ b, (F b).card + 44 ≤ 44 * ((Finset.univ.biUnion F).card +
      (Finset.univ.filter (fun b => (F b).Nonempty)).card) := by
  set U := Finset.univ.biUnion F with hU
  set Ls := Finset.univ.filter (fun b => (F b).Nonempty) with hLs
  set e := ∑ b, (F b).card with he_def
  have h1 : ∑ b, (F b).offDiag.card ≤ U.offDiag.card := by
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_offDiag] at hx ⊢
      obtain ⟨b, h1, h2, h3⟩ := hx
      exact ⟨Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, h1⟩,
        Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, h2⟩, h3⟩
    · intro b _ b' _ hbb'
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_offDiag] at hx hx'
      exact hrf b b' x.1 x.2 hbb' hx.2.2 hx.1 hx.2.1 hx'.1 hx'.2.1
  have h2 : ∑ b, (F b).card ^ 2 = ∑ b, (F b).offDiag.card + e := by
    rw [he_def, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [offd, sq]
  have h3 : U.offDiag.card + U.card = U.card * U.card := offd U
  have h4 : e = ∑ b ∈ Ls, (F b).card := by
    rw [he_def, hLs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with h
    · rfl
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
  have h5 : e ^ 2 ≤ Ls.card * ∑ b ∈ Ls, (F b).card ^ 2 := by
    rw [h4]; exact sq_sum_le_card_mul_sum_sq
  have h6 : ∑ b ∈ Ls, (F b).card ^ 2 ≤ ∑ b, (F b).card ^ 2 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  obtain ⟨b0, _, hb0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun b => (F b).card) (by omega)
  have hb0n : (F b0).Nonempty := Finset.card_ne_zero.mp hb0
  obtain ⟨a0, ha0⟩ := hb0n
  have hP : 1 ≤ U.card := Finset.card_pos.mpr ⟨a0, Finset.mem_biUnion.mpr ⟨b0, Finset.mem_univ _, ha0⟩⟩
  have hLp : 1 ≤ Ls.card := Finset.card_pos.mpr ⟨b0, by
    rw [hLs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨a0, ha0⟩⟩⟩
  have hQ : ∑ b ∈ Ls, (F b).card ^ 2 + U.card ≤ U.card * U.card + e := by
    omega
  have hmain : e * e + Ls.card * U.card ≤ Ls.card * (U.card * U.card) + Ls.card * e := by
    have := Nat.mul_le_mul_left Ls.card hQ
    rw [mul_add, mul_add] at this
    rw [sq] at h5
    omega
  have hlt : e + 1 ≤ 44 * U.card + Ls.card := by
    by_contra hc
    have hc' : 44 * U.card + Ls.card ≤ e := by omega
    have i1 := Nat.mul_le_mul_left e hc'
    have i2 := Nat.mul_le_mul_left (44 * U.card) hc'
    have i3 := Nat.mul_le_mul_right (U.card * U.card) hL
    have i4 : 1 * 1 ≤ U.card * U.card := Nat.mul_le_mul hP hP
    nlinarith [i1, i2, i3, i4, hmain]
  omega

lemma partA2 {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : β → Finset α)
    (hrf : ∀ b b' a a', b ≠ b' → a ≠ a' → a ∈ F b → a' ∈ F b → a ∈ F b' → a' ∈ F b' → False)
    (hH : (Finset.univ.biUnion F).card ≤ 1893 ∨
      (Finset.univ.filter (fun b => (F b).Nonempty)).card ≤ 1893)
    (he : 1 ≤ ∑ b, (F b).card) :
    ∑ b, (F b).card + 44 ≤ 44 * ((Finset.univ.biUnion F).card +
      (Finset.univ.filter (fun b => (F b).Nonempty)).card) := by
  rcases hH with hH | hH
  · set G : α → Finset β := fun a => Finset.univ.filter (fun b => a ∈ F b) with hG
    have hsum : ∑ a, (G a).card = ∑ b, (F b).card := by
      simp only [hG, Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_boole]
      simp
    have hU : Finset.univ.biUnion G = Finset.univ.filter (fun b => (F b).Nonempty) := by
      ext b
      rw [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨a, -, ha⟩
        exact ⟨Finset.mem_univ _, a, by simpa [hG] using ha⟩
      · rintro ⟨-, a, ha⟩
        exact ⟨a, Finset.mem_univ _, by simp [hG, ha]⟩
    have hLs : Finset.univ.filter (fun a => (G a).Nonempty) = Finset.univ.biUnion F := by
      ext a
      simp [hG, Finset.Nonempty]
    have hrf' : ∀ a a' b b', a ≠ a' → b ≠ b' → b ∈ G a → b' ∈ G a → b ∈ G a' → b' ∈ G a' →
        False := by
      intro a a' b b' haa hbb h1 h2 h3 h4
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3 h4
      exact hrf b b' a a' hbb haa h1 h3 h2 h4
    have := partA G hrf' (by rw [hLs]; exact hH) (by rw [hsum]; exact he)
    rw [hsum, hU, hLs] at this
    omega
  · exact partA F hrf hH he

-- Part B: constant replacement and the dependency count.

def cst (n : ℕ) (gs : List Gate) (K : Finset ℕ) : List Gate :=
  List.ofFn (fun k : Fin gs.length => if k.val ∈ K then gs[k.val] else
    ⟨if val gs (fun _ : Fin n => false) (n + k.val) then GateOp.and else GateOp.or, []⟩)

lemma cst_length (n : ℕ) (gs : List Gate) (K : Finset ℕ) : (cst n gs K).length = gs.length := by
  simp [cst]

lemma cst_in (n : ℕ) (gs : List Gate) (K : Finset ℕ) (k : ℕ) (hk : k < (cst n gs K).length)
    (hK : k ∈ K) : (cst n gs K)[k] = gs[k]'(by rw [cst_length] at hk; exact hk) := by
  simp [cst, hK]

lemma cst_out (n : ℕ) (gs : List Gate) (K : Finset ℕ) (k : ℕ) (hk : k < (cst n gs K).length)
    (hK : k ∉ K) : (cst n gs K)[k] =
      ⟨if val gs (fun _ : Fin n => false) (n + k) then GateOp.and else GateOp.or, []⟩ := by
  simp [cst, hK]

lemma agree {n : ℕ} (gs : List Gate) (K : Finset ℕ) (X : (Fin n → Bool) → Prop)
    (hconst : ∀ k (hk : k < gs.length), k ∉ K → ∀ x, X x →
      val gs x (n + k) = val gs (fun _ : Fin n => false) (n + k)) :
    ∀ x, X x → ∀ i, val (cst n gs K) x i = val gs x i := by
  intro x hx i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_lt _ x i h1, val_lt _ x i h1]
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge _ x i (by rw [cst_length]; exact h2), val_ge _ x i h2]
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        have hk' : k < (cst n gs K).length := by rw [cst_length]; exact hk
        rw [val_gate _ x k hk']
        by_cases hK : k ∈ K
        · rw [cst_in n gs K k hk' hK, val_gate gs x k hk]
          congr 1
          apply List.map_congr_left
          intro j _
          split_ifs with hj
          · exact ih j hj
          · rfl
        · rw [cst_out n gs K k hk' hK, hconst k hk hK x hx]
          cases val gs (fun _ : Fin n => false) (n + k) <;> simp [GateOp.eval]

lemma dep (n : ℕ) (K : Finset ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ k (hk : k < gs.length), k ∉ K → gs[k].inputs = []) →
    ∀ outs : List ℕ, ∃ S : Finset ℕ, S.card ≤ outs.length + (K.filter (· < gs.length)).card ∧
      ∀ x y : Fin n → Bool, (∀ i (h : i < n), i ∈ S → x ⟨i, h⟩ = y ⟨i, h⟩) →
        ∀ o ∈ outs, val gs x o = val gs y o := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ outs
    refine ⟨outs.toFinset, ?_, ?_⟩
    · have := List.toFinset_card_le outs
      omega
    · intro x y hxy o ho
      rw [val_nil, val_nil]
      split_ifs with h
      · exact hxy o h (List.mem_toFinset.mpr ho)
      · rfl
  | append_singleton gs g ih =>
    intro hfan hK outs
    have hfan' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hK' : ∀ k (hk : k < gs.length), k ∉ K → gs[k].inputs = [] := by
      intro k hk hk2
      have := hK k (by simp; omega) hk2
      rwa [List.getElem_append_left hk] at this
    have hg2 := hfan g (by simp)
    have hc1 : (K.filter (· < gs.length)).card ≤ (K.filter (· < (gs ++ [g]).length)).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have := hx.2
      simp only [List.length_append, List.length_singleton] at this ⊢
      omega
    have hc2 : gs.length ∈ K → (K.filter (· < gs.length)).card + 1 ≤
        (K.filter (· < (gs ++ [g]).length)).card := by
      intro h
      rw [← Finset.card_insert_of_notMem (s := K.filter (· < gs.length)) (a := gs.length)
        (by simp)]
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter, List.length_append,
        List.length_singleton] at hx ⊢
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ⟨h, by omega⟩
      · exact ⟨h1, by omega⟩
    by_cases hmem : n + gs.length ∈ outs
    · obtain ⟨S, hS, hv⟩ := ih hfan' hK' (outs.erase (n + gs.length) ++ g.inputs)
      refine ⟨S, ?_, ?_⟩
      · have hlen : (outs.erase (n + gs.length)).length + 1 ≤ outs.length := by
          rw [List.length_erase_of_mem hmem]
          have := List.length_pos_of_mem hmem
          omega
        rw [List.length_append] at hS
        by_cases hgK : gs.length ∈ K
        · have := hc2 hgK
          omega
        · have h0 : g.inputs = [] := by
            have := hK gs.length (by simp) hgK
            simpa using this
          rw [h0] at hS
          simp only [List.length_nil] at hS
          omega
      · intro x y hxy o ho
        rw [val_snoc, val_snoc]
        split_ifs with ho'
        · congr 1
          apply List.map_congr_left
          intro j hj
          exact hv x y hxy j (List.mem_append_right _ hj)
        · exact hv x y hxy o (List.mem_append_left _ ((List.mem_erase_of_ne ho').mpr ho))
    · obtain ⟨S, hS, hv⟩ := ih hfan' hK' outs
      refine ⟨S, by omega, ?_⟩
      intro x y hxy o ho
      have ho' : o ≠ n + gs.length := fun h => hmem (h ▸ ho)
      rw [val_snoc, val_snoc, if_neg ho', if_neg ho']
      exact hv x y hxy o ho

def X7 (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (S : Finset (Fin N)) :
    Fin (N + N) → Bool := fun (x8 : Fin (N + N)) =>
  Fin.addCases (fun (x9 : Fin N) => Decidable.decide ¬∃ x10 ∈ S, I x9 x10)
    (fun (x9 : Fin N) => Decidable.decide (x9 ∈ S)) x8

def X9 (N : ℕ) (a b : Fin N) : Fin (N + N) → Bool := fun (x11 : Fin (N + N)) =>
  Decidable.decide (x11 = Fin.castAdd N a ∨ x11 = Fin.natAdd N b)

def X8 (N : ℕ) (C : Circuit) : Circuit :=
  { gates := List.map (fun (x8 : Gate) => if x8.op.eval [] = Bool.true ∧
      x8.inputs.length = (2 : ℕ) ∧ (x8.inputs.all fun (x9 : ℕ) => Decidable.decide ((0 : ℕ) <
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD x9 (0 : ℕ))) = Bool.true
      then { op := GateOp.or, inputs := [] : Gate } else x8) C.gates,
    output := C.output : Circuit }

def ep (N : ℕ) (p : Fin N) : Fin (N + N) → Bool := fun v => decide (v = Fin.castAdd N p)

def el (N : ℕ) (l : Fin N) : Fin (N + N) → Bool := fun v => decide (v = Fin.natAdd N l)

lemma partB (N : ℕ) (C : Circuit) (E : Fin N → Finset (Fin N))
    (Pr : Fin C.size → Prop) [DecidablePred Pr]
    (hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (F1 : ∀ l, ∀ p ∈ E l, val C.gates (X9 N p l) C.output = true)
    (F2 : ∀ p, val C.gates (ep N p) C.output = false)
    (F3 : ∀ l, val C.gates (el N l) C.output = false)
    (hPr : ∀ k : Fin C.size, ¬ Pr k →
      (val C.gates (fun _ : Fin (N + N) => false) (N + N + k.val) = true ∨
        ∀ l, ∀ p ∈ E l, val C.gates (X9 N p l) (N + N + k.val) = false)) :
    (Finset.univ.biUnion E).card + (Finset.univ.filter (fun l => (E l).Nonempty)).card ≤
      Fintype.card {k // Pr k} + 1 := by
  set gs := C.gates with hgs
  set K : Finset ℕ := (Finset.univ.filter Pr).map Fin.valEmbedding with hK
  have hKc : K.card = Fintype.card {k // Pr k} := by
    rw [hK, Finset.card_map, Fintype.card_subtype]
  let X : (Fin (N + N) → Bool) → Prop := fun x => ∃ l, ∃ p ∈ E l, ∀ v, x v = true → X9 N p l v = true
  have hconst : ∀ k (hk : k < gs.length), k ∉ K → ∀ x, X x →
      val gs x (N + N + k) = val gs (fun _ : Fin (N + N) => false) (N + N + k) := by
    intro k hk hkK x hx
    have hnP : ¬ Pr ⟨k, hk⟩ := by
      intro h
      apply hkK
      rw [hK, Finset.mem_map]
      exact ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
    have hP := hPr ⟨k, hk⟩ hnP
    by_cases hz : val gs (fun _ : Fin (N + N) => false) (N + N + k) = true
    · rw [hz]
      exact mono gs hmono _ x (fun v h => by simp at h) _ hz
    · have hz' : val gs (fun _ : Fin (N + N) => false) (N + N + k) = false := by simpa using hz
      rw [hz']
      rcases hP with hP | hP
      · exact absurd hP hz
      · obtain ⟨l, p, hp, hxle⟩ := hx
        by_contra hc
        have h1 := mono gs hmono x (X9 N p l) hxle _ (by simpa using hc)
        rw [hP l p hp] at h1
        exact absurd h1 (by simp)
  have hag := agree gs K X hconst
  have hfan : ∀ g ∈ cst (N + N) gs K, g.inputs.length ≤ 2 := by
    intro g hg
    unfold cst at hg
    rw [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    split_ifs
    · exact (hmono _ (List.getElem_mem _)).2
    all_goals simp
  have hKe : ∀ k (hk : k < (cst (N + N) gs K).length), k ∉ K →
      (cst (N + N) gs K)[k].inputs = [] := by
    intro k hk hkK
    rw [cst_out _ gs K k hk hkK]
  obtain ⟨S, hS, hv⟩ := dep (N + N) K (cst (N + N) gs K) hfan hKe [C.output]
  have hS' : S.card ≤ K.card + 1 := by
    have := Finset.card_le_card (Finset.filter_subset (· < (cst (N + N) gs K).length) K)
    simp only [List.length_singleton] at hS
    omega
  have hpts : ∀ l, ∀ p ∈ E l, p.val ∈ S := by
    intro l p hp
    by_contra hpS
    have h := hv (el N l) (X9 N p l) (by
      intro i h hi
      have hne : i ≠ p.val := fun h' => hpS (h' ▸ hi)
      simp only [el, X9, Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd]
      simp [hne]) C.output (List.mem_singleton_self _)
    rw [hag (el N l) ⟨l, p, hp, fun v hv => by simp [el, X9] at hv ⊢; exact Or.inr hv⟩,
      hag (X9 N p l) ⟨l, p, hp, fun v hv => hv⟩, F3 l, F1 l p hp] at h
    exact absurd h (by simp)
  have hlns : ∀ l, ∀ p ∈ E l, N + l.val ∈ S := by
    intro l p hp
    by_contra hlS
    have h := hv (ep N p) (X9 N p l) (by
      intro i h hi
      have hne : i ≠ N + l.val := fun h' => hlS (h' ▸ hi)
      simp only [ep, X9, Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd]
      simp [hne]) C.output (List.mem_singleton_self _)
    rw [hag (ep N p) ⟨l, p, hp, fun v hv => by simp [ep, X9] at hv ⊢; exact Or.inl hv⟩,
      hag (X9 N p l) ⟨l, p, hp, fun v hv => hv⟩, F2 p, F1 l p hp] at h
    exact absurd h (by simp)
  set A := (Finset.univ.biUnion E).image (fun p : Fin N => p.val) with hA
  set B := (Finset.univ.filter (fun l => (E l).Nonempty)).image (fun l : Fin N => N + l.val)
    with hB
  have hAc : A.card = (Finset.univ.biUnion E).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hBc : B.card = (Finset.univ.filter (fun l => (E l).Nonempty)).card := by
    apply Finset.card_image_of_injective
    intro a b h
    apply Fin.ext
    simp only at h
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hA, Finset.mem_image] at hxA
    rw [hB, Finset.mem_image] at hxB
    obtain ⟨p, _, rfl⟩ := hxA
    obtain ⟨l, _, hl⟩ := hxB
    have := p.isLt
    omega
  have hsub : A ∪ B ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rw [hA, Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      rw [Finset.mem_biUnion] at hp
      obtain ⟨l, _, hpl⟩ := hp
      exact hpts l p hpl
    · rw [hB, Finset.mem_image] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      rw [Finset.mem_filter] at hl
      obtain ⟨p, hp⟩ := hl.2
      exact hlns l p hp
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

lemma glue (N : ℕ) (C : Circuit) (E : Fin N → Finset (Fin N))
    (Pr : Fin C.size → Prop) [DecidablePred Pr]
    (hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrf : ∀ b b' a a', b ≠ b' → a ≠ a' → a ∈ E b → a' ∈ E b → a ∈ E b' → a' ∈ E b' → False)
    (hH : (Finset.univ.biUnion E).card ≤ 1893 ∨
      (Finset.univ.filter (fun b => (E b).Nonempty)).card ≤ 1893)
    (F1 : ∀ l, ∀ p ∈ E l, val C.gates (X9 N p l) C.output = true)
    (F2 : ∀ p, val C.gates (ep N p) C.output = false)
    (F3 : ∀ l, val C.gates (el N l) C.output = false)
    (hPr : ∀ k : Fin C.size, ¬ Pr k →
      (val C.gates (fun _ : Fin (N + N) => false) (N + N + k.val) = true ∨
        ∀ l, ∀ p ∈ E l, val C.gates (X9 N p l) (N + N + k.val) = false)) :
    ∑ b, (E b).card ≤ 44 * Fintype.card {k // Pr k} := by
  by_cases he0 : ∑ b, (E b).card = 0
  · rw [he0]; exact Nat.zero_le _
  · have hA := partA2 E hrf hH (by omega)
    have hB := partB N C E Pr hmono F1 F2 F3 hPr
    omega

theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3]
    (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x2 → Finset (Fin x2)),
    (Finset.univ.biUnion x6).card ≤ (1893 : ℕ) ∨
      Fintype.card { x10 : Fin x2 // (x6 x10).Nonempty } ≤ (1893 : ℕ) →
    (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
    (∀ (x13 : Fin x2), Fintype.card { x14 : Fin x2 // x3 x14 x13 } = x1 + (1 : ℕ)) →
    (∀ (x14 x15 : Fin x2), x14 ≠ x15 → ∃! x17 : Fin x2, x3 x14 x17 ∧ x3 x15 x17) →
    PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →
    (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → x5.eval (List.ofFn (X7 x2 x3 x16)) = Bool.false) →
    (∀ (x17 x18 : Fin x2), x18 ∈ x6 x17 → x3 x18 x17 ∧
      x5.eval (List.ofFn (X9 x2 x18 x17)) = Bool.true ∧
      (X8 x2 x5).eval (List.ofFn (X9 x2 x18 x17)) = Bool.false) →
    ∑ x18 : Fin x2, (x6 x18).card ≤ (44 : ℕ) * Fintype.card { x18 : Fin x5.size //
      (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x18) Bool.false =
        Bool.false ∧ ∃ (x19 : Fin x2), ∃ x20 ∈ x6 x19,
        (x5.wires (List.ofFn (X9 x2 x20 x19))).getD (x2 + x2 + ↑x18) Bool.false = Bool.true } := by
  intro q N I _ C E hH hq hN hline huniq hmin hsound hE
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmin.1 g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have hrf : ∀ b b' a a', b ≠ b' → a ≠ a' → a ∈ E b → a' ∈ E b → a ∈ E b' → a' ∈ E b' →
      False := by
    intro b b' a a' hbb haa h1 h2 h3 h4
    obtain ⟨l, _, hl⟩ := huniq a a' haa
    have e1 := hl b ⟨(hE b a h1).1, (hE b a' h2).1⟩
    have e2 := hl b' ⟨(hE b' a h3).1, (hE b' a' h4).1⟩
    exact hbb (e1.trans e2.symm)
  have hH' : (Finset.univ.biUnion E).card ≤ 1893 ∨
      (Finset.univ.filter (fun b => (E b).Nonempty)).card ≤ 1893 := by
    rw [Fintype.card_subtype] at hH
    exact hH
  have F1 : ∀ l, ∀ p ∈ E l, val C.gates (X9 N p l) C.output = true :=
    fun l p hp => (hE l p hp).2.1
  have F2 : ∀ p, val C.gates (ep N p) C.output = false := by
    intro p
    have h0 : val C.gates (X7 N I ∅) C.output = false := hsound ∅ (by simp)
    by_contra hc
    have := mono C.gates hmono (ep N p) (X7 N I ∅) (by
      intro v hv
      simp only [ep, decide_eq_true_eq] at hv
      subst hv
      simp [X7]) C.output (by simpa using hc)
    rw [h0] at this
    exact absurd this (by simp)
  have F3 : ∀ l, val C.gates (el N l) C.output = false := by
    intro l
    have h0 : val C.gates (X7 N I {l}) C.output = false := hsound {l} (by simp; omega)
    by_contra hc
    have := mono C.gates hmono (el N l) (X7 N I {l}) (by
      intro v hv
      simp only [el, decide_eq_true_eq] at hv
      subst hv
      simp only [X7, Fin.addCases_right]
      simp) C.output (by simpa using hc)
    rw [h0] at this
    exact absurd this (by simp)
  refine glue N C E _ hmono hrf hH' F1 F2 F3 ?_
  intro k hk
  by_cases hz : val C.gates (fun _ : Fin (N + N) => false) (N + N + k.val) = true
  · exact Or.inl hz
  · right
    intro l p hp
    by_contra hc
    apply hk
    refine ⟨?_, l, p, hp, ?_⟩
    · have h1 : val C.gates (fun _ : Fin (N + N) => false) (N + N + k.val) = false := by
        simpa using hz
      rw [← List.ofFn_const]
      exact h1
    · have h1 : val C.gates (X9 N p l) (N + N + k.val) = true := by simpa using hc
      exact h1

end PEqualNP.Outside.L_meta_4659_aux

theorem PEqualNP.Outside.L_meta_4659 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x2 → Finset (Fin x2)),   have x7 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x7 : Finset (Fin x2)) (x8 : Fin (x2 + x2)) => Fin.addCases (fun (x9 : Fin x2) => Decidable.decide ¬∃ x10 ∈ x7, x3 x9 x10) (fun (x9 : Fin x2) => Decidable.decide (x9 ∈ x7)) x8;   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => if x8.op.eval [] = Bool.true ∧ x8.inputs.length = (2 : ℕ) ∧ (x8.inputs.all fun (x9 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x9 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x8) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };   have x9 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x9 x10 : Fin x2) (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x9 ∨ x11 = Fin.natAdd x2 x10);   (Finset.univ.biUnion x6).card ≤ (1893 : ℕ) ∨ Fintype.card { x10 : Fin x2 // (x6 x10).Nonempty } ≤ (1893 : ℕ) → (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x13 : Fin x2), Fintype.card { x14 : Fin x2 // x3 x14 x13 } = x1 + (1 : ℕ)) → (∀ (x14 x15 : Fin x2), x14 ≠ x15 → ∃! x17 : Fin x2, x3 x14 x17 ∧ x3 x15 x17) → PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → x5.eval (List.ofFn (x7 x16)) = Bool.false) → (∀ (x17 x18 : Fin x2), x18 ∈ x6 x17 → x3 x18 x17 ∧ x5.eval (List.ofFn (x9 x18 x17)) = Bool.true ∧ x8.eval (List.ofFn (x9 x18 x17)) = Bool.false) → ∑ x18 : Fin x2, (x6 x18).card ≤ (44 : ℕ) * Fintype.card { x18 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x18) Bool.false = Bool.false ∧ ∃ (x19 : Fin x2), ∃ x20 ∈ x6 x19, (x5.wires (List.ofFn (x9 x20 x19))).getD (x2 + x2 + ↑x18) Bool.false = Bool.true } := by
  exact PEqualNP.Outside.L_meta_4659_aux.main
