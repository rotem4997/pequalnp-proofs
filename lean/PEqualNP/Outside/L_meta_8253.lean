import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8253

def step (w : List Bool) (g : Finset ℕ × Finset ℕ) : List Bool :=
  w ++ [Decidable.decide (∀ x8 ∈ g.1, w.getD x8 Bool.false = Bool.true) || Decidable.decide (∀ x8 ∈ g.2, w.getD x8 Bool.false = Bool.true)]

def W (n : ℕ) (gs : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) : List Bool :=
  List.foldl step (List.ofFn x ++ [Bool.false]) gs

def val (n : ℕ) (gs : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) (S : Finset ℕ) : Bool :=
  Decidable.decide (∀ x7 ∈ S, (W n gs x).getD x7 Bool.false = Bool.true)

def t (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  if 2 < (A.filter (· < n)).card then {n} else A

def T (n : ℕ) (g : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ := (t n g.1, t n g.2)

theorem getD_app_lt (w : List Bool) (b : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_eq (w : List Bool) (b : Bool) (i : ℕ) (h : i = w.length) :
    (w ++ [b]).getD i false = b := by
  subst h
  simp [List.getD_eq_getElem?_getD]

theorem getD_app_gt (w : List Bool) (b : Bool) (i : ℕ) (h : w.length < i) :
    (w ++ [b]).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  rfl

theorem fold_len (gs : List (Finset ℕ × Finset ℕ)) : ∀ (init : List Bool),
    (List.foldl step init gs).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp
  | cons g l ih => intro init; rw [List.foldl_cons, ih]; simp [step]; omega

theorem fold_low (gs : List (Finset ℕ × Finset ℕ)) : ∀ (init : List Bool) (i : ℕ), i < init.length →
    (List.foldl step init gs).getD i false = init.getD i false := by
  induction gs with
  | nil => intro init i _; simp
  | cons g l ih =>
    intro init i h
    rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
    exact getD_app_lt _ _ _ h

theorem W_len (n : ℕ) (gs : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :
    (W n gs x).length = n + 1 + gs.length := by
  unfold W; rw [fold_len]; simp

theorem W_n (n : ℕ) (gs : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) :
    (W n gs x).getD n false = false := by
  unfold W; rw [fold_low _ _ _ (by simp)]
  exact getD_app_eq _ _ _ (by simp)

theorem W_in (n : ℕ) (gs : List (Finset ℕ × Finset ℕ)) (x : Fin n → Bool) (i : Fin n) :
    (W n gs x).getD i false = x i := by
  unfold W; rw [fold_low _ _ _ (by simp), getD_app_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem W_snoc (n : ℕ) (l : List (Finset ℕ × Finset ℕ)) (g) (x : Fin n → Bool) :
    W n (l ++ [g]) x = step (W n l x) g := by
  simp [W, List.foldl_append]

theorem andL (n : ℕ) (x : Fin n → Bool) (new old : List Bool) (A : Finset ℕ)
    (hI : ∀ w, new.getD w false = true → old.getD w false = true)
    (hE : (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ 2 →
      ∀ w, new.getD w false = old.getD w false)
    (hn : new.getD n false = false)
    (ho : ∀ i : Fin n, old.getD i false = x i) :
    (decide (∀ w ∈ t n A, new.getD w false = true) = true →
      decide (∀ w ∈ A, old.getD w false = true) = true) ∧
    ((Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ 2 →
      decide (∀ w ∈ t n A, new.getD w false = true) =
      decide (∀ w ∈ A, old.getD w false = true)) := by
  unfold t
  split
  · rename_i hc
    have hf : decide (∀ w ∈ ({n} : Finset ℕ), new.getD w false = true) = false := by
      rw [decide_eq_false_iff_not]
      intro hh
      have h2 := hh n (Finset.mem_singleton_self n)
      rw [hn] at h2
      exact Bool.noConfusion h2
    rw [hf]
    refine ⟨by simp, fun hx => ?_⟩
    symm
    rw [decide_eq_false_iff_not]
    intro hall
    have hsub : A.filter (· < n) ⊆
        (Finset.univ.filter (fun i : Fin n => x i = true)).image Fin.val := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_image]
      refine ⟨⟨w, hw.2⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← ho ⟨w, hw.2⟩]
      exact hall w hw.1
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    omega
  · constructor
    · intro h
      rw [decide_eq_true_iff] at h ⊢
      exact fun w hw => hI w (h w hw)
    · intro hx
      congr 1
      apply propext
      constructor
      · intro h w hw; rw [← hE hx w]; exact h w hw
      · intro h w hw; rw [hE hx w]; exact h w hw

theorem inv (n : ℕ) (x : Fin n → Bool) (gs : List (Finset ℕ × Finset ℕ)) :
    ∀ w, ((W n (gs.map (T n)) x).getD w false = true → (W n gs x).getD w false = true) ∧
      ((Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ 2 →
        (W n (gs.map (T n)) x).getD w false = (W n gs x).getD w false) := by
  induction gs using List.reverseRecOn with
  | nil => intro w; simp
  | append_singleton l g ih =>
    intro w
    have hl : (W n (l.map (T n)) x).length = (W n l x).length := by simp [W_len]
    rw [List.map_append, List.map_singleton, W_snoc, W_snoc]
    have hI := fun w => (ih w).1
    have hE := fun hx w => (ih w).2 hx
    obtain ⟨a1, a2⟩ := andL n x _ _ g.1 hI hE (W_n _ _ _) (W_in _ _ _)
    obtain ⟨b1, b2⟩ := andL n x _ _ g.2 hI hE (W_n _ _ _) (W_in _ _ _)
    unfold step
    rcases lt_trichotomy w (W n l x).length with h | h | h
    · rw [getD_app_lt _ _ _ (hl ▸ h), getD_app_lt _ _ _ h]; exact ih w
    · rw [getD_app_eq _ _ _ (h.trans hl.symm), getD_app_eq _ _ _ h]
      constructor
      · intro hh
        rw [Bool.or_eq_true] at hh ⊢
        exact hh.imp a1 b1
      · intro hx
        exact congrArg₂ (· || ·) (a2 hx) (b2 hx)
    · rw [getD_app_gt _ _ _ (hl ▸ h), getD_app_gt _ _ _ h]; simp

theorem t_mem (n : ℕ) (A : Finset ℕ) (w : ℕ) (h : w ∈ t n A) : w ∈ A ∨ w = n := by
  unfold t at h
  split at h
  · right; simpa using h
  · left; exact h

theorem t_card (n : ℕ) (A : Finset ℕ) : ((t n A).filter (· < n)).card ≤ 2 := by
  unfold t
  split
  · have : ({n} : Finset ℕ).filter (· < n) = ∅ := by
      ext w; simp; omega
    rw [this]; simp
  · omega

theorem main (x1 : ℕ) (x2 : List (Finset ℕ × Finset ℕ))
    (h : ∀ (x4 : ℕ) (x5 : x4 < x2.length), ∀ x6 ∈ x2[x4].1 ∪ x2[x4].2, x6 < x1 + (1 : ℕ) + x4) :
    ∃ (x5 : List (Finset ℕ × Finset ℕ)),
      x5.length = x2.length ∧
        (∀ (x6 : ℕ) (x7 : x6 < x5.length), ∀ x8 ∈ x5[x6].1 ∪ x5[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧
          (∀ x6 ∈ x5, {x8 ∈ x6.1 | x8 < x1}.card ≤ (2 : ℕ) ∧ {x8 ∈ x6.2 | x8 < x1}.card ≤ (2 : ℕ)) ∧
            ∀ (x6 : Fin x1 → Bool) (x7 : Finset ℕ),
              ((Finset.univ.filter (fun x8 : Fin x1 => x6 x8 = Bool.true)).card ≤ (2 : ℕ) →
                  val x1 x5 x6 x7 = val x1 x2 x6 x7) ∧
                (val x1 x5 x6 x7 = Bool.true → val x1 x2 x6 x7 = Bool.true) := by
  refine ⟨x2.map (T x1), by simp, ?_, ?_, ?_⟩
  · intro k hk w hw
    have hk2 : k < x2.length := by simpa using hk
    rw [List.getElem_map] at hw
    have hh := h k hk2
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · rcases t_mem _ _ _ hw with h1 | h1
      · exact hh w (Finset.mem_union_left _ h1)
      · omega
    · rcases t_mem _ _ _ hw with h1 | h1
      · exact hh w (Finset.mem_union_right _ h1)
      · omega
  · intro g hg
    rw [List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    exact ⟨t_card _ _, t_card _ _⟩
  · intro x S
    have hinv := inv x1 x x2
    unfold val
    constructor
    · intro hx
      congr 1
      apply propext
      constructor
      · intro hh w hw; rw [← (hinv w).2 hx]; exact hh w hw
      · intro hh w hw; rw [(hinv w).2 hx]; exact hh w hw
    · intro hh
      rw [decide_eq_true_iff] at hh ⊢
      exact fun w hw => (hinv w).1 (hh w hw)

end PEqualNP.Outside.L_meta_8253

theorem PEqualNP.Outside.L_meta_8253 : ∀ (x1 : ℕ) (x2 : List (Finset ℕ × Finset ℕ)),   have x3 : List (Finset ℕ × Finset ℕ) → (Fin x1 → Bool) → Finset ℕ → Bool := fun (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Fin x1 → Bool) (x5 : Finset ℕ) =>     have x6 : List Bool := List.foldl (fun (x6 : List Bool) (x7 : Finset ℕ × Finset ℕ) => x6 ++ [Decidable.decide (∀ x8 ∈ x7.1, x6.getD x8 Bool.false = Bool.true) || Decidable.decide (∀ x8 ∈ x7.2, x6.getD x8 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x3;     Decidable.decide (∀ x7 ∈ x5, x6.getD x7 Bool.false = Bool.true);   (∀ (x4 : ℕ) (x5 : x4 < x2.length), ∀ x6 ∈ x2[x4].1 ∪ x2[x4].2, x6 < x1 + (1 : ℕ) + x4) →     ∃ (x5 : List (Finset ℕ × Finset ℕ)),       x5.length = x2.length ∧         (∀ (x6 : ℕ) (x7 : x6 < x5.length), ∀ x8 ∈ x5[x6].1 ∪ x5[x6].2, x8 < x1 + (1 : ℕ) + x6) ∧           (∀ x6 ∈ x5, {x8 ∈ x6.1 | x8 < x1}.card ≤ (2 : ℕ) ∧ {x8 ∈ x6.2 | x8 < x1}.card ≤ (2 : ℕ)) ∧             ∀ (x6 : Fin x1 → Bool) (x7 : Finset ℕ),               ((have x8 : Finset (Fin x1) := {x8 : Fin x1 | x6 x8 = Bool.true};                   x8.card ≤ (2 : ℕ)) →                   x3 x5 x6 x7 = x3 x2 x6 x7) ∧                 (x3 x5 x6 x7 = Bool.true → x3 x2 x6 x7 = Bool.true) := by
  intro x1 x2
  exact PEqualNP.Outside.L_meta_8253.main x1 x2
