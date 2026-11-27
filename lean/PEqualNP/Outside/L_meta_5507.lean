import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5507_aux

open PEqualNP.CircuitLowerBounds

def mg (g : Gate) (m : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 65535
  | GateOp.and, [a] => m.getD a 0
  | GateOp.and, [a, b] => m.getD a 0 &&& m.getD b 0
  | GateOp.or, [] => 0
  | GateOp.or, [a] => m.getD a 0
  | GateOp.or, [a, b] => m.getD a 0 ||| m.getD b 0
  | _, _ => 0

def dd : List ℕ → List ℕ
  | [] => []
  | x :: l => if x ∈ l then dd l else x :: dd l

theorem mem_dd (l : List ℕ) (x : ℕ) : x ∈ dd l ↔ x ∈ l := by
  induction l with
  | nil => simp [dd]
  | cons y l ih =>
    unfold dd
    by_cases h : y ∈ l
    · rw [if_pos h, ih]; simp only [List.mem_cons]; constructor
      · intro h2; exact Or.inr h2
      · rintro (rfl | h2)
        · exact h
        · exact h2
    · rw [if_neg h]; simp [ih]

def rawc (S : List ℕ) : List ℕ :=
  0 :: 65535 :: S.flatMap (fun x => S.flatMap (fun y => [x &&& y, x ||| y]))

def cands (S : List ℕ) : List ℕ := dd (rawc S)

def hit (x : ℕ) : Bool := decide (x % 65536 = 3)

def chk : ℕ → List ℕ → Bool
  | 0, S => S.any hit || (rawc S).any hit
  | k + 1, S => S.any hit || (cands S).any (fun v => chk k (v :: S))

def m0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

theorem chk_false : chk 0 (0 :: m0) = false := by decide +kernel

theorem getD_snoc (m : List ℕ) (v i : ℕ) :
    (m ++ [v]).getD i 0 = if i < m.length then m.getD i 0 else if i = m.length then v else 0 := by
  by_cases h1 : i < m.length
  · rw [if_pos h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = m.length
    · subst h2; rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp
    · rw [if_neg h2, List.getD_eq_getElem?_getD]
      have : (m ++ [v]).length ≤ i := by simp; omega
      rw [List.getElem?_eq_none this]; rfl

theorem getD_app_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem getD_app_gt (l : List Bool) (b : Bool) (i : ℕ) (h : l.length < i) :
    (l ++ [b]).getD i false = false := by
  rw [List.getD_eq_default]
  simp; omega

theorem mg_mem (g : Gate) (m S : List ℕ) (hS : ∀ i, m.getD i 0 ∈ S)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    mg g m ∈ rawc S := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨ho, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  simp only [rawc, List.mem_cons, List.mem_flatMap]
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases ho with rfl | rfl <;> simp [mg]
  · rcases ho with rfl | rfl
    · right; right; refine ⟨m.getD a 0, hS a, m.getD a 0, hS a, ?_⟩; simp [mg]
    · right; right; refine ⟨m.getD a 0, hS a, m.getD a 0, hS a, ?_⟩; simp [mg]
  · rcases ho with rfl | rfl
    · right; right; refine ⟨m.getD a 0, hS a, m.getD b 0, hS b, ?_⟩; simp [mg]
    · right; right; refine ⟨m.getD a 0, hS a, m.getD b 0, hS b, ?_⟩; simp [mg]
  · simp at hl

theorem chk_hit (k : ℕ) (S : List ℕ) (x : ℕ) (hx : x ∈ S) (h : hit x = true) : chk k S = true := by
  cases k
  · simp only [chk, Bool.or_eq_true, List.any_eq_true]; left; exact ⟨x, hx, h⟩
  · simp only [chk, Bool.or_eq_true, List.any_eq_true]; left; exact ⟨x, hx, h⟩

theorem snd (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (k : ℕ) (m S : List ℕ), gs.length ≤ k + 1 → (∀ i, m.getD i 0 ∈ S) → ∀ o,
      hit ((gs.foldl (fun m g => m ++ [mg g m]) m).getD o 0) = true → chk k S = true := by
  induction gs with
  | nil =>
    intro k m S _ hS o ho
    simp only [List.foldl_nil] at ho
    exact chk_hit k S _ (hS o) ho
  | cons g gs ih =>
    intro k m S hk hS o ho
    simp only [List.foldl_cons] at ho
    have h1 := mg_mem g m S hS (hgs g List.mem_cons_self)
    cases k with
    | zero =>
      have hnil : gs = [] := by simp at hk; exact hk
      subst hnil
      simp only [List.foldl_nil] at ho
      rw [getD_snoc] at ho
      simp only [chk, Bool.or_eq_true, List.any_eq_true]
      split_ifs at ho with a b
      · left; exact ⟨_, hS o, ho⟩
      · right; exact ⟨_, h1, ho⟩
      · right; refine ⟨0, ?_, ho⟩; simp [rawc]
    | succ k' =>
      have h1' : mg g m ∈ cands S := by unfold cands; rw [mem_dd]; exact h1
      have h2 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) k' (m ++ [mg g m]) (mg g m :: S)
        (by simp at hk; omega) (by
          intro i
          rw [getD_snoc]
          split_ifs with a b
          · exact List.mem_cons_of_mem _ (hS i)
          · exact List.mem_cons_self
          · have := hS m.length
            rw [List.getD_eq_default _ _ (le_refl _)] at this
            exact List.mem_cons_of_mem _ this) o ho
      simp only [chk, Bool.or_eq_true, List.any_eq_true]
      right
      exact ⟨mg g m, h1', h2⟩

theorem rel (p : ℕ) (hp : p < 16) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (d : List Bool) (m : List ℕ), d.length = m.length →
      (∀ i, d.getD i false = (m.getD i 0).testBit p) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false
        = ((gs.foldl (fun m g => m ++ [mg g m]) m).getD i 0).testBit p := by
  induction gs with
  | nil => intro d m _ h; exact h
  | cons g gs ih =>
    intro d m hl h
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => d.getD i false) = (mg g m).testBit p := by
      obtain ⟨op, ins⟩ := g
      obtain ⟨ho, hlen⟩ := hgs _ List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
      simp only at hlen
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · rcases ho with rfl | rfl
        · simp [GateOp.eval, mg]
          interval_cases p <;> decide
        · simp [GateOp.eval, mg]
      · rcases ho with rfl | rfl <;> simp only [GateOp.eval, mg, List.map_cons, List.map_nil, h a, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
      · rcases ho with rfl | rfl <;> simp only [GateOp.eval, mg, List.map_cons, List.map_nil, h a, h b, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false, Nat.testBit_and, Nat.testBit_or]
      · simp at hlen
    refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hl]) ?_
    intro i
    rw [getD_snoc]
    rcases lt_trichotomy i d.length with hi | hi | hi
    · rw [getD_app_lt _ _ _ hi, if_pos (by omega)]; exact h i
    · subst hi; rw [getD_app_eq, if_neg (by omega), if_pos hl]; exact hv
    · rw [getD_app_gt _ _ _ hi, if_neg (by omega), if_neg (by omega)]; simp

theorem inp : ∀ u v : Fin 4, ∀ i : Fin 8,
    (PEqualNP.Represents.oneEach u v).getD i false = (m0.getD i 0).testBit (4 * u.val + v.val) := by
  decide +kernel

theorem inp2 (u v : Fin 4) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = (m0.getD i 0).testBit (4 * u.val + v.val) := by
  by_cases hi : i < 8
  · exact inp u v ⟨i, hi⟩
  · have h1 : (PEqualNP.Represents.oneEach u v).length ≤ i := by simp [PEqualNP.Represents.oneEach]; omega
    have h2 : m0.length ≤ i := by simp [m0]; omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]; simp

end PEqualNP.Outside.L_meta_5507_aux

open PEqualNP.Outside.L_meta_5507_aux in
theorem PEqualNP.Outside.L_meta_5507 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 2 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) 1 := by
  constructor
  · refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩], 9⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp
    · decide +kernel
  · rintro ⟨C, hmono, hsize, hrep⟩
    have hgs := hmono
    set x := (C.gates.foldl (fun m g => m ++ [mg g m]) m0).getD C.output 0 with hx
    have key : ∀ u v : Fin 4, x.testBit (4 * u.val + v.val) = (3 : ℕ).testBit (4 * u.val + v.val) := by
      intro u v
      have h := hrep u v
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h
      rw [rel (4 * u.val + v.val) (by omega) C.gates hgs _ m0 (by simp [PEqualNP.Represents.oneEach, m0]) (inp2 u v) C.output] at h
      exact h
    have hh : hit x = true := by
      simp only [hit, decide_eq_true_eq]
      show x % 2 ^ 16 = 3
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hi : i < 16
      · have := key ⟨i / 4, by omega⟩ ⟨i % 4, by omega⟩
        have e : 4 * (i / 4) + i % 4 = i := by omega
        simp only [e] at this
        simp [hi, this]
      · have : (3 : ℕ) < 2 ^ i :=
          lt_of_lt_of_le (by norm_num : (3 : ℕ) < 2 ^ 16) (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [hi, Nat.testBit_eq_false_of_lt this]
    have hS : ∀ i, m0.getD i 0 ∈ (0 :: m0) := by
      intro i
      by_cases h : i < m0.length
      · rw [List.getD_eq_getElem _ _ h]; exact List.mem_cons_of_mem _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]; exact List.mem_cons_self
    have := snd C.gates hgs 0 m0 (0 :: m0) hsize hS C.output hh
    rw [chk_false] at this
    exact absurd this (by simp)
