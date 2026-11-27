import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3915

open PEqualNP.MetaComplexity

def run (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

theorem run_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op ((run gs x).getD g.left false)
      ((run gs x).getD g.right false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List BinaryGate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
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

theorem run_prefix (gs hs : List BinaryGate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) : (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_snoc, run_length, List.length_append,
      if_neg (by omega), ih]

def Sg (g : BinaryGate) : Prop := ∃ a b : Bool, g.op = fun x y => x == a && y == b

def Good (n : ℕ) (ds : List BinaryGate) : Prop :=
  ∀ (j : ℕ) (hj : j < ds.length), ds[j].left < ds[j].right ∧ ds[j].right < n + j

theorem good_snoc {n : ℕ} {ds : List BinaryGate} {g : BinaryGate} (h : Good n ds)
    (h1 : g.left < g.right) (h2 : g.right < n + ds.length) : Good n (ds ++ [g]) := by
  intro j hj
  rcases Nat.lt_or_ge j ds.length with h3 | h3
  · rw [List.getElem_append_left h3]; exact h j h3
  · have : j = ds.length := by simp at hj; omega
    subst this
    simpa using ⟨h1, h2⟩

def Rep (n : ℕ) (ds : List BinaryGate) (f : List Bool → Bool) : Prop :=
  (∃ c, ∀ x, x.length = n → f x = c) ∨
    ∃ k < n + ds.length, ∃ s, ∀ x, x.length = n → f x = ((run ds x).getD k false != s)

theorem rep_snoc {n : ℕ} {ds : List BinaryGate} {f : List Bool → Bool} (g : BinaryGate)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, s, hs⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, s, fun x hx => ?_⟩
    rw [run_prefix ds [g] x k (by rw [hx]; exact hk)]
    exact hs x hx

theorem rep_eq {n : ℕ} {ds : List BinaryGate} {f : List Bool → Bool} (b : Bool)
    (h : Rep n ds f) : Rep n ds (fun x => f x == b) := by
  rcases h with ⟨c, hc⟩ | ⟨k, hk, s, hs⟩
  · exact Or.inl ⟨c == b, fun x hx => by dsimp only; rw [hc x hx]⟩
  · refine Or.inr ⟨k, hk, s == b, fun x hx => ?_⟩
    dsimp only
    rw [hs x hx]
    cases (run ds x).getD k false <;> cases s <;> cases b <;> rfl

theorem step {n : ℕ} (ds : List BinaryGate) (hG : Good n ds) (hS : ∀ g ∈ ds, Sg g)
    (f g : List Bool → Bool) (hf : Rep n ds f) (hg : Rep n ds g) (a b : Bool) :
    ∃ es : List BinaryGate, Good n es ∧ (∀ g ∈ es, Sg g) ∧ es.length ≤ ds.length + 1 ∧
      (∀ h, Rep n ds h → Rep n es h) ∧ Rep n es (fun x => f x == a && g x == b) := by
  rcases hf with ⟨c, hc⟩ | ⟨k, hk, s, hs⟩
  · refine ⟨ds, hG, hS, by omega, fun h hh => hh, ?_⟩
    by_cases hca : c = a
    · rcases rep_eq b hg with ⟨c', hc'⟩ | ⟨k, hk, s, hs⟩
      · exact Or.inl ⟨c', fun x hx => by dsimp only; rw [hc x hx, hca]; simpa using hc' x hx⟩
      · exact Or.inr ⟨k, hk, s, fun x hx => by dsimp only; rw [hc x hx, hca]; simpa using hs x hx⟩
    · exact Or.inl ⟨false, fun x hx => by dsimp only; rw [hc x hx]; simp [hca]⟩
  · rcases hg with ⟨c, hc⟩ | ⟨l, hl, t, ht⟩
    · refine ⟨ds, hG, hS, by omega, fun h hh => hh, ?_⟩
      by_cases hcb : c = b
      · rcases rep_eq a (Or.inr ⟨k, hk, s, hs⟩ : Rep n ds f) with ⟨c', hc'⟩ | ⟨k, hk, s, hs⟩
        · exact Or.inl ⟨c', fun x hx => by dsimp only; rw [hc x hx, hcb]; simpa using hc' x hx⟩
        · exact Or.inr ⟨k, hk, s, fun x hx => by dsimp only; rw [hc x hx, hcb]; simpa using hs x hx⟩
      · exact Or.inl ⟨false, fun x hx => by dsimp only; rw [hc x hx]; simp [hcb]⟩
    · have add : ∀ (k l : ℕ) (p q : Bool) (h : List Bool → Bool), k < l → l < n + ds.length →
          (∀ x, x.length = n → h x = ((run ds x).getD k false == p && (run ds x).getD l false == q)) →
          ∃ es : List BinaryGate, Good n es ∧ (∀ g ∈ es, Sg g) ∧ es.length ≤ ds.length + 1 ∧
            (∀ h, Rep n ds h → Rep n es h) ∧ Rep n es h := by
        intro k l p q h hkl hln hh
        refine ⟨ds ++ [⟨fun x y => x == p && y == q, k, l⟩], good_snoc hG hkl hln, ?_, by simp,
          fun h hh => rep_snoc _ hh, Or.inr ⟨n + ds.length, by simp, false, fun x hx => ?_⟩⟩
        · intro g hg
          rcases List.mem_append.1 hg with h1 | h1
          · exact hS g h1
          · rw [List.mem_singleton.1 h1]; exact ⟨p, q, rfl⟩
        · rw [run_snoc, getD_snoc, run_length, hx, if_pos rfl, hh x hx]
          simp
      have e : ∀ x, x.length = n → (f x == a && g x == b) =
          ((run ds x).getD k false == (a != s) && (run ds x).getD l false == (b != t)) := by
        intro x hx
        rw [hs x hx, ht x hx]
        generalize (run ds x).getD k false = u
        generalize (run ds x).getD l false = v
        cases u <;> cases v <;> cases s <;> cases t <;> cases a <;> cases b <;> rfl
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact add k l _ _ _ hkl hl e
      · subst hkl
        refine ⟨ds, hG, hS, by omega, fun h hh => hh, ?_⟩
        by_cases hpq : (a != s) = (b != t)
        · refine Or.inr ⟨k, hk, !(a != s), fun x hx => ?_⟩
          dsimp only
          rw [e x hx, ← hpq]
          cases (run ds x).getD k false <;> cases (a != s) <;> rfl
        · refine Or.inl ⟨false, fun x hx => ?_⟩
          dsimp only
          rw [e x hx]
          revert hpq
          generalize (a != s) = p
          generalize (b != t) = q
          cases (run ds x).getD k false <;> cases p <;> cases q <;> simp
      · exact add l k _ _ _ hkl hk fun x hx => by rw [e x hx, Bool.and_comm]

theorem all (n : ℕ) (gs : List BinaryGate) (hS : ∀ g ∈ gs, Sg g) :
    ∃ ds : List BinaryGate, Good n ds ∧ (∀ g ∈ ds, Sg g) ∧ ds.length ≤ gs.length ∧
      ∀ w, Rep n ds (fun x => (run gs (x ++ [false])).getD w false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun j hj => by simp at hj, by simp, le_rfl, fun w => ?_⟩
    by_cases hw : w < n
    · refine Or.inr ⟨w, by simpa using hw, false, fun x hx => ?_⟩
      change (x ++ [false]).getD w false = (x.getD w false != false)
      rw [getD_snoc, if_neg (by omega)]
      simp
    · refine Or.inl ⟨false, fun x hx => ?_⟩
      change (x ++ [false]).getD w false = false
      rw [getD_snoc]
      split_ifs
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h3, h4⟩ := ih fun g' hg' => hS g' (by simp [hg'])
    obtain ⟨a, b, hop⟩ := hS g (by simp)
    obtain ⟨es, e1, e2, e3, e4, e5⟩ := step ds h1 h2 _ _ (h4 g.left) (h4 g.right) a b
    refine ⟨es, e1, e2, by simp; omega, fun w => ?_⟩
    by_cases hw : w = n + 1 + gs.length
    · have : ∀ x, x.length = n → (run (gs ++ [g]) (x ++ [false])).getD w false =
          ((run gs (x ++ [false])).getD g.left false == a &&
            (run gs (x ++ [false])).getD g.right false == b) := by
        intro x hx
        rw [run_snoc, getD_snoc, run_length, List.length_append, hx,
          if_pos (by simp; omega), hop]
      rcases e5 with ⟨c, hc⟩ | ⟨k, hk, s, hs⟩
      · exact Or.inl ⟨c, fun x hx => (this x hx).trans (hc x hx)⟩
      · exact Or.inr ⟨k, hk, s, fun x hx => (this x hx).trans (hs x hx)⟩
    · have : ∀ x, x.length = n → (run (gs ++ [g]) (x ++ [false])).getD w false =
          (run gs (x ++ [false])).getD w false := by
        intro x hx
        rw [run_snoc, getD_snoc, run_length, List.length_append, hx, if_neg (by simp; omega)]
      rcases e4 _ (h4 w) with ⟨c, hc⟩ | ⟨k, hk, s, hs⟩
      · exact Or.inl ⟨c, fun x hx => (this x hx).trans (hc x hx)⟩
      · exact Or.inr ⟨k, hk, s, fun x hx => (this x hx).trans (hs x hx)⟩

theorem main (n : ℕ) (C : BinaryCircuit) (p : Bool) (hS : ∀ g ∈ C.gates, Sg g) :
    ∃ (D : BinaryCircuit) (q : Bool), D.size ≤ C.size ∧ (∀ g ∈ D.gates, Sg g) ∧
      Good n D.gates ∧ (D.size = 0 ∨ D.output = n + D.size - 1) ∧
      ∀ x : List Bool, x.length = n → (D.eval x != q) = (C.eval (x ++ [false]) != p) := by
  obtain ⟨ds, h1, h2, h3, h4⟩ := all n C.gates hS
  have hC : ∀ x, C.eval (x ++ [false]) = (run C.gates (x ++ [false])).getD C.output false :=
    fun x => rfl
  rcases h4 C.output with ⟨c, hc⟩ | ⟨k, hk, s, hs⟩
  · refine ⟨⟨[], n⟩, c != p, Nat.zero_le _, by simp, fun j hj => by simp at hj, Or.inl rfl,
      fun x hx => ?_⟩
    rw [hC, show (run C.gates (x ++ [false])).getD C.output false = c from hc x hx]
    change (x.getD n false != (c != p)) = _
    rw [List.getD_eq_default _ _ (by omega)]
    simp
  · rcases Nat.lt_or_ge k n with hkn | hkn
    · refine ⟨⟨[], k⟩, s != p, Nat.zero_le _, by simp, fun j hj => by simp at hj, Or.inl rfl,
        fun x hx => ?_⟩
      rw [hC, show (run C.gates (x ++ [false])).getD C.output false = _ from hs x hx]
      have e := run_prefix [] ds x k (by rw [hx]; simpa using hkn)
      rw [List.nil_append] at e
      change (x.getD k false != (s != p)) = _
      rw [e]
      change _ = ((x.getD k false != s) != p)
      simp
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      have hj : j < ds.length := by omega
      have hlen : (ds.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      refine ⟨⟨ds.take (j + 1), n + j⟩, s != p, ?_, fun g hg => h2 g (List.mem_of_mem_take hg), ?_,
        Or.inr ?_, fun x hx => ?_⟩
      · change (ds.take (j + 1)).length ≤ C.gates.length
        omega
      · intro i hi
        simp only [List.getElem_take]
        exact h1 i (by rw [hlen] at hi; omega)
      · change n + j = n + (ds.take (j + 1)).length - 1
        omega
      · rw [hC, show (run C.gates (x ++ [false])).getD C.output false = _ from hs x hx]
        have e := run_prefix (ds.take (j + 1)) (ds.drop (j + 1)) x (n + j) (by rw [hx, hlen]; omega)
        rw [List.take_append_drop] at e
        change ((run (ds.take (j + 1)) x).getD (n + j) false != (s != p)) = _
        rw [← e]
        simp

end PEqualNP.Outside.L_meta_3915

theorem PEqualNP.Outside.L_meta_3915 : have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; ∀ (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool), x1 x4 → ∃ (x7 : PEqualNP.MetaComplexity.BinaryCircuit) (x8 : Bool), x7.size ≤ x4.size ∧ x1 x7 ∧ x2 x3 x7 ∧ (x7.size = (0 : ℕ) ∨ x7.output = x3 + x7.size - (1 : ℕ)) ∧ ∀ (x9 : List Bool), x9.length = x3 → (x7.eval x9 != x8) = (x4.eval (x9 ++ [Bool.false]) != x5) := by
  intro _ _ n C p hS
  obtain ⟨D, q, h1, h2, h3, h4, h5⟩ := PEqualNP.Outside.L_meta_3915.main n C p hS
  exact ⟨D, q, h1, h2, fun j => h3 j j.2, h4, h5⟩
