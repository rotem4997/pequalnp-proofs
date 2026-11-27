import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_730

theorem kernelTwoSets {V : Type*} (D : V → V → Prop) (X Y : Set V)
    (hX : ∀ u ∈ X, ∀ v ∈ X, ¬ D u v) (hY : ∀ u ∈ Y, ∀ v ∈ Y, ¬ D u v) :
    ∃ K : Set V, K ⊆ X ∪ Y ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
      ∀ v ∈ X ∪ Y, v ∉ K → ∃ k ∈ K, D v k := by
  classical
  let avoid (S T : Set V) : Set V := {v | v ∈ S ∧ ∀ k ∈ T, ¬ D v k}
  have anti (S : Set V) {T U : Set V} (h : T ⊆ U) : avoid S U ⊆ avoid S T :=
    fun _ hv => ⟨hv.1, fun k hk => hv.2 k (h hk)⟩
  let F : Set V →o Set V := ⟨fun A => avoid X (avoid Y A), fun A B h => anti X (anti Y h)⟩
  let A := F.lfp
  let B := avoid Y A
  have he : avoid X B = A := F.map_lfp
  have hA (u : V) : u ∈ A ↔ u ∈ X ∧ ∀ v ∈ B, ¬ D u v := by
    change u ∈ A ↔ u ∈ avoid X B
    rw [he]
  have hB (u : V) : u ∈ B ↔ u ∈ Y ∧ ∀ v ∈ A, ¬ D u v := Iff.rfl
  refine ⟨A ∪ B, ?_, ?_, ?_⟩
  · rintro u (ha | hb)
    · exact Or.inl ((hA u).1 ha).1
    · exact Or.inr ((hB u).1 hb).1
  · rintro u (ha | hb) v (hc | hd)
    · exact hX u ((hA u).1 ha).1 v ((hA v).1 hc).1
    · exact ((hA u).1 ha).2 v hd
    · exact ((hB u).1 hb).2 v hc
    · exact hY u ((hB u).1 hb).1 v ((hB v).1 hd).1
  · intro v hv hnot
    by_contra! h
    apply hnot
    rcases hv with hx | hy
    · exact Or.inl ((hA v).2 ⟨hx, fun k hk => h k (Or.inr hk)⟩)
    · exact Or.inr ((hB v).2 ⟨hy, fun k hk => h k (Or.inl hk)⟩)

theorem kernelOfColor {V : Type*} (H : SimpleGraph V) (hc : H.Colorable 2)
    (D : V → V → Prop) (h : ∀ u v, H.Adj u v ↔ D u v ∨ D v u) :
    ∃ K : Set V, (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧
       ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  obtain ⟨c⟩ := hc
  let S (i : Fin 2) : Set V := {v | c v = i}
  have hi (i : Fin 2) : ∀ u ∈ S i, ∀ v ∈ S i, ¬ D u v := by
    intro u hu v hv hd
    exact c.valid ((h u v).2 (Or.inl hd)) (hu.trans hv.symm)
  obtain ⟨K, _, hK, ha⟩ := kernelTwoSets D (S 0) (S 1) (hi 0) (hi 1)
  refine ⟨K, ?_, fun v => ha v ?_⟩
  · intro u hu v hv he
    exact ((h u v).1 he).elim (hK u hu v hv) (hK v hv u hu)
  · change c v = 0 ∨ c v = 1
    exact (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) (c v)

open SimpleGraph

/-- On a shortest odd closed walk, no walk can shorten both arcs between two positions. -/
private theorem noShortcut730 {V : Type*} {H : SimpleGraph V} {x : V} (p : H.Walk x x)
    (ho : Odd p.length)
    (hmin : ∀ (u : V) (q : H.Walk u u), Odd q.length → p.length ≤ q.length)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.length)
    (r : H.Walk (p.getVert i) (p.getVert j)) :
    j - i ≤ r.length ∨ p.length - (j - i) ≤ r.length := by
  let a : H.Walk (p.getVert i) (p.getVert j) :=
    ((p.drop i).take (j - i)).copy rfl (by rw [Walk.drop_getVert, Nat.add_sub_of_le hij])
  let b := (p.drop j).append (p.take i)
  have ha : a.length = j - i := by
    simp [a, inf_eq_left.mpr (show j - i ≤ p.length - i by omega)]
  have hb : b.length = p.length - (j - i) := by
    simp [b, inf_eq_left.mpr (show i ≤ p.length by omega)]
    omega
  have ha' : (a.append r.reverse).length = j - i + r.length := by simp [ha]
  have hb' : (r.append b).length = r.length + (p.length - (j - i)) := by simp [hb]
  rw [Nat.odd_iff] at ho
  by_cases h : Odd (a.append r.reverse).length
  · have hle := hmin _ _ h
    omega
  · rw [Nat.odd_iff] at h
    have hh : Odd (r.append b).length := by rw [Nat.odd_iff]; omega
    have hle := hmin _ _ hh
    omega

theorem inducedOdd730 {n : ℕ} (H : SimpleGraph (Fin n)) (h : ¬ H.Colorable 2) :
    ∃ (m : ℕ) (_ : 3 ≤ m) (_ : Odd m) (f : Fin m → Fin n), Function.Injective f ∧
      ∀ i j, H.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val := by
  classical
  change ¬ H.IsBipartite at h
  rw [isBipartite_iff_forall_walk_even_length] at h
  push Not at h
  obtain ⟨v, q, hq⟩ := h
  let P := fun k : ℕ => ∃ (u : Fin n) (w : H.Walk u u), w.length = k ∧ Odd k
  have hex : ∃ k, P k := ⟨q.length, v, q, rfl, by simpa using hq⟩
  obtain ⟨x, p, hp, ho⟩ := Nat.find_spec hex
  have hmin (u : Fin n) (w : H.Walk u u) (hw : Odd w.length) : p.length ≤ w.length :=
    hp ▸ Nat.find_min' hex ⟨u, w, rfl, hw⟩
  rw [← hp] at ho
  have hm : 3 ≤ p.length := by
    have := p.length_ne_one
    rw [Nat.odd_iff] at ho
    omega
  refine ⟨p.length, hm, ho, fun i => p.getVert i.val, ?_, ?_⟩
  · have distinct {i j : ℕ} (hij : i < j) (hj : j < p.length) :
        p.getVert i ≠ p.getVert j := by
      intro he
      let r : H.Walk (p.getVert i) (p.getVert j) := (Walk.nil : H.Walk _ _).copy rfl he
      have hs := noShortcut730 p ho hmin hij.le hj r
      have hr : r.length = 0 := by simp [r]
      omega
    intro i j he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h' | h' | h'
    · exact False.elim (distinct h' j.isLt he)
    · exact h'
    · exact False.elim (distinct h' i.isLt he.symm)
  · have forward {i j : ℕ} (hi : i < p.length) (hj : j < p.length) (hij : i ≤ j)
        (he : H.Adj (p.getVert i) (p.getVert j)) :
        (i + 1) % p.length = j ∨ (j + 1) % p.length = i := by
      have hne : i ≠ j := by rintro rfl; exact he.ne rfl
      have hs := noShortcut730 p ho hmin hij hj he.toWalk
      simp only [Adj.length_toWalk] at hs
      rcases hs with hs | hs
      · left
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · right
        have hlast : j + 1 = p.length := by omega
        rw [hlast, Nat.mod_self]
        omega
    have next {i j : ℕ} (hi : i < p.length) (he : (i + 1) % p.length = j) :
        H.Adj (p.getVert i) (p.getVert j) := by
      have ha := p.adj_getVert_succ hi
      by_cases h' : i + 1 < p.length
      · rw [Nat.mod_eq_of_lt h'] at he
        exact he ▸ ha
      · have hl : i + 1 = p.length := by omega
        simp [hl] at he ha
        simpa [← he] using ha
    intro i j
    constructor
    · intro he
      rcases le_total i.val j.val with hij | hji
      · exact forward i.isLt j.isLt hij he
      · exact (forward j.isLt i.isLt hji he.symm).symm
    · rintro (he | he)
      · exact next i.isLt he
      · exact (next j.isLt he).symm

theorem odd_obstruction {n m : ℕ} (H : SimpleGraph (Fin n))
    (hm : 3 ≤ m) (hodd : Odd m) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hadj : ∀ i j, H.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨
      (j.val + 1) % m = i.val) :
    ¬ (∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧
        ∀ v, v ∉ K → ∃ k ∈ K, D v k) := by
  classical
  intro hkernel
  let ix (t : ℕ) : Fin m := ⟨t % m, Nat.mod_lt _ (by omega)⟩
  let s (i : Fin m) := ix (i.val + 1)
  have sw (i : Fin m) : s (s i) ≠ i := by
    intro he
    have hi := i.isLt
    have hv := congrArg Fin.val he
    change ((i.val + 1) % m + 1) % m = i.val at hv
    rw [Nat.mod_add_mod] at hv
    by_cases h : i.val + 1 + 1 < m
    · rw [Nat.mod_eq_of_lt h] at hv
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : m ≤ i.val + 1 + 1),
          Nat.mod_eq_of_lt (by omega)] at hv
      omega
  have edge (i : Fin m) : H.Adj (f i) (f (s i)) :=
    (hadj _ _).2 (.inl rfl)
  let D (u v : Fin n) : Prop := H.Adj u v ∧
    ((∃ i, f i = u ∧ f (s i) = v) ∨
      (u ∉ Set.range f ∧ (v ∈ Set.range f ∨ u < v)))
  have mem (i : Fin m) : f i ∈ Set.range f := ⟨i, rfl⟩
  have arc (i : Fin m) : D (f i) (f (s i)) :=
    ⟨edge i, .inl ⟨i, rfl, rfl⟩⟩
  have out (i : Fin m) (v) (hd : D (f i) v) : f (s i) = v := by
    rcases hd.2 with ⟨j, hj, hv⟩ | ⟨hn, _⟩
    · simpa only [hf hj] using hv
    · exact (hn (mem i)).elim
  have cover (u v) : H.Adj u v ↔ (D u v ∨ D v u) := by
    constructor
    · intro ha
      by_cases hu : u ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hu
        by_cases hv : v ∈ Set.range f
        · obtain ⟨j, rfl⟩ := hv
          rcases (hadj i j).1 ha with hij | hji
          · exact Or.inl ((Fin.ext hij : s i = j) ▸ arc i)
          · exact Or.inr ((Fin.ext hji : s j = i) ▸ arc j)
        · exact .inr ⟨ha.symm, .inr ⟨hv, .inl (mem _)⟩⟩
      · by_cases hv : v ∈ Set.range f
        · exact .inl ⟨ha, .inr ⟨hu, .inl hv⟩⟩
        · rcases lt_or_gt_of_ne ha.ne with h | h
          · exact .inl ⟨ha, .inr ⟨hu, .inr h⟩⟩
          · exact .inr ⟨ha.symm, .inr ⟨hv, .inr h⟩⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1.symm
  have asym (u v) (h : D u v) (h' : D v u) : False := by
    rcases h.2 with ⟨i, rfl, rfl⟩ | ⟨hu, hh⟩
    · exact sw i (hf (out (s i) _ h'))
    · rcases h'.2 with ⟨j, _, hj⟩ | ⟨hv, hh'⟩
      · exact hu ⟨_, hj⟩
      · exact (lt_asymm (hh.resolve_left hv)) (hh'.resolve_left hu)
  obtain ⟨K, hind, habs⟩ := hkernel D cover asym
  have alt (i : Fin m) : f (s i) ∈ K ↔ f i ∉ K := by
    constructor
    · intro hs hi
      exact hind _ hi _ hs (edge i)
    · intro hi
      obtain ⟨k, hk, hd⟩ := habs _ hi
      exact out i _ hd ▸ hk
  let P (t : ℕ) := f (ix t) ∈ K
  have step (t : ℕ) : P (t + 1) ↔ ¬ P t := by
    have e : s (ix t) = ix (t+1) := Fin.ext (Nat.mod_add_mod _ _ _)
    simpa only [e] using alt (ix t)
  have even (a : ℕ) : P (2*a) ↔ P 0 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [show 2*(a+1) = 2*a+1+1 by omega, step, step, not_not]
      exact ih
  obtain ⟨a, ha⟩ := hodd
  have close : P m ↔ P 0 := by simp [P, ix]
  have bad : P 0 ↔ ¬ P 0 := calc
    P 0 ↔ P m := close.symm
    _ ↔ ¬ P (2*a) := by rw [ha, step]
    _ ↔ ¬ P 0 := not_congr (even _)
  tauto

end PEqualNP.Outside.L_meta_730

open PEqualNP.Outside.L_meta_730 in
theorem PEqualNP.Outside.L_meta_730 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
  (∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) ↔
  H.Colorable 2 := by
  intro n H
  constructor
  · intro hk
    by_contra h
    obtain ⟨m, hm, ho, f, hf, ha⟩ := inducedOdd730 H h
    exact odd_obstruction H hm ho f hf ha hk
  · intro hc D hD _
    exact kernelOfColor H hc D hD
