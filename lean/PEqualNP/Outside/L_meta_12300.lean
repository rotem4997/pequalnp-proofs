import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12300

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Live

variable {α : Type} [DecidableEq α]

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

theorem build_mono {ops : α → α → Finset α} {goal : α} {a b : ℕ} {av : Finset α}
    (h : a ≤ b) (hb : build ops goal a av) : build ops goal b av := by
  induction h with
  | refl => exact hb
  | step _ ih => exact Or.inl ih

theorem build_sub {ops : α → α → Finset α} {goal : α} {k : ℕ} {av av' : Finset α}
    (hsub : av ⊆ av') (hb : build ops goal k av) : build ops goal k av' := by
  induction k generalizing av av' with
  | zero => exact hsub hb
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

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

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, _, rest, rfl, tail⟩
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

end Live

def basicOps {W : ℕ} (a b : BitVec W) : Finset (BitVec W) :=
  {a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a}

def holds {W : ℕ} (A : Finset (BitVec W)) (u : BitVec W) : Prop :=
  u = 0 ∨ u = ~~~0 ∨ ∃ a ∈ A, u = a ∨ u = ~~~a

theorem holds_insert {W : ℕ} {A : Finset (BitVec W)} {u z : BitVec W} (h : holds A u) :
    holds (insert z A) u := by
  rcases h with rfl | rfl | ⟨a, ha, h⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨a, Finset.mem_insert_of_mem ha, h⟩)

theorem holds_not {W : ℕ} {A : Finset (BitVec W)} {u : BitVec W} (h : holds A u) :
    holds A (~~~u) := by
  rcases h with rfl | rfl | ⟨a, ha, hu⟩
  · exact .inr (.inl rfl)
  · exact .inl (by simp)
  · rcases hu with hu | hu
    · exact .inr (.inr ⟨a, ha, .inr (by rw [hu])⟩)
    · exact .inr (.inr ⟨a, ha, .inl (by rw [hu, BitVec.not_not])⟩)

theorem bv_and_or_not_basic {W : ℕ} (a b : BitVec W) :
    ∀ x ∈ ({a, ~~~a} : Finset (BitVec W)), ∀ y ∈ ({b, ~~~b} : Finset (BitVec W)),
      ∀ z ∈ ({x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x} : Finset (BitVec W)),
        ∃ w ∈ basicOps a b, z = w ∨ z = ~~~w := by
  intro x hx y hy z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz | hz | hz <;>
    rw [hz, hx, hy]
  · exact ⟨a &&& b, by simp [basicOps], .inl rfl⟩
  · exact ⟨a ||| b, by simp [basicOps], .inl rfl⟩
  · exact ⟨a &&& ~~~b, by simp [basicOps], .inl rfl⟩
  · exact ⟨b &&& ~~~a, by simp [basicOps], .inl rfl⟩
  · exact ⟨a &&& ~~~b, by simp [basicOps], .inl rfl⟩
  · exact ⟨b &&& ~~~a, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a &&& b, by simp [basicOps], .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)⟩
  · exact ⟨a ||| b, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨b &&& ~~~a, by simp [basicOps], .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a &&& ~~~b, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a ||| b, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a &&& b, by simp [basicOps], .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a ||| b, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a &&& b, by simp [basicOps], .inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨b &&& ~~~a, by simp [basicOps], .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩
  · exact ⟨a &&& ~~~b, by simp [basicOps], .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp; try (cases a[i] <;> cases b[i] <;> rfl))⟩

theorem bv_same_basic {W : ℕ} (a : BitVec W) :
    ∀ x ∈ ({a, ~~~a} : Finset (BitVec W)), ∀ y ∈ ({a, ~~~a} : Finset (BitVec W)),
      ∀ z ∈ ({x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x} : Finset (BitVec W)),
        z = 0 ∨ z = ~~~0 ∨ z = a ∨ z = ~~~a := by
  intro x hx y hy z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz | hz | hz <;>
    rw [hz, hx, hy]
  · exact .inr (.inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp))
  · exact .inr (.inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp))
  · exact .inr (.inr (.inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inr (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inl (by apply BitVec.eq_of_getElem_eq; intro i hi; simp)

theorem bv_const_basic {W : ℕ} (u v : BitVec W) (h : (u = 0 ∨ u = ~~~0) ∨ (v = 0 ∨ v = ~~~0))
    (z : BitVec W) (hz : z ∈ basicOps u v) :
    z = 0 ∨ z = ~~~0 ∨ z = u ∨ z = ~~~u ∨ z = v ∨ z = ~~~v := by
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases h with (hu | hu) | (hv | hv) <;> rcases hz with hz | hz | hz | hz <;> rw [hz]
  · exact .inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inr (.inr (.inr (.inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))))
  · exact .inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inr (.inr (.inr (.inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))))
  · exact .inr (.inr (.inr (.inr (.inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))))
  · exact .inr (.inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp))
  · exact .inr (.inr (.inr (.inr (.inr (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))))
  · exact .inl (by rw [hu]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inr (.inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inr (.inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inr (.inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)))
  · exact .inr (.inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp))
  · exact .inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp)
  · exact .inr (.inr (.inr (.inl (by rw [hv]; apply BitVec.eq_of_getElem_eq; intro i hi; simp))))

theorem bv_holds_basic {W : ℕ} {A : Finset (BitVec W)} {u v z : BitVec W}
    (hu : holds A u) (hv : holds A v) (hz : z ∈ basicOps u v) :
    holds A z ∨ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w A) z := by
  by_cases hc : (u = 0 ∨ u = ~~~0) ∨ (v = 0 ∨ v = ~~~0)
  · left
    rcases bv_const_basic u v hc z hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact hu
    · exact holds_not hu
    · exact hv
    · exact holds_not hv
  · rcases hu with rfl | rfl | ⟨a, ha, hua⟩
    · exact False.elim (hc (.inl (.inl rfl)))
    · exact False.elim (hc (.inl (.inr rfl)))
    · rcases hv with rfl | rfl | ⟨b, hb, hvb⟩
      · exact False.elim (hc (.inr (.inl rfl)))
      · exact False.elim (hc (.inr (.inr rfl)))
      · by_cases hab : a = b
        · subst hab
          left
          have h1 := bv_same_basic a u (by simp [hua]) v (by simp [hvb]) z hz
          rcases h1 with h1 | h1 | h1 | h1 <;> rw [h1]
          · exact .inl rfl
          · exact .inr (.inl rfl)
          · exact .inr (.inr ⟨a, ha, .inl rfl⟩)
          · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
        · right
          obtain ⟨w, hw, hzw⟩ := bv_and_or_not_basic a b u (by simp [hua]) v (by simp [hvb]) z hz
          exact ⟨a, ha, b, hb, hab, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self _ _, hzw⟩)⟩

def IsConst {M : ℕ} (w : BitVec M) : Prop := w = 0 ∨ w = ~~~0

def isConstBool {M : ℕ} (w : BitVec M) : Bool := (w == 0) || (w == ~~~0)

theorem isConstBool_iff {M : ℕ} (w : BitVec M) : isConstBool w = true ↔ IsConst w := by
  simp [isConstBool, IsConst]

theorem live_kill_card {N M : ℕ} (f : BitVec N → BitVec M)
    (hf_and : ∀ a b, f (a &&& b) = f a &&& f b)
    (hf_or : ∀ a b, f (a ||| b) = f a ||| f b)
    (hf_not : ∀ a, f (~~~a) = ~~~(f a))
    {goal : BitVec N} (hnc : ¬ IsConst (f goal))
    {k : ℕ} {s : Finset (BitVec N)} (hlive : live basicOps goal k s) :
    ∀ (A : Finset (BitVec M)), (∀ w ∈ s, holds A (f w)) →
      ∃ m, (s.filter (fun w => isConstBool (f w) = true)).card + m ≤ k ∧
        ∃ t, (t = f goal ∨ t = ~~~(f goal)) ∧ build basicOps t m A := by
  have hf_ops : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
    intro a b z hz
    simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · exact .inl (hf_and a b)
    · exact .inr (.inl (hf_or a b))
    · exact .inr (.inr (.inl (by rw [hf_and, hf_not])))
    · exact .inr (.inr (.inr (by rw [hf_and, hf_not])))
  induction k generalizing s with
  | zero =>
    intro A hA
    change s = {goal} at hlive
    subst hlive
    have hfilt : ({goal} : Finset (BitVec N)).filter (fun w => isConstBool (f w) = true) = ∅ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl hc; exact hnc ((isConstBool_iff _).1 hc)
    rw [hfilt, Finset.card_empty]
    have hg := hA goal (by simp)
    rcases hg with h0 | h1 | ⟨a, ha, hfa⟩
    · exact False.elim (hnc (.inl h0))
    · exact False.elim (hnc (.inr h1))
    · refine ⟨0, by omega, a, ?_, ha⟩
      rcases hfa with h | h
      · exact .inl h.symm
      · exact .inr (by rw [h, BitVec.not_not])
  | succ k ih =>
    intro A hA
    rcases hlive with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, rfl, tail⟩
    · obtain ⟨m, hm, t, ht, hbld⟩ := ih skip A hA
      exact ⟨m, by omega, t, ht, hbld⟩
    · let P : BitVec N → Prop := fun w => isConstBool (f w) = true
      have hfz : f z ∈ basicOps (f a) (f b) := hf_ops a b z hz
      have hfa : holds A (f a) := hA a (by simp)
      have hfb : holds A (f b) := hA b (by simp)
      have hznotr : z ∉ rest := fun hm => hzout (by simp [hm])
      by_cases hcab : IsConst (f a) ∨ IsConst (f b)
      · have hfz_holds : holds A (f z) := by
          rcases bv_const_basic (f a) (f b) hcab (f z) hfz with h | h | h | h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact h ▸ hfa
          · exact h ▸ holds_not hfa
          · exact h ▸ hfb
          · exact h ▸ holds_not hfb
        have hA' : ∀ w ∈ insert z rest, holds A (f w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hfz_holds
          · exact hA w (by simp [hw])
        obtain ⟨m, hm, t, ht, hbld⟩ := ih tail A hA'
        have hcard : ((insert a (insert b rest)).filter P).card ≤ ((insert z rest).filter P).card + 1 := by
          by_cases hPa : IsConst (f a) <;> by_cases hPb : IsConst (f b)
          · have hPz : IsConst (f z) := by
              rcases bv_const_basic (f a) (f b) (.inl hPa) (f z) hfz with h | h | h | h | h | h
              · exact .inl h
              · exact .inr h
              · exact h ▸ hPa
              · rcases hPa with h1 | h1 <;> [exact .inr (h ▸ h1 ▸ rfl); exact .inl (by rw [h, h1, BitVec.not_not])]
              · exact h ▸ hPb
              · rcases hPb with h1 | h1 <;> [exact .inr (h ▸ h1 ▸ rfl); exact .inl (by rw [h, h1, BitVec.not_not])]
            have h1 : (insert z rest).filter P = insert z (rest.filter P) := by
              ext w
              simp only [Finset.mem_filter, Finset.mem_insert, P, isConstBool_iff]
              constructor
              · rintro ⟨rfl | hw, hc⟩
                · exact .inl rfl
                · exact .inr ⟨hw, hc⟩
              · rintro (rfl | ⟨hw, hc⟩)
                · exact ⟨.inl rfl, hPz⟩
                · exact ⟨.inr hw, hc⟩
            rw [h1, Finset.card_insert_of_notMem (fun hm => hznotr (Finset.mem_filter.mp hm).1)]
            have h2 : (insert a (insert b rest)).filter P ⊆ insert a (insert b (rest.filter P)) := by
              intro w hw
              simp only [Finset.mem_filter, Finset.mem_insert] at hw ⊢
              rcases hw.1 with rfl | rfl | hr
              · exact .inl rfl
              · exact .inr (.inl rfl)
              · exact .inr (.inr ⟨hr, hw.2⟩)
            have h3 := Finset.card_le_card h2
            have h4 := Finset.card_insert_le a (insert b (rest.filter P))
            have h5 := Finset.card_insert_le b (rest.filter P)
            omega
          · have h2 : (insert a (insert b rest)).filter P ⊆ insert a (rest.filter P) := by
              intro w hw
              simp only [Finset.mem_filter, Finset.mem_insert] at hw ⊢
              rcases hw.1 with rfl | rfl | hr
              · exact .inl rfl
              · exact False.elim (hPb ((isConstBool_iff _).1 hw.2))
              · exact .inr ⟨hr, hw.2⟩
            have h3 := Finset.card_le_card h2
            have h4 := Finset.card_insert_le a (rest.filter P)
            have h5 : rest.filter P ⊆ (insert z rest).filter P := Finset.filter_subset_filter _ (Finset.subset_insert _ _)
            have h6 := Finset.card_le_card h5
            omega
          · have h2 : (insert a (insert b rest)).filter P ⊆ insert b (rest.filter P) := by
              intro w hw
              simp only [Finset.mem_filter, Finset.mem_insert] at hw ⊢
              rcases hw.1 with rfl | rfl | hr
              · exact False.elim (hPa ((isConstBool_iff _).1 hw.2))
              · exact .inl rfl
              · exact .inr ⟨hr, hw.2⟩
            have h3 := Finset.card_le_card h2
            have h4 := Finset.card_insert_le b (rest.filter P)
            have h5 : rest.filter P ⊆ (insert z rest).filter P := Finset.filter_subset_filter _ (Finset.subset_insert _ _)
            have h6 := Finset.card_le_card h5
            omega
          · exact False.elim (hcab.elim hPa hPb)
        dsimp only [P] at hcard
        exact ⟨m, by omega, t, ht, hbld⟩
      · have hPa : ¬ IsConst (f a) := fun h => hcab (.inl h)
        have hPb : ¬ IsConst (f b) := fun h => hcab (.inr h)
        have hcard : ((insert a (insert b rest)).filter P).card ≤ ((insert z rest).filter P).card := by
          apply Finset.card_le_card
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_insert] at hw ⊢
          rcases hw.1 with rfl | rfl | hr
          · exact False.elim (hPa ((isConstBool_iff _).1 hw.2))
          · exact False.elim (hPb ((isConstBool_iff _).1 hw.2))
          · exact ⟨.inr hr, hw.2⟩
        dsimp only [P] at hcard
        rcases bv_holds_basic hfa hfb hfz with hfz_holds | ⟨a', ha', b', hb', hab', w, hw, hzw⟩
        · have hA' : ∀ u ∈ insert z rest, holds A (f u) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact hfz_holds
            · exact hA u (by simp [hu])
          obtain ⟨m, hm, t, ht, hbld⟩ := ih tail A hA'
          exact ⟨m, by omega, t, ht, hbld⟩
        · have hA' : ∀ u ∈ insert z rest, holds (insert w A) (f u) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact hzw
            · exact holds_insert (hA u (by simp [hu]))
          obtain ⟨m, hm, t, ht, hbld⟩ := ih tail (insert w A) hA'
          exact ⟨m + 1, by omega, t, ht, Or.inr ⟨a', ha', b', hb', hab', w, hw, hbld⟩⟩

abbrev W64 := BitVec 64

def legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def isBinary (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

def bit64 (k : Fin 64) (v : W64) : Bool := v[k.val]

def step64 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def action64 (w : List W64) (g : Gate) : W64 :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => w.getD i 0
  | .and, [i, j] => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, [i, j] => w.getD i 0 ||| w.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(w.getD i 0)
  | _, _ => 0

theorem getD_map_bit64 (k : Fin 64) (w : List W64) (i : ℕ) :
    (w.map (bit64 k)).getD i false = bit64 k (w.getD i 0) := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), bit64]

theorem action64_spec (w : List W64) (g : Gate) (hg : legal g) (k : Fin 64) :
    step64 (w.map (bit64 k)) g = (w ++ [action64 w g]).map (bit64 k) := by
  obtain ⟨hop, hlen⟩ := hg
  simp only [step64, List.map_append, List.map_cons, List.map_nil]
  congr 1; congr 1
  have hz0 : (0 : W64)[k.val] = false := by simp
  rcases hop with h | h | h
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨a, b⟩⟩⟩
    · simp only [h, hin, action64, GateOp.eval, List.map_nil, List.all_nil, bit64, BitVec.getElem_not, hz0, Bool.not_false]
    · simp only [h, hin, action64, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, getD_map_bit64]
    · simp only [h, hin, action64, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq, getD_map_bit64, bit64, BitVec.getElem_and]
    · simp [hin] at hlen
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨a, b⟩⟩⟩
    · simp only [h, hin, action64, GateOp.eval, List.map_nil, List.any_nil, bit64, hz0]
    · simp only [h, hin, action64, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq, getD_map_bit64]
    · simp only [h, hin, action64, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq, getD_map_bit64, bit64, BitVec.getElem_or]
    · simp [hin] at hlen
  · rcases hin : g.inputs with _ | ⟨i, rest⟩
    · simp only [h, hin, action64, GateOp.eval, List.map_nil, List.headD_nil, bit64, BitVec.getElem_not, hz0, Bool.not_false]
    · simp only [h, hin, action64, GateOp.eval, List.map_cons, List.headD_cons, getD_map_bit64, bit64, BitVec.getElem_not]

theorem holds_getD64 {A : Finset W64} {w : List W64} (hw : ∀ u ∈ w, holds A u) (i : ℕ) :
    holds A (w.getD i 0) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
    exact .inl rfl

theorem gate_reach64 (w : List W64) (av : Finset W64) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then
      holds av (action64 w g) ∨
        ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ basicOps a b, holds (insert z av) (action64 w g)
    else holds av (action64 w g) := by
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with h | h | h
  · simp only [isBinary, h, ite_true]
    rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨a, b⟩⟩⟩
    · left; simp [h, hin, action64, holds]
    · left; simpa [h, hin, action64] using holds_getD64 hw i
    · simpa [h, hin, action64] using bv_holds_basic (holds_getD64 hw i) (holds_getD64 hw j) (by simp [basicOps])
    · simp [hin] at hlen
  · simp only [isBinary, h, ite_true]
    rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨a, b⟩⟩⟩
    · left; simp [h, hin, action64, holds]
    · left; simpa [h, hin, action64] using holds_getD64 hw i
    · simpa [h, hin, action64] using bv_holds_basic (holds_getD64 hw i) (holds_getD64 hw j) (by simp [basicOps])
    · simp [hin] at hlen
  · simp only [isBinary, h, Bool.false_eq_true, ite_false]
    rcases hin : g.inputs with _ | ⟨i, rest⟩
    · simp [h, hin, action64, holds]
    · simpa [h, hin, action64] using holds_not (holds_getD64 hw i)

theorem compile64 (target : W64) (hnc0 : target ≠ 0) (hnc1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g) :
    ∀ (w : List W64) (av : Finset W64), (∀ u ∈ w, holds av u) →
      (∀ k : Fin 64, (gs.foldl step64 (w.map (bit64 k))).getD out false = bit64 k target) →
      ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs with
  | nil =>
    intro w av hw he
    have same : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      have h1 := he ⟨i, hi⟩
      rw [List.foldl_nil, getD_map_bit64] at h1
      exact h1
    have hout := holds_getD64 hw out
    rw [same] at hout
    rcases hout with h0 | h1 | ⟨t, ht, hteq⟩
    · exact False.elim (hnc0 h0)
    · exact False.elim (hnc1 h1)
    · refine ⟨t, ?_, ht⟩
      rcases hteq with rfl | h
      · exact .inl rfl
      · exact .inr (by rw [h, BitVec.not_not])
  | cons g gs ih =>
    intro w av hw he
    let z := action64 w g
    have stepOK := action64_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step64 ((w ++ [z]).map (bit64 k))).getD out false = bit64 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W64) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (fun u hu => by
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach64 w av hw g (hg g (by simp))
    cases hbin : isBinary g
    · simp only [hbin, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, hbin] using cont av hw stepClass
    · simp only [hbin, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, hbin]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def nOps (M a b : Nat) : List Nat :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.xor b M), Nat.land b (Nat.xor a M)]

def nOpsFS (M a b : Nat) : Finset Nat :=
  ((nOps M a b).filter (fun c => !Nat.beq c 0)).toFinset

def eBV {W : ℕ} (v : BitVec W) : Nat :=
  (if v.getLsbD 0 then ~~~v else v).toNat

theorem eBV_not {W : ℕ} (hW : 0 < W) (v : BitVec W) : eBV (~~~v) = eBV v := by
  unfold eBV
  have h0 : (~~~v).getLsbD 0 = !v.getLsbD 0 := by
    simp [BitVec.getLsbD_not, hW]
  rw [h0]
  cases hv : v.getLsbD 0 <;> simp [BitVec.not_not]

theorem nat_beq_false_iff {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  cases h : Nat.beq a b
  · exact ⟨fun _ heq => by subst heq; simp [Nat.beq_refl] at h, fun _ => rfl⟩
  · exact ⟨fun hc => (by cases hc), fun hne => False.elim (hne (Nat.eq_of_beq_eq_true h))⟩

theorem bv_not_toNat {W : ℕ} (v : BitVec W) : (~~~v).toNat = Nat.xor v.toNat (2 ^ W - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.xor_eq, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_not]
  by_cases hi : i < W
  · simp [hi]
  · have hge : W ≤ i := Nat.le_of_not_lt hi
    have hlt : v.toNat < 2 ^ i := lt_of_lt_of_le (BitVec.isLt v) (Nat.pow_le_pow_right (by omega) hge)
    have hvf : v.getLsbD i = false := by rw [← BitVec.testBit_toNat]; exact Nat.testBit_lt_two_pow hlt
    simp [hi, hvf]

theorem eBV_le_mask {W : ℕ} (v : BitVec W) : eBV v < 2 ^ W := by
  unfold eBV; exact BitVec.isLt _

theorem eBV_lt_testBit_ge {W : ℕ} (v : BitVec W) {i : ℕ} (hi : W ≤ i) : (eBV v).testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (eBV_le_mask v) (Nat.pow_le_pow_right (by omega) hi))

theorem eBV_zero {W : ℕ} : eBV (0 : BitVec W) = 0 := by simp [eBV]

theorem eBV_basicOps_mem {W : ℕ} (hW : 0 < W) (a b z : BitVec W) (hz : z ∈ basicOps a b) :
    eBV z ∈ nOps (2 ^ W - 1) (eBV a) (eBV b) := by
  let a' : BitVec W := if a.getLsbD 0 then ~~~a else a
  let b' : BitVec W := if b.getLsbD 0 then ~~~b else b
  have ha0 : a'.getLsbD 0 = false := by
    dsimp only [a']; cases h : a.getLsbD 0
    · simp [h]
    · simp [BitVec.getLsbD_not, hW, h]
  have hb0 : b'.getLsbD 0 = false := by
    dsimp only [b']; cases h : b.getLsbD 0
    · simp [h]
    · simp [BitVec.getLsbD_not, hW, h]
  have ha_eq : a = a' ∨ a = ~~~a' := by
    dsimp only [a']; cases h : a.getLsbD 0 <;> simp [BitVec.not_not]
  have hb_eq : b = b' ∨ b = ~~~b' := by
    dsimp only [b']; cases h : b.getLsbD 0 <;> simp [BitVec.not_not]
  obtain ⟨w, hw, hzw⟩ := bv_and_or_not_basic a' b' a (by simp [ha_eq]) b (by simp [hb_eq]) z hz
  have hez : eBV z = eBV w := by
    rcases hzw with rfl | rfl
    · rfl
    · exact eBV_not hW w
  rw [hez]
  have hea : eBV a = a'.toNat := rfl
  have heb : eBV b = b'.toNat := rfl
  rw [hea, heb]
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hw
  simp only [nOps, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with rfl | rfl | rfl | rfl
  · left
    have h0 : (a' &&& b').getLsbD 0 = false := by simp [BitVec.getLsbD_and, ha0]
    simp only [eBV, h0, Bool.false_eq_true, ite_false, BitVec.toNat_and, Nat.land_eq]
  · right; left
    have h0 : (a' ||| b').getLsbD 0 = false := by simp [BitVec.getLsbD_or, ha0, hb0]
    simp only [eBV, h0, Bool.false_eq_true, ite_false, BitVec.toNat_or, Nat.lor_eq]
  · right; right; left
    have h0 : (a' &&& ~~~b').getLsbD 0 = false := by simp [BitVec.getLsbD_and, ha0]
    simp only [eBV, h0, Bool.false_eq_true, ite_false, BitVec.toNat_and, bv_not_toNat, Nat.land_eq]
  · right; right; right
    have h0 : (b' &&& ~~~a').getLsbD 0 = false := by simp [BitVec.getLsbD_and, hb0]
    simp only [eBV, h0, Bool.false_eq_true, ite_false, BitVec.toNat_and, bv_not_toNat, Nat.land_eq]

theorem nat_land_mask_of_lt {W x : ℕ} (hx : x < 2 ^ W) : Nat.land x (2 ^ W - 1) = x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.land_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < W
  · simp [hi]
  · simp [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))]

theorem nat_land_xor_self {W x : ℕ} (hx : x < 2 ^ W) : Nat.land x (Nat.xor x (2 ^ W - 1)) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.land_eq, Nat.xor_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
  by_cases hi : i < W
  · simp [hi]
  · simp [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))]

theorem build_to_nbuild {W : ℕ} (hW : 0 < W) {t : BitVec W} {k : ℕ} {A : Finset (BitVec W)}
    (hb : build basicOps t k A) (ht : eBV t ≠ 0) :
    build (nOpsFS (2 ^ W - 1)) (eBV t) k ((A.image eBV).erase 0) := by
  induction k generalizing A with
  | zero =>
    exact Finset.mem_erase.mpr ⟨ht, Finset.mem_image_of_mem eBV hb⟩
  | succ k ih =>
    rcases hb with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih skip)
    · have htail := ih tail
      have hmem := eBV_basicOps_mem hW a b z hz
      by_cases hz0 : eBV z = 0
      · have heq : ((insert z A).image eBV).erase 0 = (A.image eBV).erase 0 := by
          ext u; simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_insert]
          constructor
          · rintro ⟨hu0, w, rfl | hw, rfl⟩
            · exact False.elim (hu0 hz0)
            · exact ⟨hu0, w, hw, rfl⟩
          · rintro ⟨hu0, w, hw, rfl⟩
            exact ⟨hu0, w, .inr hw, rfl⟩
        rw [heq] at htail
        exact Or.inl htail
      · have hins : ((insert z A).image eBV).erase 0 = insert (eBV z) ((A.image eBV).erase 0) := by
          ext u; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
          constructor
          · rintro ⟨hu0, w, rfl | hw, rfl⟩
            · exact .inl rfl
            · exact .inr ⟨hu0, w, hw, rfl⟩
          · rintro (rfl | ⟨hu0, w, hw, rfl⟩)
            · exact ⟨hz0, z, .inl rfl, rfl⟩
            · exact ⟨hu0, w, .inr hw, rfl⟩
        rw [hins] at htail
        by_cases ha0 : eBV a = 0
        · rw [ha0] at hmem
          simp only [nOps, Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.zero_and, Nat.zero_or,
            Nat.zero_xor, List.mem_cons, List.not_mem_nil, or_false] at hmem
          have hzb : eBV z = eBV b := by
            rcases hmem with h | h | h | h
            · exact False.elim (hz0 h)
            · exact h
            · exact False.elim (hz0 h)
            · rw [← Nat.land_eq, nat_land_mask_of_lt (eBV_le_mask b)] at h; exact h
          have hb_in : eBV z ∈ (A.image eBV).erase 0 := by
            rw [hzb]; exact Finset.mem_erase.mpr ⟨hzb ▸ hz0, Finset.mem_image_of_mem eBV hb⟩
          rw [Finset.insert_eq_of_mem hb_in] at htail
          exact Or.inl htail
        · by_cases hb0 : eBV b = 0
          · rw [hb0] at hmem
            simp only [nOps, Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.and_zero, Nat.or_zero,
              Nat.zero_xor, List.mem_cons, List.not_mem_nil, or_false] at hmem
            have hza : eBV z = eBV a := by
              rcases hmem with h | h | h | h
              · exact False.elim (hz0 h)
              · exact h
              · rw [← Nat.land_eq, nat_land_mask_of_lt (eBV_le_mask a)] at h; exact h
              · simp only [Nat.zero_and] at h; exact False.elim (hz0 h)
            have ha_in : eBV z ∈ (A.image eBV).erase 0 := by
              rw [hza]; exact Finset.mem_erase.mpr ⟨hza ▸ hz0, Finset.mem_image_of_mem eBV ha⟩
            rw [Finset.insert_eq_of_mem ha_in] at htail
            exact Or.inl htail
          · by_cases heab : eBV a = eBV b
            · rw [heab] at hmem
              simp only [nOps, Nat.land_eq, Nat.lor_eq, Nat.and_self, Nat.or_self,
                List.mem_cons, List.not_mem_nil, or_false] at hmem
              have hza : eBV z = eBV b := by
                rcases hmem with h | h | h | h
                · exact h
                · exact h
                · rw [← Nat.land_eq, nat_land_xor_self (eBV_le_mask b)] at h; exact False.elim (hz0 h)
                · rw [← Nat.land_eq, nat_land_xor_self (eBV_le_mask b)] at h; exact False.elim (hz0 h)
              have hb_in : eBV z ∈ (A.image eBV).erase 0 := by
                rw [hza]; exact Finset.mem_erase.mpr ⟨hza ▸ hz0, Finset.mem_image_of_mem eBV hb⟩
              rw [Finset.insert_eq_of_mem hb_in] at htail
              exact Or.inl htail
            · refine Or.inr ⟨eBV a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem eBV ha⟩,
                eBV b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem eBV hb⟩, heab,
                eBV z, ?_, htail⟩
              simp [nOpsFS, hmem, nat_beq_false_iff, hz0]

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

def NRun (M goal : Nat) (k : Nat) (ws : List Nat) : Prop :=
  ∀ P : Nat → List Nat → Prop,
    (∀ u, P u [goal]) →
    (∀ {u xs ys}, xs.Perm ys → P u xs → P u ys) →
    (∀ {u a b r c} (ka kb : Bool),
      c ∈ nOps M a b → c ≠ 0 → c ∉ (a :: b :: r) →
      P u (c :: kept ka a (kept kb b r)) →
      P (u + 1) (a :: b :: r)) →
    P k ws

theorem NRun.done {M goal : Nat} (u : Nat) : NRun M goal u [goal] :=
  fun _ d _ _ => d u

theorem NRun.perm {M goal u : Nat} {xs ys : List Nat} (hp : xs.Perm ys) (h : NRun M goal u xs) :
    NRun M goal u ys :=
  fun P d p s => p hp (h P d p s)

theorem NRun.step {M goal u a b c : Nat} {r : List Nat} (ka kb : Bool)
    (hc : c ∈ nOps M a b) (hnz : c ≠ 0) (hfresh : c ∉ (a :: b :: r))
    (h : NRun M goal u (c :: kept ka a (kept kb b r))) :
    NRun M goal (u + 1) (a :: b :: r) :=
  fun P d p s => s ka kb hc hnz hfresh (h P d p s)

theorem NRun.fold {M goal : Nat} {P : ∀ u ws, NRun M goal u ws → Prop}
    (done : ∀ u, P u [goal] (NRun.done u))
    (perm : ∀ {u xs ys} (hp : xs.Perm ys) (h : NRun M goal u xs), P u xs h → P u ys (NRun.perm hp h))
    (step : ∀ {u a b r c} (ka kb : Bool) (hc : c ∈ nOps M a b) (hnz : c ≠ 0) (hfresh : c ∉ (a :: b :: r))
      (h : NRun M goal u (c :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (NRun.step ka kb hc hnz hfresh h))
    {k ws} (h : NRun M goal k ws) : P k ws h := by
  have hex := h (fun u xs => ∃ h' : NRun M goal u xs, P u xs h')
    (fun u => ⟨NRun.done u, done u⟩)
    (fun hp ⟨h', ih⟩ => ⟨NRun.perm hp h', perm hp h' ih⟩)
    (fun ka kb hc hnz hf ⟨h', ih⟩ => ⟨NRun.step ka kb hc hnz hf h', step ka kb hc hnz hf h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem NRun.weaken {M goal k : Nat} {ws : List Nat} (h : NRun M goal k ws) :
    NRun M goal (k + 1) ws := by
  induction h using NRun.fold with
  | done u => exact NRun.done (u + 1)
  | perm hp _ ih => exact NRun.perm hp ih
  | step ka kb hc hnz hf _ ih => exact NRun.step ka kb hc hnz hf ih

theorem NRun.len {M goal k : Nat} {ws : List Nat} (h : NRun M goal k ws) :
    ws.length ≤ k + 1 := by
  induction h using NRun.fold with
  | done u => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | step ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

theorem live_to_nrun {M goal k : Nat} {s : Finset Nat} (hl : live (nOpsFS M) goal k s) :
    ∀ ws : List Nat, ws.Nodup → ws.toFinset = s → NRun M goal k ws := by
  induction k generalizing s with
  | zero =>
    intro ws hnd hto
    change s = {goal} at hl
    subst hl
    have hperm : ws.Perm [goal] := by
      refine (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton goal)).2 ?_
      intro x
      rw [← List.mem_toFinset, hto, Finset.mem_singleton, List.mem_singleton]
    exact NRun.perm hperm.symm (NRun.done 0)
  | succ k ih =>
    intro ws hnd hto
    rcases hl with skip | ⟨a, ha, b, hb, hab, z, hz, hzout, rest, rfl, tail⟩
    · exact NRun.weaken (ih skip ws hnd hto)
    · have ham : a ∈ ws := by rw [← List.mem_toFinset, hto]; exact ha
      have hbm : b ∈ ws := by rw [← List.mem_toFinset, hto]; exact hb
      have hp1 : ws.Perm (a :: ws.erase a) := List.perm_cons_erase ham
      have hbm' : b ∈ ws.erase a := (hnd.mem_erase_iff.2 ⟨hab.symm, hbm⟩)
      let r := (ws.erase a).erase b
      have hp : ws.Perm (a :: b :: r) := hp1.trans ((List.perm_cons_erase hbm').cons a)
      have hnr : r.Nodup := (hnd.erase a).erase b
      have ha_nr : a ∉ r := fun h => (hnd.mem_erase_iff.1 (List.mem_of_mem_erase h)).1 rfl
      have hb_nr : b ∉ r := fun h => ((hnd.erase a).mem_erase_iff.1 h).1 rfl
      let ka : Bool := decide (a ∈ rest)
      let kb : Bool := decide (b ∈ rest)
      have hzn : z ∉ (a :: b :: r) := by
        intro hm
        have hmw : z ∈ ws := hp.mem_iff.2 hm
        exact hzout (hto ▸ List.mem_toFinset.2 hmw)
      have hnd' : (z :: kept ka a (kept kb b r)).Nodup := by
        refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr hb_nr) ?_⟩
        · rw [mem_kept, mem_kept]
          rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | hr)
          · exact hzn (by simp)
          · exact hzn (by simp)
          · exact hzn (by simp [hr])
        · rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hab h
          · exact ha_nr h
      have hto' : (z :: kept ka a (kept kb b r)).toFinset = insert z rest := by
        ext x
        simp only [List.mem_toFinset, List.mem_cons, mem_kept, Finset.mem_insert, ka, kb, decide_eq_true_eq]
        constructor
        · rintro (rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩ | hr)
          · exact .inl rfl
          · exact .inr h
          · exact .inr h
          · have hxw : x ∈ ws := List.mem_of_mem_erase (List.mem_of_mem_erase hr)
            have hxa : x ≠ a := fun e => ha_nr (e ▸ hr)
            have hxb : x ≠ b := fun e => hb_nr (e ▸ hr)
            have hxs : x ∈ insert a (insert b rest) := hto ▸ List.mem_toFinset.2 hxw
            simp only [Finset.mem_insert] at hxs
            rcases hxs with rfl | rfl | hxr
            · exact False.elim (hxa rfl)
            · exact False.elim (hxb rfl)
            · exact .inr hxr
        · rintro (rfl | hxr)
          · exact .inl rfl
          · by_cases hxa : x = a
            · subst hxa; exact .inr (.inl ⟨hxr, rfl⟩)
            · by_cases hxb : x = b
              · subst hxb; exact .inr (.inr (.inl ⟨hxr, rfl⟩))
              · have hxw : x ∈ ws := by rw [← List.mem_toFinset, hto]; simp [hxr]
                have hx1 : x ∈ ws.erase a := hnd.mem_erase_iff.2 ⟨hxa, hxw⟩
                have hx2 : x ∈ r := (hnd.erase a).mem_erase_iff.2 ⟨hxb, hx1⟩
                exact .inr (.inr (.inr hx2))
      have hz_ops : z ∈ nOps M a b ∧ z ≠ 0 := by
        simp only [nOpsFS, List.mem_toFinset, List.mem_filter, Bool.not_eq_true', nat_beq_false_iff] at hz
        exact hz
      have hrun := ih tail (z :: kept ka a (kept kb b r)) hnd' hto'
      exact NRun.perm hp.symm (NRun.step ka kb hz_ops.1 hz_ops.2 hzn hrun)

theorem nrun_bits {W goal k : Nat} {ws : List Nat} (h : NRun (2 ^ W - 1) goal k ws)
    (i j : Nat) (hi : i < W) (hj : j < W)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : goal.testBit i = goal.testBit j := by
  have hmi : (2 ^ W - 1).testBit i = true := by simp [Nat.testBit_two_pow_sub_one, hi]
  have hmj : (2 ^ W - 1).testBit j = true := by simp [Nat.testBit_two_pow_sub_one, hj]
  induction h using NRun.fold with
  | done _ => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | @step u a b r c ka kb hc _ _ _ ih =>
    apply ih
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    intro w hmem
    simp only [List.mem_cons, mem_kept] at hmem
    rcases hmem with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr
    · simp only [nOps, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp [Nat.land_eq, Nat.lor_eq, Nat.xor_eq, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha, hb, hmi, hmj]
    · exact ha
    · exact hb
    · exact hw w (by simp [hr])

def allSep (M : Nat) : List Nat → Nat → Nat → Bool
  | [], m0, m1 => Nat.beq m0 0 || Nat.beq m1 0
  | w :: ws, m0, m1 =>
    Nat.beq m0 0 || Nat.beq m1 0 ||
    (allSep M ws (Nat.land m0 w) (Nat.land m1 w) &&
     allSep M ws (Nat.land m0 (Nat.xor w M)) (Nat.land m1 (Nat.xor w M)))

theorem exists_testBit_of_ne_zero {W m : Nat} (hm : m < 2 ^ W) (hne : m ≠ 0) :
    ∃ i < W, m.testBit i = true := by
  by_contra h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < W
  · cases ht : m.testBit i
    · rfl
    · exact False.elim (h ⟨i, hi, ht⟩)
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))

theorem land_lt_two_pow {W a b : Nat} (ha : a < 2 ^ W) : Nat.land a b < 2 ^ W := by
  rw [Nat.land_eq, Nat.and_comm]
  exact Nat.and_lt_two_pow b ha

theorem allSep_false {W : Nat} : ∀ (ws : List Nat) (m0 m1 : Nat),
    m0 < 2 ^ W → m1 < 2 ^ W → allSep (2 ^ W - 1) ws m0 m1 = false →
    ∃ i < W, ∃ j < W, m0.testBit i = true ∧ m1.testBit j = true ∧ ∀ w ∈ ws, w.testBit i = w.testBit j
  | [], m0, m1, h0, h1, hf => by
    simp only [allSep, Bool.or_eq_false_iff, nat_beq_false_iff] at hf
    obtain ⟨i, hi, hti⟩ := exists_testBit_of_ne_zero h0 hf.1
    obtain ⟨j, hj, htj⟩ := exists_testBit_of_ne_zero h1 hf.2
    exact ⟨i, hi, j, hj, hti, htj, fun _ hm => by cases hm⟩
  | w :: ws, m0, m1, h0, h1, hf => by
    simp only [allSep, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hf
    rcases hf.2 with hf1 | hf2
    · obtain ⟨i, hi, j, hj, hti, htj, hall⟩ := allSep_false ws _ _ (land_lt_two_pow h0) (land_lt_two_pow h1) hf1
      simp only [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hti htj
      refine ⟨i, hi, j, hj, hti.1, htj.1, ?_⟩
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [hti.2, htj.2]
      · exact hall u hu
    · obtain ⟨i, hi, j, hj, hti, htj, hall⟩ := allSep_false ws _ _ (land_lt_two_pow h0) (land_lt_two_pow h1) hf2
      simp only [Nat.land_eq, Nat.xor_eq, Nat.testBit_and, Nat.testBit_xor,
        Nat.testBit_two_pow_sub_one, hi, hj, decide_true, Bool.and_eq_true] at hti htj
      refine ⟨i, hi, j, hj, hti.1, htj.1, ?_⟩
      intro u hu
      rcases List.mem_cons.1 hu with hu | hu
      · rw [hu]; cases hwi : w.testBit i <;> cases hwj : w.testBit j <;> simp_all
      · exact hall u hu

theorem nrun_allSep {W goal k : Nat} {ws : List Nat} (hgoal : goal < 2 ^ W)
    (h : NRun (2 ^ W - 1) goal k ws) :
    allSep (2 ^ W - 1) ws (Nat.xor goal (2 ^ W - 1)) goal = true := by
  cases hs : allSep (2 ^ W - 1) ws (Nat.xor goal (2 ^ W - 1)) goal
  · exfalso
    have hlt : Nat.xor goal (2 ^ W - 1) < 2 ^ W := by
      rw [Nat.xor_eq]
      exact Nat.xor_lt_two_pow hgoal (Nat.sub_lt (Nat.two_pow_pos W) (by omega))
    obtain ⟨i, hi, j, hj, hti, htj, hall⟩ := allSep_false ws _ _ hlt hgoal hs
    simp only [Nat.xor_eq, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hi, decide_true] at hti
    have heq := nrun_bits h i j hi hj hall
    cases hgi : goal.testBit i <;> simp_all
  · rfl

def ok1 (M goal : Nat) : List Nat → Bool
  | [a] => Nat.beq a goal
  | [a, b] => Nat.beq a goal || Nat.beq b goal ||
      Nat.beq (Nat.land a b) goal || Nat.beq (Nat.lor a b) goal ||
      Nat.beq (Nat.land a (Nat.xor b M)) goal || Nat.beq (Nat.land b (Nat.xor a M)) goal
  | _ => false

theorem ok1_perm {M goal : Nat} {xs ys : List Nat} (hp : xs.Perm ys) : ok1 M goal xs = ok1 M goal ys := by
  induction hp with
  | nil => rfl
  | @cons x l₁ l₂ hp _ =>
    cases l₁ with
    | nil => rw [hp.nil_eq]
    | cons a t =>
      cases t with
      | nil => rw [hp.singleton_eq]
      | cons b t2 =>
        have hl := hp.length_eq
        cases l₂ with
        | nil => simp at hl
        | cons _ y1 => cases y1 with
          | nil => simp at hl
          | cons _ _ => rfl
  | swap x y l =>
    cases l with
    | nil =>
      simp only [ok1, Nat.land_eq, Nat.lor_eq]
      rw [Nat.and_comm y x, Nat.or_comm y x]
      cases Nat.beq x goal <;> cases Nat.beq y goal <;>
        cases Nat.beq (x &&& y) goal <;> cases Nat.beq (x ||| y) goal <;>
        cases Nat.beq (x &&& Nat.xor y M) goal <;> cases Nat.beq (y &&& Nat.xor x M) goal <;> rfl
    | cons _ _ => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem nrun_ok1 {M goal : Nat} : ∀ {u : Nat} {ws : List Nat}, u ≤ 1 → NRun M goal u ws → ok1 M goal ws = true := by
  intro u ws hu h
  induction h using NRun.fold with
  | done _ => simp [ok1]
  | perm hp _ ih => rw [← ok1_perm hp]; exact ih hu
  | @step u' a b r c ka kb hc _ _ htail ih =>
    have hu0 : u' = 0 := by omega
    subst hu0
    have hl := NRun.len htail
    cases ka <;> cases kb <;> simp [kept] at hl
    cases r with
    | cons _ _ => simp at hl
    | nil =>
      have h1 := ih (by omega)
      simp only [kept, Bool.false_eq_true, ite_false, ok1, Nat.beq_eq] at h1
      subst h1
      simp only [nOps, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [ok1, Bool.or_eq_true, Nat.beq_eq]
      rcases hc with h | h | h | h <;> simp [h]

def ok2Pair (M goal a b : Nat) : Bool :=
  (nOps M a b).any fun c => Nat.beq c goal || ok1 M goal [c, a] || ok1 M goal [c, b]

def ok2Triple (M goal a b d : Nat) : Bool :=
  (nOps M a b).any fun c => Nat.beq c goal || ok1 M goal [c, d]

def ok2 (M goal : Nat) : List Nat → Bool
  | [a] => Nat.beq a goal
  | [a, b] => ok1 M goal [a, b] || ok2Pair M goal a b
  | [a, b, d] => ok2Triple M goal a b d || ok2Triple M goal a d b || ok2Triple M goal b d a
  | _ => false

theorem nOps_comm (M a b : Nat) (c : Nat) : c ∈ nOps M a b ↔ c ∈ nOps M b a := by
  simp only [nOps, List.mem_cons, List.not_mem_nil, or_false, Nat.land_eq, Nat.lor_eq]
  rw [Nat.and_comm a b, Nat.or_comm a b]
  constructor <;> (rintro (h | h | h | h) <;> simp [h])

theorem ok2Pair_comm (M goal a b : Nat) : ok2Pair M goal a b = ok2Pair M goal b a := by
  apply Bool.eq_iff_iff.2
  simp only [ok2Pair, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, (nOps_comm M a b c).1 hc, ?_⟩
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h <;> simp [h]
  · rintro ⟨c, hc, h⟩
    refine ⟨c, (nOps_comm M b a c).1 hc, ?_⟩
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h <;> simp [h]

theorem ok2Triple_comm (M goal a b d : Nat) : ok2Triple M goal a b d = ok2Triple M goal b a d := by
  apply Bool.eq_iff_iff.2
  simp only [ok2Triple, List.any_eq_true]
  constructor <;> (rintro ⟨c, hc, h⟩; exact ⟨c, (nOps_comm M _ _ c).1 hc, h⟩)

theorem ok2_perm {M goal : Nat} {xs ys : List Nat} (hp : xs.Perm ys) : ok2 M goal xs = ok2 M goal ys := by
  induction hp with
  | nil => rfl
  | @cons x l₁ l₂ hp _ =>
    cases l₁ with
    | nil => rw [hp.nil_eq]
    | cons a t =>
      cases t with
      | nil => rw [hp.singleton_eq]
      | cons b t2 =>
        cases t2 with
        | nil =>
          rcases List.perm_pair.1 hp.symm with rfl | rfl
          · rfl
          · simp only [ok2, ok2Triple_comm M goal b a x]
            cases ok2Triple M goal x a b <;> cases ok2Triple M goal x b a <;> cases ok2Triple M goal a b x <;> rfl
        | cons _ _ =>
          have hl := hp.length_eq
          rcases l₂ with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at hl ⊢ <;> rfl
  | swap x y l =>
    cases l with
    | nil =>
      simp only [ok2, ok1_perm (List.Perm.swap x y []), ok2Pair_comm]
    | cons d t =>
      cases t with
      | nil =>
        simp only [ok2, ok2Triple_comm M goal y x d]
        cases ok2Triple M goal x y d <;> cases ok2Triple M goal x d y <;> cases ok2Triple M goal y d x <;> rfl
      | cons _ _ => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem nrun_ok2 {M goal : Nat} {ws : List Nat} (h : NRun M goal 2 ws) : ok2 M goal ws = true := by
  have hmain : ∀ {u : Nat} {xs : List Nat}, u ≤ 2 → NRun M goal u xs → ok2 M goal xs = true := by
    intro u xs hu hr
    induction hr using NRun.fold with
    | done _ => simp [ok2]
    | perm hp _ ih => rw [← ok2_perm hp]; exact ih hu
    | @step u' a b r c ka kb hc _ _ htail ih =>
      have hu1 : u' ≤ 1 := by omega
      have h1 := nrun_ok1 hu1 htail
      have hl := NRun.len htail
      cases r with
      | nil =>
        simp only [ok2, Bool.or_eq_true, ok2Pair, List.any_eq_true]
        right
        refine ⟨c, hc, ?_⟩
        cases ka <;> cases kb <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false] at h1 hl
        · exact .inl (.inl h1)
        · exact .inr h1
        · exact .inl (.inr h1)
        · simp at hl; omega
      | cons d r2 =>
        cases r2 with
        | nil =>
          cases ka <;> cases kb <;> simp [kept] at hl
          · simp only [kept, Bool.false_eq_true, ite_false] at h1
            simp only [ok2, Bool.or_eq_true, ok2Triple, List.any_eq_true]
            exact .inl (.inl ⟨c, hc, .inr h1⟩)
          · omega
          · omega
          · omega
        | cons _ _ =>
          cases ka <;> cases kb <;> simp [kept] at hl <;> omega
  exact hmain le_rfl h

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at *
  · cases hti : tag.testBit i <;> cases htd : tag.testBit (i - d) <;>
      cases hwi : w.testBit i <;> cases hwd : w.testBit (i - d) <;> cases hwp : w.testBit (d + i) <;>
      simp_all
  · cases hti : tag.testBit i <;> cases hwi : w.testBit i <;> cases hwp : w.testBit (d + i) <;> simp_all

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [moved tag d i 0 h]; split_ifs <;> simp

theorem move_inv (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [moved tag d i _ h]
  have ht := congrArg (fun v : Nat => v.testBit i) h
  have ht2 := congrArg (fun v : Nat => v.testBit (d + i)) h
  simp only [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_shiftLeft] at ht ht2
  by_cases h1 : tag.testBit i
  · simp only [h1, ite_true, moved tag d (d + i) w h, Nat.testBit_shiftLeft]
    have h2 : tag.testBit (d + i) = false := by
      have : d ≤ d + i := Nat.le_add_right d i
      have h3 : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [this, h3, h1] at ht2
      exact ht2
    simp [h2, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
  · simp only [h1, Bool.false_eq_true, ite_false]
    by_cases h2 : (tag <<< d).testBit i
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [decide_eq_true_eq, Bool.and_eq_true] at h2
      simp only [h2.2, ite_true, Nat.add_sub_of_le h2.1]
    · simp only [h2, Bool.false_eq_true, ite_false, moved tag d i w h, h1]

theorem move_inj (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) {a b : Nat}
    (heq : moveBits tag d a = moveBits tag d b) : a = b := by
  have := congrArg (moveBits tag d) heq
  rwa [move_inv tag d a h, move_inv tag d b h] at this

def moveOK (M goal tag d : Nat) : Bool :=
  Nat.beq (Nat.land tag (Nat.shiftLeft tag d)) 0 &&
  Nat.beq (moveBits tag d M) M &&
  Nat.beq (moveBits tag d goal) goal

theorem nrun_move {M goal u : Nat} {ws : List Nat} (h : NRun M goal u ws)
    (tag d : Nat) (hok : moveOK M goal tag d = true) :
    NRun M goal u (ws.map (moveBits tag d)) := by
  simp only [moveOK, Bool.and_eq_true, Nat.beq_eq, Nat.land_eq, Nat.shiftLeft_eq] at hok
  obtain ⟨⟨hz, hm⟩, hg⟩ := hok
  have hhom := move_hom tag d hz
  have h0 := move_zero tag d hz
  induction h using NRun.fold with
  | done u0 =>
    simp only [List.map_cons, List.map_nil, hg]
    exact NRun.done u0
  | perm hp _ ih => exact NRun.perm (hp.map _) ih
  | @step u' a b r c ka kb hc hnz hf _ ih =>
    simp only [List.map_cons, kept_map] at ih ⊢
    refine NRun.step ka kb ?_ ?_ ?_ ih
    · simp only [nOps, List.mem_cons, List.not_mem_nil, or_false, Nat.land_eq, Nat.lor_eq, Nat.xor_eq] at hc ⊢
      rcases hc with rfl | rfl | rfl | rfl
      · exact .inl (hhom a b).1
      · exact .inr (.inl (hhom a b).2.1)
      · exact .inr (.inr (.inl (by rw [(hhom a _).1, (hhom b M).2.2, hm])))
      · exact .inr (.inr (.inr (by rw [(hhom b _).1, (hhom a M).2.2, hm])))
    · intro hcz; exact hnz (move_inj tag d hz (hcz.trans h0.symm))
    · intro hcm
      have h1 : moveBits tag d c ∈ (a :: b :: r).map (moveBits tag d) := by simpa using hcm
      obtain ⟨w, hw, hweq⟩ := List.mem_map.1 h1
      exact hf ((move_inj tag d hz hweq).symm ▸ hw)

def hw (w : Nat) : Nat :=
  let x := Nat.land (w * 2654435761 + 1) 0xffffffff
  let y := Nat.land (Nat.xor x (Nat.shiftRight x 15) * 2246822519) 0xffffffff
  Nat.land (Nat.xor y (Nat.shiftRight y 13) * 3266489917) 0xffffffff

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := Nat.land (hz zs) 0xffffffff

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if Nat.blt (lo + 1) hi then
      let mid := (lo + hi) / 2
      if Nat.ble (read mid) h then bsr read h f mid hi else bsr read h f lo mid
    else lo

def eraseOne (x : Nat) : List Nat → Option (List Nat)
  | [] => none
  | y :: ys => if Nat.beq x y then some ys else match eraseOne x ys with | none => none | some r => some (y :: r)

theorem eraseOne_perm {x : Nat} : ∀ {ys r : List Nat}, eraseOne x ys = some r → ys.Perm (x :: r)
  | [], _, h => by simp [eraseOne] at h
  | y :: ys, r, h => by
    simp only [eraseOne] at h
    split at h
    next heq => cases h; rw [Nat.eq_of_beq_eq_true heq]
    next =>
      cases he : eraseOne x ys with
      | none => rw [he] at h; cases h
      | some r' => rw [he] at h; cases h; exact ((eraseOne_perm he).cons y).trans (List.Perm.swap _ _ _)

def isPermFast : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, ys => match eraseOne x ys with | none => false | some r => isPermFast xs r
  | _, _ => false

theorem isPermFast_sound : ∀ {xs ys : List Nat}, isPermFast xs ys = true → xs.Perm ys
  | [], [], _ => List.Perm.refl _
  | [], _ :: _, h => by simp [isPermFast] at h
  | x :: xs, ys, h => by
    simp only [isPermFast] at h
    cases he : eraseOne x ys with
    | none => rw [he] at h; cases h
    | some r => rw [he] at h; exact ((isPermFast_sound h).cons x).trans (eraseOne_perm he).symm

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (u : Nat) (zs : List Nat) : Bool :=
  let j := idx u zs
  Nat.blt j (N u) && isPermFast zs (S u j)

def okChild (M goal : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (u : Nat) (zs : List Nat) : Bool :=
  !allSep M zs (Nat.xor goal M) goal ||
  (if Nat.beq u 2 then !ok2 M goal zs else found S N idx u (ori zs))

def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => Nat.beq x y || memNat x ys

theorem memNat_eq_true (x : Nat) (xs : List Nat) : memNat x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [memNat]
  | cons y ys ih => simp [memNat, ih, Nat.beq_eq]

def checkC (goal : Nat) (slack : Nat) (ok : List Nat → Bool) (a b : Nat) (r : List Nat) (ws : List Nat) (c : Nat) : Bool :=
  if Nat.beq c 0 || memNat c ws then true
  else !Nat.beq c goal &&
    ok (c :: r) &&
    (Nat.beq slack 0 || (ok (c :: a :: r) && ok (c :: b :: r))) &&
    (Nat.blt slack 2 || ok (c :: a :: b :: r))

def checkPair (M goal : Nat) (slack : Nat) (ok : List Nat → Bool) (ws : List Nat) (a b : Nat) (r : List Nat) : Bool :=
  checkC goal slack ok a b r ws (Nat.land a b) &&
  checkC goal slack ok a b r ws (Nat.lor a b) &&
  checkC goal slack ok a b r ws (Nat.land a (Nat.xor b M)) &&
  checkC goal slack ok a b r ws (Nat.land b (Nat.xor a M))

def scanWith (M goal : Nat) (slack : Nat) (ok : List Nat → Bool) (ws : List Nat) (a : Nat) :
    List Nat → List Nat → Bool
  | [], _ => true
  | b :: xs, pre => checkPair M goal slack ok ws a b (pre ++ xs) && scanWith M goal slack ok ws a xs (b :: pre)

def scanPairs (M goal : Nat) (slack : Nat) (ok : List Nat → Bool) (ws : List Nat) :
    List Nat → List Nat → Bool
  | [], _ => true
  | a :: xs, pre => scanWith M goal slack ok ws a xs pre && scanPairs M goal slack ok ws xs (a :: pre)

theorem scanWith_sound (M goal slack : Nat) (ok : List Nat → Bool) (ws : List Nat) (a : Nat) :
    ∀ (xs pre : List Nat), scanWith M goal slack ok ws a xs pre = true →
      ∀ {b r}, xs.Perm (b :: r) → ∃ ra, (pre ++ r).Perm ra ∧ checkPair M goal slack ok ws a b ra = true := by
  intro xs; induction xs with
  | nil => intro _ _ b r hp; have := hp.length_eq; simp at this
  | cons x xs ih =>
    intro pre h b r hp
    simp only [scanWith, Bool.and_eq_true] at h
    by_cases hbx : x = b
    · subst hbx; exact ⟨pre ++ xs, List.Perm.append_left pre hp.cons_inv.symm, h.1⟩
    · have hxmem : x ∈ r := (List.mem_cons.1 (hp.mem_iff.1 List.mem_cons_self)).resolve_left hbx
      have hp' : xs.Perm (b :: r.erase x) :=
        (hp.trans (((List.perm_cons_erase hxmem).cons b).trans (List.Perm.swap _ _ _))).cons_inv
      obtain ⟨ra, hra, hck⟩ := ih (x :: pre) h.2 hp'
      have hpr : (pre ++ r).Perm ((x :: pre) ++ r.erase x) :=
        (List.Perm.append_left pre (List.perm_cons_erase hxmem)).trans List.perm_middle
      exact ⟨ra, hpr.trans hra, hck⟩

theorem scanPairs_sound (M goal slack : Nat) (ok : List Nat → Bool) (ws : List Nat) :
    ∀ (xs pre : List Nat), scanPairs M goal slack ok ws xs pre = true →
      ∀ {a b r}, xs.Perm (a :: b :: r) →
        ∃ ra, (pre ++ r).Perm ra ∧
          (checkPair M goal slack ok ws a b ra = true ∨ checkPair M goal slack ok ws b a ra = true) := by
  intro xs; induction xs with
  | nil => intro _ _ a b r hp; have := hp.length_eq; simp at this
  | cons x xs ih =>
    intro pre h a b r hp
    simp only [scanPairs, Bool.and_eq_true] at h
    by_cases hax : x = a
    · subst hax
      obtain ⟨ra, hra, hck⟩ := scanWith_sound M goal slack ok ws x xs pre h.1 hp.cons_inv
      exact ⟨ra, hra, Or.inl hck⟩
    · by_cases hbx : x = b
      · subst hbx
        have hp' : xs.Perm (a :: r) := (hp.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨ra, hra, hck⟩ := scanWith_sound M goal slack ok ws x xs pre h.1 hp'
        exact ⟨ra, hra, Or.inr hck⟩
      · have hxmem : x ∈ r := by
          have := hp.mem_iff.1 List.mem_cons_self
          rcases List.mem_cons.1 this with h1 | h2
          · exact absurd h1 hax
          · exact (List.mem_cons.1 h2).resolve_left hbx
        have hp' : xs.Perm (a :: b :: r.erase x) := by
          have p1 : (a :: b :: r).Perm (x :: a :: b :: r.erase x) :=
            (((List.perm_cons_erase hxmem).cons b).trans (List.Perm.swap _ _ _) |>.cons a).trans (List.Perm.swap _ _ _)
          exact (hp.trans p1).cons_inv
        obtain ⟨ra, hra, hck⟩ := ih (x :: pre) h.2 hp'
        have hpr : (pre ++ r).Perm ((x :: pre) ++ r.erase x) :=
          (List.Perm.append_left pre (List.perm_cons_erase hxmem)).trans List.perm_middle
        exact ⟨ra, hpr.trans hra, hck⟩

def bar (M goal : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (u i : Nat) : Bool :=
  let ws := S u i
  let slack := (u + 1) - ws.length
  !Nat.beq ws.length 1 &&
  scanPairs M goal slack (okChild M goal S N idx ori (u - 1)) ws ws []

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem checkPair_comm_mem {M goal slack : Nat} {ok : List Nat → Bool} {ws : List Nat} {a b c : Nat} {ra : List Nat}
    (h : checkPair M goal slack ok ws a b ra = true ∨ checkPair M goal slack ok ws b a ra = true)
    (hc : c ∈ nOps M a b) :
    checkC goal slack ok a b ra ws c = true ∨ checkC goal slack ok b a ra ws c = true := by
  simp only [nOps, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases h with h | h
  · left
    simp only [checkPair, Bool.and_eq_true] at h
    rcases hc with rfl | rfl | rfl | rfl
    · exact h.1.1.1
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  · right
    simp only [checkPair, Bool.and_eq_true] at h
    rcases hc with rfl | rfl | rfl | rfl
    · rw [Nat.land_eq, Nat.and_comm, ← Nat.land_eq]; exact h.1.1.1
    · rw [Nat.lor_eq, Nat.or_comm, ← Nat.lor_eq]; exact h.1.1.2
    · exact h.2
    · exact h.1.2

theorem bar_sound {W goal maxU : Nat} (hgoal : goal < 2 ^ W)
    (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat)
    (hori : ∀ {u ys}, NRun (2 ^ W - 1) goal u ys → NRun (2 ^ W - 1) goal u (ori ys))
    (hchk : ∀ u, 3 ≤ u → u ≤ maxU → ∀ i < N u, bar (2 ^ W - 1) goal S N idx ori u i = true) :
    ∀ u, 3 ≤ u → u ≤ maxU → ∀ i < N u, ¬ NRun (2 ^ W - 1) goal u (S u i) := by
  intro u
  induction u with
  | zero => intro h3; omega
  | succ u ih =>
    intro h3 hle i hi hrun
    have hbar := hchk (u + 1) h3 hle i hi
    simp only [bar, Bool.and_eq_true, Bool.not_eq_true', nat_beq_false_iff] at hbar
    have hne1 : (S (u + 1) i).length ≠ 1 := hbar.1
    have hscan := hbar.2
    have hcases_gen : ∀ {v xs}, v = u + 1 → NRun (2 ^ W - 1) goal v xs →
        xs.length = 1 ∨
        ∃ a b r c ka kb, xs.Perm (a :: b :: r) ∧ c ∈ nOps (2 ^ W - 1) a b ∧ c ≠ 0 ∧ c ∉ (a :: b :: r) ∧
          NRun (2 ^ W - 1) goal u (c :: kept ka a (kept kb b r)) := by
      intro v xs hv hr
      induction hr using NRun.fold with
      | done _ => exact .inl rfl
      | perm hp _ ihp =>
        rcases ihp hv with h1 | ⟨a, b, r, c, ka, kb, hp2, hc, hnz, hf, htail⟩
        · exact .inl (hp.length_eq.symm.trans h1)
        · exact .inr ⟨a, b, r, c, ka, kb, hp.symm.trans hp2, hc, hnz, hf, htail⟩
      | @step u' a b r c ka kb hc hnz hf htail _ =>
        have hu' : u' = u := by omega
        subst hu'
        exact .inr ⟨a, b, r, c, ka, kb, List.Perm.refl _, hc, hnz, hf, htail⟩
    rcases hcases_gen rfl hrun with h1 | ⟨a, b, r, c, ka, kb, hp, hc, hnz, hf, htail⟩
    · exact hne1 h1
    · obtain ⟨ra, hra, hcp⟩ := scanPairs_sound _ _ _ _ _ (S (u + 1) i) [] hscan hp
      simp only [List.nil_append] at hra
      have hcc := checkPair_comm_mem hcp hc
      have hcnm : memNat c (S (u + 1) i) = false := by
        cases hm : memNat c (S (u + 1) i)
        · rfl
        · exact False.elim (hf (hp.mem_iff.1 ((memNat_eq_true c _).1 hm)))
      have hlen_tail := NRun.len htail
      have hlen_s : (S (u + 1) i).length = r.length + 2 := by
        have := hp.length_eq; simp at this; omega
      have hok_child : ∃ zs, (c :: kept ka a (kept kb b r)).Perm zs ∧
          okChild (2 ^ W - 1) goal S N idx ori u zs = true := by
        have extract : ∀ {x y : Nat} (kx ky : Bool),
            checkC goal ((u + 1) + 1 - (S (u + 1) i).length)
              (okChild (2 ^ W - 1) goal S N idx ori u) x y ra (S (u + 1) i) c = true →
            (c :: kept kx x (kept ky y r)).length ≤ u + 1 →
            okChild (2 ^ W - 1) goal S N idx ori u (c :: kept kx x (kept ky y ra)) = true := by
          intro x y kx ky hck hlt
          simp only [checkC, hcnm, nat_beq_false_iff.2 hnz, Bool.false_or, Bool.false_eq_true, ite_false,
            Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hck
          cases kx <;> cases ky <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hlt ⊢
          · exact hck.1.1.2
          · simp at hlt
            exact (hck.1.2.resolve_left (by omega)).2
          · simp at hlt
            exact (hck.1.2.resolve_left (by omega)).1
          · simp at hlt
            exact hck.2.resolve_left (by omega)
        rcases hcc with hcc | hcc
        · refine ⟨c :: kept ka a (kept kb b ra), ?_, extract ka kb hcc hlen_tail⟩
          exact (keep_perm (keep_perm hra kb b) ka a).cons c
        · have hp_swap : (c :: kept ka a (kept kb b r)).Perm (c :: kept kb b (kept ka a r)) := by
            cases ka <;> cases kb <;> simp only [kept, ite_true, Bool.false_eq_true, ite_false]
            · exact List.Perm.refl _
            · exact List.Perm.refl _
            · exact List.Perm.refl _
            · exact (List.Perm.swap b a r).cons c
          have hlt' : (c :: kept kb b (kept ka a r)).length ≤ u + 1 := hp_swap.length_eq ▸ hlen_tail
          refine ⟨c :: kept kb b (kept ka a ra), hp_swap.trans ((keep_perm (keep_perm hra ka a) kb b).cons c),
            extract kb ka hcc hlt'⟩
      obtain ⟨zs, hzs_p, hokc⟩ := hok_child
      have hrun_zs : NRun (2 ^ W - 1) goal u zs := NRun.perm hzs_p htail
      have hsep := nrun_allSep hgoal hrun_zs
      simp only [okChild, hsep, Bool.not_true, Bool.false_or] at hokc
      by_cases hu2 : u = 2
      · subst hu2
        have hb2 : Nat.beq 2 2 = true := rfl
        simp only [hb2, ite_true, Bool.not_eq_true'] at hokc
        have h2 := nrun_ok2 hrun_zs
        rw [h2] at hokc; cases hokc
      · have hne2 : Nat.beq u 2 = false := nat_beq_false_iff.2 hu2
        simp only [hne2, Bool.false_eq_true, ite_false, found, Bool.and_eq_true, Nat.blt_eq] at hokc
        have hrun_ori := hori hrun_zs
        have hrun_tab := NRun.perm (isPermFast_sound hokc.2) hrun_ori
        exact ih (by omega) (by omega) (idx u (ori zs)) hokc.1 hrun_tab

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_join {f : Nat → Bool} {n1 o n2 : Nat}
    (h1 : span f n1 o = true) (h2 : span f n2 (o + n1) = true) :
    span f (n1 + n2) o = true := by
  induction n1 generalizing o with
  | zero => simpa [span] using h2
  | succ k ih =>
    simp only [span, Bool.and_eq_true] at h1
    have e : k + 1 + n2 = (k + n2) + 1 := by omega
    rw [e]; simp only [span, Bool.and_eq_true]
    exact ⟨h1.1, ih h1.2 (by simpa [Nat.add_assoc, Nat.add_comm 1 k] using h2)⟩

theorem span_ok {f : Nat → Bool} {n o : Nat} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => intro i h1 h2; omega
  | succ k ih =>
    intro i h1 h2
    simp only [span, Bool.and_eq_true] at h
    by_cases hi : i = o
    · subst hi; exact h.1
    · exact ih h.2 i (by omega) (by omega)

def unpack32 : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v =>
    let w := Nat.land v 0xffffffff
    if Nat.beq w 0 then [] else w :: unpack32 k (Nat.shiftRight v 32)

def unpack16 : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v =>
    let w := Nat.land v 0xffff
    if Nat.beq w 0 then [] else w :: unpack16 k (Nat.shiftRight v 16)

def bestPairH (acc : List Nat × Nat) (b : List Nat) : List Nat × Nat :=
  let hb := hk b
  if Nat.blt hb acc.2 then (b, hb) else acc

def ori5Step (cand : List Nat) (acc : List Nat × Nat) : List Nat × Nat :=
  bestPairH (bestPairH acc cand) (cand.map (moveBits 0x22222222 1))

def ori5 (ws : List Nat) : List Nat :=
  let w1 := ws.map (moveBits 0x00f000f0 4)
  let w2 := ws.map (moveBits 0x0000ff00 8)
  let w3 := w1.map (moveBits 0x0000ff00 8)
  let w4 := w2.map (moveBits 0x00f000f0 4)
  let w5 := w3.map (moveBits 0x00f000f0 4)
  let acc0 := (ws, hk ws)
  let acc1 := bestPairH acc0 (ws.map (moveBits 0x22222222 1))
  (ori5Step w5 (ori5Step w4 (ori5Step w3 (ori5Step w2 (ori5Step w1 acc1))))).1

theorem move5_01 : moveOK 0xffffffff 0xe8888880 0x22222222 1 = true := by decide +kernel
theorem move5_23 : moveOK 0xffffffff 0xe8888880 0x00f000f0 4 = true := by decide +kernel
theorem move5_34 : moveOK 0xffffffff 0xe8888880 0x0000ff00 8 = true := by decide +kernel

theorem bestPairH_nrun {M goal u : Nat} {acc : List Nat × Nat} {b : List Nat}
    (ha : NRun M goal u acc.1) (hb : NRun M goal u b) : NRun M goal u (bestPairH acc b).1 := by
  unfold bestPairH
  by_cases h : Nat.blt (hk b) acc.2 = true
  · simp only [h, ite_true]; exact hb
  · simp only [h, ite_false]; exact ha

theorem ori5Step_nrun {u : Nat} {cand : List Nat} {acc : List Nat × Nat}
    (hc : NRun 0xffffffff 0xe8888880 u cand) (hb : NRun 0xffffffff 0xe8888880 u acc.1) :
    NRun 0xffffffff 0xe8888880 u (ori5Step cand acc).1 :=
  bestPairH_nrun (bestPairH_nrun hb hc) (nrun_move hc 0x22222222 1 move5_01)

theorem ori5_nrun {u : Nat} {ws : List Nat} (h : NRun 0xffffffff 0xe8888880 u ws) :
    NRun 0xffffffff 0xe8888880 u (ori5 ws) := by
  have h01 := bestPairH_nrun (acc := (ws, hk ws)) h (nrun_move h 0x22222222 1 move5_01)
  have h1 := nrun_move h 0x00f000f0 4 move5_23
  have h2 := nrun_move h 0x0000ff00 8 move5_34
  have h3 := nrun_move h1 0x0000ff00 8 move5_34
  have h4 := nrun_move h2 0x00f000f0 4 move5_23
  have h5 := nrun_move h3 0x00f000f0 4 move5_23
  exact ori5Step_nrun h5 (ori5Step_nrun h4 (ori5Step_nrun h3 (ori5Step_nrun h2 (ori5Step_nrun h1 h01))))

def ori4Coset (base : List Nat) (acc : List Nat × Nat) : List Nat × Nat :=
  let c1 := base.map (moveBits 0x00f0 4)
  let c2 := c1.map (moveBits 0x0c0c 2)
  let c3 := c2.map (moveBits 0x2222 1)
  bestPairH (bestPairH (bestPairH (bestPairH acc base) c1) c2) c3

def ori4 (ws : List Nat) : List Nat :=
  let a1 := ws.map (moveBits 0x2222 1)
  let a2 := ws.map (moveBits 0x0c0c 2)
  let a3 := a1.map (moveBits 0x0c0c 2)
  let a4 := a2.map (moveBits 0x2222 1)
  let a5 := a3.map (moveBits 0x2222 1)
  let acc0 := (ws, hk ws)
  (ori4Coset a5 (ori4Coset a4 (ori4Coset a3 (ori4Coset a2 (ori4Coset a1 (ori4Coset ws acc0)))))).1

theorem move4_01 : moveOK 0xffff 0xfee8 0x2222 1 = true := by decide +kernel
theorem move4_12 : moveOK 0xffff 0xfee8 0x0c0c 2 = true := by decide +kernel
theorem move4_23 : moveOK 0xffff 0xfee8 0x00f0 4 = true := by decide +kernel

theorem ori4Coset_nrun {u : Nat} {base : List Nat} {acc : List Nat × Nat}
    (hc : NRun 0xffff 0xfee8 u base) (hb : NRun 0xffff 0xfee8 u acc.1) :
    NRun 0xffff 0xfee8 u (ori4Coset base acc).1 := by
  have h1 := nrun_move hc 0x00f0 4 move4_23
  have h2 := nrun_move h1 0x0c0c 2 move4_12
  have h3 := nrun_move h2 0x2222 1 move4_01
  exact bestPairH_nrun (bestPairH_nrun (bestPairH_nrun (bestPairH_nrun hb hc) h1) h2) h3

theorem ori4_nrun {u : Nat} {ws : List Nat} (h : NRun 0xffff 0xfee8 u ws) :
    NRun 0xffff 0xfee8 u (ori4 ws) := by
  have h1 := nrun_move h 0x2222 1 move4_01
  have h2 := nrun_move h 0x0c0c 2 move4_12
  have h3 := nrun_move h1 0x0c0c 2 move4_12
  have h4 := nrun_move h2 0x2222 1 move4_01
  have h5 := nrun_move h3 0x2222 1 move4_01
  exact ori4Coset_nrun h5 (ori4Coset_nrun h4 (ori4Coset_nrun h3 (ori4Coset_nrun h2 (ori4Coset_nrun h1 (ori4Coset_nrun h (acc := (ws, hk ws)) h)))))

def N5 : Nat → Nat
  | 3 => 138
  | 4 => 1103
  | 5 => 1440
  | 6 => 284
  | 7 => 10
  | 8 => 1
  | _ => 0

def SC5_3_0 : Nat := 0xf0f00000ccccccccaaaaaaa000ff0000f0f0f0f0eeee00008888888800fa00faffffffc0f0000000ccccccccaaaaaaaaff00ff00f0fc00c0ccccccccaaaaaaaaffff0000f0f0f0f0ef00aa0088888888ff000a00f0fff0f0ccccccccaaaaaaaaff0f0000f0f0fff0ccccccccaaaaaaaaff00ff00f0f0f0f0eeee880088888888ffff0000f000f000cccc8880aaaaaaaaffff0000ee00ee00888888880f0f0e0effffff00f00000f0ccccccccaaaaaaaaf0f0f0f0eeee00008888888800ee00eeffff0000ff00ff00e0a0f0f088888888f0f0f0f0ee00aa00888888880000aaaaff000000ccccccccaaaaaaa00f0f0f00f0000000ccccccccaaaaaa00a0a0a0a0f000f000ccccccc0aaaaaaaa0000f000ff00ff00e0e0e0e0888888880000eaeaf000ff00ccccccccaaaaaaaa0000ff0cffff0000f000f000ccccc8c0aaaaaaaaffff10f0f0f0f0f0ee00ee0088888888ffffff00ccccccccaaaaaaaa0ffffff0ffff0000f0f0a0a0ee00ee0088888888ffff0000f0f0f0f0ec00ee0088888888ffff0000f0f0f0f0cc00cc00a8888888ff00ff00f8f8f0f0eeee000088888888ffff0000f0f000f0ee00ee0088888888ffff0000f000f000cccccccca8a8a8a0ffff0000ff00ff00888888881f0e1f0eff00ff00f0f0f0f0888888881100ffccff0f0000f0f0f0f0ee00ee0088888888ff00ff00f0f0f0f0888888881100ff88
def HC5_3_0 : Nat := 0x9425a2608dce14108ac7d0008891cfb08667a6a07eea85207ed969507c406c107722e74072981d8067cc9eb0674a1b50627ac0e05aab3ce05897b63056ca905054d2aef049b76f70478f46b03ca1ff303aeca990362564e033ec6c602f4fcdc02bd2d5c029d877d0140aef2012c6fdc00b6b078008659b200667e3f005c63af
def SC5_3_1 : Nat := 0xff00ff00eeee0000e0f0e0f088888888ff0fff00f0f08080ccccccccaaaaaaaaffffc0c0f0003f00ccccccccaaaaaaaaffff0000ff00ff00e0e0eee088888888ffff0000ff00ff00e0e2e0e288888888ffff0000ee00ff00e0e0f0f088888888ff88ff00f0f000f0ccccccccaaaaaaaaffff8880f000f000ccccccccaaaaaaaaffff0000f0f0f0f0ea00aa0088888888fff0fff0f000f000eeee000088888888f0ff0000ccccccccaaaaaaa000ff0000ff00ff00f0f00000ccccccccaaaaa8a0ff00ff00fafa0000e0e0e0e088888888ff00ff00f0f0f0f0e0ff000088888888ffff0000ff00ff00e0e0e6e688888888f0f0f0f0ccccccccaaaaaaaa00f0f0faff00ff00f0f00000c8c88888aaaaa0a0f0f0f0f0ccccccc0aaaaaaaa00fffff0ff000000f0f00000ccccccc0aaaaaaaaf0000000ccccccccaaaaaaaa0000000affff0000f0f0f0f0ee00fef088888888ffff0000f080ff80ccccccccaaaaaaaaff000000f0000000ccccccccaaaaaaa0fffffff0f0000000ccccccccaaaaaaa0ffff0000f0f0f0f0ec00ec0088888888ff00f000f0f00000ccccccccaaaaaaa0ffff00c0f000ff00ccccccccaaaaaaaaff008800f8f8f0f0ccccccccaaaaaaaaff00ff00eeee0000888888880f0f0c0cff00ff00f0f0e0e0eeee000088888888ffff0000ff11ff00e0e0f0f088888888f0f0f0f0ccccccccaaaaaaa000f0f0f0
def HC5_3_1 : Nat := 0x180997e117d8b4ca174cc0e616e7b68b167b137315b8fac015a80931157d05b71569535e148cce921449005013f2693b13a920e7139a9451130fb69612843f1e11d7861311b83a871090d7e7107b9ec9101bc8bc1003fca10ef7528b0e8376730d21edbe0cfd32340c5d4ada0b17ba6d0a3fd3a20a1787740a0a6fd6099b9694
def SC5_3_2 : Nat := 0xff00ff00eeee0000888888880f0f0e0eff00ff00f0f0f0f0efef000088888888ff00ff00f0f0f0f08888888866ee0000eeee0000e0e0e0e08888888800ee00eeffff0000ee00aa00888888880e0e0a0aff00ff00e0e0e0e0888888880000ff88ff00ff00c8c88888aaaa0000a0a0a0a0f0f0f0f0ef0f0000ee00ee0088888888ffff0000e0e0f0f08888888800ee00eeff00ff00f8f0f8f0eeee000088888888ffff0000f0f0f0f0e800e80088888888ffff0000f1f1f0f0ee00ee0088888888fefe0000f0f0f0f0ee00ee0088888888ffffee00f0f0f0f0ee00000088888888ff00ff00eeee0000888888880f0f0808f0a0a0a0ccccccccaaaa0000aa00aa00f800f800f0f0f0f0eeee000088888888ff000000ccccccccaaaaaaaa0ffffff0ffff0f00f000f000ccccccccaaaaaaa0fffffff0ccccccccaaaaaaaa0ffffff0ff00ff00f0000000ccccccc0aaaaaaaaff00ff00f0ff00c0ccccccccaaaaaaaa00000000f0000000ccccccc0aaaaaaaaffff0000f0f0f0f0ef00ee0088888888ffff0000f000f000ccccccc055555550eeee0000888888880e0e0e0e00ee00eeffff0000f080f080ee00ee0088888888ffff0000f0f010f0ee00ee0088888888ffff0000f0f0fef0ee00ee0088888888ff0f0000f0f0f0f0ccccccc0aaaaaaaafffff0f0f0000000ccccccc0aaaaaaaaf0f0f0f0ccccccccaaaaaaa000f0fff0
def HC5_3_2 : Nat := 0x31dc729a30f08056306193e42e532c212e2d005c2de504b52cb9c1222c605f2e2c5a745126b0751825fa59a325081abc227caeb421e8c7d7217c8d5321798c25212f9be6209c68742052d65a20288c5c1fbce9c01dce2b6e1dcc7f861db5531c1d3abd931ceabcbc1ccfce3f1ac9dcb51a1fa6d919f50e231947933218e7f441
def SC5_3_3 : Nat := 0xff0ffff0f0f00000ccccccccaaaaaaaaffff0000ee00ee00888888880e080e08ff00ff00f0ff00f0ccccccccaaaaaaaafccc0000f000f000ccc0ccc0aaaaaaaaffff0000f000f000ccccccc0aaaaaaa0ffff0000ff00ff00e0e0e0f088888888f0f00000ccccccccaaaaaaaa00f0000afffff0f0f0000a00ccccccccaaaaaaaaffff0000f0f0f0f0ee00ee0088888888ff00ff00f8f88888ccccc0c0aaaaaaaaffff0000e0e0e0e0888888887700ff00ff00ff00f1f1f0f0eeee000088888888f0f0f0f0eeff0000ee00ee0088888888ffff0000e800e800e0e0e0e088888888f0f0f0f0eeee0000888888887700ff00ffff0000f0f0f0f0888888886f006f00ffff0000ff0fff00e0e0e0e088888888ffff0000ff00ff00e0e0e0c088888888ff0fff00f0f0f0f0eeee000088888888ffff0000f00af00accccccccaaa0aaa0ffff0000f000f000ccccccc0aaaaaaaaffff0000ccccccccaaaaaaaa0ffffff0f00a0000ccccccccaaaaaaaa000a000af0000000ccccccccccccccc0aaaaaaaaffaaffa0f0000000ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaa2ff00ff00f0f00000ececa0a088888888ffff0000ec00ec00e0e0e0e088888888ffff0000f0f0f0f0e000ee0088888888ffff0cf0f000f000ccccccccaaaaaaaaff00ff00f0f0f0f0efff000088888888ff0cffc0f0f00000ccccccccaaaaaaaa
def HC5_3_3 : Nat := 0x67fd8144671936165ecce1bb5cce85245790b39f577849a457112822553777fc53ca5cee51ac9283517c5f674fbb0b7e4f6ff1954dd8e40f4cf2cc8b4af2bf414a83a6794a7663c245fa139d44a764ba43736e0f40d968bd40639e113cdc9a733c49c30637a9211f35037eaf3500782a340a64923326464b3306a12b31eaadf4
def SC5_3_4 : Nat := 0xfffffff0f0000000ccccccccaaaaaaaafffffff0f0000000cccccccc55555550f0000000ccccccccaaaaaaaa0ffffff0fff0fff0f8880000ccccccccaaaaaaaaeeee0000ee00ee00e0e0e0e088888888ff00ff00f0f00000eeeee0e088888888ffffff00f0f0f0f0ee00000088888888ff00ff00f8f88080ccccccccaaaaaaaaf0f0f0f0eeee0000ee00ee0088888888f0f0f0f0eaea0000ea00ea0088888888
def HC5_3_4 : Nat := 0xfa6630e3d42d8067af92350ea27f1da59efddeea80d94aa97f758adc7ca16691771f547e6bac6b68
def readS5_3 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight (if Nat.blt c 2 then (if Nat.blt c 1 then SC5_3_0 else SC5_3_1) else (if Nat.blt c 3 then SC5_3_2 else (if Nat.blt c 4 then SC5_3_3 else SC5_3_4))) (128 * o)
  unpack32 4 v
def readH5_3 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight (if Nat.blt c 2 then (if Nat.blt c 1 then HC5_3_0 else HC5_3_1) else (if Nat.blt c 3 then HC5_3_2 else (if Nat.blt c 4 then HC5_3_3 else HC5_3_4))) (32 * o)) 0xffffffff
def SC5_4_0 : Nat := 0xffff0000ff00ff00c0c0c0c0a0a0aaaa88888888ffff0000faf0faf0ccccccccaaaaaaaa0af00af0ff00ff00fcfc0000ccccccccaaaaaaaa3c3c3c3cff000000f0f0f0f0ccccccccaaaaaaaa0fff0f00ffff0000ff00ff00f0f0a0a0cc88cc88aaaaaaaaffff0000f000f000ccc0ccc0aaaaaaaa0c0c0c0cffff0000ff00ff00e0e0e0e08888888855550000ffff0000f0f0f2f2ccccccccaaaaaaaa00ff00ccffff0000ff00ff00f0c0f0c0ccccccccaa88aaaaffff0000ff00ff00ccccccccaaaaaaaa0f3f0a2affff0000fa00fa00aaaaaaaa323232320a0a0a0affff0000ff00ff00ccccccccaa8888880f0c0c0cffff00c0ff00ff00f0f000f0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccc545454540000ffaaff00ff00f0f0f0f0ccccccccaaaaaaaa73ff0000ff0f0000f0f0f0f0ccccccccaaaaaaaaaa00ff00ffdf0000ff00ff00f0f0f0f0ccccccccaaaaaaaafffffff0ffff0000f000f000aaaaaaaa33333330ff00ff00f0f0f0f0cccc0000aa00000088888888f0f0f0f0ccccccccaaaaaaaa00fc00fc0000ffccfffff0f0f0f0f0f0ccccccccaaaaaaaa00f0fff0ffff0000ff00cc00f0f0a0a0ccccccccaaaaaaaaffff0000fd00fc00f0f0f0f0ccccccccaaaaaaaaffff0000f0f3f0f2ccccccccaaaaaaaa00ff00aaffff0000ff00ff00f0f0f0f0ccccccccaa88aa80ffff0000f0f3f0f0ccccccccaaaaaaaa00ff00ccff00ff00f0f0f0f0f0f00000eeee000088888888ffff0000f000fa00ccccccccaaaaaaaa0000a0a0ffff0000fc00fc00ccccccccaaaaaaaa0f0f0c0cffcc0000ff00ff00ccccccccaaaaaaaa0f0f0a0aff00ff00f0f00000ccccccccaaaaaaaa0f0ff0f0ffff0000f000f000ccccccccaaaaaaaa0000fcf0
def HC5_4_0 : Nat := 0x10b5a4f00e9ee7200e06ea700e018f800c53cf800be1ef800b218e700ae161100ab014d00a59efb00a42ca300a1fbd400a19faa00a1872e008fe7b80082acbe007df5cd00776bd700536780004d1b4e0045c25d00437a14004365320041885c003c4498003b6f53003772ab00345ed6002edbcd00275f850011220f0001e619
def SC5_4_1 : Nat := 0xffffff00f0f0f0f0ccccccccaaaaaaaa0fffff00ffff0000ff00ff00f0f0f0f0c8c8c8ccaaaaaaaaffff0000f0f0f0f0f000f000ccccccc0aaaaaaaaffff0000ff00ff00f0f0f0f08888888866664444ffff0500ff00ff00f0f0f0f0c8ccc8ccaaaaaaaaffff0000ff00ff00e0e0a0e0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccc545454540000eeeeffff0000ff00ff00f0f0f0f0cc888c88aaaaaaaaffff0000f0f0f0f0ccdcccdcaaaaaaaa00fc00fcffff0000f700ff00f0f0f0f0ccccccccaaaaaaaafffffff0ff00ff00ccccccccaaaaaaaa0f00fff0ffff0000fc00fc00f000f0f0ccccccccaaaaaaaaffffff00ff0000ccf0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0eeeeeeee666666660000eeeef0f00000ccccccccaaaaaaaa0f00ff0000ff00f0ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0cffff0000ff00ff00ccccccccaa88aa880e0e0e0effff0000ff00ffa2f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccc5544554400fc00fcff00ff00f0f0f0f0ccccccccaaaa444444444444ff000000f0f0f0f0ccccccccaaaaaaaa0000a0aafa00fa00f0f0f0f0aaaaaaaa323232320000fafaffff0000ff00ff00f000f0f0cccccccca8a8a8a8ffff0000f00af00accccccccaaaaaaaa00aa00aaffff0000f0f0f0f0ccccccccaaaaaaaa04ee04eeffff0000ff00ff00f0f0a0a0c8c8c8c8aaaaaaaaffff0000fc00cc00ccccccccaaaaaaaa0c0c0c0cffff0000f000f000ccccccccaaaaaaaa000c000cffff0000ff00cc00f0f0f0f0aaaa888833330000ff000f00f0f0f0f0ccccccccaaaaaaaa0000a0aaffff0000ff00ff00f0f0fff0eeeeeeee88888888ffff0000ff00ff00ccccccccaaaaaaaa0f0f00f0
def HC5_4_1 : Nat := 0x1c67a5701c33ab001b8a7ac01b5123201ae3be901a7361c0199b8ca018c414e0183f5ed01761cbe016f968a016ddfa7016b0f48016850ca016582740162de320158d3270156ee3c014be6ce0149fde00149e8e2013f787e013ea62f01378e3501356fdc011ec1ee011c7367011ad6910119669a0116c1600114552b010d9c5a
def SC5_4_2 : Nat := 0xff00ff00f0f0f0f0f0f00a0accccccccaaaaaaaaffff0000f800f800c0c0c0c0aaaaaaaa88888888ffffff00f0f000f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00e0e0e0e0e000e00088888888ffff0000f0c0f0c0ccccccccaaaaaaaa00ea00eaffff0a00ff000a00f0f0f0f0ccccccccaaaaaaaaffff0302ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f000f0f0ccccccccaaaaaaaa00000f00fff0fff0ff000000f0fff0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccccaa00aaaaaaaaaaffff0000ff00ff00f0f0f0f0cccc00ccaaaa88aaffff0000fa00ea00f0f0c0c0ccccccccaaaaaaaaffff0000ff000f00f0c0c0c0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccc5555545400ff00fcffff0000fff0fff0f000c000ccccccccaaaaaaaaffff0000fc00fc00f3f0f3f0ccccccccaaaaaaaaffce0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff00aaffff0000f000f0f0ccccccccaaaaaaaaffff0004ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccccccca0a0aaaaaaaaff00ff00fefe0000e0e0e0e0ccccccccaaaaaaaaffff0000f0f0f0f0ee00aa00aaaaaaaa22222222ff00ff00ccccccccaaaaaaaa0f0c0f0c0000fafaffff0000fff0fff0f00f0000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaa888833333300ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaaffff0000fa00fa00f0f0f0f0cccccccca0aaa0aaffff0000ff00ff00f3f0f3f0cccccccca8a8a8a8ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fcf8ffff0000ff88ff88f0f0f0f0ee00ee0088888888ffff0000f303ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0c0ccccccccaaaaaa88
def HC5_4_2 : Nat := 0x2f8dfa702f57b4702d7b21c02d21ded02cefe1d02cc8a0102b1da0c02a33ebd028beb3902634e4c025e606b0257713b0248953d02382575022ad2eb021517c3021419a2020d9c74020bd7b401fd626f01fc77ad01fc277b01fb73a101fb661601f9b31e01f5806101e6327901e5de4b01e1a3ed01dab5ae01d770aa01d06f05
def SC5_4_3 : Nat := 0xffff0c00f0f0f0f0f000f000ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f040cfafa0000f0f0f0f0ccccccccaaaaaaaa00fe00feffff0044ff00ff00f0f4f0f4ccccccccaaaaaaaaff00ff00f0f000f0cccccccccccc4444aaaaaaaaffff0000ff00ff00ccccccccaaaaaa880f0f0f0cffff0000fa00fa00ccccccccaaaaaaaa0f0c0f0cf0f0f0f0ccccccccaaaaaaaa00f0f0f0000000ccff00ff00f0fff000ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0ccc0ccc0a8a8a8a8ffff0000ff00ff00ccccccccaa88aa880f0f0a0affff0000ff00fa00f0f0f0f0ccccccccaaaaaaaaffff0000ff0fff00f0f0f0f0cccccccc54545454ff00ff00fafa0202f0f0f0f0ccccccccaaaaaaaaffff0000f080f080ccccccccaaaaaaaa00880088ff55ff00ff0f0000f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccccccc2222aaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f00afa0ffffff00ff000000f0f0c0c0ccccccccaaaaaaaaffff0000f0f0f0f0cccc8888aaaaaaaa00ff00aaff00ff00fefe0000f0f0f0f0aaaaaaaa32323232ffff0000ff88ff00ccccccccaaaaaaaa7070f0f0ffff0050ff00ff00f0f0f0f0cc88cc88aaaaaaaaffff0000ff00ff00f0e0f0e0ccccccccaaaaaaaaffff0000ff000000ccccccccaaaaaaaa0f0f000cffff0000ff00ff00f0f0f0f0eeee444488888888ff000f00f0f0f0f0ccccccccaaaaaaaa4444ccccffff0000f0f2f0f2ccccccccaaaaaaaa00ee00eeff00ff00f0f0f0f0cc888888aaaaaaaa0000aaaaff00ff00eeee0000ccccccccaaaaaaaa0e0e0a0aff0f0000f0f0f0f0cc0ccc0caaaaaaaa00cc00ccff00ff00f0f0fff0ccccccccaaaaaaaa0000fffc
def HC5_4_3 : Nat := 0x3f8eb5103d96e2403d8f0d703c7127203c18d3f03c0586103b9f0c803a2547d03a2293403a146f503a0784f039bb4c8038ebdb4038c9a210382ee4203805e00037ea248037b76a003794cbe037550a2036a7fa103662a5703651e1d035e5851034379740322baa4032046c103184d8f03109b4303094bcf030711d402fff07f
def SC5_4_4 : Nat := 0xfffffff0ffff0000f000ff00ccccccccaaaaaaaaff04ff04fbfb0000f0f0f0f0ccccccccaaaaaaaaff0f0000ff00ff00f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0fff2ccccccccaaaaaaaaff00ff00fafa0000f0f0f0f0cccccccca8a8a8a8ffff0000ff00ff00c8c8c8c8aaaaaaaaa0a0f0f0ffff0000fb00aa00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f000f0c8c888c8aaaaaaaaff00ff00fafa0000f0f0f0f0cccccccc5a5a5a5affff0000ff00ff00fcccccccc0c0c0c0aaaaaaaaffff0000f000f000ccc0ccc0aaaaaaaa33330000ffffff00ff888888f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ee00ee008888888877770000ff00ff00fcfc0000f0f0f0f0cccccccc55555454ffff0000fff0ffc0f000f000ccccccccaaaaaaaaffff0100ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0f00f000f000ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaabbaa88ffff0000f0f0f0f0cc88cc88aaaaaaaa00ff00ccffff0000ff00ff00aaaaaaaa33cc33cc0f0c0f0cffff0000ff00ff00f0f0f0f0aaaaaaaa33333232ffcc0000ff00ff00f0f0f0f0cccccccc55554444ffff0000fff0fff0ccccccccaaaaaaaa70007000ff00ff00f0f0f0f0888888885555000033ff0000ffff0000ff00ff00f0f0f0f0cccccccc55557474ff00ff00fcfc0000f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0c8c8c8c8a2a2a2a2ff00ff00e0e0c0c0cccccccccccc0000aaaaaaaaffff8800ff00ff00f8f0f8f0ccccccccaaaaaaaaff0fff00f0f0f0f0ccccccccaaaaaaaa0f0ff0f0ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aabaaaba32323232
def HC5_4_4 : Nat := 0x515059d050d85650501dd1004fae93b04df5cbe04d90b7004cd637a04cbe08d04c6b16804bc3c7304b1d7d404aaa0e704a0ba8c049fd92b049ad5b20499f47a04980df004858e550484bb0404839074046a9ddf0467e4fd044938a604349cec0432623b042d65d904269e5d0424db00041d8a1c0418fc9e040da2490408f5b3
def SC5_4_5 : Nat := 0xffff0000f1f0f1f0ccccccccaaaaaaaa00ee00eeff00ff00f0f0d0d0ccccccccaaaaaaaa0000ccccffff0000ff00cc00f0f0fcf0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f3c0f3cffff0000f0f0f0f0cc00cc00aa00aa0088888888f0f0f0f0f0f00000ccccccccaaaaaaaa00f000ccffff0000ff00ff00f0f0f0f0ccccccccaaa8a8a8ff0f0000f0f0f0f0ccccccccaaaaaaaa00cf00ccffff0ff0f000f000ccccccccaaaaaaaa0ff00ff0ffff0f00f0f0f0f0f0000000ccccccccaaaaaaaaff000000f0f0f0f0cc00ccccaaaaaaaa00cc00ccffff0000ccccccccaaaaaaaa0fff0f000a0a0a0affff0000f000f000cfc0cfc0ccccccccaaaaaaaaff00ff00ccccccccaaaaaaaa0f0c0f0c0000ffccffff0000f0f0f0f0ccccccccaaaaaaaa00ff00feffcf0000f0f0f0f0cccccccccc00cc00aaaaaaaaffff0000ff00ff00ccddccccaaaaaaaa0f0a0f0affff0000ff0ffff0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaa888833332222f0f0f0f0ccccccccaaaaaaaa00ee00ee0000fcfcffff0000f0f2f0f2ccccccccaaaaaaaa00fa00faffee0000ff00ff00f0f0f0f0ccccccccaa88aa88ffff0000f0f0f0f0ee00cc00aaaaaaaa22222222ffff0000fff0fff0f000f000ccccccc0aaaaaaaaffff0000ff00ff00f0f5f0f0aaaaaaaa33223322ffffff00ff0aff0af0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa37223722ff00aa00f0f0f0f0ccccccccbbbb0000aaaaaaaafff0fff0f0000000ccccccccaaaaaaaa00ff0000fe00fe00f0f0f0f0ccccccccaaaaaaaa0000fafaffaa0000f0f0f0f0f000ff00ccccccccaaaaaaaaffff0000ff00ffc0f0f0fcfcccccccccaaaaaaaa
def HC5_4_5 : Nat := 0x654e09a064d2a7a064c8344064249b4063a1dd2061d18d6061a0b140618432b06021f8605fc252d05f2dc7005e6342405e0263e05dc279c05d8658e05cf444f05b76a2805b0df35058b0e4305899d7205808d1b057f365105643b600558d7ee05436293053d1df205383bb305336e3a05316f1a05316b66053066a9051539e2
def SC5_4_6 : Nat := 0xffff0000fd00fd00f0f0f0f0aaaaaaaa32323232ff000000ccccccccccc0ccc0aaaaaaaa0f0f0000ff00ff00f0f000f0ccccccccaaaaaaaa0f0ff000ffff0000ff02ff02f0f0f0f0cccccccca8a8a8a8ffff0000ff00ff00f0f0f0f0cc88cc88aaeeaaeeff00ff00f0f0f0f0eeff0000ccccccccaaaaaaaaff00ff00ccccccccaaaaaaaa0f000f0a0000f0f0ffff0000f0f0f0f0cc8ccc8caf00af00aaaaaaaaffff0000ff00ff00f0c0f0c0aaaaaaaa33223322ffff0f00ff00ffaaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00cccccccc554455440f0c0f0cffff0000ff00ff00f0f0f0f0cccccccc66666666ff00ff00f0f0f0f0e0e0e0e0888888880000eeeeffffcc00ff00ff00f0f000f0ccccccccaaaaaaaaff3f0000f0f0f0f0ccccccccaaaaaaaa00aa00aaffff0500ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00c0c0c0c0a0a0f0f088888888ffff1010ff00ff00e0e0e0e0ccccccccaaaaaaaaffff0000faaafaaaf000f000ccccccccaaa0aaa0f0f0f0f0ccccccccaaaaaaaa0f00fff000ff0000ffff0000ff00ff00f0f0c0f0ccccccccaaaa88aaff00ff00fcfc1010f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00e0c0f0c0ccccccccaaaaaaaafa00fa00f0f0f0f0ccccccccaaaaaaaa0000fffaff00ff00fcfc0000f0f0f0f0ccccccccaaaaa8a800000000ffffff00f00000f0ccccccccaaaaaaaa00000000f0f0f0f0eeee00008888888800ee00eeff00ff00f0ff0000ccccccccc0ccc0c0aaaaaaaaff00ff00f5ff0000f0fff0f0ccccccccaaaaaaaaffff00c0f0f0f0f0ccccccccaaaaaaaa00ff00ccffff0000ff00ff00f0f0f0f0efefaaaa88888888ffff0000ff00ff00f0f0f0f0c8ccc8ccaaaaaaaa
def HC5_4_6 : Nat := 0x722d7a407203a6f071ef95b071c28ad0713177a0711302207048ec406fe9aef06ec2eed06e6288c06daf31c06daefac06d3db2c06ce712c06c4f7fd06c1fa3f06b986a006b7e05d06ab037d06aa3a4506974f7406966e74068dffb40689c59706874f51067cc9eb0674a1b5066e33ad066c83f1065f358a065e5dca0657dd25
def SC5_4_7 : Nat := 0xffff8800ff88ff88f0f0f0f0ccccccccaaaaaaaaff000000f0f0f0f0cccccc00aaaaaaaa88888888ff000000f0fff0f0ccccccccaaaaaaaa00aa00aaf0f0f0f0ccccccccaaaaaaaa00fa00fa0000fcfc00000000ff0f0000f0f0fff0ccccccccaaaaaaaaffff0000f0f0f0f0cc88ccccaaaaaaaa00ff00aaff000000ccccccccaaaaaaaa0f000f0000fff0f0ff00ff00f0f0f0f0eeee00008888888800ff0000ffff0000ff00ff00f0f3f0f2aaaaaaaa33332222ffff0000ff00ff00f0f0d0d0ccccccccaaaa8888ff00ff00f0f00000ccccccccaaaaaaaa00ff00f0ffff0000ff00ff00f8f8f8f0ccccccccaaaaaaaaffff0000ff00ff00e0e0e0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa8a8a8affff00f0ff00ff00f0f000f0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa0f0f0a0a00ff00faffff0000f0f0f0f0ee00ee00888888880000f0f0ffff0000ff00ff00f0f0c080ccccccccaaaaaaaaffff0000ff00ff00eeee0000e0e0e0e088888888fffff0f0ff00ff00f0f01010ccccccccaaaaaaaaffff0000f0f0f0f0ccccccc0aaaaaaaa00ff00f0ffffccc0ff00ff00f0f00000ccccccccaaaaaaaaff00ff00f0f00000ccccccccaaaa0000aaa0aaa0ff00ff00f0000000ccccccccaaaaaaaaaaaaa0a0ffff0000fff0fff0f000f000cccccccca888a888ffc0ffc0ff3f0000f0f0f0f0ccccccccaaaaaaaafffff0f0ff00ff00f0f000c0ccccccccaaaaaaaaffff0000f1fff0f0ee00ee00ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaa888800ee00ccff00ff00ccccccccaaaaaaaa0e0e0e0e0000fafaffff0000ff00ff00f0f0f0f0cccccccc55555450ffff0000ff00ff00f0f0f0f0cccc0000a8a88888
def HC5_4_7 : Nat := 0x80a513a07ffe48b07f51a0b07f1dcfe07ed969507ebb75e07e9421407da8ef607da1e4f07d804d707d3803b07c4156307bb8eff07bb182b07b9ff260798007c078d142c078bf9240784216b077e3a4007742f83077287fe076f7de1076a903c076a26360767c62407539d14074c4c7c07482bea07461d400741418a072759b4
def SC5_4_8 : Nat := 0xff00ff00fcfd0000ccccccccaaaaaaaa0f0a0f0aff0faa00ff0f0000f0f0f0f0ccccccccaaaaaaaaffff0000f500ff00ccccccccaaaaaaaa5050f0f0ffff0000ff00ff00f0808080ccccccccaaaaaaaafffffff0ff00fff0f0f00000ccccccccaaaaaaaaff00ff00ccccccccaaaa88880f0f0c0c0000ccccffff0000ff00cc00f0c0c0c0ccccccccaaaaaaaaffff0000ff00ff00f0f050f0ccccccccaaaaaaaaffff8888ff00ff00f0fff0f0ccccccccaaaaaaaaffffcc00ff00ff00f0f0a0a0ccccccccaaaaaaaafffc0000ff00ff00f0f0f0f0cccccccc55445544ffff0000ff00ff00ccccccccaaaaaaaa0eff0e0efff0fff0f0ff0000f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc55aa55aaffff0000ff00ffc0ccccccccaaaaaaaa0f000f00ffff0f00f0f0f0f0ccccccccaaaaaaaa00f00000ff00ff00f0f0f0f0ccccccccaaaa88883333ccccffff0000ff00ff00f0f0f0f0cdcd8888aaaaaaaaffff0000f000f000ccccccccaff0aff0aaaaaaaaffffff00ff00ff00f00000f0ccccccccaaaaaaaaff000000f0f0f0f0ccccccccaaaaaaaaaa0aaa00ff00ff00f0f0f0f0eeee00008888888800ee00eeffff0000ff00ff00f0f0f0f09999888811110000ffff0000f000ff00ccccccccccccc0c0aaaaaaaaffff0000ff00ff00f0f0f7f0ccccccccaaaaaaaaffff0000fff4fff4f000f000ccccccccaaaaaaaafcfc0000fc00fc00f0f0f0f0aaaaaaaa30303030ffff0000ff00ff00ccccccccaaaaaaaa0e0e000effff0000ff00aa00f0f0f0f0cccc88ccaaaaaaaaffff1010ff00ff00f0f0f0f0aaaaaaaa32323232ffff0000ffa0ffa0f0c0f0c0ccccccccaaaaaaaaff0f0000f0f0fff0ccccccccaaaaaaaa00f000f0
def HC5_4_8 : Nat := 0x8fed42f08fe4d1208f9fe3c08f45ec108f3ac1408e8341e08e452b408df82f908d9766508cc890008a7ded5089ba7680894f8f90891441a088ccc89087c21ed0878cc8d0875d8aa08741f5e086d34250865369a08650bef085ef1e4085053b7084d90a3084b486d0847f48608402cd108379d400825e8510812c5ab080c020b
def SC5_4_9 : Nat := 0xffff0000ff00ff00cccc8888aaaaaaaa0f0f0f0affff0000fff0fff0f000f000cccccccca8a8a8a8fff0fff0ccccccccaaaaaaaa0f00fff000ff0000ffa0ffa0ff000000ccccccccaaaaaaaa0f0f0000ffff0000f0f0f0f0cc88cc88aaaaaaaa00ff00aaff00ff00f0ff0000f0f0f0f0ccccccccabaaabaaffff0000f0f0f0f0ee00aa00ccccccccaaaaaaaaffff0000ff00ee22f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000fbaaffff0000f0f0f0f0ccccccccaaaaaaaa00ff00ecffff0000ff00ff00f0f0f0f0cc88888855550000ff00ff00fcfcc0c0f0f00000ccccccccaaaaaaaaff0f0000ff00ff00f0f0fff0ccccccccaaaaaaaaffff00f0ff00ff00f0f0a0a0ccccccccaaaaaaaaff00ff00f0fc0000ccccccccaaaaaaaa0c0c0c0cffff0000fc00ff00f0f0f0f0ccccccccababaaaaff00ff00f0f0f0f0ccccccccaaaa44440000ccccffff0000ff00ff00ccccccccaaaaaaaa0e0f0e0eff00ff00f0ff0000ccccccccaaaaaaaa00c000c0ff00ff00f5fff0f0f0f00000ccccccccaaaaaaaaffff0000f0f0c0c0ccccccccaaaaaaaa00fa00eaffff0000f0faf0faf000f0f0ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaaa8a0a8a0ff00ff00f0f0f0f0ccccccccaaaaaaaa00ffff00ffff0000f0d0f0d0dd00dd00ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000feeeffff0000f0f0f0f0ccccccccaaaaaaaa7f000f00ff00ff00efef0000e0e0e0e0ccccccccaaaaaaaaff00ff00f0f0f0f0eefe0000ccccccccaaaaaaaaff00ff00fcfc0000f0f0fff0ccccccccaaaaaaaaffaa0000ff50ff50f0f0f0f0ccccccccaaaaaaaaffff0000fa00fa00ccccccccaaaaaaaa0e0e0e0e
def HC5_4_9 : Nat := 0xa72c95d0a4c9d450a4a6a870a4969160a35396e0a29e0550a278cf30a19d1b20a07e0af0a04245109f7d40009ed846709de00cf09b816fa09b62e0e09aeade9099b86510995dada0992b02709893a1409860fc90983e5ca09813afb09800ad2096495e309395aef09239d9d0912501d090df09c090989980908aed809049a67
def SC5_4_10 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaafffffff0ff00ff00ccccccccaaaaaaaa0f0ffff0ffff0000ff00ff00ccccccccaaaaaaaa0f00ffc0ffff0000fff00ff0f000f000ccccccccaaaaaaaaffaa0000f0f0f0f0aaaaaaaaaa00aa0033223322ffff0000ff00ff00f0f0f0f0aaaaaaaa33322222ffff0000ff00ff50f0f0a0a0ccccccccaaaaaaaaffcf0000ff00ff00f0f0f0f0ccccccccaa88aa88ffff0000ccccccccaaaaaaaa5a5a5a5a00fa00faffff0000fc00ff00ccccccccaaaaaaaa0c0c0c0cfafa0000ccccccccaaaaaaaa0a0a0a0a00fa00faffff0f00ff00ff00f0f0f0f0ccccccccabaaabaaff00ff00eeee0000cccccccc444444440e0e0e0effff0000ff00ff00f0fff0f0ccccccccaa88aaaaffccff44ff000000f0f0f0f0ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaa0ff0fff0ff000000f0f0f0f0eeaacc00ccccccccaaaaaaaaff00fc00fcfc0000f0f0f0f0ccccccccaaaaaaaafff0fff0f0000000ccccccccaaaaaaaaaaaa0000ffff0000ff008a00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccc8c8aaaaaaaa0000fafaff00ff00fafaf0f0f0f00000ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa33ffcc00ffff0000ff000f00f0f0f0f0aaaaaaaa33332222ff00ff00f0f0f0f0ccccccccaaaa88880000eeeeff00ff00f000f0f0ccccccccaaaaaaaa0000fcfcffff0000f0f0f0f0c8c8c8c8aaaaaaaa00ff00aaff00ff00f0ff0000ccccccccaaaaaaaa0c0c0c0cffff0000ff00ff00f0f2f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0efef0000aaaaaaaa32323232ffff0000f0f0f0f0ee00ee00888888880000ee00ffff0000f0f0f0f0ccccccccaaaaaaaa00ff00ae
def HC5_4_10 : Nat := 0xb6b9b7b0b68c79c0b6781550b5c7c1d0b5904f00b4de4350b4ab0530b3e65660b3c5e690b393bc20b368a4a0b313ccb0b2777b20b19316b0b1239620b0ee9e00aeb8bb10ad37c150accfef50ac6fa560ac473f10ac2ae2f0abf66f90ab04f060a95d3050a93d3390a8ebe640a83259c0a80f50b0a8058110a7a5a400a78bac1
def SC5_4_11 : Nat := 0xffff8080ff00ff00f0f0f0f0eeeeeeee88888888ffffff00f000f0f0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f09999888855550000ffff0000ff00aa00ccccccccaaaaaaaa0e0e0e0effffff00ff000f00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0aaaa0000888888883030f0f0ffff0000ff00ff00f000f080ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0fcc0cffff0000ff0fff00f0f0f0f0ccccccccaaaa8888ffff0000fa00fa00f0f0f0f0ccccc8c8aaaaaaaaff00ff00f0f0f0f0cccc0000aaaa888822220000ffff0000fffcfff0f000f000ccccccccaaaaaaaaffff0000ff00ff00c4c4c4c4a0a0a0a00c0c0c0cffff0000ff00ff00cccccc88aaaaaaaa0f0a0f0affff0f00f000f000ccccccccaaaaaaaa00f000f0f0f0f0f0ef000f00eeee0000ccccccccaaaaaaaaff00ff00f0f01010ccccccccaaaaaaaa00000e0effff0000ff00ff00d0d0d0d08888888830303030ffff0000f000ff00cfcfc0c0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccc5555545400ff00ccff00ff00fcfc0000c0c0c0c0aaaaaaaa88888888ff00ff00f0f0f0f0ccccccccaaaaaaaa7fff0000ffff00fcf0f0f0f0ccccccccaaaaaaaa00f000fcff00ff00f0f0f0f0eeaaeeaa888888880000eeaaffff0000fa00ea00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0fff0aaaaaaaa33223322ffff0000ff10ff10f0f0f0f08888888810101010ffbbff00ff000000f0f0f0f0ccccccccaaaaaaaaff00ff00f0f00000ccccccccaaaaaaaa000f00f0ffff0000f0f0f0f0f000f0fcccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000cccccccc88aa88aaffff0000f0f0f0f0ea00ea00aaaaaaaa88888888
def HC5_4_11 : Nat := 0xce7e8870cc85fdc0cc1537e0cbd6bbb0cbc40560ca8ebf80c9c52460c8c838d0c8ad7ef0c82f1180c72f2da0c6d94e90c64e5800c60f7dd0c53fc400c46d0100c418e630c248ef60c0e2dcc0c0c16f50c0ad72b0bf7b9030bf2c45e0be5c6600bcd8c550bc852ac0bc014580bb4ba4a0badba510ba276a80b8a900e0b6f3de3
def SC5_4_12 : Nat := 0xf0f0f0f0ec00ec00ccccccccaaaaaaaa0000ececff00ff00f0f0f0f0eeee0000ccccccccaa88aa88ffff0000ff0055aaf0f0f0f0ccccccccaaaaaaaaffff0000ff10ff10f0f0f0f0eeeeeeee88888888ffff0000f000f0f0cc00cc00aaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccccccabababaaff00ff00f0f0f0f0cccc0000aaaa888888888888ffff0000ff00ff00f0f0f2f2aaaaaaaa33332222ff00ff00f0f0f0f0efef0000dcdcdcdcaaaaaaaaffff0000ff00ff00f0f0f0f0ececcccc88888888ffff5f00ff00ff00f0f0a0a0ccccccccaaaaaaaaffffff00f0f000f0f000f000ccccccccaaaaaaaaffff0000ff000b00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccc555544440000fafaffff0000f000f000ccccccccaaaaaaaa004c004cffff0000f0f0f0f0ee88ee88ee00ee0088888888ffff0000f0f0c0c0ccccccccaaaaaaaa00fc00fcff0aff00ff000000f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000aaaa000088888888ffff0000ff00aa00ccccccccaaaaaaaa0f0a0a0affff0000ff00ff00f0f0c0c0cccccccca8a88888ffff0000f000f0f0ccccccccaaaaaaaa0c000c00ffff0000fc000c00ccccccccaaaaaaaa0c0c0c0cf0f0f0f0f000f000ccccccccaaaaaaaa0f0fff00ffff0000ffccff00f0f0f0f0cc88cc88aaaaaaaaffff0000f000fff0f000f0f0ccccccccaaaaaaaa00000000ffff0000f0f0f0f0ec00ec0088888888ffff0022ff00ff00f0f0f0f0ccccccccaaaaaaaafffff0f0ff00ff00f0f00000eeeeeeee88888888ffff0000ff00ff00f0f0a0a0cccccccc55555500ffff0000fe00ff00f0f0f0f0ccccccccaaaaaaaaffffff00ff000000f0f0f0f0ccccccccaaaaaaaa
def HC5_4_12 : Nat := 0xe41544a0e37afb00e2082260e1fda840e190dd90e1017b60df871340df72a6e0de2fe360de145230ddaf3990dda2bb00dd592840dce47e00da67ef90d92b2600d91e57b0d7ad9cc0d761ed10d6b6bca0d68ff130d5533ea0d37e9b80d34438c0d3440930d2917670d21edbe0d1c14f30d05c6e30cff748a0cff0e580cef67d8
def SC5_4_13 : Nat := 0xfff00000ff00ff00f0f0f0f0ccccccccaaaaaaa0ff0f0000ff00ff00f0fff0f0ccccccccaaaaaaaaff00ff00f0f0f0f0eeee00008888888844444444ff00ee00f0f0f0f0ccccccccaaaaaaaa0000eeeeffcc0000ff00ff00e0e0e0e0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccccccc0000aa888888ffff0000ff88ff00f0f0f0f0cc88cc88aaaaaaaaffaa0000ff00ff00f050f0f0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccccc00cc00aa8aaa8affff8080ff00ff00f0f08080ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ec00ec0088888888ffff0000f0f0f0f0ccccccccaaaaaaaa00fcf0fcff00ff00fafa0000cccccccca0a0a0a00a0a0a0affff00f0ff00ff00f0faf0faccccccccaaaaaaaaffff0000ff00aa00ccccccccaaaaaaaa0f0f0a0affff0000f0f0f0f0ccccccccaaaaaaaa00fffff0fff0fff0ff000000f0f0f0f0ccccccc0aaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa33323232ffff0000ff00ff00f8fff0f0ccccccccaaaaaaaaffff0000f000ff00ccccccccaaaaaaaaaaaa0a0affff00f0ff00ff00f0ff00f0ccccccccaaaaaaaaff00ff00f0f0f0f0eaff0000ccccccccaaaaaaaaff000f00f0f0f0f0ccccccccaaaaaaaa0000ffaaff00ff00f0f00000ccccccccaaaaaaaa0000ff0cffff0000ff00ff00f1fff0f0ccccccccaaaaaaaaffff0000f000ff00ccccccccaaaaaaaa0f0f0c0cffff0000ff00ff00ccccdcdcaaaaaaaa0f0f0a0affff0000ff00ff00f0f0f0f0cccc8888aaaa0000ffff0000f0f0f0f0ee00ee008888888800cc00ccffff0000fd00fd00f0f0f0f0cccccccc54545454ffcc0000f0c0f0c0cccccccccc00cc00aaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa1010fcfc
def HC5_4_13 : Nat := 0xf808da00f700d2e0f6baab80f5170a50f4829c20f437da70f3f38210f331abe0f2fd5910f2e0f8b0f1257f80f116ea80f0854470f059e420f0510e30f02c8450f0156680efd4eee0ef840510ef1ddf50ecd3cb10ec761680ec2e22c0ebbe2950eaa45ae0ea5583e0ea27f400e8c280d0e7e64df0e7ca1900e6bbb280e6ae9a1
def SC5_4_14 : Nat := 0xffff0000f0c0f0c0ccccccccaaaaaaaa00ff00aaffcc0000f0f0f0f0cf00cf00ccccccccaaaaaaaaffff0000f0c0f0c0ccccccccaaaaaaaa00cc00ccffff0000ff00ff00eeeeeeee888888880f0a0f0aff00ff00f0f0f0f0cccccccca8a8aaaa0000fcfcffff0000f0f0f0f0ee00ee00ccccccccbabababaff3f0000f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000f0f0f0f0ccccccccaaaaaaaa33cc33ccffff1100ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0fff0ccccccccaaaaaaaa00ff00ccffff0000ff00ffe0f0f0f0f0ccccccccaaaaaaaaffff0000fc00fc00ccccccccc0f0c0f0aaaaaaaaffff0000ff00ff00e0e0e0e08888888870707070fffff000ff000f00f0f0f0f0ccccccccaaaaaaaaff008800f0f0f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f4f0f4aaaaaaaa33223322ff00ff00f0f0f0f0eeee0000888888880c0c0c0cff00cfccff000f00f0f0f0f0ccccccccaaaaaaaaff00fff0f0fff0f0ccccccccaaaaaaaa0000f0f0ffff0000f0f0f0f0cc88cc88aa00aa0000cc00ccff000000f0f0f0f0ccccccccaaaaaaaa55ffff00fffffff0fff00000f000f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cc22cc22aaaaaaaaffff0000f000ff00f000f0f0ccccccccaaaaaaaaffff0000ff000f00f0f0f0f0cccc8c8caaaaaaaaffff0000fd00fd00c0c0c0c0aaaaaaaa22222222ffff0000ff00ff00f0f0f0f0eee0eee088888888ff000f00f0f0f0f0ccccccccaaaaaaaa0000eeeeffff0000fb00fb00f4f4f4f4ccccccccaaaaaaaaff00ff00f0f0f0f0ecec0000aaaaaaaa88888888ffff0000ffccffccf0f0f0f0ee00ee0088888888ffff0000fa00fa00f0f0f0f0cccccccc55554444
def HC5_4_14 : Nat := 0x114a220d112cfcf911295976109f950b109e1905108da39910802b701077cfbf107796a61075c762106edb3a1067b08e1060d1f21054c6a01054c1e61043c4fd10418f981034ccf310325b681020a993100b913b1004cc010ffdf63a0fe45c180fca48d90fc823550fc243360fbb13c80fbb05d50f941d290f924a7d0f8cc507
def SC5_4_15 : Nat := 0xffff0000f0f0f0f0ccccccccaaaaaaaa00fa00eaff000f00f0f0f0f0ccccccccaaaaaaaa00000a0aff00ff00ccccccccaaaaaaaa0e0a0e0a0000eeaaff000000fcfcfcf0f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0f000f000eeee000088888888ff00ff00f0ff0000ccccccccaaaaaaaa00ff00f0ff00ff00f0f0f0f0eeee00008888888844440000ffff0000fa000a00f0f0f0f0ccccccccaaaaaaaaff0f0000ff00fff0f0f0f0f0ccccccccaaaaaaaaffff0ff0f0f0f0f0ccccccccaaaaaaaa00f000f0fffff0f0f0f00000ccccccccaaaaaaaa00ff00fcff0f0000f0f0f0f0ccccccccaaaaaaaa00f0fff0ff880000ff00ff00f0f0f0f0eeeeeeee88888888f0f0f0f0ccccccccaaaaaaaa00ff00cc0000f0fcffff0000ff00ff00ccccccccaaaaaaaa0f0fff0afffffff0ff00ff00f0f00000ccccccc0aaaaaaaaffff0000ff00ff00e0e0e0e0aaaa000088888888ff0f0000ff05ff00f0f0f0f0ccccccccaaaaaaaaff00fff0fcfc0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa33223320ffff0000f0c0f0c0cccccccccc00cc00aa88aa88ffff0000ff00ff00f0f0fff0c8c8ccc8aaaaaaaaffff0000ff00ff00f0f0f0f0eac0eac088888888ffff0f00ff00ff00f0f0f0f0cccccccc55555550ffff0000f000ff00ccccccccaaaaaaaa00f0f0f0ffff0000ff00ff00f0f0f0f08888888810105050ffff0000ff00ff00f0faf0f0ccccccccaaaaaaaaffff0000ff000a00f0f0f0f0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa0e0e0e0e00ff00eeffff0000f000f000ccccccccaaaaaaaa0000ccc0ff0f0000f0f0f0f0ccccccccaaaaaaaa00f000fcfafa0000fa00fa00f0f0f0f0cccccccca0a0a0a0
def HC5_4_15 : Nat := 0x12fc2ae312f7edc212f6b52a12e53d0d12dd088a12da266512d562cb12cd450f12cbbe68129e4a9d1293479a128f19511264d367125a9a7c1245b080120d660911ffb1ad11fefb1b11f7473111f6b9a211e4d3f211d9fa2811d5375511d2c94b11c901c111c04a9411b37b4611aea13f117cc6891173e7ca1163efa511621d49
def SC5_4_16 : Nat := 0xff00ff00f0f0f0f0eeee00008888888833330000ffff0000ff00ff00f0f0f0f0aa88aa8832323232f0f0f0f0cccccccccccc0000aaaaaaaa00f0fff0ffff0000ff00ff00f0f0f0f0aa88aa8833003300ffff0000ff00cf00ccccccccaaaaaaaa0f0f0c0cffaa0500ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa7700ff007070f0f0ffff0000ff00ff00ccccccccaaaaaaaa0fff00f0ffff0000f0000f00ccccccccaaaaaaaa0000f0f0ffcc0000ff00ff00f0c0f0c0ccccccccaa88aa88ffff0000ff00ff00e0f0e0f0cccccccc88888888ffff0000ccccccccaaaaaaaa0f0f0a0a00ff00eeff000000f0f0f0f0ccccccccaaaaaaaa00ffcc00fff0fff0f000f000ccccccccaaaaaaaa0000fcfcffff0000ff00ff00f0f0f5f0ccccddccaaaaaaaaffff0000ff00cc00f0f0d0d0ccccccccaaaaaaaaff00ff00fcfc0000f0f0f0f0cccccccc55545554ffff00f0f000ff00ccccccccaaaaaaaa00f000f0ff00ff00e0e0e0e0aaaaaaaa888888880000eeeeff00ff00f0f0f0f0f0f00000c8c88888aaaa0000ffff0000f0f0f0f0ccccccccaaaaaaaa05ff00aaffff0000f0f000f0ccccccccaaaaaaaa00f0fff0ffaa0000ff00ff00f0a0f0a0ccccccccaaaaaaaaffff0000ff00ff00f0f3a0a2ccccccccaaaaaaaaffbb0000ff00ff00ccccccccaaaaaaaa0f0a0f0affff0000ff00ff00ccccccccaaaaaaaa0f0d0f0cff00ff00f0f0f0f0cccccccca8a8a8a80000f8f8ff000f00f0f0f0f0cccc0000aaaaaaaa88888888ff00ff00f0f0f0f0ccccccccaaaaaaaa4444aaaaffff0000ff80ff80f0f0f0f0ccccccccaaaaaaaaf0f00000f0000f00ccccccccaaaaaaaa0f0ff0f0ffff0000ff00ff00ccccccccaaaaaaaaa5f0a5f0
def HC5_4_16 : Nat := 0x14354874142f4a8014230925141f0cf314182df7140c0bc513ed443113dfb0a913dc972d13dadc3f13c4bb3e13c46bb113b14fc613a1ca4f139e0ec4139903111395ae0d139415cc138c34f7138a2ec413844a5413694a0413684015135f3cc21357854a13508c8a133a07e2131db1f71315eed1130e83311304a02012ff7891
def SC5_4_17 : Nat := 0xffff0000f0f000f0ccccccccaaaaaaaa00ffff00fffcfff0ff000000f0f0f0f0ccccccccaaaaaaaaffcf0000ff00ff00f0f0f0f0cccccccc55445544ffff0000f0fff0f0ccccccccaaaaaaaa00ff00ccffff0000ff00ff00f0f0f0f0ccccccccaa8aaaaaffff0000ff00ff00cccc8888555500000f0f0a0affff0000ff00ab00f0f0f0f0cccccccc54545454ff008800f0f0f0f0ccccccccaaaaaaaaaaaa0000ff00ff00fafaf0f0f0ff0000ccccccccaaaaaaaaff000000ccccccccaaaaaaaa0f000f0000000c0cffff0000fff0fff0f0f0f0f0ee00ee0088888888ffff0000ff00fff0f0f0a0a0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0202fafaffccff00ff00ff00f0f000f0ccccccccaaaaaaaafff0fff0f000f000ccccccccaaaaaaaa0000fcccffff3300ff00ff00f0f0f0f0ccccccccaaaa88aaffff00f0ff00ff00f000ff00ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaa8a8a00ff00ccff00ff00fcfcfcfcf0f0f0f0eeee000088888888ffff0f00f0f0f0f0ccccccccaaaaaaaa00ff0f00ff000000f0f0f0f0ccccccccaaaaaa00000000aaffff0000ee00ee00ccccccccaaaaaaaa0f0c0f0cffff0000ff00ff00ccccccccaaaaaaaa0f0f5f0affff0000ff00ff00e0e0e2e2ccccccccaaaaaaaafff0fff0f0000000ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f0f0f0ee88ee8888888888ffff0000ffc0ffc0f030f030ccccccccaaaaaaaaffff0000ff00fff0f0f0f0f0aaaaaaaa33223322ff03ff00f0f0f0f0ccccccccaaaaaaaa0000fcfcffaa0000f0f0f0f0ccccccccaaaaaaaa3f003f00ffff0000f0f0f0f0cc88ccccaaaaaaaa00aa00aaff000000f0f0f0faf0f0f0f0ccccccccaaaaaaaa
def HC5_4_17 : Nat := 0x162e3beb16161363160b2efa1607d3c116029f1515fc4f7615f2440115f051c115c9545915be7aaf15afc6cd15a406ef1599f1e1158d7bdd158cd8ec15894f2c15661490155cf7a2155b24be1552377315400ca5153913b115361e3b1532a3aa1514134d14f0ab9214e4407e14b6104514accca21496dea414657f87143b0c29
def SC5_4_18 : Nat := 0xffff0000f0f0f0f0aaaaaaaa3232323200ff00faf0f0f0f0ccccccccaaaaaaaa00fa00fa0000f0faffcc0000ff00ff00f0f0f0f0cccccccc54545454ffcc0000ff00ff00f0c0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccc5555444400ff00eeffff0000f0a0f0a0ccccccccaaaaaaaa3f003f00ffff0000fd00fd00ccccccccc0c0c0c0aaaaaaaaff00ff00f0f0f0f0ccccccccaa88aa880000ffeefffff0f0ff00ff00f0f00000aaaaaaaa33223322ffff0000ff00ffc0ccccccccaaaaaaaa0f0f0000ffff0000f0f0f0f0eeaaeeaa8888888800aa00aaffff0000ff00ff00f0c0c0c0cccccccc55444444ff00ff00f0f0f0f0eeee00008888888800008888ffff0000fcf0fcf0f0000000ccccccccaaaaaaaaff00ff00f0f0f0f0ee0e0000ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0fc00fc0ffff0000ff00ff00cccccccca8a8a8a80f0f0808ff000f00f0f0f0f0cfcf0000ccccccccaaaaaaaaffff0000ff00ff00c8c8c8c8aaaaaaaa3030f0f0ffff0000f0f0f0f0eeeeeeee8888888800fe00feffff0000f0f0f0f0ccccccccaaaaaaaa00fc00fcffff0000f800f800f0f0f0f0cccccccca8a8a8a8ffff0000ff00ff00f0f0f0f0cccccccca8a88888ff000f00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000f0f0f0f0cc88cc88aaaaaaaa00aa00aafff80000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa0fff0f000000f0f0ffff0000ff05fa00f0f0f0f0ccccccccaaaaaaaaffff0000f8f8f8f8f0f0f0f0ee00ee0088888888ff00ff00f0ff0000f0f0f0f0ccccccccaa88aa88ffff0000ff00ff00f0a0f0a0aaaaaaaa32223222ffff0000ff00cc00ccccccccaaaa88880f0f0c0c
def HC5_4_18 : Nat := 0x1826d2ad1815926f180ffba2180c56c61804f12917f85a8417f388cd17ee97c617b9c46417adc3c5178e1d21178bccbe1786d99b176a268c1743c8311740b588173c5c061733233017152c7f170926291708009516ef6a9916df1a2d16be070b16af019716ab2b97169a96e21686bc5016842ec5167b39f6163fdae516340cb5
def SC5_4_19 : Nat := 0xffff0000ee00ee00ccccccccaaaaaaaa0e0e0e0effff0000ff00ff00a0a0a0a08888888840404040ffff0000f0f0f0f0ee00ee008888888866666666ff00ff00e0e0f0f0ccccccccaaaaaaaa0000eeeeff00ff00f0f000c0ccccccccaaaaaaaa000000ccffff0000ff00ff00c8c8c8c8c0c0c0c0a0a0a0a0ffffee00ffff0000f0f0f0f0ee00ee0088888888ffcf0000ff30ff30f0f0f0f0ccccccccaaaaaaaaff00aa00f0f0f0f0eeee0000ccccccccaaaaaaaaffff0000f0f0f0f0ec00cc00ccccccccaaaaaaaaffff0000fa00ff00f0f0fff0ccccccccaaaaaaaaff0f0000ff00ff00ccccccccaaaaaaaa0f0a0f0aff000000f0f0f0f0cccc0000aa00aa0088888888ff00ff00fcfff0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaa8affffff00f0f0f0f0ccccccccaaaaaaaa00f0f0f0ffff0000ff00ff00f0c0c0c0ccccccccaa888888ffff0000ff0fff00f0f0f0f0c8c8c8c8aaaaaaaaff00ff00f0f0f0f0c8c8c8c8aaaaaaaa0000ffc8ff88ff00f0f0f0f0ccccccccaaaaaaaa77770000ff00ff00f0f0f0f0eeee0000cccccccc55445544ff3b0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff0fff00f0f0f0f0cc88cc88aaaaaaaaff00ff00f0f000c0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0c0c0ccccccccaaaababaff0f0f00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ea00ea00e0e0e0e0ccccccccaaaaaaaaffff0000ff000c00ccccccccaaaaaaaa0f0f0c0cffff8080ff00ff00f0f0a0a0ccccccccaaaaaaaafffff0f0fa00aa00f0f00000ccccccccaaaaaaaaff00ff00f0f0f0f0f0f000ccccccccccaaaaaaaaffff0000fc00fc00f0f0f0f0eeeeeeee88888888
def HC5_4_19 : Nat := 0x1a83bd501a81bed41a3744871a2e26aa19fc8ce119f8f92d19eed0c919bef27c199c4844199237471986e241196940af195d1235193603e719356289192f87e41928aefa19271e03191655d2190814cb1904794418d058c518cd990d18c73eed18a84aea18a5226f18937a421892eb261889dcb218749bc318741f00183ecb88
def SC5_4_20 : Nat := 0xffff0000ff00ff00aaaaaaaa333332320f0f0a0aff00ff00f0ff00f0f0f0f0f0ccccccccaaaaaaaaff00ff00f0c0f0c0ccccccccaaaaaaaa0000ffaaffff0000ff00ff00f0f0f0f0eaeaeeee88888888ffff0000f0f0f0f0cc88cc88aa00aa0000aa00aaff00fff0f0f0f0f0ccccccc0aaaaaaaa0000f0f0ff00ff00eeee0000e0e0e0e0cccccccc44444444ff00ff00e0e0e0e0ccccccccaaaaaaaa0000ffccffff0000fe10fe10f0f0f0f0ccccccccaaaaaaaaffff0000ff00fa00ccccccccaaaaaaaa0f0f0a0af0f0f0f0ef00ef00ccccccccaaaaaaaa0000eeeeff000000faf0faf0ccccccccaaaaaaaa0f0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00fff000ffff0000cccc8888aaaaaaaa0f0f0a0a00ff00aaffff0000ff00ff00e0e0e0e08888888800008888ffff0000ff00ff00f0f0f0f0cccccccc54445544ff00ff00f0fa0000ccccccccc0c0c0c0aaaaaaaaff88ff00f0f0f0f0ccccccccaaaaaaaa0000f0f0f0f0f0f0eaea0000ea00ea00ccccccccaaaaaaaaff00ff00f0f0f0f0cc88cc88aa00aa000000ffaaffff00f0ff00ff00f0f03030ccccccccaaaaaaaaffff0000fa00fa00f0f0f0f0aaaaaaaa32323232f0c0f0c0cccccccccc00cc00aaaaaaaa0000ffccffff0000f0a0f0a0ccccccccaaaaaaaa00fa00faff00ff00eaea0000ccccccccaaaaaaaa0a0a0a0aff0000aaf0f0f0f0ccccccccaaaaaaaa000000aaff00ff00f0f000c0cccccccccccc0000aaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000efaaffff0000ff00ff00f0f0f0f0cccdccccaaaaaaaaffff0000ff00ff00eecceecce0c0e0c088888888ffff0000ff00ff00e0e0f0f0cccccccc44444444fff0fff0ff000000ccccccccaaaaaaaa0f0f0000
def HC5_4_20 : Nat := 0x1d285e0e1d121b581cf54b261cc613421cbb3a531ca7c6971c8fe7171c8f40a01c5da80b1c5974f71c4e26131c35ec771c3448681c3310d11c106c771c0e96ed1bfb5bf31bf46e6b1befb0c31bec9b431bde4de41bdb11c01bb2d2061b7a3f491b6f774b1b3ec8771b30e3dc1ac0bde21ab647e11aaa0e451a972f471a915ecf
def SC5_4_21 : Nat := 0xff00ff00fcfc0000f0f0f0f0cccccccca8a8a8a8ff00ff00f0f00000ccccccccc0ffc0c0aaaaaaaaffff0000f0f0f0f0ee00ff00aaaaaaaa8888ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaa0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fffaffff0000f000f0f0ccccccccaaaaaaaa3f003f00ffff0000f0f0e0e0ccccccccaaaaaaaa00ee00eeffff0000ff00ff00e0c0e0c0ccccccccaa88aa88ffff0000f0f0f0f0ccccccccaaaaaaaa00fa000affff0000f0f0f0f0ee00ee00aaaaaaaa88888888ffcc0000ff00ff00f0c0f0c0cccccccc55445544ff0000ccff000000f0f0f0f0ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaa00f00ff0ffff0000f0f0f0f0f0000f00ccccccccaaaaaaaaf0f0f0f0eeee0000ccccccccaaaaaaaa00ff00eeff00ff00f0f00000ddddd0d0ccccccccaaaaaaaaf0f0f0f0ccccccccaaaaaaaa00ff000000ccf0fcff00ff00f0f000f0ccccccccaaaaaaaa0f0f0f00ffff0000ff00ff00f0f0f0f0cccccccc64646464fffffff0ffffff00f0000000ccccccccaaaaaaaaffff0000ff00ff00d0d0d0d0cccccccca8a8a8a8ffff0000ff00ff00f0f0f0f0cccccccc55455544ffee0000ff00ff00f0e0f0e0ccccccccaaaaaaaaffffff00ff0a0a0af0f0f0f0ccccccccaaaaaaaaffff0000f000ff00ccccccccaaaaaaaaa0a0a0a0ffff00f0ff00ff00f0f00000ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaa000f000f0ffff0000ff00ff00e0e0f0f08888888811110000ffff0000fa00fa00c8c8c8c8aaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0a0cccc8888aaaaaaaaff00ff00f0a0a0a0ccccccccaaaaaaaaaaaa0000ffff0000ff00ff00cccccccc666666660e0e0e0e
def HC5_4_21 : Nat := 0x2004c67d1ffcef041fd95eea1f88e10b1f66e1b21f4ad4131efd29441ef8a63b1eef0a501ec7f0561ea7a5d31ea5216e1e80acb41e5f198c1e5ba3121e527e371e4424b41e2ce2a81e28f2a01e1767c31e1545bb1e06734b1dfad6821dd1aae01dcc89a51db898801db6e2471dabf70d1d9656de1d835a881d5dbda31d510ab3
def SC5_4_22 : Nat := 0xffff0000ff00ff00f8f0faf0ccccccccaaaaaaaaff00ff00f0f0fff0ccccccccaaaaaaaa0000eeeeffaa0000f0f0f0f0ccccccccaa00aa0044444444ff000f00f0f0f0f0ccccccccaaaaaaaa000000aaff0fff00f0f0f0f0ccccccccaaaaaaaa77770000ffff0000ff00ff00ccccccccaaaaaaaa0f0a0a0affff0000ff00ff00eeeeeeee8888888870f070f0ffff0000f800f800ccccccccaaaaaaaa80808080ffff0000ff00ff00f0f0f0f0ccccccccaaaababaffff0000ff00ff00e0e0f0f08888888855550000ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0effff0000ff00ff00ccccccccaaaaaaaa0f080808ffff00f0ff0fff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f08888888866666666fffff0f0f0000000ccccccccaaaaaaaa00000f00ff00ff00f0f0f0f0cccccccc545454540000fafaff00ff00feee0000f0f0f0f0ccccccccaaaaaaaaff00ff00f2f2f2f2f0ff0000ccccccccaaaaaaaafff0fff0ff000000ccccccccaaaaaaaa0fff0000ffffff00ccccccccaaaaaaaa0f0f0f0000f0f0f0ffff0000ff00fff0f000ff00ccccccccaaaaaaaaff00ff00f0ff0000f0f0f0f0cccccccc55445544ff0fff00ff00ff00f0f000f0ccccccccaaaaaaaaff0f0000fc00fc00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0eeeeeeeeee00ff0088888888ff00ff00ccccccccc0c0c0c0a8a8a8a80000fcfcffff0000f0f0f0f0cc88cc88aaaaaaaaaa00aa00fffff0f0ffff0000ccccccccaaaaaaaa0fff0ff0ffff0000ff00ff00f0f0f0f0ee0eee0e88888888ff008800f0f0f0f0ccccccccaaaaaaaa0000ccccff00ff00f0f00000ccffc0f0ccccccccaaaaaaaafffffff0ffff0000f000f000ccccccccaaaaaaaa
def HC5_4_22 : Nat := 0x22d7bdf522c9a08122c35b6222bdf109229675b7228fb69122713941227033d0221e6604220e58a721e1b68221d10c5d21c0730f21953db921905b5121765e852173e198216ce1d92165419a215d8cbf215204852148038a2126d4572108772c2093eb9c20810dde206a350a2054e6b0203e3e9e203766192018b93d200d1f6c
def SC5_4_23 : Nat := 0xffff0000f0f0f0f0f000ff00eeeeeeee88888888ff00ff00f0e0f0e0eeee0000ccccccccaaaaaaaafffff0f0ff00ff00f8f80000ccccccccaaaaaaaaffff0000fff0fff0f000f000aaaaaaaa32223222ff00ff00f0f0f0f0eeee0000aaaaaaaa22222222ff0fff00f5f50000f0f0f0f0ccccccccaaaaaaaaff0ffff0f0f0f0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0e0f0c0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa0f0f000000ff000affff0000fff0fcf0f000c000ccccccccaaaaaaaaff0fff00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0ccccc8c8aaaaaaaaff00ff00f0f0f0f0cccccccc545454540000ffccf000f0c0ccccccccaaaaaaaa0000ff000000ccccffff0000fc0cff00f0f0f0f0ccccccccaaaaaaaaff000000f0f0f0f0ccccccccaaaaaaaa000000eeffff0000ff00ff00f0f0f0f0cccccccca8aaa8a8ffff0000ff00ff00f0f0f0f0aaaaaa8833333300ffff0000ff00ff00f0f0f0f0545454543c3c3c3cffff0000fff0fff0ccccccccaaaaaaaa0fff0f00ff00aa00f0f0f0f0ccccccccaaaaaaaaaaaa0000ffff0000fc00fc00f0f0a0a0ccccccccaaaaaaaaff00ff00f0fa0000ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0a0a0cccccccca8a8a8a8ffff0000ff00ff00f0f0f0f0cccc8888aaaaffaaff00ff00fcf80000f0f0f0f0cc88cc88aaaaaaaaffff0000ccccccccaaaaaaaa0f0e0f0e00ee00eeffffff00ff000000ccccccccaaaaaaaa0e0e0e0effdd0000f0f0f0f0ccccccccaaaaaaaa00ee00eeffff0000fc00fc00f0f0f0f0aaaaaaaa33223322ffff0000e0e0e0e0ccccccccaaaaaaaa00ff00eeffff0000ff00ff00ccccccccaaaaaaaa0f0f0f08
def HC5_4_23 : Nat := 0x26b547f926b34fe126a718f926a04b8a26952d93269402d52642bae1263daf3a25eb78c225bf7f3e2582cf5725600d3325571280254a51c9254333d6253f68922537258d2529549524f43f8924bd49832417d88623e0bfb323b74a4323b1863b2387237e237f67d5237211a3236582df22f51a8622f2c90922e535ee22dea0f9
def SC5_4_24 : Nat := 0xff00ff00f0f00000ccccccccaaaaaaaa0c0cc0c0ffff1010f0f0f0f0ef00ef00ccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000cccccccc66666666ffff0000ff00ff00f0f0f0f0cccc8888aa88aa88ffff0000ff00ff00f0a0f0a0ccddccccaaaaaaaaffff0a00f500f500f0f0f0f0ccccccccaaaaaaaaffff0000fc00fc00f0f0fcf0ccccccccaaaaaaaaff00ff00f0f000f0dddd0000ccccccccaaaaaaaaf0f0f0f0f000fe00ccccccccaaaaaaaa0000eeeefffff0f0ff00ff00f0f00000aaaaaaaa33332222ffff0000ff00fff0f0f00000ccccccccaaaaaaaaffffff00f0f00000ccccccccaaaaaaaa00ff00f0fffffff0f000f0f0ccccccccaaaaaaaa0000f0f0ffff0000f0f0f0f0ccccccccbb44bb44aaaaaaaaffff0000ff00ff00f0f0f0f08888888810001000ffff0000ff00ff00f0f0f0f0ccc8ccc0aaaaaaaaffff00f0ff00ff00f0f0f0f0aaaaaaaa33332232ffff0000ff00ff00f0f0f0f0cccccccc55554444ff00ff00f0fff0f0ccccccccaaaaaaaa0000eeeeffff0000ff04ff44f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa77887788ffff0000ff00ff00ccccccccc3c0c3c0aaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f000f08fffffff0ff00ff00ccccccccaaaaaaaa0f00ff00ffff0000ff00ff44f0f0f0f0cccccccc55445544ff00ff00f4fc0000f0f0f0f0ccccccccaaaaaaaaf0f0f0f0eeee0000ee00ee00ccccccccaaaaaaaaffffeeeeff00ff00f0f0f0f0eeee000088888888ffff0000ff00ff00ccccccccaaaaaaaa0f0f2e2effff0000f0f0f0f0ccccccccaaaaaaaa7f007f00fffff0f0ff000c00f0f0f0f0ccccccccaaaaaaaaffff1100ff00ff00ccccccccaaaaaaaa0e0e0e0e
def HC5_4_24 : Nat := 0x2a7a6ffd2a341f862a2fe73c2a0806f92a04f68229fcca1329e9c8e329bda59029b2e60f29b04d7729a4887529944ce1298e95ea2982d6bc295cc80e29574b272904c6722869e122285bace0284f6cde282afd6c28227b1f2803878427f7f1f027f44a6627b25709276299d927564b3e2751810d273548a127232f9126edb1ad
def SC5_4_25 : Nat := 0xffff0000ff00ff00f0f0f0f0cccccccca8a8a888ffff0000f0f0f0f0f088f088ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000eeceffff0000f000f000ccccccccaaaaaaaaa00aa00affff0000f0f0f0f0ee00ee00aaaaaaaa88cc88ccffff0000fc00cc00f0f0f0f0ccccccccaaaaaaaaffff0000f000f0f0ccccccccaa00aa0044444444ffff0000f0f0f0f0ccccccccaaaaaaaa50aa50aaffff0000ff00ff00ccccccccaaaaaaaa0ff0f0f0ff000000f0f0f0f0ccccccccaaaaaaaaa0a0a0aaffcc0000ff00cc00f0f0f0f0ccccccccaaaaaaaaf0f0f0f0efef0000ef00ef00ccccccccaaaaaaaaffff8080ff00ff00f0f00000ccccccccaaaaaaaaff00ff00f0ff0000ccccccccaaaaaaaa0000f0f0ffff0000fa00fa00f0f0f0f0ccccccccaaaa8888ffff0000f0c0f0f0cccccccccc00ff00aaaaaaaaffff0000fff0fff0f000f050ccccccccaaaaaaaaffff0000ff00ff00f0f0c0c0cccc0000aaaa8888ffffeeeeffff0000ff00ff00e0e0e0e088888888ffcf0000ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0fc0000ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0aaaaaaaa33336666ff0f0f00f0f0f0f0ccccccccaaaaaaaa0f0f0f00ff00ff00f8f80000ccccccccaaaaaaaa00f000f0ff00ff00ccccccccccccc0c0aaaaaaaa0f00ff00ffff0000ff00ff00f0f0f0f0efefeeee88888888ff00ff00f0f0f0f0cccc8888aaaa000055550000ff00ff00fafa0000f0f0f0f0cccccccc54544444ffff0000f0f0f0f0cccccccc5454444400fc00ccffffff00f0000000ccccccccaaaaaaaa00f0f0f0ff00ff00fcfc0c00f0f0f0f0ccccccccaaaaaaaaffff0000fff0fff0ccccccccaaaaaaaa0ff00ff0
def HC5_4_25 : Nat := 0x2e84fd1c2e6d0a7a2e692cb22e1d1be52e03daef2d9d6b1c2d7750d12d6fd8902d50186f2ce6a3872ccd14172c8e8f462c8a5e382c819af22c30f5e72c1b248c2c0be0772be0366f2bdfde1a2bc748c12bb4a3642b7ed2592b55a9a92b4a70c32b33400a2b3138662b0f17192adfc1ae2ace8e3e2acb63e72a994aa82a8320a5
def SC5_4_26 : Nat := 0xff50ff50ff0f0000f0f0f0f0ccccccccaaaaaaaaff000000f0fffff0f0f0f0f0ccccccccaaaaaaaaffff0044ff00ff00f0a0f0a0ccccccccaaaaaaaaff0aff00f0f00000ccccccccaaaaaaaa0a0a0a0affff0000f000f0f0ccccccccc0ccc0ccaaaaaaaafffff0f0ff00ff00ccccccccaaaaaaaa0f0ffcfcffff0000fff0fff0f000f000ccc8ccc8aaaaaaaaff00ff00f0f0f0f0eeee0000888888880000f0f0fffffff0ff000000ccccccccaaaaaaaa0f0f0f00fff0fff0fff00000ccccccccaaaaaaaa0fff0000ffff0000f0f0f0f0f000ff00aaaaaaaa33223322ffff0000ffa0ffa0ccccccccaaaaaaaa0fff0000ffff0000f0f0f0f0ccccccccaaaaaaaa88f088f0ff00ff00f0f00000eeeee0e0ccccccccaaaaaaaafffa0000fff0fff0f000f000ccccccccaaaaaaaa00000000ff00ff00f0f0f0f0efef000088888888ffff0000ff00ff00f0f0f0f0cc88cc88aa88aa88fffff0f0ff0fff00f0f00000ccccccccaaaaaaaaffff0f00f0f0f0f0ee00ee00ccccccccaaaaaaaaff00ff00fcfc00f0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0a0cccccccc55555500ff00ff00f0e0f0e0ccccccccaaaaaaaa0000ffeeff00ff00f0f0f0f0ccccccccaaaaaaaa0000fca8ffff0000ff00ff00f0f0f0f08888888811111010ffff00b0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0ff0f0f0f0f0ccccccccaaaaaaaa0ff00ff0ffffff00f0f0f0f0ee000000ccccccccaaaaaaaaf0ff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaff0f0000f0f0f0f0f000ff00ccccccccaaaaaaaaff00ff00f0ff0f00f0f0f0f0ccccccccaaaaaaaaff00ff00eeff0000e0e0e0e0ccccccccaaaaaaaafff0fff0ff880000f0f0f0f0ccccccccaaaaaaaa
def HC5_4_26 : Nat := 0x33573bcc3334c3f933246c5b3312d0a432afbf3f32abf46932436e69324004ee31e3a2c13199ee783169457a315a4c2a313b6aa0311c900431173a6d30f0805630c7efc530b0172330ad80953096b889307d7ae6306a37f7305f4fc630164d0c2fed8cbd2fe79e492fb8d0372fa6241f2f7ef39d2f2bfe9d2eefba8e2e875d5f
def SC5_4_27 : Nat := 0xffff0000ff00ff0088888888666666660e0e0e0eff0fff00f0f0f0f0ccccccccaaaaaaaa0000fff0ffff0000ff00ff00f0f0f0f09999000088888888ff880000ff00ff00f080f080ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0e0e0c0cffcf0000f0f0f0f0ccccccccaaaaaaaa00fc00fcffff0000f0f0f0f0eeeeeeee8888888800ee00eeff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cdccddccaaaaaaaaffff0000ff80ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff0fff00f0f0f0f0ccccccc0aaaaaaaaffffff00f0f0f0f0ccccccccaaaaaaaa00f0ff00ffaaaaaaf0f0f0f0ccccccccaaaa0000aa00aa00ff00ff00f0f0f0f0efee0f00ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaa0000000affff0000ff00ff00f0f0f0f0eaeaeaea62626262fffffff0f0f00000ccccccccaaaaaaaa00ff0000ffff0000ff000f00f0f0f0f0aaaaaaaa33222322ff0fff00f0f00000ccccccccaaaaaaaa00f000f0fff0fff0f00f0000f000f000ccccccccaaaaaaaaffff0000ff00ff00f080f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa0ff0fff0ffff0000f0f0f0f0888888881010101000ee00eeffffff00ff000000e0e0e0e0ccccccccaaaaaaaaff000000f0f0f0f0ccccccccaaaaaa00a0a0a0a0ffff0000ff00ff00e0e0c0c0aaaa000088888888ffff0000ff00ff00f0f0f0f0cccccccc99889988ffff0000f0f0f0f0eeeeeeeeee00ee0066666666ff000000f0f0f0f0ccccccccaaaaaaaa3f3f3f00ffaa0000ff44ff44f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeecc88888888ffff0ff0fff0fff0ccccccccaaaaaaaa0ff00ff0
def HC5_4_27 : Nat := 0x380b58c037f1b37a37b7df3d3797cf0b376d24b33763addb3735652d37041d5136e9e60536d2db4036c61cf936bb737f367d45f23630cffc36228d52361df35c359c8184355c636e35536eed3532d7a134fcf21034f468a334d59f0134cdf24434bc160834aa55a134a0aeb43482969533e14f5833ce663f33bf87df3387ce8b
def SC5_4_28 : Nat := 0xff0f0000f0f0f0f0ccccccccaaaaaaaa3f003f00f0f0f0f0f0000000ccccccccaaaaaaaa0f0f0f00ff001f00f0f0f0f0ccccccccaaaaaaaa0000eeeeff00ff00f0f0f0f0cccc8888aaaa000044444444ffff0000ff00ff00f0f040f0ccccccccaaaaaaaaf0f0f0f0ccccccccaaaaaaaa0f00ff0000ff00f0ffff0000ff00ff00f0f0f0f0cccc8888aaaa00aaffff0000ff00ff00f0f0f0f0cccccccc6a6a6a6affff0000ff00ff00f010f0f0ccccccccaaaaaaaaeeee0000ee00ee00ccccccccaaaaaaaa0e0e0e0effff1010ff10ff10f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0c0f0c0cccccc00aaaaaaaaffff0000f0000000ccccccccaaaaaaaa000c000cffff0000ff11ff10f0f0f0f0ccccccccaaaaaaaaffffaa00ff0f0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee66666666ffff0000ff00ff00f0f0f0f0aaaaaaaa333c333cfffffff0ff000000f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cc3ccc3caaaaaaaaffff2222ff00ff00f0f0f0f0ccccccccaaaa8888ffff0000ff00ff00f0f0e0e0eeeeeeee88888888ff000000fafafa00f0f0f0f0ccccccccaaaaaaaafff0fff0ff00ff00f0ff0000ccccccccaaaaaaaaff00ff00f0f0f0f0cc88cc88aaaaaaaa0000ffccffffff00ff000000f0f0f0f0cccccccc55555544ff030000f0f0f0f0ccccccccaaaaaaaa000000fcff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffeeffff0000f000f000ccccccccaaaaaaaa444c444cffff1100ff00ff00e0e0e0e0ccccccccaaaaaaaaffff0000ff00ffe0e0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccffccaaaa88aaffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_4_28 : Nat := 0x3ee56b983ea73c0a3e5f868d3e523bc63e0685553df097163dec1af23de09a503dd8ca033dd8b4e03dbb1f4d3d5d06583c9c31573c6d44883c4354e43be08fc73bad31c43b5179e93b195dfa3aecb8cf3ad84aec3aa6e2283aa44d933a95edd93903dad038b94f7b38777b2138602c6c38562112384d65a638378179380b79c7
def SC5_4_29 : Nat := 0xff00ff00f0f0f0f0cccc8888aaaa000000008888fffff0f0ff00ff00ccccccccaaaaaaaa0f0cffccffff1000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ccccccccaaaaaaaa0fff00000000fff0ffff0000ff00ff00f0f0f0f0cccc888854545050ffff0000ff00ff00f0f0f0f0ccccccccaaaa8888ffeeff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000f000f0f0ccccccccccc0ccc0aaaaaaaaffff0000ff00ff00f0f0f0f0eeee666688888888ffff0000ff00ff00f0f0ffc0ccccccccaaaaaaaaff00ff00f00000f0ccccccccaaaaaaaa00ffff0000000000ffff0000f000f000ccccccc0aaaaaaaafffff0f0ff00ff00f0f00000cccccccc55555550ff0fff00f0f0f0f0ccccccccaaaaaaaa0f0fff00f0f0f0f0eeee0000ee00ee00aaaaaaaa88888888ff00ff00f0fe0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0e0e0e0e088888888ffff0000ff13ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f000f0ccccccccaaaaaaaa00ee00eefffffff0f0f00000f000f000ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff8afff0fff0ff00ff00f0f0f0f0eeee000088888888ffff0000ff00ee00f0f0c0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ecececec8a8a8a8aff880000ff00ff00ccccccccaaaaaaaa0f080f08ff00ff00f0f0f0f0ccccddccaaaaaaaa0000ffaaffff0000ff00ff00f0f0f0f0cccccccc55aaaaaaffff0000ff00ff00e0e0e0e0ccccccccbabababaffff0000fa00fa00f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00e0eee0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa32322222ffff8080ff00ff00f000f000ccccccccaaaaaaaa
def HC5_4_29 : Nat := 0x466d6aa9465a428f45fa84f245ee736545ed2670450e12024509992544f1008c446d786a4423fc8043f8b5eb43736e0f42faa0ba4241b8d9421ce7e64154f04f414c1a29412c8df640d94184409efb18406f60024062b78f40539488403d6bae403cca2f40294be3401270933fca27373f889fa43f3e24a63f30ec193f2ff417
def SC5_4_30 : Nat := 0xff00ff00f0fff0f0ccccccccaaaaaaaa00f0f0f0ffff0f00ff00ff00ccccccccaaaaaaaa0f00fff0fff0ff00f0f00000ccccccccaaaaaaaa00ff00f0ff00ff00f0f0f0f0eeeeeeee888888880000f8f8fff0fff0ff0f0000f000f000ccccccccaaaaaaaaffff0000eeeeeeee888888880e0e0e0e00ee00eeffff0000ff00ff00f0f0f0f0cccccc00aaaaaa88ffff0000ff00ff00f0f0f0f0c000c000a888a888ff00ff00f0f00000ccccccccaaaaaaaaaaaaaaa0ffff0000ff00ff00f0f0f0f0888888881f1f0000ff00ff00f0f00000ccccccccaaaaaaaa0f0ffff0ffff0000ff00ff00f0f0f0f0cccccccc55555554ffff0000ff00ff00f0f0f0f0ccccccceaaaaaaaaffff0000fef0fef0e000e000ccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000cccccccc55554444ffff0000ff00ff00f0f0f0f0eeeeeeee76767676ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff0cffff0000f0f0f0f0eeaaeeaaee00ee0088888888ff000000ccccccccaaaaaaaaa0a0a0a00f0f0f00ffff0000ff00ff00f0f0f0f0aaaa88883333ccccffff0000ff00ff00f0f0f0f0a888a88830003000ffff0000f0f0f0f0ee00ee00cc88cc88aaaaaaaaffff0000fff5fff0f000f000ccccccccaaaaaaaaffff0000ff00ff00c0c0c0c08a8a8a8a22222222ffff0000ff00ff00f0f0f0f0ccccccc055555550ffff0000fd00dd00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0e000ff00ccccccccaaaaaaaaf0f0f0f0f0000000ccccccccaaaaaaaa0f0fff00fffff0f0ff00ff00f0f00000ccccccccaa88aa88ff00ff00f0fff0f0ccccccccaaaaaaaa0000fafaffff0000ff00ff00f0f0f0f0cccccccca8888888ffff0000f0000000ccccccccaaaaaaaa0ff0fff0
def HC5_4_30 : Nat := 0x4ed70ba04ec051374ea1ab6f4e3afca74e173dae4dab80344d34fe124d0d8d264cd316824cc8dfaf4cab7fa94c56fcf04bdef2454bddf3d54bbed8b24b5dedb84b46f7374ad1f5784a9b26c94a90faef4a4ee17d49f2d9ee49bf5d08497868da4910a690490ade3c490894e748b59e5248aa6ddb4838529b47c54cbb469044a6
def SC5_4_31 : Nat := 0xff00ff00f0ff00f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa1f1f0e0efffffff0ffff0000f0000000ccccccccaaaaaaaaffff0000f0f0fff0ccccccccaaaaaaaa00f000f0ff00ff00f0f0fff0ccccccccaaaaaaaa00ffff00ffff0000ff00ff00f0f0f0e0ccccccccaaaaaaaaffffff00f5000000f0f0f0f0ccccccccaaaaaaaaff00ff00ff000000ccccccccaaaaaaaa0ffff0f0f0f0f0f0eeeeeeeeeeee00008888888800ee00eeff00ff00f0ff00f0ccccccccaaaaaaaa0f00ff00fffff0f0ff00ff00f0ff00f0ccccccccaaaaaaaaf0f0f0f0ccccccccaaaaaaaa00ee00ee0000eeeeff000f00f0f0f0f0ccccccccaaaaaaaa88880000ffff0000f0f0f0f0ccccccccaaaaaaaa00ff0088ffff0000ff00ff00e0e0e0e0888888880e0e0e0effff0000ff00ff00f0f0a0b0ccccccccaaaaaaaaffff0000f000ff00ccccccccaaaaaaaa0f0ff0f0ffff0000f000fff0f000f000ccccccccaaaaaaaafffa0000ff00ff00f0f0f0f0aaaaaaaa33323332ff00ff00f0f0f0f0eeea0000ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa00ff0ff000000000ffff0000f0f0f0f0ee00ee0088888888ff000000f0f0f0f0ccccccccaaaaaaaaaaaaaa22ffff00f0f0f0f0f0ee00ee00ccccccccaaaaaaaafff00000ff00ff00f0fff0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0e0c0c0cf000f000ccccccccaaaaaaaa0000fff00000aaaaff00aa00f0f0a0a0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0eeeeaaaa88888888ffff0000ff00ff00f0f0f0f09988998888888888eeee0000ee00ee00e0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0d0f0d0ccccccccaaaaaaaa
def HC5_4_31 : Nat := 0x5ecce1bb5e3156445b8e7a325b6fe0ba5b564ed55b173b705af482045abbca465a8a5cbd5a4f4e2e5a47f56758eab083586a5f545859f19d57c23530574b069f56f67d3456420ed85515630c54d3e6c653e1081753ca5cee5386c40952e5b3f052cb987252a1708e518dba15518226c24faaec1b4f5afcc14f4124454f27b748
def SC5_4_32 : Nat := 0xff00ff00f0f0f0f0ccccccccaaaaa0a00000fafaffff0000ff00ff80f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa777f0000ffff0000ff00ff00f0f0f0f08888888866006600ccccccccaaaaaaaa0e0e0e0e00ee00ee0000eeeeffff0000f0f0f0f0ee00ee008888888888008800ff880000ff00ff00f0f0f0f0ccccccccaaaaaaaaff000000f0f0f0f0ccccccccaaaaaa0044444444ffff0000f0f0f0f0ef00ff00ccccccccaaaaaaaaff000f00f0ff0000ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0ccccccc8aaaaaaaafbfb0000fb00fb00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee99889988ffff0000ff00fd00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ee00ee00888888886600660000000000ff0ffff0f0f00000ccccccccaaaaaaaaffff0000cccccccc555544440f0f0c0c00ff00ccff00ff00fac80000f0f0f0f0ccccccccaaaaaaaaffffff00f00000f0ccccccccaaaaaaaa00ffff00ffff0000ff00ff00f0f0f0f0ccccccccaaaa6666ffff0000ff00ff00f0f0f0f0ccccdcccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f000effffff00f0f0f0f0ccccccccaaaaaaaa00eeeeeeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaa2fffff0f0ff0ffff0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0e0e0f0f088888888f0f0f0f0ccccccccaaaaaaaa00ee00ee0000f0fef1ff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa1e1e1e1effff0000f0fef0f0ccccccccaaaaaaaa00ee00eeff00ff00f0ff00f0ccccccccaaaaaaaa00f000f0ff00ff00f0ff0000e0e0e0e0ccccccccaaaaaaaa
def HC5_4_32 : Nat := 0x715dd0de714d186870319f1d70054f4d6f60cb8a6eb1fef56e925dba6c7b821a6bb9ee0a6b49523c69cd083f69be335169a64ecf6900c52f68a7561b67fd814467604ef866b2c01f65b982916591e0ec6574a62f64cba07363862960637f0a1c637894f062a859e9621de25360472ba3601bb2b05efe4ea25eeb4d315ee2a7bd
def SC5_4_33 : Nat := 0xffff0000ff00ff00f0f0f0f08888888811001100ffff0000ff00ff00f0f0f0f0cccccccc54444444ffffff00f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0888888886666eeeeffff0000f0f0f0f0ee00ee008888888811001100ffffff00fff0f0f0f0000000ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaa00080008ffffff00ff0000f0f0f0f0f0ccccccccaaaaaaaaff00ff00f0f00000ccccccccaaaaaaaa00000f0affff0000f000f000ccccccccccc0ccc0aaaaaaaaf0f0f0f0ccccccccaaaaaaaa00f800f80000f8f8ffff0000f0f0f0f0ee00ee008888888880808080ffff0000ff00fc00f0f0f0f0ccccc0c0aaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc9a9a9a9aff0fff00f0000000ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0f0f0ccccccc0aaaaaaa0ffff0f00f0f0f0f0ccccccccaaaaaaaa00f0f0f0ff000f00f0f0f0f0ccccccccaaaaaaaa00008888e0e0e0e0ccccccccaaaaaaaa00ee00ee0000eeeeffff0000f0f0f0f0aaaaaaaa55aa55aa33223322fffffff0f0f00000ccccccccaaaaaaaa00f00000ffff0000f0f0f0f0ccccccccaaaaaaaa0eee00eeffffff00f0f0f0f0ccccccccaaaaaaaa00f0f000ffff0000f000f000ccccccccaaa0aaa00aaa0aaaffff0000ccccccccaaaaaaaa0f0a0f0a00fc00fcffff0000ff00ff00f000f0f0ccccccccaa88aa88fffff0f0fff0fff0f0000000ccccccccaaaaaaaa00000000f0f0f0f0eeee0000ee00ee0088888888ffff0000ff00ff00e0e0e0e0888888881f1f0000f0f0f0f0ccccccccaaaaaaaa0fff0f000000f0f0ffff0000ff80ff80ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0cccccccc55885588
def HC5_4_33 : Nat := 0x9eaca6639c4bd6ec9be534729a671743974ead3194f8059192628e9e90a148bf8ee7bcb78e09f7fd86b018fa8661e0aa83ae72168390ada5837a5f9283669c9c8346789f8214956180c93aef8024e0767ea0529e7d14bd4c7cd3736d7975c4aa7869847877e441ec774f4180771f547e74a76a1b73b78730735b4fed7267b47a
def SC5_4_34 : Nat := 0xfffffff0f0000000ccccccccaaaaaaaaff000000f0f0f0f0ccccccccaaaaaaaa88888800ffff0000ff00ff00f0f0f0f0cccccccc55555550ffff0000ff00ff00c0c0c0c0a0a0a0a008080808f0f0f0f0eeeeeeeeeeee0000ee00ee0088888888fffff0f0ff00ff00ccccccccaaaaaaaa0f0ffff0ffff0000ff00ff00f0f0f0f05555555033333330ffff0000ff00ff00f0f0f0f0aaaaaaaa4cccccccffff0000ff00ff00f0f0f0f0ee00000088888888ffff00f0ff00ff00f0fff0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee88888888ffff0000ccccccccaaaaaaaa0f0f0e0e00ff00eeffff0000f0f0f0f0eeeeeeeeee00ee0088888888ffff0000f0f0f0f0ee00ee008888888810101010ffff0000ff00ff00f0f0f0f0eaaaaaaacccccccc
def HC5_4_34 : Nat := 0xfa6630e3ea40e1dee532eaffdb920dfccb350f86c66c6e5ac59d376ac1ea6223bedd0785b1abfd84af3e1128ae65d06ca7e017f6a58051caa2bd9e0f
def readS5_4 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight (if Nat.blt c 17 then (if Nat.blt c 8 then (if Nat.blt c 4 then (if Nat.blt c 2 then (if Nat.blt c 1 then SC5_4_0 else SC5_4_1) else (if Nat.blt c 3 then SC5_4_2 else SC5_4_3)) else (if Nat.blt c 6 then (if Nat.blt c 5 then SC5_4_4 else SC5_4_5) else (if Nat.blt c 7 then SC5_4_6 else SC5_4_7))) else (if Nat.blt c 12 then (if Nat.blt c 10 then (if Nat.blt c 9 then SC5_4_8 else SC5_4_9) else (if Nat.blt c 11 then SC5_4_10 else SC5_4_11)) else (if Nat.blt c 14 then (if Nat.blt c 13 then SC5_4_12 else SC5_4_13) else (if Nat.blt c 15 then SC5_4_14 else (if Nat.blt c 16 then SC5_4_15 else SC5_4_16))))) else (if Nat.blt c 26 then (if Nat.blt c 21 then (if Nat.blt c 19 then (if Nat.blt c 18 then SC5_4_17 else SC5_4_18) else (if Nat.blt c 20 then SC5_4_19 else SC5_4_20)) else (if Nat.blt c 23 then (if Nat.blt c 22 then SC5_4_21 else SC5_4_22) else (if Nat.blt c 24 then SC5_4_23 else (if Nat.blt c 25 then SC5_4_24 else SC5_4_25)))) else (if Nat.blt c 30 then (if Nat.blt c 28 then (if Nat.blt c 27 then SC5_4_26 else SC5_4_27) else (if Nat.blt c 29 then SC5_4_28 else SC5_4_29)) else (if Nat.blt c 32 then (if Nat.blt c 31 then SC5_4_30 else SC5_4_31) else (if Nat.blt c 33 then SC5_4_32 else (if Nat.blt c 34 then SC5_4_33 else SC5_4_34)))))) (160 * o)
  unpack32 5 v
def readH5_4 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight (if Nat.blt c 17 then (if Nat.blt c 8 then (if Nat.blt c 4 then (if Nat.blt c 2 then (if Nat.blt c 1 then HC5_4_0 else HC5_4_1) else (if Nat.blt c 3 then HC5_4_2 else HC5_4_3)) else (if Nat.blt c 6 then (if Nat.blt c 5 then HC5_4_4 else HC5_4_5) else (if Nat.blt c 7 then HC5_4_6 else HC5_4_7))) else (if Nat.blt c 12 then (if Nat.blt c 10 then (if Nat.blt c 9 then HC5_4_8 else HC5_4_9) else (if Nat.blt c 11 then HC5_4_10 else HC5_4_11)) else (if Nat.blt c 14 then (if Nat.blt c 13 then HC5_4_12 else HC5_4_13) else (if Nat.blt c 15 then HC5_4_14 else (if Nat.blt c 16 then HC5_4_15 else HC5_4_16))))) else (if Nat.blt c 26 then (if Nat.blt c 21 then (if Nat.blt c 19 then (if Nat.blt c 18 then HC5_4_17 else HC5_4_18) else (if Nat.blt c 20 then HC5_4_19 else HC5_4_20)) else (if Nat.blt c 23 then (if Nat.blt c 22 then HC5_4_21 else HC5_4_22) else (if Nat.blt c 24 then HC5_4_23 else (if Nat.blt c 25 then HC5_4_24 else HC5_4_25)))) else (if Nat.blt c 30 then (if Nat.blt c 28 then (if Nat.blt c 27 then HC5_4_26 else HC5_4_27) else (if Nat.blt c 29 then HC5_4_28 else HC5_4_29)) else (if Nat.blt c 32 then (if Nat.blt c 31 then HC5_4_30 else HC5_4_31) else (if Nat.blt c 33 then HC5_4_32 else (if Nat.blt c 34 then HC5_4_33 else HC5_4_34)))))) (32 * o)) 0xffffffff
def SC5_5_0 : Nat := 0xffff0000f0f0f0f0ccccccccaa0aaa0a00f000f000aa00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00cc0cccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000f0000ffff0000ff0fff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff00ccff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00ccccccccc0f0c0f0aaaaaaaaa0a0a0a0ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa55550000ff00ff00f0f0f0f0ccccccccaaaaaaaa5f5f00000000a0a0ffff0000f0f0f0f0cccccccccc00cc00aaaaaaaa00330000ffff0000ff00ff00f0f0f0f0f000c000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa40404444ffff0000f0f0f0f0ccccccccaf00af00aaaaaaaa00500050ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5f5f0000ff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33003300ffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaaaaaa8888ffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa0a0a0a0affff0000f0f0f0f0cc00cc00aaaaaaaa8888888800f000f0ffff0000ff00ff00f0f0f0f0ccccccccb0f0b0f0aaaaaaaaffff0000ff00ff00fcfcccccf0f0f0f0aaaaaaaa33330000ffff0000ff00ff00f0f0f0f0ccccccccaf00aa00aaaaaaaaffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaa00300030ffff0000f500f500f0f0f0f0ccccccccaaaaaaaa00aa00aaff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa0000fafaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa8aaa8affff0000ff00ff00cccccccccc00cc00aaaaaaaa0f0f0a0affff0000ff00ff00f0f00000cccccccca0a0a0a00a0a0a0affff0000f000f000ccccccccaaaaaaaaa0a0a0a000aa00aafffff0f0ff00ff00fcfcfcfcf0f00000ccccccccaaaaaaaa00000000ff00ff00f0f00000ccccccccaaaaaaaa0f0ff0f0ffff0000ff0fff00f0f0f0f0ccccccccaaaaaaaa0000ff00ffff0000ff00ff00f0f0f0f0aaaaaaaa888888883f3f0000ffff0000ff00ff00f0f0f0f0cccccccccc4ccc4caaaaaaaa
def HC5_5_0 : Nat := 0x9ee788009cf58d009cc39f009b5efd00976c180095e724008e0aa7008dc6800089d973007b0ce30068d1fe006092ab005b7fd500542c8c0053e4f1005033fe004c508c0045a85c00456fb40043ed5b00331904002d7a0200285cad00256d6b0021c172002038e700133c25001128440011220f0006b690000292ae00012418
def SC5_5_1 : Nat := 0xff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff0000000a0affffccccff00ff00f0f0f0f0cccccccc555544440000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88ff8888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa222a222ffff0000ff00ff00f0f0fff0ccccccccaaaaffaaaaaaaaaaffff0500ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500ffff0000ff00ff00f000f000ccccccccaaaaaaaa0f0a0f0a00000000ffff0000f000f000ccccccccaaaaaaaa000c000cffff0000ff00ff00f0f0f0f0cccccccca0aaa0aa05000500ff00ff00f0f0f0f0ccccccccaaaafefeaaaaaaaa0000fcfcffff0000ff00ff00f0f0f0f0cccc8888c0c08080aaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa00aaaaaa0000ccccffff0000ff00ff00f0f0f0f0cccccccc5555444400003300ffff0000ff00ff00f0f0f0f0eeeeeeee8888888810101010ff00ff00ff00cc00f0f0f0f0cccccccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0f0c0f0c0cccccccc55445544ffff0000ff00ff00f0f0f0f0ccccccccaeaaaeaaaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00002a2affff0000ff00ff00f000f0f0ccccccccaaaaaaaa00550000ff00ff00ff000000f0fff0f0f0f0f0f0ccccccccaaaaaaaaffff3030ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa0000ffff0000ffccffccff00ff00f0f0f0f0ccccccccaaaa8888ffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa3f003f00ffff0000ff0fff0cff00ff00ccccccccaaaaaaaa0f0f0c0cffff0000ff00ff00f0f0f0f0c8ccc8ccaaaaaaaa55005500ff00ff00f0f00000cccccccccccc0000aaaaaaaa3030f0f0ff00ff00f0faf0faf0f0f0f0ccccccccaaaaaaaa0000f0faffff0000ff00ff00f0f0f0f0ccccccccaafaaaaaaaaaaaaaffff0000ff00ff00f0f0f0f0ceeeceeeccccccccaaaaaaaaffff0000ff00ff00ff00bb00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f000f000cccccccca0a0a0a044444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0022aaaa
def HC5_5_1 : Nat := 0x14e8ba0014e19c6014135730140622f0135ac100133c54d012cda38011ad69101199666011913b60102c8fd00fe834300f850bc00f4060400ef8b9b00eedb9500ee522000ed095000e274f300dc253100d9e6c500d5ff9100d4919d00cafe3400c9a83300c0a60400bd299b00af0ef500ac2ee500a7ad3e00a5d74e00a33bc9
def SC5_5_2 : Nat := 0xffffff00ffff0000ff00ff00f0f0f0a0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00050000ffff0000fff3fff0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00cc008800000000ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaaffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa00ee00eeffffffaaffff0000ff00ff00ccccccccaaaaaaaa0f0a0f0affff0000fa00fa00f0f0f0f0cccccccccccc0000aaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa00aa0000ccccffff0000ff00ff00f0f00000ccccccccaaaaaaaa00a000a0ffff0000f0f0fff0f000ff00ccccccccaaaaaaaa0000ff00ffff00ccff00ff00f0f0f0f0ccccccccaaaaaaaa000000ccff00ff00f0f0f0f0ccccccccaaaaaaaa0fff00000000f000ff00ff00f0f0f0f0ccccccccaaaaaaaa555500003f3f0000ffff0000ff00ff00f0f0f0f0ccccccccaa88aa8822222222ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa30003300ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffcc0000aa88ffff0000ff00ff00f0f0f0f0aaaaaaaa4c4c4c4c30303030ffff0000ff00ff00f4f4fcfcf0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffcc0000aaaaff00ff00f0f0f0f0ccccccccaaaaaaaaaa00ff000000aaaaffff0000ffccffccff00ff00aaaaaaaa330033000f0c0f0cff00ff00ff000000f000f0f0ccccccccaaaaaaaa00ff0000ff00ff00f0f0f0f0eeff0000ccccccccaaaaaaaa55005500ffff0000ff00ff00f0f00000ccccccccaaaaaaaa80808080ffff0000ff00ff00f0f0f0f0cf000000ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa7070707008080808ffff0000ff00ff00f0f0f0f0c4c4c4c4aaaaaaaa02020202ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa3b3b0000ff00ff00fafa0000f0f0f0f0ccccccccc8c8c8c8aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5050f050ffff0000ffcc0000f0f0f0f0ccccccccaaaaaaaa00cc00cc
def HC5_5_2 : Nat := 0x20f428f0208dfec01fc46b601f602da01f5806101ee36d601e732e001e6d9d401dbfbab01d9332e01d76b7701ccba0c01cc38bb01cb33ad01c76d9501c3d48101bc12ad01b60da101a9a802019f6bb9019d61dd019b4f45018d66440182fb3001780a9501717ec201683f9b01614db101600736015cb35e015960b90155865c
def SC5_5_3 : Nat := 0xffff0000ff00f000f0f0f0f0ccccccccaaaaaaaa00000f00ffccccccff00ff00ff000000f0f0f0f0cccc0000aaaaaaaaff00ff00f0f0f0f0ccccffccccccccccaaaaaaaa0000ccccffffe0e0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f030f030ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0cccccccc554455440000aaaaffff0000ff00ff00f0f0f0f0c0c0c0c0aaaaaaaa0c0cccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa70007000ffff0000ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa8888ccccff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa0a0a0000ffff0000ff00ff00ccccccccaaaaaaaa333300000f0a0f0affcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55555544ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa0077ff0000fffff0f0ff00ff00f0f00000ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f0f0f0eeaaeeaaccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa0aaa0a00aa00aaffff0000f0f0fff0f000ff00ccccccccaaaaaaaa0f0f0000ffff0000fefefefef0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa000000ffff0000f300f300ccccccccaaaaaaaa0f000f000c0c0c0cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa23232222ffaaffaaffaa0000ff00ff00f0f0f0f0ccccccccaa00aa00ffffcf00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ee00eeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa3322332233003300ffff0000f0f0f0f0eeeeeeeeaaaaaaaa8888888800ee00eeffff0000ff00ff00f0f0f0f0cccccccc5500550000aa00aaffff0000ff00ff00f0f0f0f0aaaaaaaa8888888833333300ffff0000ff00ff00f0f0f0f0cc00cc00aaaaaaaa88888888ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaa00f000f0ffff0000ff55ff50ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_5_3 : Nat := 0x2b9ce4502b9657602b50bef02aafe7d02a5fb1e029e3739029ca3270299729e02993f7e0294f2a302851a22027fe1c0027da1db027b9546027336af027334050270e64c026c13e40269729802669bb60259c76e025774960250afea024e259d0246602f023e7e690232f895022e6bd20221a591021e4f500213ebd70210f5ed
def SC5_5_4 : Nat := 0xffff0000ff00ff00ff007700f0f0f0f0ccccccccaaaaaaaa00000000ffff0000f0f0f0f0cccc8888aaaaaaaa00ff00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30003000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c00000000f0f0ffffff00ffff0000f000f000ccccccccaaaaaaaa00f000f0ffff0000ffa0ffa0f0f0f0f0ccccccccaaaaaaaa3300330000000000ffff0000ff00ff00f0e0f0e0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa000055000000ffff0000ff00ff00c0c0c0c0aaaaaaaa888888880a0a0a0afffff0f0ff00ff00f0f00000ccccccccaaaaaaaa00ff00f0ffff0c00ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c0c0cffff0000ff00ff00fafffafaf0fff0f0ccccccccaaaaaaaafffff0f0ff000000f0f0f0f0ccccccccaaaaaaaa0f000f00ffffaaaaff00ff00f0f0f0f0ccccccccbbbb0000aaaaaaaaf0f0f0f0ccccccccaaaaaaaa0f0f000000f000f00000ff00ffff0000ff00aa00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0ccccccccaaaa0000a8a8a8a8f0f0f0f0f000ff00ccccccccaaaaaaaa0f0f00000000f0f0ffff0000ff00ff00f0f0a0a0ccccccccaaaaaaaa33003300ffff0000ff88ff00f0f0f0f0ccccccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0cc00ccccaaaaaaaa33330000f0f0f0f0f000f000ccccccccaaaaaaaa0000ff000000ccccffff0000ff00ff00f000f000ccccccccaaaaaaaa000c000cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa04000400ffff0000ff00ff00f0f0f0f0cccccccc55aa55aa55005500ffff00ccff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0888888884444444422222222ffffccccffff0000ff00ff00f0f0f0f0ccccccccaaaa8a8affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000000fcffff8888ffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffcc000000ccffeeffeeffee0000ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_5_4 : Nat := 0x3791de8037550a2036ff291036a61cd036554d403651527035e5851035da68d03518191034e93e7034ddc99034dd01e034b4afd0346b0970342a625033606390335ed8403303dd0032c751303246976032439c60310dd6d030b40cb030b1fd703030f280301110702fb689d02f5ac3802e4250802e1aed902d4b9ad02d37edc
def SC5_5_5 : Nat := 0xffff0000fff0fff0ff0fff00ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0aaaa0000888888884444ccccffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa00f000f000000000ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa8a8a0a0ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa0000ffccff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaaaaa0a0affff0000fff0fff0f000f000ccccccccaaaaaaaa0ccc0cccffffff00ff000000f0f0f0f0ccccccccaaaaaaaaaa000000ffff0000ff00cf00f0f0f0f0ccccccccaaaaaaaa00003030ffff0000ff00ff00f0f0f0f0ccccccccaaaabbaa0000ff00ffaaffaaf0f0f0f0ccccccccaaaaaaaa00aa00aa0000ffaaffff0000ff000000ccccccccaaaaaaaaa0a0a0a00f000f00ffff0000f0f0f0f0ccccccccaaccaaccaaaaaaaa00cc00ccff00ff00f0f0f0f0ccff0000ccccccccaaaaaaaa0000ff00ffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaafffffcfcffff0000ff00ff00ccccccccaaaaaaaa0f0f0c0cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa7070f0f0ffff0000ff00ff00f4f4f4f4f0f0f0f0cccccccc50505050ffff0000ff00ff00ccccccccaaaaaaaa333322220f0f0a0affff0000ffaaaaaaff00ff00f0f0f0f0cccccccc55000000ffaa0000ff00ff00f0f0f0f0cccccccccc880000aaaaaaaaffff0000ff00ff00fcfcfcfcccccccccaaaaaaaa0f0a0f0affffccccffff0000ff00ff00f0fff0f0ccccccccaaaaaaaaffff0000ff0cff00f0f0f0f0ccccccccaaaaaaaa0f0f000000000000ffff0000ff00fa00f0f0f0f0ccccccccaaaaaaaaffff0000ff003300f0f0f0f0ccccccccaaaaaaaa000000ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0e0c0e0cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30003030ff00ff00f0f0f0f0f0000000ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa77003300ff00ff00f0f0f0f0eeee0000ccccccccaaaaaaaa0e0e0e0e
def HC5_5_5 : Nat := 0x43b8f3f0436648c042c0dbf040da249040976a0040910a803eff1e603ee208a03ea681303e9bbcf03e6bd9603e4a0af03e237f903d6bed903d0190903ce18a103c8f35403bcfef303b9d05603b672d803b4df7603acaa4003aaf66c03a08857039da51a039bb4c80392326d03865533038315040381a912037fe812037be7af
def SC5_5_6 : Nat := 0xffff0000ff00ff00f0f0f0f0cccccccca8a8a8a844444444ffff0000ff00ff00fafafafaccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f3a2f3a2f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa0f00ff0000f000f0ffff0000ff000000f0f0f0f0ccccccccaaaaaaaa00cc00ccffff0000f000f000ccccccccc0c0c0c0aaaaaaaa0000ff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f00000000ff00ffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaa0000f0f0ff00ff00f0f0f0f0cccc0000aaaaaaaa2222222200002222ffff0000ff00ff00f0f0f0f0cccc8888aaaaaaaa50505050ffff0000ff00ff00f0f0f0f0cccccccca0aaa0aa0a000a00ffff0000ff00ff00f0f0f0f0cccccccca8aaa8aa0f000f00ffff0000ff000f00f0f0f0f0ccccccccaaaaaaaa00cc00ccffff0000f0f0f0f0ccccccccaaaaaaaa00ee00ee00ee0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa3f3f0c0cffff0000ff00ff00ccccccccaaaaaaaa0f0a0f0a03020302ffff0000f0f0f0f0f0f00000f000ff00ccccccccaaaaaaaaffff0000ff00cc00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ffaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff003f00f0f0f0f0ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa1f001f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa77335500ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5f5f4c4cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000a000ffff0000ff00ff00ff000000f0c0c0c0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0aaaaaaaa33333232ffff0000ff00ff00f0f0f0f0cccccccccc00cc0055554444ff00ff00f0f0f0f0ccccccccaaaaaaaa00f0f0f00000aaaaffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa00fa00faffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaaaa00aa00ffff0000ff0aff00f0f0f0f0ccccccccaaaaaaaa0a0a0000ffff0000ff005f00f0f0f0f0ccccccccaaaaaaaaa0a0a0a0
def HC5_5_6 : Nat := 0x52b796b051ddb57051cd8e0051c092a051a8238051684cc0514a4e905138a5e050f380c050b649e0504650704e81de204e75ab604da3bbf04b886bd04b6307b049cf7470491c77a0490ef9e048f9a54048d2e7a048467b40482f51404751c96046c26f9046a9ddf046246ea045d70c3045676620453f20b044f559104403c1c
def SC5_5_7 : Nat := 0xff00ff00ccccccccaaaaaaaa0f0c0f0c0000ffccff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa3f3f0000ffff0000ff00ff00ccccccccaaaaaaaa0f000f0000ff00f0ffff0000f0f0f0f0dd00dd00aaaaaaaa3300330022222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8080ccccffff0000ff00ff00f0f0f0f0f000f000cccccccca888a888ffff0000ff00ff00f0f0f0f0aaaaaaaa3333222203030202ffff0000ff00ff00f0f0f0f0aaaaaaaa8888888833332222ffff0000ff00ff00f0f0f0f0eecceecccccccccc88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4040c0c0ffff0000ff00aa00f0f0f0f0cccccccccccc0000aaaaaaaaffff0000ff00cc00f0f0f0f0f0f0c0c0ccccccccaaaaaaaaffff0000ff00ff00ff00fa00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0cfcf0000ccccccccaaaaaaaa0000ff00ffffaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0c0f0cffff0000fc00fc00f0f0f0f0ccccccccaaaaaaaa0000fc00ffff0000ff00ff00fcffccccf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccfccccccccccaaaaaaaaffff0000ff00aa00f0f0f0f0ccccccccaaaaaaaa00cc44ccffff0000ff00ff00f0f0f0f0c8c8c8c8aaaaaaaa0000f0f0ffff0000ff00cc00f0f0f0f0ccccccccaaaaaaaa0000cc00ffff0000ff00ff00f5a0f5a0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888cc88ffff0000ff00ff00f0f0f0f0cccc8888aaaaaaaa00ff00aaffff0000f0f0f0f0cc44cc44aaaaaaaa00cc00cc00aa00aaffff0000fc00fc00f0f0f0f0ccccccccaaaaaaaa44444444ffffff00ff000000f0f0f0f0ccccccccc0c0c0c0aaaaaaaaffff0000fff0fff0ff005500f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccc8888aaaaaaaa00cc00ccff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa4444ccccff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f0f0f0ffff0000f0f0f0f0ececececec00ec00ccccccccaaaaaaaa
def HC5_5_7 : Nat := 0x5dc279c05da204d05d3aae805c9845e05bbc4d205ba602e05b798d605b300b605a43b1705a08cfb059fab28059e2ebf058c1f020589c10e05860479057b7c6f0577408505767edc056e2808056d0f54056b67c80569ff2805668e330565badc056171c0055ab2e30551e4fe054d704f0544f2450543d87d053325de052c2eeb
def SC5_5_8 : Nat := 0xffff0000ff00ff00f0f0f0f0cfcfccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0f0f0f050ccccccccaaaaaaaaffff0000ff000000f0f0f0f0dd00dd00ccccccccaaaaaaaaffff0000ff00ff00fcfcececf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22000000ffff0000ff00ff00ff005000f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0cc00cc00aaaaaaaa2222222222002200ffff0000ffccffccff00ff00f0f0f0f0cccc8888aaaaaaaa00000000ffff0000ff00ff00f0f0f0f0c8ccc8ccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00eeff00ff00ff000000f0f0fcfcf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa330033000022002200000000ffff0000f0f0f0f0cc00cc00aa00aa0088888888ffff0000ff00ff00f0f0f0f0ccccccccbbbbaaaa50505050ffff0000ff00ff00ccccccccaaaaaaaa0a0a0a0a05050000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa0aaa0affffff00ffaaaaaaff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0a0f0a0000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa005000f0ff00ff00fcfc0000f0f0f0f0ccccccccaaaaaaaa54540000ffff0000ff00ff00f0f0f0f0cccccccca8a8a8a80c0c0c0cffff0000ff00ff00f0f0f0f0ee00ee00ccccccccaaaaaaaaffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f00ffff0000ffccffccff000f00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa88aa8800330000ffff0000ff00ff00f0f0f0f0ccccccccaabb0000aaaaaaaaffff0000ff00cc00f0f0f0f0ccccccccaaaaaaaa00ff00ccffff0000ff00ff00f0f0f0f0cccccccccc004400aaaaaaaaffff0000fcf0fcf0f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000f0f0f0f0ccccccccaaaaaaaa00cc000000aa00aaffff0000f0faf0faf0f0f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500
def HC5_5_8 : Nat := 0x6a1ed51069562d20693c31c068e7ba0068afdc5067d77f1066bc25b0658d7e30657dd25065380c706490ee40641802f063a1dd206336115062a47c8061fe1030614bbfb060d04d7060ad25706089a8606015e4b05fe0c8305fba5af05fb405405f8fa8a05f5a09705f3625a05efabbe05ecb5ff05dfaaab05df9d4405dd6689
def SC5_5_9 : Nat := 0xff00ff00f0f0f0f0eeaa0000cccccccccc00cc00aaaaaaaaffff3030ff00ff00f0f0f0f0ccccccccaaaaaaaa33330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55445500ffff0000ff00ff00ccccccccaaaaaaaaa0a0a2a20f0f0c0cffff0000ff00ff00f0f0f0f0cceecceeaaaaaaaa88888888ffff0000ff00ffaaf0f0f0f0ccccccccaaaaaaaa0000ff00ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa55005500ffff0000f0f0f0f0ccccccccaaaaaaaa3300ff0000cc00ccffff0000ff00ff00f0f0f0f0cccccc00aaaaaaaa22222222ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa0aaa00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22ee22eeffff0000ff00ff00f0f00000ccccccccaaaaaaaa000a000aff00ff00f0f00000ccccccccaaaaaaaa00f000f00000cccc00000000ff00ff00f0f0f0f0eeff0000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa54545454ffffccccffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaaffff0000ffaaffaaff00ff00f000f0f0ccccccccaaaaaaaaffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaa8888ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff00000000fcfcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f00ff00ffff0000f0f0f0f0ccccccccaaaaaaaa3300330000ff00ccffff0000ffaaff00f0f0f0f0ccccccccaaaaaaaa00aa0000fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0ff0000f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa6666666600000000ffff0000ff00ff00cccccccc554455440f0c0f0c00000000ffff0000ff00ff00f0f0f0f0cccccccc66666666ffff0000ff11ff00f0f0f0f0ccccccccaaaaaaaa33330000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa00f0f0f0ff00ff00f0f0f0f0ccccccccaaaaaaaa050500000000fafa00000000ffff0500ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0bbaabbaaaaaaaaaa33223322
def HC5_5_9 : Nat := 0x7a5ec2f079910680795ec9c078f87c707677fc307649f68076132e6074bff5507479b8907397fc4072f949d071a443207168e7907113022070f8b2f06fc399106f86c9d06f37be106ef8ab306ee07ee06ebf31f06e6e47106e6af2706e532f106de232f06daf31c06daefac06cae5c906c715b206c593a306c1fa3f06c1f048
def SC5_5_10 : Nat := 0xffff0000ff00ff00f0f0f0f0cccccccc55aa55aaffff0000ff00ff00f0f0f0f0aaaaaaaa3333303022222222ffff0000fa00fa00f0f0f0f0ccccccccaaaaaaaa05050000ffff0000ff00ff00f0f0f0f0eeaaeeaaccccccccaa00aa00ffff0000ff00ff00f000f000ccccccccaaaaaaaa08080808ffff0000ff00ff00f0f0f0f0eeeeeeeea0a0a0a088888888ffffff00fffff0f0ff000000f0f0f0f0ccccccccaaaaaaaaffff5544ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000fffaf0f0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccacacacacaaaaaaaaa0a0a0a0fff00000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000f0f0f0f0ccccccccaaaaaaaaaa00aa0077007700ffff0000ff00ff00f8f8f8f8ccccccccc0c0c0c0aaaaaaaaffff0000ffccff00ff000000f0f0f0f0ccccccccaaaaaaaaffffaa88ffff0000ff00ff00f0f0f0f0ccccccccaa88aa88ffff0000ff00ff00f0f0f0f0cc00cc00aa00aa0088888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30307070ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000c0000ffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaa0e0e0e0effff00ccffff0000f0f0f0f0ccccccccaaaaaaaa00ff00ccffff0000fcccffccf0f0f0f0f000ff00ccccccccaaaaaaaaffff0000ff00ff00f0f0fff0ccccccccc0c0ccc0aaaaaaaa00000000ff00ff00f0f00000ccccccccaaaaaaaa00ff00f0ffff0000ff00ff00f0f0f0f0888888883333000022222222ffff0000ff00dd00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00fcf0fcf0f0f0f0f0ccccccccaaaaaaaa00000000ffff00f0ff00ff00f0f000f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa222222220000fafaffff0000ff000000f0f0f0f0ccccccccaaaaaaaaaaaaaa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa00a0ffffaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaa2222
def HC5_5_10 : Nat := 0x891441a0887346c088410ca087f6cc1086e090f086d021e086a7b840866675608620a02085809f00851fd9508435bee0842b0db083a51f40831041f082a880c0828a9df080de975080a06cc08057a8b0804e7c607e7452d07d43d7307d3803b07c5065907c3ffdc07beb4c307b9ff2607b4b7ae07b301c907afcaab07a7e49b
def SC5_5_11 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4c4c4444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00330022ffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaa0a0a0a0affff0000f0f0f0f0f000ff00ccccccccaaaaaaaaa000aa00ff00ff00f0f0f0f0ccccccccaaff0000aaaaaaaa55000000ffffff00f0f0f0f0ccccccccaaaaaaaa00ff00000000f0f0ff00ff00f0f0f0f0f0000000ccccccccaaaaaaaaaaaa0000ffffff00ffff0a0aff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaa30303030ffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccababaaaa03030000ffffccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaa88ffff0000f0f0f0f0ccccccccaaaaaaaa00f000000000ff00ff00ff00f0f0f0f0ccccccccaaaaeeeeaaaaaaaa0000aaaaffffff00ffff0000ff00ff00f0f0f0f0cccccccc5555555000000000ffff0000ff00ff00f0f050f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccceeeeaaaaaaaa0000ccccffff0000f0fff0f0ccccccccaaaaaaaa0f000f0000ff0000ffff0000ffccffccff00ff00f0f3f0f0ccccccccaaaaaaaaffff0000fc00fc00f0f0f0f0f000f000ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaaa0a0a0a00ccc0cccffff0000ff00ff00f0f0f0f0ddddcccccccccccc88888888ffff0000ff00ff00fafaf0f0ccccccccaaaaaaaa0f000f00ffff0000ff000000f0f0f0f0ccccccccaaaaaaaaaaaa00aafff0fff0ff00ff00ccccccccaaaaaaaa0f0f00000000ff00fffffffaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa0f0f0c0c00ff00ccffff0000ff00ff00f0f0f0f0f0c0f000ccccccccaaaaaaaaffffaaaaffff5050ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccceeeeaaaaaaaa00008888ffff0000ff00ff00f0f0f0f0f000f000cccccccca8a8a8a8ffffcc44ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_5_11 : Nat := 0x9614470093f086d093df197092c19b80926e02c09241756091d38ed091ae10409198fdf091545eb090bdc60090a4ff308fa98c908f1f3db08e421df08df82f908d3820708d2c94208cf74fe08cc10b508c8570108c42b9108c2d8dc08bf3e4d08b4d52b08b483b808a742ee08a5ee7c08a3802a089d2879089cd73d0895ad1a
def SC5_5_12 : Nat := 0xffff0000fffafffaff00ff00f0f0f0f0ccc8ccc8aaaaaaaaffff0000ffaaaaaaff00ff00f0f0f0f0ccccccccaa00aa00fffff0a0ffff0000ff00ff00f0a0f0a0ccccccccaaaaaaaaffff3300ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaaffaaffaaff00ff00fafa0000f0f0f0f0ccccccccaaaaaaaaffff0000fff0fff0ff00ff00ccccccccaaaaaaaa0f00ff00ffff0000ffa0a0a0ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ff00ff00f0ff0000ccccccccaaaaaaaa0c0c0c0cfffafffaff00ff00fafa0000f0f0f0f0ccccccccaaaaaaaaffffa0aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0cc00cc00aaaaaaaa00ff000000cc00ccffff0000ff00ff00f0f0f0f0aaaaaaaa3030303022222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa2020ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaaaaaa222200000000ffff0000f0f0f0f0ee00aa00ccccccccaaaaaaaaffff0000fc00fc00f0f0f0f0ccccccccaaaaaaaa33330000ff00ff00f0f0f0f0cccccccccccc4444aaaaaaaa0000f0f0ffff0a0affff0000ff00ff00f0f00000ccccccccaaaaaaaaffff0000ffaaffaaff00ff00ccccccccaaaaaaaa0f0e0f0effff0000f0f0f0f0f000f000ccccccccaaaaaaaa00000f00ffff0000f500f500f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00fdf0fdf0f0f0f0f0ccccccccaaaaaaaaffff0000f000f000ccccccccaaaaaaaaaa00aa00a0a0a0a0ffff0000ff00ff00fefefefef0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa888888880000ffaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000fff00000ccccffff0000f0f0f0f0ccccccccaaaaaaaa0c000c0000ff0000ffff0000ff00ff00f0f0f0f0cccccccc4444444422220000fffa0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccc0c0f0f0aaaaaaaa3030303000000000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ffff00fffafffafffa0000ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_5_12 : Nat := 0xaa826c40a9d285a0a9cca7e0a9947860a99232c0a8e38300a8a3c880a83259c0a8215130a807a220a74c5530a6445810a5a8c8d0a485c190a278cf30a24509f0a0df2790a06ded10a0604f40a016fcb09e8ad7509d2d06509ce6f9809c76bca09c593dc09b4d30609b0eb6409a14fbb099300e109807efa09800ad2097bf2c8
def SC5_5_13 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000f8f8ffff00f0ff00ff00f0f0f0f0cccccccccc0ccc0caaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0fccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00cc00f0f0f0f0ccccccccaaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4c4c0c0cffff0000ff80ff80f0f0f0f0ccccccccc0c0c0c0aaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaafffff0f0ffff0000ff00ff00f8f8f8f8ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f0a0a000f000affff0000ff00ff00f0f0f0f0ccccccccaaaaffeeaaaaaaaaffff0000ff00ff00f0f3f0f0f0f0f0f0ccccccccaaaaaaaaffff0000fcfcfcfcfc00fc00f0f0f0f0ccccccccaaaaaaaaff00ff00fcfc0000f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaffaaaa00550000ff00ff00f0f0f0f0dddd0000ccccccccaaaaaaaaaaaa0000ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa30303030ffff0000ff00ff00fcfcfcfcf0f0f0f0cccccccca8a8a8a8ffffff00ffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaa000000f0ffff0000ff00ff00fafafafaf0f0f0f0cccccccca0a0aaaaffff0000ffccffccff00ff00f0d0f0d0ccccccccaaaaaaaafffff0fcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33333330ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00a0f0f0ffffaaaaffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0ef0f0f0f0eeeeeeeeeeee0000ccccccccaaaaaaaa00ee00ee00000000ff00ff00fafaf0f0f0f00000ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa888888880000eeeefff00000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8f008f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaa000000aaaa
def HC5_5_13 : Nat := 0xb90d0490b8f7f600b8c6c390b8a06f10b83182d0b76061e0b7100570b6b9b7b0b5b47610b513f440b4e3f240b4cc10c0b4a2ce90b49009d0b47cbbb0b4024ad0b31b1c70b1af3710b1ad6360b185da20afc513c0aefa4d70aebea930ae602d30adf76200ad0ae180acda2180ac2ae2f0abdc5780abba2840aacd5020aa9451a
def SC5_5_14 : Nat := 0xffff0000ff00ff00f0f0f0f0cccccccc5544554422222222ffff0000ff00ff00faaafaaaccccccccaaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0f0cccccccca0a0a0a08888aaaaffff0000f0f0f0f0ccccccccaaaaaaaa3300330000cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88888800ffff0000ff005f00f0f0f0f0ccccccccaaaaaaaa0000a0a0ff00ff00f0f00000ccccccccaaaaaaaa0c0c0c0c0000aaaaffff0000fff0fff0ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0e0e0e0e0aaaaaaaa88888888ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0c8c8c8c8aaaaaaaa50505050ff00ff00faaafaaaf0f0f0f0ccccccccaaaaaaaa0000faaaff0f0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000fff0fff0ff000f00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ee00aa00ccccccccaaaaaaaaffff0000ff00ff00eaeaeaeaccccccccaaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0f0ccccc0c0cc00cc00aaaaaaaaffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaa00cc00ccffff0000feaafeaafc00fc00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccc0c0c0c0aaaaaaaa0f0f0f00ffff0000ff00ff00f0f0f0f0cccccccca0a0000088888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0e0a0e0ffff0000ff00ff00ccccccccb0b0b0b0aaaaaaaa04040404ffff0000ff00ff00f0f0f0f0ddddccccaaaaaaaa44444444ffff0000ff00ff00f0f0f0f0cccccccccc00cf00aaaaaaaaffff0000ff00ff00f0f0f2f2f0f0f0f0ccccccccaaaaaaaaffff0000ff050000f0f0f0f0ccccccccaaaaaaaa00fa00faffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000404ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000e0effff0000ff00ff00f0f0f0f0c0c0c0c0aaaaaaaa08080808ffff0000ff00ff00ccccccccc8c8c8c8aaaaaaaaa0a0a0a0ff00ff00f0f0f0f0ccccccccaaaaaaaa222222220000ffcc
def HC5_5_14 : Nat := 0xc9437290c8b98270c85521e0c7ba8f20c6e4c610c6bdb200c6b34f70c4be4260c49ad910c4013920c24d2600c2107ad0c1d77d40c18bca40c17f72d0c16263d0c06a15e0c04db110bfc7e0e0bfc1d7c0bf8f2270be3e8650bdc9a690bd5981a0bcb22d80bbf67ca0bb965b10bb12a810baa034a0ba5ea0b0ba42a5c0b956ba9
def SC5_5_15 : Nat := 0xffff0000ff00ff00faaa0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0ff0f00f0f0000ffff0000ff00ff00f0f0f0f0f030f030ccccccccaaaaaaaa00000000ffff0022ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa00aa0054545454ffff0000ffccffccff00ff00f0f0f0f0cc88cc88aaaaaaaaffffaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f0a0affff0000ff00ff00ccccccccaaaaaaaa8080808070707070ffff0000ff00ff00f3f03300f0f0f0f0ccccccccaaaaaaaaffffff00ff000000f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00fcfcfcfcccccccccc0c0c0c054545454ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005000ffffaaaaff00aa00f0f0f0f0ccccccccaaaaaaaaaaaa0000ffff0000ff00ff00f0f0f0f0ccffcccccccc0000aaaaaaaa00000000ffffff00ff000000f0f0f0f0ccccccccaaaaaaaaffffcc88ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ff000000f0f0f0f0aaaaaaaa33332222ffff0000f000f000ccccccccaaaaaaaa00f000f00000ff00ffff0000ff00ff00f0f0f0f0cccccccc5050000044444444ff00ff00f0fff0f0f0f00000ccccccccaaaaaaaa00ff000000000000ffffff00ff000f00f0f0f0f0ccccccccaaaaaaaaffff0000ffccccccf0f0f0f0cccccccccc00cc00aaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa8c8c8c8c44444444ffff0000ff0fff00f0f0f0f0ccccccccaaaaaaaa88888888ffff0000f0f0f0f0ccccccccaaaaaaaa1111000000ee00eeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0aaaaaff00ffccf0f0f0f0ccccccccaaaaaaaa0000ff000000ccccffff0000f0f0f0f0ccccccccaaaaaaaa00ee00ee000e000effff0000ff00ff00ccccccccaaaaaaaa0f0f00000c0c0c0cffff0000f0f0f0f0ccccccccaaaaaaaa3300330000ff00aaffff0000ffccffccff00cc00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc5555444450504040
def HC5_5_15 : Nat := 0xd386ddd0d3243f80d287d7d0d1c14f30d1bc3eb0d18c0af0d1853400d17d7000d15ec260d0dd34e0d0d125e0d0c69020d06d01c0cf896d50cef67d80cdbf2810cd3e0c20cd2731c0cceb9510cc308cf0cbc40560cb621c60cb524b80cb2ca620cabc6410ca9c9cd0ca8cf2b0ca228790c9da15b0c9c71890c96fdcb0c94fbd7
def SC5_5_16 : Nat := 0xffffff00ffff0000ff00ff00f0f0f0f0ccccccccaa88aa8800000000ffff0000ff00ff00f0f0f0f0cccc8888aaaa0000ffff0000ff00ff00f0f0f0f0bbbbaaaaaaaaaaaa22222222ff00ff00f0f0f0f0cccccccccccc0000aaaa000044444444ffff0000ff22ff22f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f500f500ccccccccaaaaaaaa0c0c0c0cffff0000ff00ff00f080f080ccccccccaaaaaaaa88888888ffff2222ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaff00ff00f0f000f0ccccccccaaaaaaaa00ff00000000ff00ffff0000ff00ff00f0f0f0f0cccccccca8a8a8a857005700ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00008080ffff0000ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa33223322ffff0000ff00ff00fafafafaf0f0f0f0eeeeeeee88888888ffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0c0c0c0c08888888850505050ffff0000f0f0f0f0dd00dd00ccccccccaaaaaaaa33003300ffffff00ffff0000f0fff0f0ccccccccaaaaaaaa00ff0000ffff0000ff000000faf0faf0f0f0f0f0ccccccccaaaaaaaaffff0000ff000000f0f0f0f0ccccccccaa00aa0000aaaaaaff00ff00fcfc0000f0f0f0f0ccccccccaaaaaaaa02020202ffff0000ff00ff00f0f0f0f0ccccccccaa00bb0055554444ffff0000ff00ff00f0f0f0f0cfcccfccaaaaaaaa22222222ffff0000fc00fc00f0f0f0f0ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0c0f0c0ccccccccaaaaaaaa55445544ffff0000f0f0f0f0cccccccccccccc00aaaaaaaa00f000f0ffffccccf0f0f0f0cccccccccccc0000aaaaaaaa00ff00ccffff0000ff00ff00ccccccccc0c0c0c0a0a0a0a088888888ffff0000ff00ff00f0f0f0f0cccccccca8a8a8a80000ccccffff0000ff00ff00f0f0f0f0aaaaaaaa30f030f022222222ffff0000ff00ff00f0f0f0f0ccccccccbaba3030aaaaaaaaffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa0e000e00ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa00002222
def HC5_5_16 : Nat := 0xe93ef000e8c280d0e8b14bb0e8547610e7a83150e4e53d60e3b75c60e38f7cd0e353a9e0e2b3ae90e2239000e07c9b10e0699ab0e0664600e054d900df4e9d60df1f9c90df071ce0dedfea10de0139f0ddbe7cd0dcd8dbb0dac3b540da735600da1023d0d9c30fe0d84a58c0d7d01dc0d51d4bf0d5074480d4c08990d3a9d84
def SC5_5_17 : Nat := 0xffff0000ff000f00f0000000ccccccccaaaaaaaa0000f0f0ffff2200ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00fafafafaf0f0f0f0ccccccccafaaafaaffff0000f0f0f0f0f000f0f0ccccccccaaaaaaaa00cc00ccffaa0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccccccccc00aaaaaaaaffff0000f0f0f0f0ccccccccc0c0c0c0aaaaaaaa00fc00fcffff0000ff33ff22ff00ff00f0f0f0f0aaaaaaaa33332222ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f000000fafaffff0000ff00ff00f0f0f0f0cccccccc545454540000fcfcfffff0f0ffff0000ff00ff00ccccccccaaaaaaaa0fff00f0fffffff0ffff0000ff00ff00f0f00000ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c0c0c0000fcfcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa05005500ffff0000ff00ff00f5f0f5f0ccccccccaaaaaaaa0c0c0c0cffff0000ff00ff00f0f0f0f0ddddccccaaaaaaaa44440000ffff0000ff00ff00f0f0f0f0cccccccccc00cc0caaaaaaaafffff0f0ffff0000ff00ff00ccccccccaaaaaaaa0f0f0f0000000000ffff0000ff00aa00ccccccccaaaaaaaa0f0f0a0affff0000ffaaffaaf0f0f0f0ccccccccaa00aa0044444444ffff0000ff00ff00f0f0f0f0ccccccccaaff000088888888ffff0000ff00ff00ccccccccaaaaaaaa0f0000000a0a0a0affff0000ff00ff00f0f0c0c0ccccccccaaaaaaaa0000aaaaffffff00ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeceeececcccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0affaaffffff00ff00ff00ff000f00f0f0f0f0ccccccccaaaaaaaaffccccccffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0000fcfc0000fc00ffff0000f0f0f0f0ccccccccaaaaaaaaaa00ff0000cc00ccffffccccffff0000ff00cc00f0f0f0f0cccccccc55554444ffff0000f0f0f0f0cccccccccc00cc00aaaaaaaa22002200
def HC5_5_17 : Nat := 0xf91e6060f87faa00f7e29c60f75fc9b0f7354d30f7301010f6a7dbb0f65fbc50f6208920f60ef080f5ac4550f57f3c70f568b550f5431ea0f4994f00f3f502d0f24df320f14b4020f0510e30f010e5b0efa7bcd0ef9e4390ee435e60edfd2120ec815dc0ebf545d0eacaa900eac2a130ea170010e9a935e0e99f25d0e9727d3
def SC5_5_18 : Nat := 0xffff0000ff00ff00f0f0f0f0ddddccccaaaaaaaa33330000ffff0000ff000000f0f0f0f0ccccccccaaaaaaaa0000fff0ffff0000ff00ff00f0f0f0f0cf0fcc00ccccccccaaaaaaaa00000000ffff0000f0f0f0f0ccccccccaaaaaaaa33cc33cc00000000ffff1100ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f4f4f4f4ccccccccaaaaaaaa50505050ffffccccffff0000ff00ff00f0f0f0f0cccceeeeaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa04040404ffff0000ff00ff00f0f0f0f0ccfcccfcaaaaaaaa00c000c0ffffc0c0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ccccffff0000ff22ff22ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccf0ccf0cccccccccc00cc00aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0fcf00ccffff0000ff00ff00f5ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00cccccccca0a0a0a00c0c0c0c0a0a0a0affff0000ff00ff00f3000000f0f0f0f0ccccccccaaaaaaaaffff0000ff50ff50f0f0f0f0ccccccccaaaaaaaa00ff0000ffff0000f0f0f0f0f0ccf0ccccccccccaaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa8888ffff0000ff00ff00f8f8f8f8ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0f0f0eaeac0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c00cc00ffff0000ff00ff00fdfdccccf0f0f0f0ccccccccaaaaaaaaffff0000fffafffafff0fff0f000f000ccccccccaaaaaaaaffff0000ffccffeeff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0a0f0a0a0a0a0affff0000f0f0f0f0ccccccccaaaaaaaa00ff00f000000f00ffff0000ff00ff00f0f0f0f0c8c8ccccaaaaaaaa05050000ffff0000ff00ff00f0f0f0f0ccccccccafafaaaa55550000ffff0000ff00ff00f0f0f0f0ccccccccbbbb8888aaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaaaa00aa0000cc0000ffff0000ff00ff50f0f0f0f0ccccccccaaaaaaaa0000f0f0
def HC5_5_18 : Nat := 0x109f35d6109815a810935ac31077cfbf107796a610722a2110603908105bc2b41050866c104dca3e104c81d91047b2ac102e9a27102c7cde102a55d4102262d210185bc110123d4f100ba56a0ffe9f2b0ff6fab50ff4f9870ff32eb30fef559a0feb53750fdb73de0fbcf7a20fb65c4b0fab8cf50f9f208d0f9ade1e0f98fdb9
def SC5_5_19 : Nat := 0xffff0000f0f0fff0ccccccccaaaaaaaa00ff00000000ff00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22222020ffff0000ff00ff00f0f0f0f0eeeeffeeccccccccaaaaaaaaffff0000ff00dd00f0f0f0f0ccccccccaaaaaaaa2222222200000000ffff0000ff00ff00f0faf0f0ccccccccaaaaaaaa00000000ffff0000ff000a00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa8c8c8c8c33330000ffff0000ff00ff00f0f0f0f0aaaaaaaa4c4c4c4c22222222ffff0000ff00ff00c0c0c0c0aaaaaaaaa0a0a0a00c0c0c0cffff0000ff00ff00f0f0f0f0aaaaaaaa303030300c0cccccffff0000ff00ff00f0f0f0f0cc00cc00aaaaaaaa88cc88ccff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaa0aaa0aaffff0000ff00ff00f0f0f0f0ccccccccaaffaa00aaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc88aa88aa22002200ffffaaaaffff0000ff00ff00f0f0f0f0cccccccc55554444ffff0000ff00ff00f0f0c0c0cccccccccccc0000aaaaaaaa00000000ffff0000f0c0f0c0ccccccccaaaaaaaa00cc00ccffff0000fa00fa00f0f0f0f0ccccccccaaaaaaaa0f000f00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff00000000aaffff0000f0f0f0f0ccccccccaaaaaaaa5555000000ee00eeffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff30f0f0f0f0ccccccccaaaaaaaa00003030ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa0000aaaaffffff00ff000000f0f0f0f0cccccccccccccc00aaaaaaaaffff0000ff00ff00ff00aa00ccccccccaaaaaaaa0f0f0a0affff0000ff000000f0f0f0f0ccccccccaaaaaaaa0f0f0f00ffffff88ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000fff0fff0ff00ff00f030f030ccccccccaaaaaaaaff00ff00f0f0f0f0ccccffccaaaaaaaa0000ff000000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33333030ffff0000ff00ff00f0f05050ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f000f00000000f0
def HC5_5_19 : Nat := 0x11cd0bb211cada2811c8da9611b9ffcc11b37b4611aea13f117ec2741176b398116bf6f5115e357f115a39e9115963d211592ac2115929481158d8b8114ddad511295976112085b911148ee7110e27db110496bc10fc783910fc57ce10f6cd5e10f57b1d10d9b8bf10d25b3810c8adbf10c3462a10b299e410b24f4310a128c2
def SC5_5_20 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000a0ffff0000ff00ff00f0f0f0f0e0e0f0f0ccccccccaaaaaaaaffff0000ffaaffaaff00ff00f0f0f0f0ccddccccaaaaaaaaffff0000ff00ff00eeeeeeeeccccccccaaaaaaaa0f0f0e0effff0000ff00ff00f0c0f0c0ccccccccaaaaaaaa50505050ffff0000f500ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4444ff44ffff0000ff00ff00ccccccccaaaaaaaaa8a8a8a80c0c0c0cffff0000f0f0f0f0eeeeeeeeccccccccaaaaaaaa00ff00ccffff0000fff0fff0ff00cc00f0f0f0f0ccccccccaaaaaaaaffff8888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaaa2a2ffff0000ff00ff00f0f0f0f0cccccccc5544554400440044fffff0f0ffff0000f0f0f0f0ccccccccaaaaaaaa00fc00fcfffff000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff0cff0cf0f0f0f0ccccccccaaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33f300f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33cc33ccff00ff00fdfd0000f0f0f0f0ccccccccaaaaaaaa02020202ffff0000ffc0ffc0ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fffcffff0000f0f0f0f0ccccccccaaaaaaaa00ff00cc00002222ffff0000ff00ff00fcfc00fcf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f000f0ccccccccaaaaaaaaa0a0a0a0fff0f0f0ff00ff00ff000000ccccccccaaaaaaaa0f0f0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaa0000fcfcffff0000ff00ff00f5f0f5f0f000f000ccccccccaaaaaaaaffff0000f0f0f0f0ccff0000cccccccccc00cc00aaaaaaaaff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa0000eeeeffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa0000cc00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55dd00cc
def HC5_5_20 : Nat := 0x12f042b212eb9f4412e12d9b12e07b6d12e0360912d0f0dd12cd960912b9b81612b53e6712b47a1b12996f521298907712862b3d12843a41128314411278585c1273dc1a126881e2126839f91258abc91257e11f1251f5cb123e7443121263ed1210de7511f469e611f2044711e50de211e208be11dea58411de370a11d88546
def SC5_5_21 : Nat := 0xffff0000ff00ff00f0f0f0f0aaaaaaaa3333222233003300ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55550500ffffff00f0f0f0f0f000f000ccccccccaaaaaaaa0000f0f0ffff0000f0f0f0f0ccccccccaaeeaaeeaaaaaaaa00ee00eeffff0000ff00ff00f0f0f0f0cccccccc8888888822aa22aa00000000ffff0000ff00ff00f0f0f0f0aa88aa8833003300ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa30303030ffff0000ff00ff00f0f0f0f0dcdcdcdccc00cc00aaaaaaaaffff0000ff00ff00f0f0a0a0ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f0ccccccccaa88aa8822002200ffff0000ff00ff00ccccccccaaaaaaaa0fff00f000f000f0ffffffccffff0000ff00ff00f0f0f0f0cccccccc5555444400000000ffff0000ff00ff00ccccccccaaaaaaaa0fff00f0ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaa0000fcccffff0000ff0fff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa44444444ff00ff00f0f000f0ccccccccaaaaaaaaaaaa00000000ff00ffff0000ff00ff00f0f0f0f0cccccccccc04cc04aaaaaaaaffff00fcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f0f0000f000f0ffff0000f0f0f0f0ccccccccaaaaaaaa888888887700ff00ffff0000ff00ff00ff000a00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0f0c0cffff0000f0f0f0f0ccccccccaaaaaaaa5555000000fa00fa00000000ffaa0000ff00ff00f0a0f0a0ccccccccaaaaaaaaff00ff00f0f0f0f0f0000000ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa03000000fffffff0ffff0000ff0fff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f000000ffccffff0000ff00ff00f0f0f0f0cccccccca0a0a0a02a2a2a2affff00f0f0f0f0f0ccccccccaaaaaaaa00f000f000cc00cc00000000ffff0000ff80ff80f0f0f0f0ccccccccaaaaaaaa
def HC5_5_21 : Nat := 0x1435077c1432d0b6142690ea1422c7421421954f141f0cf314137756141339c8140ef649140648ea13fe1c1f13e10be513dfb0a913dd12e413d3aa6e13d12f5413d0ca7913c219ab13bedad413b80bcc13ab8350139f0b7913768447137667671368401513644d4513636747135fce561342bc8d1341dce41325b64f130e8331
def SC5_5_22 : Nat := 0xffff0000ffaaf0a0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa008c008cff00ff00f0f0f0f0ccccccccaaaaaaaa303000000000ccccffff30f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0808ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000fefefefef0f0f0f0ccccccccaaaaaaaa00fc00fcffeeffeeff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffeeffff0000ff00ff00f3f0f3f0ccccccccaaaaaaaa03000300ff00ff00ff000000f0f0f0f0cccc0000aaaaaaaa88888888ffff0000f0f0f0f0f0f00000ccccccccaaaaaaaa00ee00eeff330000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff0000ffff0000ff80ff80ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa03030300ffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccdcdcccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f000000ff00f0ffff0000ff00ff00f0f0f0f0eeccffccccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000e0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc4444444411001100ffff0000ff00ff00ccccccccaaaaaaaa555500000f0f0c0cffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaa50505050ffff0000f000f000cccccccccc00cc00aaaaaaaaa0a0a0a0ffff5500ff00ff00f0f0f0f0ccccccccaaaaaaaa55000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0e000e00ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa0c0c0c0cffff0000ff00ff00f3f30000ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00ccccccccaaaaaaaa404040400a0a0a0affcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff00ffffff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fafaffff0000ff00ff00f8f8f8f8f0f0f0f0c8c8c8c8aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22ff0000ffff0000ff00ff00f0f0f0f0cccccccc554455440f000f00
def HC5_5_22 : Nat := 0x15ddfdc415cfe72715acb94f159494b91583850c1563d0e41542e051154239ce154143b3151d147b1510ade514feed6b14fc173714f7b51314f4d9fe14f4a22414f2aece14e4571414e0b55e14d959c814be276c14bd093c14ba9f9014aa01cb14a7143414a6720114a467b91487f47e14813919146429ed1455036f1441880d
def SC5_5_23 : Nat := 0xff00ff00ff000000f0f0f0f0ccff0000ccccccccaaaaaaaaffff0000f0fff0f0ccccccccaaaaaaaa00ff00000000ff00ffffff00ffff00ccff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0f000ff00f000f000ccccccccaaaaaaaaffff0000ff33ff00ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc5a5a5a5a0a0a0a0affff0000f0f0f0f0ccccccccaaaaaaaa00fc00fc00f000f0ffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaa0000cc88ffff0000ff00ff00f2f20000f0f0f0f0ccccccccaaaaaaaa00000000ffff0000f0f0f0f0ccccccccaaaaaaaa00fc00fcffff0000ff00ff00f0f0f0f0babababa3030303022222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa88ffff0000ff00ff00ccccccccaaaaaaaa888888880f080f0800000000ffff0000ff00ff00f0f0f0f0cccccccca8a88888ff0f0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eaeaeaeacccccccc5050505000000000ff000f00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000fcfcfcfcf0f0f0f0cccccccca8a8a8a800fc00fcffff0000ff00ff00f0f0f0f0ccccccccbbbbaaaaaaaaaaaa00000000ffff0000f0f0f0f0cc88cc88aaaaaaaa00aa00aaffff0000ff00ff00f0f0f0f0f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00ccccccccafaaafaaaaaaaaaaa0a0a0a0ffff0000ff00ff00fcfcfcfcc0c0c0c0aaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f08a8a8a8a3030303022222222ffff0000ff00ff00f0f0f0f0eaaaeaaaccccccccaaaaaaaaffff0000ff00ff00fcfcccccf0f0f0f0c0c00000aaaaaaaaffff0000ff00ff00ccccccccaaaaaaaaaa00aa000e0c0e0cff00ff00f0f0f0f0ccccccccaaaaaaaa2222aaaa0000f0f0ff00ff00fcfc0000fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cfcccfccccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccbb330000aaaaaaaa
def HC5_5_23 : Nat := 0x179d0ce7175f18111759ed7317428d26174070cf1732c58d17266c0b17256643170ea7621708009516e446d116e3ac0516e070ea16df1a2d16d0454f16c9f23c16be070b16b7588b16b67a3316af019716aaf55c169cec0416858c1b167f34cf167792e4167493c6164ae7ba164297f615fbce1815f8f33315ead5f715e3950b
def SC5_5_24 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4c4c4c4cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000000ccffffccccffff0000ff00ff00f0f0c0c0aaaaaaaa33330000ffffff00ffff0000ff00ff00f0f0f0f0cccccccc55445544ff00ff00ff000000f0f0f0f0cfcf0000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccccc0cc00aaaaaaaaffff0000ff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffffff00f0f0f0f0ccccccccaaaaaaaa00f0f0f0ffff0000ff00ff00f0f0f0f0ececececcccccccc44444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0202ffff0000ff00ff00f0f0f0f0ccccfffcccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00fc00fcffff0000ff00ff00f0f0f0f0ccccccccb0b0a0a0aaaaaaaaff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaa22222222ffff0000ff00ff00fafafafaf0f0f0f0aaaaaaaa33223322ff00ff00ff000f00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f7f0f7f0f0f0f0f0ccccccccaaaaaaaafffff0f0ffff0000ff00ff00f0000000ccccccccaaaaaaaaffff0000ff00ff00fcfcccccf0f0f0f0cccccccc54544444ffffff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0ddccffccccccccccaaaaaaaaffff0000ff00cc00f0f0f0f0ccccccccaaaaaaaa00aa00aaffff0000ffaafffaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc5555550050505050ffff0000ff00ff00f0f0f0f0ccccccccbbbbbbaaaaaaaaaaffff0000ff00ff00fafaf0f0ccccccccaaaaaaaa0f0f0000ffff0000f0f0f0f0eeee0000ccccccccaaaaaaaa00ee00eefffffff0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff00ffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa50505050ffffaaaaff00ff00f0f0f0f0eeee0000ccccccccaaaaaaaa
def HC5_5_24 : Nat := 0x19a21910198f9ef41969fcb21960b8941956b4ec194287a71930061b192f87e4192360ed1915a10b1909b45d18f86acf18eb125918e198c718da35d618ba972c18ae71451887c74d18828b2a186f75b51861ed14185a510018341a75181da8ed18070be7180584fc17fda6c517e3d01817e0305f17d9144217bc59c817af8aa1
def SC5_5_25 : Nat := 0xffccff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0ccccccccaa00ff0044444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000088ffff00f0ffff0000ff00ff00ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0ccccccccaaaa0a0a44444444ffff0000f0f0f0f0ccccccccaaaaaaaa3f003f0000ff0000ffff0000ff00ff00f0f0f0f0cccc8888aaaaaaaaaa00aa00fffffff0fffff0f0ffff0000f000f000ccccccccaaaaaaaaffff0000ff00ff00f0f0fff0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f030f00ffff0000ff000000f0f0f0f0ccccccccaaaaaaaaaa00aa00ff0a0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0a0a0affff0000fff5ff00ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ffaaffaaff00ff00f0f0f0f0aaaaaaaa33333322ffffff00ff00ff00f0f0f0f0ccccccccaaaaaaaa00f0f0f0ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa000000ccfffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaa0ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa22222222ffff0000ff00ff00fc0cfc0cf0f0f0f0ccccccccaaaaaaaaffffccccffff0000ff00ff00f0f0c0f0ccccccccaaaaaaaa00000000fff0fff0ff000000ccccccccaaaaaaaa0f0f000000000000ffff0000ee00ee00ccccccccaaaaaaaa0e0e0e0effff0000ff00ff00f0f0f0f0aaaaaaaa3030303008080808ffff0000ff00ff00ccccccccc0c0c0c0aaaaaaaa0e0e0e0effff0404ff00ff00f0f0f0f0ccccccccaaaaaaaa04040404ffff0000ff00ff00ccccccccccc0ccc0aaaaaaaa0f000f00ffff0000ff00ff00f0f00000f000f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0888888883030303020202020ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ba00baff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00cc0000f0fcffff0000f0f0f0f0ccccccccaaaaaaaa88cc88cc00aa00aaffff0000f0f0fff0f0f0f0f0ccccccccaaaaaaaa00f000f0
def HC5_5_25 : Nat := 0x1bd9e1171bc7bf471bbb1f7f1bb8c32d1bb0aa611ba68b8d1b9ab6781b8833181b87191b1b80a4a61b70466b1b6e76851b5dd9681b4a9c581b1ff21e1b136b511b03f4b71af257be1aebbce21ab9bf4d1a915ecf1a83bd501a677c631a4433a81a3ad5a81a2cadb61a274a421a0c4aec1a0955ee19daba8919d01d8519b51a57
def SC5_5_26 : Nat := 0xffffff00f0f0f0f0f0f00000f0000000ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaaa0a0a0a000ff00aaffff0000ff00ff00fafafafaccccccccaaaaaaaaa0a0f0f0fffff0f0ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0effff0000ff00ff00f0f0f0f0eeeeeeee4444444422222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0ff0000fffff0f0ff00ff00f0f00000ccccccccaaaaaaaa0000f0f0ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa222222220000eeeeffff0000ff00ff00f0f0f0f0888888885050505030303030ffff0000f0f0f0f0ccccccccaaaaaaaaaa00aa005f005f00ffff0000f0f0f0f0ccccccccaaaaaaaa00ff000000ee00eeffff0000ff00ff00ccccccccaaaaaaaa0f0c0f0c00f000f0ff88ff88ff880000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ccccccccc0c0c0c0aaaaaaaa8a8a8a8affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55f055f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33330202fff0fff0ff00ff00ff000000ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f4f0f4ccccccccaaaaaaaa00cc00ccff00ff00f0f0f0f0ccccccccaaaaaaaa00fff0f00000f0f0ffff0000ff00ff00f0f0f0f0cccccccccccc888855550000ffffff00ff000000f0f0f0f0cccccccccccc0000aaaaaaaaffffaaaaffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaaffff0000fffcfffcff00ff00f0c0f0c0ccccccccaaaaaaaaffff0000f0f0f0f0cccccccccccc00ccaaaaaaaa00ff0000ffff00f0fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f00000ccccccccaaaaaaaa00f0f0f0ffff0044ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000cccccccc54544444ffff0000ff00ff00f0f0f0f0ccccccccaa88aa880088008800000000ffff0000fa00fa00f0f0f0f0aaaaaaaa32323232
def HC5_5_26 : Nat := 0x1d9f596d1d7ef2bf1d62d7581d5cca2e1d46baab1d3ad24f1cf608741cddb20e1cc6dfe81cc132fc1cc030c61cb578591ca2b67a1ca161ba1c9dda231c9963061c83752e1c81c9091c7159c01c644dca1c4eaa341c47c24c1c391d7d1c34349c1c3125c31c2917011c22b7c51c0befeb1c00a3741bf7a64e1be503d01bdb11c0
def SC5_5_27 : Nat := 0xfcfcfcfcf0f0f0f0ccccccccaaaaaaaa00fc00fc0000fcfcffff0000ffaaffaaff44ff44f0f0f0f0ccccccccaaaaaaaa00000000ff00ff00fcfc0000f0f0f0f0cccccccca8a8a8a8ffff0000ff00ff00f000ff00ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f888f888f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccff88aaccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaa0ffff0000ff00ff00f5f5f500f0f0f0f0ccccccccaaaaaaaaffaa0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c0c0c00000000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fffaffff0000fff0fff0ff00ff00f0f0fff0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaabbaa33003300ffffff00fff00000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaa3322332200000000ffff0000f0f0f0f0ee00ee00aaaaaaaa88888888ffff0000ff00ff00f0f0f0f0eeeeeeee8888888888880000ffffaaaaffff0000ff00aa00f0f0f0f0cccc8888aaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa3030303000fc00fcffff0000ff00ff00f0f0f0f0aaaaaaaa8888888830003000ffff0000f0f0f0f0f010f010ccccccccaaaaaaaa00ee00eeff00ff00f0f000f0ccccccccaaaaaaaa0000ff000000ccccffff0000f0f0f0f0eeeeeeeeee00ee00cccccccc44444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa11111100ffffccccff00ff00f0f0f0f0ccccccccaaaa88880000ccccff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff000000fafaffff0000fafafafaf0f0f0f0aaaaaaaa3232323200fa00fa00000000ffff0000f000ff00ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f0cccccccc666666662222222200000000ffff00f0ff00ff00f0f00000ccccccccaaaaaaaaff00ff00f0f00000ccccccccaaaaaaaa0a0a0a0a0000aaaafffffafaffff0000ff00ff00f0f0f0f0ccccccccaaaaa0a0
def HC5_5_27 : Nat := 0x200c8595200c19382004c67d1fbcf3df1fb9d2e71fb26b261f88e10b1f7fd1c31f7d71c01f66e1b21f27495d1f14d82e1f147ef01ee7613b1ec7f0561e9d67061e5b97231e2c10131e2a409e1e1e01491e17ded11e1426f11df8935d1df578741df24aa61dee57611de049ef1dcc89a51dbfa5211db898801db5478f1db32cc1
def SC5_5_28 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa05050000ffff00ccff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0fcf0fcccccccccaaaaaaaaa0a0a0a0ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaa0a000a00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa88aaffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ccccccccbbaaaaaaaaaaaaaaff0fff00f0f0f0f0f0f00000ccccccccaaaaaaaa0f0f0000ffff0000f0f0f0f0ccffcc00ccccccccaaaaaaaa00ff0000ffff0000ff00ff00ccccccccaaaaaaaa5f005f000c0c0c0cffff0000ff00ff00f0f0f0f0888888885555000033003300ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55110000ffff0000ff00ff00f0f0f0f0f0505050ccccccccaaaaaaaaffffaaaaffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaafffff0f0ffff0000ff00ff00f0f0f0f0ccccc8c8aaaaaaaaffff8888ff00ff00f0f0f0f0ccccccccaaaaaaaa88880000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa77227722ffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaa00aa000aff00ff00f0f0f0f0ccccccccaaaaaaaa0a0a0a0a0000fcfcffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaa0f000f00ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00000055ff000000000000ffff0000f0f0f0f0cc88cc88aaaaaaaaaa00aa00ffff0000ffc0ffc0ff00ff00f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaa3333ccccffff0000ff00ff00fefefefeccccccccaaaaaaaa0e0e0e0effff0000ff00ff00c0c0c0c0aaaaaaaa0a0a0a0a02020202ffff0000ff000000f0f0f0f0ccccccccaaaaaaaaaaa0aaa0ffffff00f0f0f0f0f0f00000ccccccccaaaaaaaa00f00000ff00ff00f0f00000cccccccccccc0000aaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000aaaffff0000ff00ff00f0a0f0a0ccccccccaaaaaaaaaaaa000000000000fffffff0ffff0000f000f000ccccccccaaaaaaaa
def HC5_5_28 : Nat := 0x21612ce5215bb42821599c42214533c42139b6c421340850212f6284212d3aa9212c38f42126d95d211ffe3b211a2bba21150e1f20fa715d20db20df20d07be120c4633420a2ad6220a09ded208786ba20823f2c206a350a205722972046dedc203d86d12033e6a120227ce5201f562d201eec7e201a6aee20137cd9200d1f6c
def SC5_5_29 : Nat := 0xffff0000fafafafaf0f0f0f0ccccccccaaaaaaaa00ff00aaffff0000fff0f0f0ff00ff00ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0fff0f00ffff0000ff00ffa0f0f0f0f0ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f8f8f8f8c0c0c0c0aaaaaaaa88888888ffffffccffff0000ff00ff00f0f0f0f0cccccccc55555544ffffc0c0ff00ff00f0f0f0f0ccccccccc0c00000aaaaaaaaffff2222ffff0000ff00ff00f0f0f0f0aaaaaaaa33332222ffffccccffff0000ff00ff00f0f0f0f0aaaaaaaa33330000ffff0000f0f0f0f0eecceecccc00cc00aaaaaaaaaa00aa00ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa0f000f0000000000ffff0000ff00ff00ccccccccaaaaaaaa0f0a0a0affff0000f0f0f0f0cccccccccccc8888aaaaaaaa00ff00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0aa00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa54445444ffff0000f0f0f0f0ccccccccaaaaaaaaaaaa000000ee00eeffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0e4e4e4e4cccccccca0a0a0a000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaababaffff0000fff0ff00f0f0f0f0f0000000ccccccccaaaaaaaaffaa0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaaffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0e00f000f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000101000000000ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0effff0000ff00cc00f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f000f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00fe00fe00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00fafafafaf0f0f0f0a0a0a0a03232323200000000ffff0000ff00ff00f0f0f0f08888888866666666ff00ff00fcfcfcfcfcfc0000ccccccccaaaaaaaa0c0c0c0cfffffcfcffff0000f0f0f0f0ccccccccaaaaaaaa00ff00fc
def HC5_5_29 : Nat := 0x23188a4c231072f3230d837b22fdf98d22fcfee822f7393622f5039b22ef87d822e017cc22d9124a229fa8a2228fb69122856b8f226c95da22628c26225bc0a1225a9f44225050f022244b7f221e6604221adc4f2218eab2220021f821e2515321e1b68221d8dc6021ca668d21bd6ee221b213ec21953db9219024ee216663c6
def SC5_5_30 : Nat := 0xffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaa1f1f0000ffff0000ff00ff00f0f0f0f0cccccccc5555550000aa00aafff0fff0ff00ff00f0f00000ccccccccaaaaaaaa000f0000ffff0000ff000000f0f0f0f0ccccccccaaaaaaaaa0aaa0aaffff0000fff0fff0ff00ff00f0fff0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa88aa8888888888ffaa0000ff00ff00fcfcfcfcf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0c0c0c0c0aa00aa0088888888ff00ff00f0f0f0f0ccccccccaaaaaaaa0000eeee00002222ffff0000f0f0f0f0ccccccccaaaaaaaa8800880000f000f0ffff0000f0f0f0f0ccccccccaaaaaaaa4444444400ee00eeffff0000ff00ff00f0f0f0f0aaaaaaaa8800880044cc44cc00000000ff00aa00f0f0f0f0ccccccccaaaaaaaaaaaa0000ffff0022ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00007700ffff0000ff00ff00ccccccccaaaaaaaa5a5a5a5a0a0a0a0afffff0f0ff00ff00f0f00000ccccccccaaaaaaaa00cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8800cc00ffff000cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffffff00ff000000f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff444444ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000a0aaffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa0000fff0ffff0000ff00ff00f0f0f0f0cccccccc554455440f0f0000ff000000f0f0f0f0ccccccccaaaaaaaa0000ff000000aaaaffff0000fff0f0f0ff00ff00ccccccccaaaaaaaa0f000000ff00ff00f0f0f0f0eeeeaaaaeeee0000ccccccccaaaaaaaaffff0000fff0fff0f0f00000f000f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaafafafaaaaaaaaaffffff00ff00ff00f0f00000ccccccccaaaaaaaa0c0c0c0cffff0000f500f500f0f0f0f0ccccccccaaaaaaaa0a000a00ffff0000ff00ff00f0f0f0f0ccccccccaaaaeeee44444444
def HC5_5_30 : Nat := 0x24eaaf7624d9a36324cecf8d24bbc0c824b955bc24ad211a249706e624949f6a24924d6224813ebe24514c8824214c8c2417d8862400ca6823edcb8723eb1f5823e7592723e1a22823e03d8a23d41d4d23b7e99b2377536523737adf23627f49234b3ba523439a7523432906233541582331ae85232db652231ff7c4231c5145
def SC5_5_31 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0aaa0a0affff00aaff00ff00f0f0f0f0ccccccccaaaaaaaa00aa0000ffff0000ff0fff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33303030ffff0000f0f0f0f0ccccccccaaffaaaaaaaaaaaa00ff00aa00000000ff00ff00f0f0f0f0eeee0000aaaaaaaa22222222ffff0000ff00ff00f0f0fcfcf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88008800ff000f00f0f0f0f0ccccccccaaaaaaaa00ff00000000f0f0ffff0000ff00ff00ccccccccaaaaaaaaaaaa00000f0f0c0cffff0000ffcc00ccff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaaa8a8ff000000f0f0f0f0cccccccccccc0000aaaaaaaa0000ff00ff00ff00f0f0f0f0ccccccccaaaa00008888888855550000fffffff0ffff0000ff00ff00f0f0f0f0cccccccc55555550ffffff00ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaaffff3030ff00ff00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000f0f0f0f0cc00cc00aaaaaaaa3300330022222222fffff2f2ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f3f30000f0f0f0f0ccccccccaaaaaaaa0000aaaa00000000ff0fff00f0f0f0f0ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00ccccccccb0b0b0b0aaaaaaaa0f000f00ffff0000ffbaffbaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeecccccccc4444444400000000ffff0000ff00ff00f0f0f0f0ccccc8c8aaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa0c0c0c0c00ee00eeff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f000000f0f0f0ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa0000eeeeffff0000ff00ff00f0f000f0ccccccccaaaaaaaa00000f00ffffaaaaffff0000ff00ff00f0f0f0f0cccccccc54545454fffff0f0ffccffccff00ff00f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccc00008888888850505050
def HC5_5_31 : Nat := 0x271e56e32701fb1e26fe1c7026c3559026b475c526952d9326860f2d26533d82262b01fa2626f28e25cbeabe25bd389f25b4e09425b4313a25aa57ed25a6b74125a3cce22594a1512590cb55258326de2582cf57257e79892579fc0f2572202325600d33252731682521b8d3250917862508712f2500ef5d24fb3ec524fb2ade
def SC5_5_32 : Nat := 0xffffff00ff000000f0f0f0f0ccccccccaaaaaaaa55555500ffff0000ffccaa88ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaa00aa004444444400ff0000ffff5000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000fff0fff0ff00ff00f0f0f0f0cccccccc5554555400000000ffff0000ff00fff0f0f00000ccccccccaaaaaaaaffff00f0f0f0f0f0ccccccccaaaaaaaaaa00aa0000f000f0fff00000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa222a222affff0000ff00ff00ccccccccaaaaaaaa303030300e0e0e0eff00ff00fefef0f0f0f0f0f0eeee0000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0ff00ff0ffff0000ff00ff00f0f0f0f0cccccccc4400440022aa22aaffff0000ff00ff00f0f0f0f0eeeceeecccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccc000c0c0aaaaaaaaffff0000ffccffccff00ff00ccccccccaaaaaaaa0f0a0f0affff0000ffaaffaaff00ff00f0f0f0f0aaaaaaaa3322332200000000ffff0000ff00ff00f0f0f0f0cccccccc55554444ff00ff00fafa0000f0f0f0f0ccccccccaaaaaaaa00fa00faffffccccffff0000ff00ff00cccc0000aaaaaaaa0f0f0c0cffff0000f0f0f0f0ccccccccaaaaaaaa0f000f0000f000f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaeeee00004444ffff0000ffcc0000ff00ff00f0f0f0f0ccccccccaa88aa88ffff0000ff00ff00fcfcfcfcf0a0f0a0ccccccccaaaaaaaafffffafaffff0000ff00ff00f0f0f0f0cccccccc55555050ffff0000ff00ff00f0f0f0f0aaaaaaaa8888cccc11110000ffffff00ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaff0f0000ff00ff00ccccccccaaaaaaaa0f0f000000f000f000000000f0f0f0f0eeee0000ee00ee00ccccccccaaaaaaaaffff88aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00bb000000000000ffff0000f0f0f0f0ccccccccaaaaaaaa7f007f00
def HC5_5_32 : Nat := 0x2a0c6a7729d386d529d3084b29c68a1129b36dd229a48875297b7a82291645a52906da6c2905c60028e6f3f628d35a9d28d329cf28c521b228aa840028950ced287d55ff2869e122285dd9a12842fd6e282ba3102829800a2809054a27f882c627e72bec27cc5b3727bed9292793ec3a276299d92745b58f274036dd273548a1
def SC5_5_33 : Nat := 0xfff0fff0fff00000ff00ff00ccccccccaaaaaaaa0f0f0000ffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaa00f0000000000000ff00ff00f0ff0000ccccccccaaaaaaaa0000f0f0ff00ff00fafa0000f0f0f0f0ccccccccaaaaaaaa0500ff00ffff0000fff0fff0ff00ff00ccccccccaaaaaaaa0ff00ff0ffff0000ff00ff00f0f0f0f0ccccccccaf00af00aaaaaaaaff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaa000f0000ffff0000ff00ff00cccccccccc0ccc0caaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa888888ffcf0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fcf0ffff0000fff0fff0ccccccccaaaaaaaa0f000f0000f000f000000000ffcf0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffffff00ff000000f0f0f0f0ccccccccaaaaaaaa0f000000ffff0000ff00ff00e0e0e0e0ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaa22220000aaaaffff0000ff00ff00f000f000ccccccccaaaaaaaa0f0f0c0cffffff00ff000000f0f0f0f0ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0f0f01010ccccccccaaaaaaaaffff0000ff00ff00ccccccccb0b0b0b0aaaaaaaa40404040ffff00f0ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000c4c4ffff0000f000f000ccccccccaaaaaaaa00cc00cc00c000c0ffff0000ff00ff00f0f0ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa080a080fffffff0ffff0000f0fff0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa0aaa0000000000ffff0000fff0fff0ccccccccaaaaaaaa0ff00ff0ffff0000ff00ff00f0f0f0f0f000f050ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0bbbb8888aaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000000ffff0000ff00ff00f0f0f0f0cccccc00aaaaaaaa88888888
def HC5_5_33 : Nat := 0x2cb675e72ca4bf822c819af22c73a88e2c738adf2c36a2c02c3545752c2531b12c10ffea2be5b4372bd7cf162bcbd3522bc748c12bb495b32baca30d2ba7a28a2b8ddc472b816e312b70a9802b5c248b2b4d79462b41ec522b1d86e22adef8832ac9649d2ab82fd72a92a11d2a8320a52a5c1a6f2a596e9a2a30c9562a2d4f0e
def SC5_5_34 : Nat := 0xff000000f0f0f0f0ccccccccaaaaaaaa0000aaaa000000aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa40404040ffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33003300ffff0000ff0aff00ff00ff00f0f0f0f0ccccccccaaaaaaaafffff0f0ff00ff00f000f000ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0fff0ccccccccaaaaaaaa50505550ff00ff00f0ff0000f0f0f0f0ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa5500550032323232ffff0000ff00ff00ccccccccaaaaaaaaa0a0a0a03f003f00ffff0000fc00fc00f0f0f0f0ccccccccaaaaaaaa50505050ff00ff00f0f0f0f0eeee0000ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0f0f0cccccccca8a8a8a850505050ff00ff00fcfcf0f0f0f0f0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaa00aa0000440044ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa80808888ff00ff00fefe0000f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeaaeeaacc00cc0088888888ffaf0000ff00ff00f0f0f0f0ccccccccaaaaaaaa50505050ffff0000ffeeffeeff00ff00f0f0f0f0cc88cc88aaaaaaaaffff0000f0f0f0f0cc00cc00aaaaaaaa8888888877007700ffff0000fff0fff0ff00ff00ccccccccaaaaaaaa0f000000ffff0000f0f0f0f0cccccccccc00cc00aaaaaaaa33003300ff00ff00f0f0f0f0eeeeaaaaccccccccaaaaaaaaaaaa0000ffff0000fff0fff0ff00ff00ccccccccaaaaaaaa0f000f0000000000ffff0000fc00cc00f0f0f0f0ccccccccaaaaaaaaffffff00ffff0000f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f0f0f0f0aaaaaaaa8888888830303030ffff0000ff00ff00f0f0f0f0cc88cc88cc00cc00aaaaaaaaffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa22002200ffff0000ff00ff00f0f0f0f0c0c0c0c0aaaaaaaa32323232ffff0000ff00ff00f0f0f0f0eeeeeeee8888888855550000ffff0000f0f0f0f0ccccccccaaaaaaaa00ff00aa00550000
def HC5_5_34 : Nat := 0x2fdfce102fdb4cd62fb60f162fa8444f2f9b9e532f8f8d762f669a772f29f8e92f236bda2ee6d0252edefe812eb796ad2ea70bb52e4c8cc42e4b659a2e33a8492e2854722e22bddd2e1c38502dec439f2dd0f9982dc006c92dbeb9482d9dd2162d9d6b1c2d4ad3972d49f9062d4938e82d3133132d1aab012ce949832cc55175
def SC5_5_35 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaee00ccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000300ffff0000ccccccccaaaaaaaa0f0f000000f000f000cc00ccffff0000ff00ff00f0f0f0f0eeeeeeeeeeee000088888888ffff0000ff00ff00fcfcfcfcf0f0f0f0aaaaaaaa33303330fffff0f0ff00ff00ccccccccaaaaaaaa0f000f000000ff00ffff0000ff00ff00fefefefef0f0f0f0aaaaaaaa32323232ffff0000fafaaaaafa00aa00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0efef0000ccccccccaaaaaaaa10101010ffffc0c0ff00ff00f0f00000ccccccccc0c0c0c0aaaaaaaaffffaaaaffff0000ff00ee00f0f0f0f0ccccccccaaaaaaaafffff000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa888888ccfffff0f0ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccc0ccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa08080808ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000eeeeffff0000ff00ff00f0f0f0f0bb00bb00aaaaaaaa22222222ffff0000ff00ff00f0f0f0f0cccccccc8888888820202020ffff0000ff00ff00fcfcfcfcf0f0f0f0ccc0ccc0aaaaaaaaffff0000ff00ff00fefefefee0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccc4444aaaaaaaa00008888ffff0000ff00ff00f0f0f0f0cccccccc8888aaaa55550000ffff0000ff00ff00f0f0f0f0f0f00000eeeeeeee88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaaa0aaffff0000ff00ff00f1f1f0f0eeeeeeeeccccccccaaaaaaaaffff1010ff00ff00f0f0f0f0ccccccccaaaaaaaa10101010ffff0000ff00ff00f0f0f0f0ccc0ccc0aaaaaaaa33330000ffffffccffff0000ff00ff00f0f0f0f0ccccccccaaaa8888ffff0000ff00ff00f0f0f0f0dcdcdcdcc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000a0f0ffff0000ff00ff00f0f0f0f0ccceccceccccccccaaaaaaaa
def HC5_5_35 : Nat := 0x33f420cd33eeb04a33bb68a033bb5207333d5602332987bc3313fe2a330a757b32e9ba8d32e54d4932b8a73832b558a5329e69c1327f30fd326f9709325387d2321ba5cd3219d1bd31f8565b31ad9d1b31a5f636316cf5883101998330f8362330c41d3830bf1451308f4acd3087c0d130853cc5307d51262ffc9a0c2fe8172f
def SC5_5_36 : Nat := 0xffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaa3f3f00000000f0f0ffff0000ff00ff00ccccccccaaaaaaaa0f0c0f0c00330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22330000ffff0000ff22ff22f0f0f0f0ccccccccaaaaaaaa22002200ffff0000f0f0f0f0ccccccccaaaaaaaaa000a00000cc00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaa00000000aa00000000ffff0000ff00ff00ccccccccaaaaaaaa0e0e0c0cffff0000ff00ff00f0f0f0f0eeeeccccaaaaaaaa22220000ffff0000ff00ff00fcf0f0f0f0f0f0f0ccccccccaaaaaaaaffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaaaa00aa0000000000ffff0000f0f0f0f0eeeeeeee8888888800ee00ee00000000ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f8f8f8f8ccccccccaaaaaaaa08080808fafafafafa00fa00f0f0f0f0ccccccccaaaaaaaa0000fafaffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0dd00dd00cccccccc88888888ffff0000ffccff00ffaaffaaf0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0cccccccccccc0000aaaa00002222aaaaff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55550000ffff0000ff00ff00ccccccccaaaaaaaa0c0c0c0c02020202ff000000f0f0f0f0ccccccccaaaaaaaa0f0f00000f000f00ffffff00ffff0000ccccccccaaaaaaaa0f0f0f0000f000f0ffff0000ff00ff00f0f0f0f0cccccccc555544440000aaaaff00ff00f0f0f0f0efef0000eeeeeeeeccccccccaaaaaaaaffff0000ffeeffeeff00ff00f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00fcfcfcf0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa10501050ffff0000ff00ff00f0f0f0f0ccccccccafafaaaa0a0a0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88ccccccffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c054545454ffff0000ffecffecff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_5_36 : Nat := 0x380b79c737e2b29037ad4f4d37aa4bda377fa86937732f53376d7728376d24b3374b0b22374920473739693b3735652d37041d5136c8200c36bb6ea136a5898a3665b9e235da504435d378e535b2f527359771d0358334e63578d872355896a7354980b9353120ef3512a79035103500350ea91a349c8c8e347474ed346667c8
def SC5_5_37 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa08088888ff00ff00eeeeeeeeccccccccaaaaaaaa0e0e0e0e0000eeeefffff0f0ff00ff00f0f00000ccccccccaaaaaaaa30300000ffff0000ff00ff00ccccccccaaaaaaaa5a5a5a5a50505050ffff0000ff00ff00f0f0f0f0ccccccccaaaa0000a0a0aaaa00000000fff0fff0ff00ff00f0ff0000ccccccccaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa00f000f000880088ffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaa30303030ffff0000ff00ff00f0f0f0f0ccccccccbb00bb00aaaaaaaafff0fff0ff000000f0f0f0f0ccccccccaaaaaaaaaaaa0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33331010ffff0000ffaaffaaff00ff00ccccccccaaaaaaaa0f0f0f0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00a000ffffff00ff00ff00f0f0f0f0f0f000f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa3232323204040404ffff0000ff00ff00f0f0f0f0cccccccc5544554411001100ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa77007700ffff0000ff00ff00f0f0f0f0eeeeeeee8888888800ee00eefffff0f0ff00ff00f0f00000f0000000ccccccccaaaaaaaaffff0000ff00ff00cccccccca0a0a0a0505050500a0a0a0affff0000ff00ff00f0f0f0f0eeeeccccaaaaaaaa88888888ffff0000ffaaffaaf0f0f0f0ccccccccaa00aa0000cc00ccffff0000ff88ff00f0f0f0f0ccccccccaaaaaaaa88880000ffff0000ff00ff00f0f0f0f0eeeeeeee8888888800ff0000ffff0000ff00ff00f0f0f0f0ccccccccaaaa00aa88888888ffff0000ff00fff0f0f0f0f0ccccccccaaaaaaaa00f0000000000000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffeeff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00cc0000fcfcffff0000fffcfff0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f0c0f0ccccccccaaaaaaaaffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00ccccccccaaaaaaaaa0a0a0a00c0c0c0c
def HC5_5_37 : Nat := 0x3b8fc09e3b7f328d3b5cd2e03b5745223b2c99da3aa44d933a9be8673a6e35653a4537353a1c6bf839e04e8039d8c1da39c1be0239b014ad39a855143933d1f73929fa043925cf67391466d638e08e3638d0897c38c6b94438b9565a389b526e389135133890af7738777b213846515e38437de638325c703829e53d381994bc
def SC5_5_38 : Nat := 0xffff0000ff00ff00f0fcfcfcf0f0f0f0ccccccccaaaaaaaaffffccccffff0000ff00ff00f0f0f0f05555444433330000ffff0000ff00ff00f0f0f0f0ccccccccaaaa888855005500ffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa00aa00aaff00ff00ccccccccc0c0c0c0aaaaaaaa0f0f00000000ff0000000000ffff0000ff00ff00f0f0f0f0aaaaaaaa32322222ffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaa30303030ffff0000ff00ff00f0f0f0f0eeeeaaaacccc8888aaaaaaaaffff0000ff00ff00f0f0f0f0f0f0f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaa88aa88ff00ff00f0fff0f0ccccccccaaaaaaaa00ff00000000f0f0ffff0000ff00ff00fafafafaf0f0f0f0c8c8c8c8a0a0a0a0ffff0000ff00ff00fafafafacccccccc505050500a0a0a0affff0000ff00fff0ff00ff00f000f000ccccccccaaaaaaaaffff4444ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc5544554433003300ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa88888888ff00ff00f0f0fafaf0f0f0f0ccccccccaaaaaaaa0000f0f0fffffefeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ffccffccf0f0f0f0cc00cc00aaaaaaaa00cc00ccff00ff00f0f0f0f0cccceeeecccccccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0cccccccca0a0a0a00a0a0a0affff0000ff00ff00f1f0f1f0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee8888888870707070ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55ff50f0ffff0000f0f0fafaf0f0f0f0f000fa00ccccccccaaaaaaaaffffeeeeffff0000f0f0f0f0ccccccccaaaaaaaa00ee00eeffff0000ff00ff00f0f0f0f0cccccccc55505550000a000a00000000ffff0000ff00ff00f0f0f0f0eeeeeeee66666666fffffff0fff00000ff00ff00f0f0f0f0ccccccccaaaaaaaaff00ff00f0f0f0f0eeee0000ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0f0f00000aaaaaaaa33223322
def HC5_5_38 : Nat := 0x4002ff2a3fde5d733f7fdd103f5511483f31e8723f30ec193f2f89453f13804f3efdc3713ef873283ecb9b123ea43e273e7a25c33e3a888e3dfd0b9f3dfbf1743dd80b433d4491383d225ad93cdf719c3cd3c8a03cab4d893ca2c6323c98028e3c673d4f3c5d90473c3bed0e3c207bf13be08fc73bdab4fe3baf48903bac33a4
def SC5_5_39 : Nat := 0xffff0000ff00ff00f0f0f0f0aaaaaaaa300030000ccc0cccffffff00ff000000f0f0f0f0ccccccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5000f000fffff0f0ffff0000ff000f00f0f0f0f0ccccccccaaaaaaaaffffff00ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0effff0000f0f0f0f0ccccccccaaaaaaaa0ff00ff00f000f00ffff0000ff00ff00f0f0f0f0a0a0a0a08888888844444444ffff0000ff00ff00fcfcfcfcccccccccc0c0c0c0a8a8a8a8ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888800000000ffff0000ff00ff00f0f0f0f0ccccccccaaaa8888ffff0000ff000000f0f0f0f0ee00ee00ccccccccaaaaaaaaffcc0000ff00ff00f0f0f0f0f0c00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccca000a00044444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0cccccccff00ff00f0f0f0f0f0f000f0ccccccccaaaaaaaa0f0f0000ffffff00ffff0000f000f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0aaaaaaaa3322332200ff0000ffff0000ff00ff00f0f0f0f0cccccccca000a0000aaa0aaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f0cff00ff00f0f00000f000f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00fcf0fcf0ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa323232320000aaaaff00ff00f0ff0000f0f0f0f0cfcccfccccccccccaaaaaaaaff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff000000000000ffff0000ff00ff00f0f0f0f0e0e0e0e088888888ffff0000f0f0f0f0ccccccccaaeeaaee00cc00cc00aa00aaffff0000ff00ff00f0f0f0f0eeeeeeee888888880c0c0c0cffff0000ff00ff00f0f0f0f0cccccccc8888888866666666ff00ff00f0f0f0f0cccc0000aaaaaaaa0000aaaa00008888ffffff00ff000000f0f0f0f0f0f0f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee8888888844444444ffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa55aa55aa
def HC5_5_39 : Nat := 0x46d2dbd146b9d0d2462698d745ae66714592ed624574f6bc4545a41e453836fa45360475450e120244f8eb4f44bb431b44a05b3c444cfa7c43b1db62438b3333434f4fef42d3a12a4275f3a3425c423941dbf84c41a6e360419175094164fe12414c1a294140163d4102531040a558a64083d32340818fce402c6e304029b49e
def SC5_5_40 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30203020ffff0000ff00ff00f4f4f4f4ccccccccc0c0c0c0aaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa00ee00ee00cc00ccffff0000ff00ff00f0f0f0f0cc00cc00aaaaaaaaaa22aa22ffff0000ff00ff00ccccccccc0c0c0c0aaaaaaaa3c3c3c3cfffffff0ffffff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0b8b8b8b8aaaaaaaa30303030ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33003f00ff00ff00f0fff0f0f0ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f2f2f2f2ccccccccaaaaaaaa02020202ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff0fff00f0f0f0f0f000ff00ccccccccaaaaaaaaffff0000ff00ff00f000f0f0ccccccccaaaaaaaa0000f0f0fffffff0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaa3232323222222222ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaa0a0000000000000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff0cffff8888ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ccccffff0000ff00ff00f8f80000f0f0f0f0ccccccccaaaaaaaaff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa00ffff00ff00ff00f0f0f0f0ccccccccaaaaaaaa111100000000eeeeffff0000ff00ff00eeeeccccccccccccaaaaaaaa0e0e0c0cffff0000ff00ff00f0f0f0f0ccccccccccccaaaaaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00fa00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f5f0000ffff0000f0f0f0f0ccccccccaaaaaaaa888800007700ff00ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaaaaa0000ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0e0000eeeeffff0000ff00ff00f0f0f0f0eeeeeeee8888888800008888ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa11001100ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa11000000ffff0000f0f0f0f0ccccccccaaaaaaaa00ee00ee0000f0f0
def HC5_5_40 : Nat := 0x4e6503994e5a2cfd4e16f7714d8ceb5a4d7b41b34d66d4c64d4c23224cfc41c74cb1a7504c812e0d4c56e4814c5002734c2fdc854be308694b9ce3504b5c2dba4b46f7374ab10b7c4a9988394a6b53d84a3c333f4a17c4a749fcb81449f888d949e425484940703448947dc14891c0d448479d134791f28c472e8d314725a6be
def SC5_5_41 : Nat := 0xffffeeeeffff0000ff00ff00f0f0f0f0eeeeeeee88888888ffffaaaaffff0000ff00ff00f0f0f0f0cccccccc5555aaaaffffff00ffff0000ff00ff00e0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0c8c8c8c8aaaaaaaa04040404fffff0f0ff00ff00f0f0f0f0ccccccccaaaaaaaa77770000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0aceceffff0000ff00ff00f0f0f0f0eeee0000cccccccc44444444ffff0000f0f0f0f0ccccccccaaaaaaaa770077000f000f00ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaa0f000000ffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaa10101010ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa50000000ffff0000ff0fff00f0f0f0f0f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88cc88ccfffffff0ffff0000ff00ff00ccccccccaaaaaaaa0f0f0f000000000000000000ffff0000f0f0f0f0ee00ee0088888888ffffff00fff0fff0ff00ff00f0f00000ccccccccaaaaaaaaffff00eeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff2222ffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0eeaaeeaacccccccc88008800ffff0000ff00ff00f0f0f0f0888888885555000011110000ffff0000ff00ff00f0f0f0f0cc88cc88aaaaaaaa00f000f0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000cccc0000aaaaffff0000ffaaaaaaff00ff00f0f0f0f0cc888888aaaaaaaaffff0000ff00ff00f0c0f0c0ccccccccaaaaaaaa3000300000000000ffff0000ff00ff00f0f0f0f0eeeeaaaa88888888ff00ff00f0f00000ccccccccaaaaaaaa0f0f00000000f0f000000000ffff0000ff00ff00f0d0f0d0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555ccccffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa11001100ffff0000ff00ff00f0f0f0f0cccccccca2a2a2a244444444ffff0000ff22ff22f0f0f0f0aaaaaaaa3300330022222222
def HC5_5_41 : Nat := 0x58170eb657567a1856fb5cc7569a7f4f5694c376560fe01c55d9a5fa55cb962355c94b2c55c3972554fb03a954a286635471ef0e54110d4453ca5cee534ede4952c9227d52bacb1e525d42a4521c653c516f3e965071ed2a506f8330506a12d54faaec1b4f2df25d4f27b7484effaa714ef02f3c4eefebbe4ed63eca4e7d21e7
def SC5_5_42 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaa00aa0055555050ffff0000fffcccccff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f000f000ccccccccaaaaaaaa3030f0f0ffff0000f0f0f0f0ccccccccaaaaaaaaaa00aa0000ff0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000000affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4c4cccccffffff00ff000000f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0aaaaaaaaaaaa222233330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa50f0f0f0fffffff0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaa0ffff8888ffff0000f0f0f0f0ccccccccaaaaaaaa00ff0088ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff88ff88ff00ff00f0f0f0f0eeeeeeee88888888ffff0000ff0a0a0aff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaeeeeaaaaaaaaffff0000f0f0f0f0ccccccccaaaaaaaa0fff00000f000f00ffffccccffff0000ff00ff00f0f0f0f0aaaa888833330000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa00000000f00000000000ffff0000f0f0fff0ccccccccaaaaaaaa00f000f0ffff0000f0f0f0f0ccccccccaa00aa004444444400cc00ccff00ff00ff000000ccccccccaaaaaaaa0f0f000000f000f0ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa00f0f0f0ffff0000ff00ff00f0f0f0f0e4e4e4e4cccccccc44444444ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0e0f0eff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa0f0f000000000000f0f0f0f0ccccccccaaaaaaaa00ee00ee0000eeeeffff0000fffafafaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaa222288888888ffffff00ffff0000ff00ff00f0f0f0f0aaaaaaaa3232323200000000ffff0000f0f0f0f0ccccccccaaaaaaaa00ff0088ffff0000ff00ff00d0d0d0d0ccccccccaaaaaaaa0a0a0a0affff0000f0f0f0f0eeeeeeeeee00ee00ccccccccaaaaaaaa
def HC5_5_42 : Nat := 0x6737356f665615e465362abe63e23eab61f8764f610ee9f4610522e0605e6044600143b660004df95f87c5745f8156835d4e69e85d3927895d2b87a55c9417fa5c828e535c3e297c5b6fe0ba5b29cef65abacaa05a1ad0ea59e3b79159bff73b59b074bc58eab08358e08657588355ff586964bb5859f19d5852195358235d51
def SC5_5_43 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccafafaf00aaaaaaaaf0f0f0f0eeeeeeeeeeee0000ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88000000ffff0f00ff00ff00ff000f00f0f0f0f0ccccccccaaaaaaaaffff0000ffaaffaaf0f0f0f0ccccccccaa00aa0055005500ffff0000ff00ff00f0f0f0f0cf00ff00ccccccccaaaaaaaafffffcfcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccb000b000aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccc0000000aaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeee8888888866666666ffff0000ff00ff00ff000000e0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00fafafafacccccccca0a0a0a088888888ffff0000ff00ff00f0f0f0f0ccccccccbbbbbb00aaaaaaaafff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fffcffff0000f0f0f0f0eeeeeeeeee00ee00aaaaaaaa88888888ffff0000fff0fff0ff00ff00f0f0f0f0eeeeeeee88888888ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ee000000ccccccccaaaaaaaa00000000ff880000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000ccccccccaa88aa88ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa00ffff00ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccbabababaffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0000000ccccccccaaaaaaaa00f0f0f0ffff0000ff00ff00f0f0f0f0aaaaaaaa8888888811001100ffff0000ff00ff00f0f0f0f0ccccccccbabababa10101010ff00ff00f000f000ccccccccaaaaaaaa0fff00000000f0f0ff00ff00f0f0f0f0ccccccccaaaaaaaa777700000000aaaaffff0000f0f0f0f0ee00ee00ee000000ccccccccaaaaaaaaffff0000ff0fff00f0f0f0f0f000f000ccccccccaaaaaaaa
def HC5_5_43 : Nat := 0x7b7a525c7b7854e17a3ba49078ca4e3178c39b4b78847c61785bd80278066d6277566fd57733ef2c75aaf8c174356eed73eab0e97312df25730f165b72ddab5e71237b0770ce864b6f204ce06e925dba6cc3a32b6c9cdd1b6c2c207e6c0157d36a3423fe6a32e09069aa39cb69a191a768a76b076808654f67c253ae67481c42
def SC5_5_44 : Nat := 0xffff0000ff00ff00f0f0f0f0cccccccc55555550ffff0000ff00ff00f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa66666666ffff0000ff00ff00faaaaaaaf0f0f0f0ccccccccaaaaaaaafffff0f0ff00ff00ff000000f000f000ccccccccaaaaaaaafffff0f0fff0ff00ff00ff00f0f00000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa7777707000000000ffff0000ff00ff00f0f0f0f0eeeeeeee8888888800000000ffff0000f0f0f0f0eeeeeeeeee00ee0088888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff00f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa04044444ffff0000ff00ff00f0f00000ccccccccaaaaaaaa0f00fff0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00eeeeeeffff0000ff00ff00fefeeeeef0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0888888881100110000000000ffffff00f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccc6666666644444444ffff0000fff0fff0f000f000ccccccccaaaaaaaa000f0000ffff0000ff00ff00f0f0f0f0aaaaaaaa4444444422222222ffff0000ff00ff00f0f0f0f0cccccccc8888888822222222ffff0000ff00ff00f0f0f0f0e2e2e2e2ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccccccccc0aaaaaaaa00000000ffff0000f000f000ccccccccccc0ccc0aaaaaaaaffff8888ffff0000ff00ff00f0f0f0f0aaaaaaaa33330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa2a2a2a2ffff0000f0f0f0f0f000ff00ccccccccaaaaaaaa00f000f0ffaaffaaffaa0000ff00ff00f0a0f0a0ccccccccaaaaaaaaffff0000ff00ff00f0fff0f0ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0aaaaaaaa3322332200aa00aafffff0f0ff00ff00f0f000f0ccccccccaaaaaaaa0000ff00ffff0000ff0eff0eff00ff00ccccccccaaaaaaaa0e0e0e0effff0000ff00ff00fcfcfcfcf0f0f0f0c0c0c0c0aaaaaaaa
def HC5_5_44 : Nat := 0xe532eaffdb4cb11bd1d88314bd1ca21cbcc4301bb1f1e6a4b0455ccdaf3e1128a7e017f6a586de2ca406f5cda3da97e6a2eda6099ec256139eaca6639be5347297c94cb496ac4481942e930b911d268290a590c08e5971f98e09f7fd89414f2988e5752a83013dc281f3876b8165f2368140a75a80530d047e31fc4f7b9bd4c2
def readS5_5 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight (if Nat.blt c 22 then (if Nat.blt c 11 then (if Nat.blt c 5 then (if Nat.blt c 2 then (if Nat.blt c 1 then SC5_5_0 else SC5_5_1) else (if Nat.blt c 3 then SC5_5_2 else (if Nat.blt c 4 then SC5_5_3 else SC5_5_4))) else (if Nat.blt c 8 then (if Nat.blt c 6 then SC5_5_5 else (if Nat.blt c 7 then SC5_5_6 else SC5_5_7)) else (if Nat.blt c 9 then SC5_5_8 else (if Nat.blt c 10 then SC5_5_9 else SC5_5_10)))) else (if Nat.blt c 16 then (if Nat.blt c 13 then (if Nat.blt c 12 then SC5_5_11 else SC5_5_12) else (if Nat.blt c 14 then SC5_5_13 else (if Nat.blt c 15 then SC5_5_14 else SC5_5_15))) else (if Nat.blt c 19 then (if Nat.blt c 17 then SC5_5_16 else (if Nat.blt c 18 then SC5_5_17 else SC5_5_18)) else (if Nat.blt c 20 then SC5_5_19 else (if Nat.blt c 21 then SC5_5_20 else SC5_5_21))))) else (if Nat.blt c 33 then (if Nat.blt c 27 then (if Nat.blt c 24 then (if Nat.blt c 23 then SC5_5_22 else SC5_5_23) else (if Nat.blt c 25 then SC5_5_24 else (if Nat.blt c 26 then SC5_5_25 else SC5_5_26))) else (if Nat.blt c 30 then (if Nat.blt c 28 then SC5_5_27 else (if Nat.blt c 29 then SC5_5_28 else SC5_5_29)) else (if Nat.blt c 31 then SC5_5_30 else (if Nat.blt c 32 then SC5_5_31 else SC5_5_32)))) else (if Nat.blt c 39 then (if Nat.blt c 36 then (if Nat.blt c 34 then SC5_5_33 else (if Nat.blt c 35 then SC5_5_34 else SC5_5_35)) else (if Nat.blt c 37 then SC5_5_36 else (if Nat.blt c 38 then SC5_5_37 else SC5_5_38))) else (if Nat.blt c 42 then (if Nat.blt c 40 then SC5_5_39 else (if Nat.blt c 41 then SC5_5_40 else SC5_5_41)) else (if Nat.blt c 43 then SC5_5_42 else (if Nat.blt c 44 then SC5_5_43 else SC5_5_44)))))) (192 * o)
  unpack32 6 v
def readH5_5 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight (if Nat.blt c 22 then (if Nat.blt c 11 then (if Nat.blt c 5 then (if Nat.blt c 2 then (if Nat.blt c 1 then HC5_5_0 else HC5_5_1) else (if Nat.blt c 3 then HC5_5_2 else (if Nat.blt c 4 then HC5_5_3 else HC5_5_4))) else (if Nat.blt c 8 then (if Nat.blt c 6 then HC5_5_5 else (if Nat.blt c 7 then HC5_5_6 else HC5_5_7)) else (if Nat.blt c 9 then HC5_5_8 else (if Nat.blt c 10 then HC5_5_9 else HC5_5_10)))) else (if Nat.blt c 16 then (if Nat.blt c 13 then (if Nat.blt c 12 then HC5_5_11 else HC5_5_12) else (if Nat.blt c 14 then HC5_5_13 else (if Nat.blt c 15 then HC5_5_14 else HC5_5_15))) else (if Nat.blt c 19 then (if Nat.blt c 17 then HC5_5_16 else (if Nat.blt c 18 then HC5_5_17 else HC5_5_18)) else (if Nat.blt c 20 then HC5_5_19 else (if Nat.blt c 21 then HC5_5_20 else HC5_5_21))))) else (if Nat.blt c 33 then (if Nat.blt c 27 then (if Nat.blt c 24 then (if Nat.blt c 23 then HC5_5_22 else HC5_5_23) else (if Nat.blt c 25 then HC5_5_24 else (if Nat.blt c 26 then HC5_5_25 else HC5_5_26))) else (if Nat.blt c 30 then (if Nat.blt c 28 then HC5_5_27 else (if Nat.blt c 29 then HC5_5_28 else HC5_5_29)) else (if Nat.blt c 31 then HC5_5_30 else (if Nat.blt c 32 then HC5_5_31 else HC5_5_32)))) else (if Nat.blt c 39 then (if Nat.blt c 36 then (if Nat.blt c 34 then HC5_5_33 else (if Nat.blt c 35 then HC5_5_34 else HC5_5_35)) else (if Nat.blt c 37 then HC5_5_36 else (if Nat.blt c 38 then HC5_5_37 else HC5_5_38))) else (if Nat.blt c 42 then (if Nat.blt c 40 then HC5_5_39 else (if Nat.blt c 41 then HC5_5_40 else HC5_5_41)) else (if Nat.blt c 43 then HC5_5_42 else (if Nat.blt c 44 then HC5_5_43 else HC5_5_44)))))) (32 * o)) 0xffffffff
def SC5_6_0 : Nat := 0xffff0000f0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa00f000f000000000ffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa00aa00880088ffffaaaaffff0000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaffff0000fff0f0f0ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaa0000cccc00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30003000ffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa00ff0000ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa0a0a0a0affff0000ff0fff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff30ff30ff00ff00f0f0f0f0ccccccccaaaaaaaa3030303000000000ffff0000ff00ff00f0f0f0f0eeaaeeaaccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000011110000ffff0000ff00ff00f0f0f0f0cccccccccc00cc00aaaaaaaa88008800ffff0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaa0ccc0ccc00000000ffff0000ff00ff00f0f0f0f0cccccccc5500550000aa00aa00000000ffff0000ff00ff00f0f0f0f0cc00cc00aaaaaaaa888888880000000000000000ffff0000ff00ff00f0f0c0c0ccccccccaaaaaaaafffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5050505050500000ffffaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00fcfcfcfcfafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ffccffccff00ff00f0f0f0f0ccccccccaaaaaaaa8888888800000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000f000000000000ffff0000ff0fff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f000000aa00aa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5f5f0000ffffccccffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffffff00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa0000f0f0
def HC5_6_0 : Nat := 0x40da24903ec841703ce18a103bc7fdc03b2ed8503aeef3d03740977036ff29103542417028fab03028bc9370277beee0273340502669bb6025faa97024ba34a023e5a82022e6bd2021e4f5001f5806101587a35015869fb014948960111fb0c00fdf204009cc39f009b5efd006d31c1005b7fd5004df2fd00269e7f00199bbf
def SC5_6_1 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa000f0f000000000000ffff0000ff00ff00fefefefef0f0f0f0ccccccccaaaaaaaaffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa0000ffffeeeeffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ffccffccff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f8f8f8f8f0f0f0f0ccccccccaaaaaaaa8888888800000000ffff0000ff00ff00fcf0fcf0f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a00a0a0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa330033000000f0f0ffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888800000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa54545454ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa00cc00ccfffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f00ff0000000000fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa5050505000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa0aaa0a00000000ffff0000ff00ff00f0f0f0f0ee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5500550000f000f000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa00aa00a000a0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa0022002200ffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa000a000affff0000ff00ff00fafaaaaaf0f0f0f0f0f00000ccccccccaaaaaaaaffffccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0a0a0a0202020200000000ffff0000ff00ff00fafafafaccccccccaaaaaaaaa0a0a0a000000000ffff0000ff000000f0f0f0f0ccccccccaaaaaaaa00cc00cc00000000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f00000000ff0000000000ffff0000ffaaaaaaff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ffccffccffcc0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0aaa0aa0f000f00
def HC5_6_1 : Nat := 0xa28653409c76bca08efb3f2085a5411081ed21007efd64c07beb4c307a8e0f1077ac279071b6e54070f8b2f070aec7207051a9d06ee07ee06e6af2706d15ecb061fe10305fe0c8305fbd1ff05dd668905b2e0810598f869058ac2b305834fe9056728eb0526be05051ddb57051a82380514a4e90490ef9e0459d6340452e855
def SC5_6_2 : Nat := 0xffff0000ffccffccff00ff00f0f0f0f0ccccccccaaaaaaaa3300330000000000ffff0000ff00ff00f0f0f0f0cccccccccccccc00aaaaaaaaffff0000ff00ff00f0f0f0f0eeeeaaaacccccccccccc0000aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaafafaaaaaaaaa0000f0f0fffffcfcffff0000ff00ff00fcfcfcfcf0f0f0f0ccccccccaaaaaaaa00000000ffffff00ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa3300330000cc00ccffff0000fff0fff0ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaafffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa30303030fffffff0ffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0f030f030ccccccccaaaaaaaa00000000ffffaaaaffff0000ff00ff00ccccccccaaaaaaaa0f0f0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500303030300000000000000000ffffff00ff000000f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0aaaaa00000000ffff0000ff00ff00ccccccccaaaaaaaa0f0f00000c0c0c0cffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888800aa00aa00000000ffff0000f0f0f0f0ccccccccaaaaaaaa3300330000cc00ccffff0000ff00ff00f0f0f0f0ccccccccbbbb0000aaaaaaaa4444444400000000ffff0000fff0fff0ff000000f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f0ffff0000ff00ff00f3f30000f0f0f0f0ccccccccaaaaaaaa0c0c0c0c00000000ffff0000fcfcfcfcfc00fc00f0f0f0f0ccccccccaaaaaaaaffffaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa2222222200000000ffff0000ff00ff00fcfcfcfcf0f0f0f0cccccccca8a8a8a8ffffff00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa33333300ffffccccffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa00aa000a000affff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa30303030ffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa44444444ffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa5555000000000000ffff0000ff00ff00f0f0f0f0aaaaaaaa3030303022222222
def HC5_6_2 : Nat := 0xf7ff8ca0f7301010f468bea0f1bb6020ee444700edfd2120e6c132c0e3c4e600e0abea50dc872480d287d7d0d1853400d0176070cef67d80ca9c9cd0c9da15b0c849d260c7ba8f20c6e5f580c4be4260b8a06f10b80fc900b4a2ce90b3f48860b1af3710b188e640b00c0780af3f1850af2281f0ae53fd90ad0f8d10a644581
def SC5_6_3 : Nat := 0xffffff00ffffaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff33ff00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000000000000000ffff0000f0f0f0f0ccccccccaaaaaaaa00fc00fc00000000ffff0000ff00ff00f0f0f0f0ccccccccbbbbaaaaaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0f0c0f0c0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa00ff0000ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa55000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa0088888888ffff0000ffa0ffa0ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a000000000ffff0000ff00ff00f0f0f0f0cfcccfccccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa55005500ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888aaaa33330000fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa0000f0f0ffff0000ff00ff00f0f0f0f0cccccccccccc0000c0c0c0c0aaaaaaaaffff0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaaa000a000ffffaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa550055000000aaaa00000000ffff8888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0cccc0000aaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000000ff0000ffff0000ff00ff00f0f0f0f0dcdcdcdcccccccccaaaaaaaa50505050ffff0000ffccffccff00ff00f0f0f0f0ccccccccaaaaaaaa0000ffccffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa0000aaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa3333303000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa04040404ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f000500050000000000ffff0000ff22ff22ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa8888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f00000a0a0000ffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa33330000ffff00ccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00cc
def HC5_6_3 : Nat := 0x180bc9f1174070cf1708009516b67a3316aaf55c168301bc167867c1163fd0991638009715f8f3331535c0fd140bef5413d564ac13440dc113267315130f4c7612ec996a12cc1c0e12996f52129890771274151c11a5693711a0ed1210bcce2610b299e4105bc2b41053e9a6104c81d9100ba56a0fb6148c0faedd950f8507d3
def SC5_6_4 : Nat := 0xffff0000ff00ff00f0f0f0f0cececececcccccccaaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0f0f0f00000f000f000ccccccccaaaaaaaaffff0000fff0fff0ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa05050000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000033330000ffff0000ff00ff00fcfcfcfcf0f0f0f0ccccccccaaaaaaaa03000300ffff0000fff0fff0fff00000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa44444444ffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaa0000f0f0fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000044440000ffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa0a0a0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa550055002222222200000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00aa0000ffff0000ff00ff00ff000000f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaaaaaa000000000000ffff0000ff00ff00f0f0fff0f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff000000f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa3300330000aa00aaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa555500000c0c0c0cffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa2a2a2a20c0c0c0cffffffccffffff00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000044444444ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa5050505000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4c4c4c4c00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa000000ccffff0000ff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f000000000ffff0000ff0f0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00fc00fc00000000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa0f0f000000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaa
def HC5_6_4 : Nat := 0x21967fea21857b502166c06221612ce51ecece9a1e774ef41e70fb3e1e141d7e1df6db3c1dcb649c1d6ee8f11d0537511cc21bfe1c9963061c37fa211c1e91971b87191b1b70466b1b06a3ec1adb15be1ab2ce161aa9b7121a93fd1e1a0530de19fbd0cd19a21910198f9ef4194e71911930061b18f86acf18e198c7185a5100
def SC5_6_5 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff00000000cccc00000000ffff0000f0f0f0f0cccccccccc00cc00aaaaaaaa3300330000000000ffff0000fff0fff0ff00ff00ccccccccaaaaaaaa0f000f0000000000ffffff00ffff0000f0f0f0f0ccccccccaaaaaaaa00f000f000000000ffff0000ff00ff00f0f0f0f0aaaaaaaa8888888830303030ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa330033000000330000000000ffff0000ff00ff00f0f0f0f0ccccccccaf00af00aaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaaaa0000a0a00000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a000aa00aaffffff00fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f0000f000f0ffffccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000000000000ffff0000ffaaffaaff00ff00f0f0f0f0aaaaaaaa332233220000000000000000ffff0000ff00ff00f0f0f0f0cccccccc5555444400000000ffff0000f0f0f0f0ccccccccaaaaaaaa0f000f0000f000f0ffff0000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa0000aaaaffffff00ffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaaffff0000ff22ff22ff00ff00f0f0f0f0ccccccccaaaaaaaa2222222200000000ffff0000ff00ff00f0f0fcfcf0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88008800fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f0000000000ffff0000ff00ff00f0f0f0f0eeeeeeeecccccccc4444444400000000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa0000eeeeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa003300330000000000ffffccccffff0000ff00ff00f0f0f0f0aaaaaaaa33330000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa2222222200f000f0ffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa0f000f0000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa303030300000000000000000ffff0000ff00ff00ccccccccaaaaaaaa0e0e0e0e00000000ffff0000ff00ff00f000f0f0ccccccccaaaaaaaa00ff0000
def HC5_6_5 : Nat := 0x2e08c23a2dc006c92d9dd2162d4ad3972d49f9062c467ad52c36a2c02c24edb62be925222a97e6072a30c9562a1c0d4a29e37050287d55ff2869e122282ba31027b2ab74277f4f812731374e26860f2d26533d822578b580257220232509178624c1d75f22e017cc226ebc6622601efa225050f021e8056d21e1b68221ca668d
def SC5_6_6 : Nat := 0xffffccccffff0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cccccccccc00cc00aaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c0c0c0a0a0a0affff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888855005500ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa444444440a0a0a0a00000000ffff0000ffaaffaaf0f0f0f0ccccccccaaaaaaaa00aa00aa00000000ffff0000ff00ff00f0f0f0f0f0f0f000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0cf00cf00ccccccccaaaaaaaa3030303000000000ffff0000ff00ff00f0f0f0f0cccccccca0a0a0a00a0a0a0a00000000ffff0000ff00ff00f0f0f0f0ccccccccbb00bb00aaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa77007700ffff0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaa0000ccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f00000ff0000000000ffff0000ff00ff00ccccccccaaaaaaaaa0a0a0a00c0c0c0c0000000000000000ffff0f00ff00ff00f0f0f0f0ccccccccaaaaaaaa0000000000000000ff00ff00f0ff0000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0c0c0c0c0000ccccffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa00cc00ccfffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000ffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa50505050ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa0e0e0e0effffff00ffff0000ff00ff00f0f0f0f0cccccccccccccc00aaaaaaaa00000000fffff000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa444444440000444400000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0808080800000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000eeeeffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa4444444444440000ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaaa00aa0000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa40404040ffff0000ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaaaaaa0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f0000000f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa444444440c0c0c0c
def HC5_6_6 : Nat := 0x4097f2cf4092f239403e31e33fa7cf833f684d033f5511483efdc3713e4372d63cab4d893a4537353929fa04390b3bce38a85c19381994bc380b79c737041d51366fc2dc34aaeac23499acbc34715d1b343cab27332437e132b558a532558450325387d2321ba5cd30b20d9e308b22a72fdb4cd62ec427762e4fc1342e1e3a6b
def SC5_6_7 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888888008800ffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa00f0000000000000ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaeeeeaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaaa0a0a0a0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa888888882222222200000000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa0f0f0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a05f5f000000000000ffff0000f0f0f0f0eeeeeeeeee00ee00ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f0f00000f000f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f000000ff00ffffeeeeffffccccffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88cc88ccffffaaaaffff0000ff00ff00f0f0f0f0cccccccccccc8888aaaaaaaa00000000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000cccc0000aaaaffff0000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaa00cc000000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa1100110000000000ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa00000000fffffff0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaaaa00aa00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0f000f000f00000000000000ff00ff00f0f0f0f0cccccccccccc0000aaaaaaaaaaaa0000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0a0a0a0a0000ccccffff0000ffaaffaaff00ff00f0f0f0f0ccccccccaaaaaaaa33223322ffff0000ff00ff00f0f0f0f0eeeeeeeee0e0e0e0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000ff000000aaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888800f000f000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa888888880000000000000000ffff0000ff00ff00f0f0f0f0ccccccccaaaa8888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa5555000050505050ffffccccffff0000ff00ff00fcfcfcfcf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa0000f0f0
def HC5_6_7 : Nat := 0x601da67c5f86d2d65f8156835d2b87a55cfd09975c1ab9ea59b074bc598a70cb58235d5157b09f69571bf6fc551135835471ef0e528ffcd75071ed2a4fd9d6a84eefebbe4c56e4814be308694b00aef548c2cfaf48947dc147b9d574478d70ec45a51a8c4578a62845546feb45360475450e120243914e2043160f0340e877b4
def SC5_6_8 : Nat := 0xffff0000ff00ff00f0f0f0f0f0000000ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa44444444222222220000000000000000ffff0000ff00ff00f0f0f0f0eeeeeeee8888888800000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00ff00f0ffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa11001100ffff0000ff00ff00ff000000f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa8888888800000000ffff0000ff00ff00f0f0f0f0aaaaaaaa4444444422222222ffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000fff000000000ffff0000ff00ff00f0f0f0f0cccccccc888888882222222200000000ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa2a2a2a2ffff0000ff00ff00f0f0f0f0f0f00000ccccccccaaaaaaaa0f00ff00ffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaa8888888800000000ffff0000ff00ff00fcfcfcfcf0f0f0f0c0c0c0c0aaaaaaaa00000000ffff0000ff00ff00f0f0f0f0eeeeeeeeaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0cccccccccc00cc00aaaaaaaa4444444400000000fffffcfcffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaa22222222fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00000f00ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa8888888877007700ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaa0a0a0a04c4c4c4cffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaa04040404ffffccccffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa888888880808080800000000ffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000fff0fff0ff00ff00f0f0f0f0ccccccccaaaaaaaa0000cccc00000000ffff0000f0f0f0f0ccccccccaaaaaaaaaa00aa0000ff0000ffff0000fff0fff0ff00ff00f0f0f0f0f000f000ccccccccaaaaaaaa
def HC5_6_8 : Nat := 0xdb4cb11bb33eadf8af3e1128a586de2ca305a6c6a06c9f89994bbf7d942e930b9382a0bb911d268288e5752a88a82ce986214d7b7b9bd4c27a3ba49078525e4b78066d6276660bf8730d32d772f462fe72d10a066f244b376e1da1d46c1df0cc6a3423fe6690ead363e23eab61b0c034
def readS5_6 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight (if Nat.blt c 4 then (if Nat.blt c 2 then (if Nat.blt c 1 then SC5_6_0 else SC5_6_1) else (if Nat.blt c 3 then SC5_6_2 else SC5_6_3)) else (if Nat.blt c 6 then (if Nat.blt c 5 then SC5_6_4 else SC5_6_5) else (if Nat.blt c 7 then SC5_6_6 else (if Nat.blt c 8 then SC5_6_7 else SC5_6_8)))) (224 * o)
  unpack32 7 v
def readH5_6 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight (if Nat.blt c 4 then (if Nat.blt c 2 then (if Nat.blt c 1 then HC5_6_0 else HC5_6_1) else (if Nat.blt c 3 then HC5_6_2 else HC5_6_3)) else (if Nat.blt c 6 then (if Nat.blt c 5 then HC5_6_4 else HC5_6_5) else (if Nat.blt c 7 then HC5_6_6 else (if Nat.blt c 8 then HC5_6_7 else HC5_6_8)))) (32 * o)) 0xffffffff
def SC5_7_0 : Nat := 0xffff0000ff00ff00fafafafaf0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0eeeeeeeeccccccccaaaaaaaaffff0000ff00ff00ff000000f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa88888888ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa22222222ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa0000aaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa00f000f0fffff0f0ffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaaffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa55005500ffff0000ff00ff00f0f0f0f0ccccccccc0c0c0c0aaaaaaaa
def HC5_7_0 : Nat := 0x6a3423fe5f8156834c56e48145360475225050f0185a51000b8a06f106e6af2705dd668903ce18a1
def readS5_7 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC5_7_0 (192 * o)
  unpack32 6 v
def readH5_7 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC5_7_0 (32 * o)) 0xffffffff
def SC5_8_0 : Nat := 0xffff0000ff00ff00f0f0f0f0ccccccccaaaaaaaa
def HC5_8_0 : Nat := 0xb6b9b7b
def readS5_8 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC5_8_0 (160 * o)
  unpack32 5 v
def readH5_8 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC5_8_0 (32 * o)) 0xffffffff
def S5 : Nat → Nat → List Nat
  | 3 => readS5_3
  | 4 => readS5_4
  | 5 => readS5_5
  | 6 => readS5_6
  | 7 => readS5_7
  | 8 => readS5_8
  | _ => fun _ => []
def H5 : Nat → Nat → Nat
  | 3 => readH5_3
  | 4 => readH5_4
  | 5 => readH5_5
  | 6 => readH5_6
  | 7 => readH5_7
  | 8 => readH5_8
  | _ => fun _ => 0
def idx5 (u : Nat) (zs : List Nat) : Nat :=
  bsr (H5 u) (hk zs) 12 0 (N5 u)

def Z5 (u i : Nat) : Bool :=
  bar 0xffffffff 0xe8888880 S5 N5 idx5 ori5 u i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_3_0 : span (Z5 3) 32 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_3_32 : span (Z5 3) 32 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_3_64 : span (Z5 3) 32 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_3_96 : span (Z5 3) 32 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_3_128 : span (Z5 3) 10 128 = true := by decide +kernel
theorem z5_3 : span (Z5 3) 138 0 = true := (@span_join (Z5 3) 64 0 74 (@span_join (Z5 3) 32 0 32 p5_3_0 p5_3_32) (@span_join (Z5 3) 32 64 42 p5_3_64 (@span_join (Z5 3) 32 96 10 p5_3_96 p5_3_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_0 : span (Z5 4) 24 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_24 : span (Z5 4) 24 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_48 : span (Z5 4) 24 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_72 : span (Z5 4) 24 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_96 : span (Z5 4) 24 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_120 : span (Z5 4) 24 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_144 : span (Z5 4) 24 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_168 : span (Z5 4) 24 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_192 : span (Z5 4) 24 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_216 : span (Z5 4) 24 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_240 : span (Z5 4) 24 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_264 : span (Z5 4) 24 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_288 : span (Z5 4) 24 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_312 : span (Z5 4) 24 312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_336 : span (Z5 4) 24 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_360 : span (Z5 4) 24 360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_384 : span (Z5 4) 24 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_408 : span (Z5 4) 24 408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_432 : span (Z5 4) 24 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_456 : span (Z5 4) 24 456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_480 : span (Z5 4) 24 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_504 : span (Z5 4) 24 504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_528 : span (Z5 4) 24 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_552 : span (Z5 4) 24 552 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_576 : span (Z5 4) 24 576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_600 : span (Z5 4) 24 600 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_624 : span (Z5 4) 24 624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_648 : span (Z5 4) 24 648 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_672 : span (Z5 4) 24 672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_696 : span (Z5 4) 24 696 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_720 : span (Z5 4) 24 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_744 : span (Z5 4) 24 744 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_768 : span (Z5 4) 24 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_792 : span (Z5 4) 24 792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_816 : span (Z5 4) 24 816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_840 : span (Z5 4) 24 840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_864 : span (Z5 4) 24 864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_888 : span (Z5 4) 24 888 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_912 : span (Z5 4) 24 912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_936 : span (Z5 4) 24 936 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_960 : span (Z5 4) 24 960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_984 : span (Z5 4) 24 984 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_1008 : span (Z5 4) 24 1008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_1032 : span (Z5 4) 24 1032 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_1056 : span (Z5 4) 24 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_4_1080 : span (Z5 4) 23 1080 = true := by decide +kernel
theorem z5_4 : span (Z5 4) 1103 0 = true := (@span_join (Z5 4) 552 0 551 (@span_join (Z5 4) 264 0 288 (@span_join (Z5 4) 120 0 144 (@span_join (Z5 4) 48 0 72 (@span_join (Z5 4) 24 0 24 p5_4_0 p5_4_24) (@span_join (Z5 4) 24 48 48 p5_4_48 (@span_join (Z5 4) 24 72 24 p5_4_72 p5_4_96))) (@span_join (Z5 4) 72 120 72 (@span_join (Z5 4) 24 120 48 p5_4_120 (@span_join (Z5 4) 24 144 24 p5_4_144 p5_4_168)) (@span_join (Z5 4) 24 192 48 p5_4_192 (@span_join (Z5 4) 24 216 24 p5_4_216 p5_4_240)))) (@span_join (Z5 4) 144 264 144 (@span_join (Z5 4) 72 264 72 (@span_join (Z5 4) 24 264 48 p5_4_264 (@span_join (Z5 4) 24 288 24 p5_4_288 p5_4_312)) (@span_join (Z5 4) 24 336 48 p5_4_336 (@span_join (Z5 4) 24 360 24 p5_4_360 p5_4_384))) (@span_join (Z5 4) 72 408 72 (@span_join (Z5 4) 24 408 48 p5_4_408 (@span_join (Z5 4) 24 432 24 p5_4_432 p5_4_456)) (@span_join (Z5 4) 24 480 48 p5_4_480 (@span_join (Z5 4) 24 504 24 p5_4_504 p5_4_528))))) (@span_join (Z5 4) 264 552 287 (@span_join (Z5 4) 120 552 144 (@span_join (Z5 4) 48 552 72 (@span_join (Z5 4) 24 552 24 p5_4_552 p5_4_576) (@span_join (Z5 4) 24 600 48 p5_4_600 (@span_join (Z5 4) 24 624 24 p5_4_624 p5_4_648))) (@span_join (Z5 4) 72 672 72 (@span_join (Z5 4) 24 672 48 p5_4_672 (@span_join (Z5 4) 24 696 24 p5_4_696 p5_4_720)) (@span_join (Z5 4) 24 744 48 p5_4_744 (@span_join (Z5 4) 24 768 24 p5_4_768 p5_4_792)))) (@span_join (Z5 4) 144 816 143 (@span_join (Z5 4) 72 816 72 (@span_join (Z5 4) 24 816 48 p5_4_816 (@span_join (Z5 4) 24 840 24 p5_4_840 p5_4_864)) (@span_join (Z5 4) 24 888 48 p5_4_888 (@span_join (Z5 4) 24 912 24 p5_4_912 p5_4_936))) (@span_join (Z5 4) 72 960 71 (@span_join (Z5 4) 24 960 48 p5_4_960 (@span_join (Z5 4) 24 984 24 p5_4_984 p5_4_1008)) (@span_join (Z5 4) 24 1032 47 p5_4_1032 (@span_join (Z5 4) 24 1056 23 p5_4_1056 p5_4_1080))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_0 : span (Z5 5) 16 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_16 : span (Z5 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_32 : span (Z5 5) 16 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_48 : span (Z5 5) 16 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_64 : span (Z5 5) 16 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_80 : span (Z5 5) 16 80 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_96 : span (Z5 5) 16 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_112 : span (Z5 5) 16 112 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_128 : span (Z5 5) 16 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_144 : span (Z5 5) 16 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_160 : span (Z5 5) 16 160 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_176 : span (Z5 5) 16 176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_192 : span (Z5 5) 16 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_208 : span (Z5 5) 16 208 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_224 : span (Z5 5) 16 224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_240 : span (Z5 5) 16 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_256 : span (Z5 5) 16 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_272 : span (Z5 5) 16 272 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_288 : span (Z5 5) 16 288 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_304 : span (Z5 5) 16 304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_320 : span (Z5 5) 16 320 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_336 : span (Z5 5) 16 336 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_352 : span (Z5 5) 16 352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_368 : span (Z5 5) 16 368 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_384 : span (Z5 5) 16 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_400 : span (Z5 5) 16 400 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_416 : span (Z5 5) 16 416 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_432 : span (Z5 5) 16 432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_448 : span (Z5 5) 16 448 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_464 : span (Z5 5) 16 464 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_480 : span (Z5 5) 16 480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_496 : span (Z5 5) 16 496 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_512 : span (Z5 5) 16 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_528 : span (Z5 5) 16 528 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_544 : span (Z5 5) 16 544 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_560 : span (Z5 5) 16 560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_576 : span (Z5 5) 16 576 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_592 : span (Z5 5) 16 592 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_608 : span (Z5 5) 16 608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_624 : span (Z5 5) 16 624 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_640 : span (Z5 5) 16 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_656 : span (Z5 5) 16 656 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_672 : span (Z5 5) 16 672 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_688 : span (Z5 5) 16 688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_704 : span (Z5 5) 16 704 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_720 : span (Z5 5) 16 720 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_736 : span (Z5 5) 16 736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_752 : span (Z5 5) 16 752 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_768 : span (Z5 5) 16 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_784 : span (Z5 5) 16 784 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_800 : span (Z5 5) 16 800 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_816 : span (Z5 5) 16 816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_832 : span (Z5 5) 16 832 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_848 : span (Z5 5) 16 848 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_864 : span (Z5 5) 16 864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_880 : span (Z5 5) 16 880 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_896 : span (Z5 5) 16 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_912 : span (Z5 5) 16 912 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_928 : span (Z5 5) 16 928 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_944 : span (Z5 5) 16 944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_960 : span (Z5 5) 16 960 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_976 : span (Z5 5) 16 976 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_992 : span (Z5 5) 16 992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1008 : span (Z5 5) 16 1008 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1024 : span (Z5 5) 16 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1040 : span (Z5 5) 16 1040 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1056 : span (Z5 5) 16 1056 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1072 : span (Z5 5) 16 1072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1088 : span (Z5 5) 16 1088 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1104 : span (Z5 5) 16 1104 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1120 : span (Z5 5) 16 1120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1136 : span (Z5 5) 16 1136 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1152 : span (Z5 5) 16 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1168 : span (Z5 5) 16 1168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1184 : span (Z5 5) 16 1184 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1200 : span (Z5 5) 16 1200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1216 : span (Z5 5) 16 1216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1232 : span (Z5 5) 16 1232 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1248 : span (Z5 5) 16 1248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1264 : span (Z5 5) 16 1264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1280 : span (Z5 5) 16 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1296 : span (Z5 5) 16 1296 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1312 : span (Z5 5) 16 1312 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1328 : span (Z5 5) 16 1328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1344 : span (Z5 5) 16 1344 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1360 : span (Z5 5) 16 1360 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1376 : span (Z5 5) 16 1376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1392 : span (Z5 5) 16 1392 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1408 : span (Z5 5) 16 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_5_1424 : span (Z5 5) 16 1424 = true := by decide +kernel
theorem z5_5 : span (Z5 5) 1440 0 = true := (@span_join (Z5 5) 720 0 720 (@span_join (Z5 5) 352 0 368 (@span_join (Z5 5) 176 0 176 (@span_join (Z5 5) 80 0 96 (@span_join (Z5 5) 32 0 48 (@span_join (Z5 5) 16 0 16 p5_5_0 p5_5_16) (@span_join (Z5 5) 16 32 32 p5_5_32 (@span_join (Z5 5) 16 48 16 p5_5_48 p5_5_64))) (@span_join (Z5 5) 48 80 48 (@span_join (Z5 5) 16 80 32 p5_5_80 (@span_join (Z5 5) 16 96 16 p5_5_96 p5_5_112)) (@span_join (Z5 5) 16 128 32 p5_5_128 (@span_join (Z5 5) 16 144 16 p5_5_144 p5_5_160)))) (@span_join (Z5 5) 80 176 96 (@span_join (Z5 5) 32 176 48 (@span_join (Z5 5) 16 176 16 p5_5_176 p5_5_192) (@span_join (Z5 5) 16 208 32 p5_5_208 (@span_join (Z5 5) 16 224 16 p5_5_224 p5_5_240))) (@span_join (Z5 5) 48 256 48 (@span_join (Z5 5) 16 256 32 p5_5_256 (@span_join (Z5 5) 16 272 16 p5_5_272 p5_5_288)) (@span_join (Z5 5) 16 304 32 p5_5_304 (@span_join (Z5 5) 16 320 16 p5_5_320 p5_5_336))))) (@span_join (Z5 5) 176 352 192 (@span_join (Z5 5) 80 352 96 (@span_join (Z5 5) 32 352 48 (@span_join (Z5 5) 16 352 16 p5_5_352 p5_5_368) (@span_join (Z5 5) 16 384 32 p5_5_384 (@span_join (Z5 5) 16 400 16 p5_5_400 p5_5_416))) (@span_join (Z5 5) 48 432 48 (@span_join (Z5 5) 16 432 32 p5_5_432 (@span_join (Z5 5) 16 448 16 p5_5_448 p5_5_464)) (@span_join (Z5 5) 16 480 32 p5_5_480 (@span_join (Z5 5) 16 496 16 p5_5_496 p5_5_512)))) (@span_join (Z5 5) 96 528 96 (@span_join (Z5 5) 48 528 48 (@span_join (Z5 5) 16 528 32 p5_5_528 (@span_join (Z5 5) 16 544 16 p5_5_544 p5_5_560)) (@span_join (Z5 5) 16 576 32 p5_5_576 (@span_join (Z5 5) 16 592 16 p5_5_592 p5_5_608))) (@span_join (Z5 5) 48 624 48 (@span_join (Z5 5) 16 624 32 p5_5_624 (@span_join (Z5 5) 16 640 16 p5_5_640 p5_5_656)) (@span_join (Z5 5) 16 672 32 p5_5_672 (@span_join (Z5 5) 16 688 16 p5_5_688 p5_5_704)))))) (@span_join (Z5 5) 352 720 368 (@span_join (Z5 5) 176 720 176 (@span_join (Z5 5) 80 720 96 (@span_join (Z5 5) 32 720 48 (@span_join (Z5 5) 16 720 16 p5_5_720 p5_5_736) (@span_join (Z5 5) 16 752 32 p5_5_752 (@span_join (Z5 5) 16 768 16 p5_5_768 p5_5_784))) (@span_join (Z5 5) 48 800 48 (@span_join (Z5 5) 16 800 32 p5_5_800 (@span_join (Z5 5) 16 816 16 p5_5_816 p5_5_832)) (@span_join (Z5 5) 16 848 32 p5_5_848 (@span_join (Z5 5) 16 864 16 p5_5_864 p5_5_880)))) (@span_join (Z5 5) 80 896 96 (@span_join (Z5 5) 32 896 48 (@span_join (Z5 5) 16 896 16 p5_5_896 p5_5_912) (@span_join (Z5 5) 16 928 32 p5_5_928 (@span_join (Z5 5) 16 944 16 p5_5_944 p5_5_960))) (@span_join (Z5 5) 48 976 48 (@span_join (Z5 5) 16 976 32 p5_5_976 (@span_join (Z5 5) 16 992 16 p5_5_992 p5_5_1008)) (@span_join (Z5 5) 16 1024 32 p5_5_1024 (@span_join (Z5 5) 16 1040 16 p5_5_1040 p5_5_1056))))) (@span_join (Z5 5) 176 1072 192 (@span_join (Z5 5) 80 1072 96 (@span_join (Z5 5) 32 1072 48 (@span_join (Z5 5) 16 1072 16 p5_5_1072 p5_5_1088) (@span_join (Z5 5) 16 1104 32 p5_5_1104 (@span_join (Z5 5) 16 1120 16 p5_5_1120 p5_5_1136))) (@span_join (Z5 5) 48 1152 48 (@span_join (Z5 5) 16 1152 32 p5_5_1152 (@span_join (Z5 5) 16 1168 16 p5_5_1168 p5_5_1184)) (@span_join (Z5 5) 16 1200 32 p5_5_1200 (@span_join (Z5 5) 16 1216 16 p5_5_1216 p5_5_1232)))) (@span_join (Z5 5) 96 1248 96 (@span_join (Z5 5) 48 1248 48 (@span_join (Z5 5) 16 1248 32 p5_5_1248 (@span_join (Z5 5) 16 1264 16 p5_5_1264 p5_5_1280)) (@span_join (Z5 5) 16 1296 32 p5_5_1296 (@span_join (Z5 5) 16 1312 16 p5_5_1312 p5_5_1328))) (@span_join (Z5 5) 48 1344 48 (@span_join (Z5 5) 16 1344 32 p5_5_1344 (@span_join (Z5 5) 16 1360 16 p5_5_1360 p5_5_1376)) (@span_join (Z5 5) 16 1392 32 p5_5_1392 (@span_join (Z5 5) 16 1408 16 p5_5_1408 p5_5_1424)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_0 : span (Z5 6) 12 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_12 : span (Z5 6) 12 12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_24 : span (Z5 6) 12 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_36 : span (Z5 6) 12 36 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_48 : span (Z5 6) 12 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_60 : span (Z5 6) 12 60 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_72 : span (Z5 6) 12 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_84 : span (Z5 6) 12 84 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_96 : span (Z5 6) 12 96 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_108 : span (Z5 6) 12 108 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_120 : span (Z5 6) 12 120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_132 : span (Z5 6) 12 132 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_144 : span (Z5 6) 12 144 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_156 : span (Z5 6) 12 156 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_168 : span (Z5 6) 12 168 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_180 : span (Z5 6) 12 180 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_192 : span (Z5 6) 12 192 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_204 : span (Z5 6) 12 204 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_216 : span (Z5 6) 12 216 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_228 : span (Z5 6) 12 228 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_240 : span (Z5 6) 12 240 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_252 : span (Z5 6) 12 252 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_264 : span (Z5 6) 12 264 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_6_276 : span (Z5 6) 8 276 = true := by decide +kernel
theorem z5_6 : span (Z5 6) 284 0 = true := (@span_join (Z5 6) 144 0 140 (@span_join (Z5 6) 72 0 72 (@span_join (Z5 6) 36 0 36 (@span_join (Z5 6) 12 0 24 p5_6_0 (@span_join (Z5 6) 12 12 12 p5_6_12 p5_6_24)) (@span_join (Z5 6) 12 36 24 p5_6_36 (@span_join (Z5 6) 12 48 12 p5_6_48 p5_6_60))) (@span_join (Z5 6) 36 72 36 (@span_join (Z5 6) 12 72 24 p5_6_72 (@span_join (Z5 6) 12 84 12 p5_6_84 p5_6_96)) (@span_join (Z5 6) 12 108 24 p5_6_108 (@span_join (Z5 6) 12 120 12 p5_6_120 p5_6_132)))) (@span_join (Z5 6) 72 144 68 (@span_join (Z5 6) 36 144 36 (@span_join (Z5 6) 12 144 24 p5_6_144 (@span_join (Z5 6) 12 156 12 p5_6_156 p5_6_168)) (@span_join (Z5 6) 12 180 24 p5_6_180 (@span_join (Z5 6) 12 192 12 p5_6_192 p5_6_204))) (@span_join (Z5 6) 36 216 32 (@span_join (Z5 6) 12 216 24 p5_6_216 (@span_join (Z5 6) 12 228 12 p5_6_228 p5_6_240)) (@span_join (Z5 6) 12 252 20 p5_6_252 (@span_join (Z5 6) 12 264 8 p5_6_264 p5_6_276)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_7_0 : span (Z5 7) 10 0 = true := by decide +kernel
theorem z5_7 : span (Z5 7) 10 0 = true := p5_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p5_8_0 : span (Z5 8) 1 0 = true := by decide +kernel
theorem z5_8 : span (Z5 8) 1 0 = true := p5_8_0

def N4 : Nat → Nat
  | 3 => 27
  | 4 => 25
  | 5 => 3
  | 6 => 1
  | _ => 0

def SC4_3_0 : Nat := 0xff00f0e0ccccaaaaff00f0f0ccccaaaaffaaccccaa0050f0ffccffaaf0f0eeeeffccfcf0cc00aaaaff00c0c0aaaa3c3cff00ccccaaaa5a5af0f0ccccaaaa7f00ff00feaaf0f0ccccff00f0f0ecccaaaa0000ffccf0f0eeaaff00f0f0eeee0088ffc0f0f0ccccaaaaffaaf0f0ccccaa00ff00fcfcaaaa3c3cff00f0f8ccccaaaaffa0fafaf0f0ccccff00f0f0aaaa444cffaaf0f0ccccaaa0ff00f8f8f0f0eeeef0f0aaaa5f004c4cf0f0ccccaaaa00fef0f0ccccaaaa3f00ff00f0f0cccca2aaff00eeccaaaa50f0fcccf0f0aaaa0f00ff00fcf0eeaacccc
def HC4_3_0 : Nat := 0x9744b323870fa764647f5f344a97fe4e2c64a4b42c58324e2bf0facf2b8b7de226022a97218486b8190e3c4b17e09abc15969f3913b6a17f112c43760e4f6cfe0c8ec7af0889c65707d5621907b64b8606c5665305b4e972047467470322aa0a028099ca0211f65101a88f41
def readS4_3 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC4_3_0 (64 * o)
  unpack16 4 v
def readH4_3 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC4_3_0 (32 * o)) 0xffffffff
def SC4_4_0 : Nat := 0xfff0ff00f0f0ccccaaaaff00f0f0ccccaaaa8800ff00f0f0ccccaaaa3f00ff00f500f0f0ccccaaaaffaaf0f0ccccaaaaaa00ff00f0f0ccccaaaa8888ff00f0f0ccccaaaa5544ff00ccccaaaa30300c0c0000ffc0f0f0ccccaaaaffeeff00f0f0ccccaaaaff00f0f0ddccccccaaaa0000ffaaf0f0ccccaa00ff00f0f0f0c0ccccaaaaffccff00fcfcf0f0aaaaff00f0f0cccc222200aaff00f0f0ccccaaaa0300fff0ff00ccccaaaa0f00ff00f0f0cccca0a00a0a0000f0f0ccccaaaa3f00ffccff00f0f0aaaa0c0cff00f0f0ccccaaaa2200ff00f0f0ccccaaaa3030ff00f0f0cccccc0022aaff00f0f0ececaaaaa0a0ffa0ff00f0f0ccccaaaa
def HC4_4_0 : Nat := 0x4d4142c540cdca623192bc6f29a1722120a557042019334f1dd336fb1b1480eb15969f391543d05914172d2513b6a17f0bc918660b8c1d340772ca56074d671705a50f3705686625047467470470a2ee042ea96302a3bb2e028870b9012ebc65000f224f
def readS4_4 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC4_4_0 (80 * o)
  unpack16 5 v
def readH4_4 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC4_4_0 (32 * o)) 0xffffffff
def SC4_5_0 : Nat := 0xfff0ff00f0f0ccccaaaaff00f0f0ccccaaaa8888ff00f0f0ccccaaaa3030
def HC4_5_0 : Nat := 0x4d4142c52019334f02a3bb2e
def readS4_5 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC4_5_0 (80 * o)
  unpack16 5 v
def readH4_5 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC4_5_0 (32 * o)) 0xffffffff
def SC4_6_0 : Nat := 0xff00f0f0ccccaaaa
def HC4_6_0 : Nat := 0x870fa764
def readS4_6 (i : Nat) : List Nat :=
  let c := i / 32
  let o := i % 32
  let v := Nat.shiftRight SC4_6_0 (64 * o)
  unpack16 4 v
def readH4_6 (i : Nat) : Nat :=
  let c := i / 32
  let o := i % 32
  Nat.land (Nat.shiftRight HC4_6_0 (32 * o)) 0xffffffff
def S4 : Nat → Nat → List Nat
  | 3 => readS4_3
  | 4 => readS4_4
  | 5 => readS4_5
  | 6 => readS4_6
  | _ => fun _ => []
def H4 : Nat → Nat → Nat
  | 3 => readH4_3
  | 4 => readH4_4
  | 5 => readH4_5
  | 6 => readH4_6
  | _ => fun _ => 0
def idx4 (u : Nat) (zs : List Nat) : Nat :=
  bsr (H4 u) (hk zs) 12 0 (N4 u)

def Z4 (u i : Nat) : Bool :=
  bar 0xffff 0xfee8 S4 N4 idx4 ori4 u i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p4_3_0 : span (Z4 3) 27 0 = true := by decide +kernel
theorem z4_3 : span (Z4 3) 27 0 = true := p4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p4_4_0 : span (Z4 4) 25 0 = true := by decide +kernel
theorem z4_4 : span (Z4 4) 25 0 = true := p4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p4_5_0 : span (Z4 5) 3 0 = true := by decide +kernel
theorem z4_5 : span (Z4 5) 3 0 = true := p4_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p4_6_0 : span (Z4 6) 1 0 = true := by decide +kernel
theorem z4_6 : span (Z4 6) 1 0 = true := p4_6_0

theorem checked5 (u : Nat) (h3 : 3 ≤ u) (h8 : u ≤ 8) : ∀ i < N5 u, Z5 u i = true := by
  interval_cases u
  · exact fun i hi => span_ok z5_3 i (Nat.zero_le i) (by simpa [N5] using hi)
  · exact fun i hi => span_ok z5_4 i (Nat.zero_le i) (by simpa [N5] using hi)
  · exact fun i hi => span_ok z5_5 i (Nat.zero_le i) (by simpa [N5] using hi)
  · exact fun i hi => span_ok z5_6 i (Nat.zero_le i) (by simpa [N5] using hi)
  · exact fun i hi => span_ok z5_7 i (Nat.zero_le i) (by simpa [N5] using hi)
  · exact fun i hi => span_ok z5_8 i (Nat.zero_le i) (by simpa [N5] using hi)

theorem checked4 (u : Nat) (h3 : 3 ≤ u) (h6 : u ≤ 6) : ∀ i < N4 u, Z4 u i = true := by
  interval_cases u
  · exact fun i hi => span_ok z4_3 i (Nat.zero_le i) (by simpa [N4] using hi)
  · exact fun i hi => span_ok z4_4 i (Nat.zero_le i) (by simpa [N4] using hi)
  · exact fun i hi => span_ok z4_5 i (Nat.zero_le i) (by simpa [N4] using hi)
  · exact fun i hi => span_ok z4_6 i (Nat.zero_le i) (by simpa [N4] using hi)

def ins5BV : List (BitVec 32) := [0xaaaaaaaa#32, 0xcccccccc#32, 0xf0f0f0f0#32, 0xff00ff00#32, 0xffff0000#32]
def ins4BV : List (BitVec 16) := [0xaaaa#16, 0xcccc#16, 0xf0f0#16, 0xff00#16]
def ins5Nat : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def ins4Nat : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem s5_root : isPermFast ins5Nat (S5 8 0) = true := by decide +kernel
theorem s4_root : isPermFast ins4Nat (S4 6 0) = true := by decide +kernel

theorem ins5_img : (ins5BV.toFinset.image eBV).erase 0 = ins5Nat.toFinset := by decide +kernel
theorem ins4_img : (ins4BV.toFinset.image eBV).erase 0 = ins4Nat.toFinset := by decide +kernel

theorem sub5_sep : ∀ (i : Fin 5), allSep 0xffffffff (ins5Nat.erase (ins5Nat.getD i.val 0)) (Nat.xor 0xe8888880 0xffffffff) 0xe8888880 = false := by decide +kernel
theorem sub4_sep : ∀ (i : Fin 4), allSep 0xffff (ins4Nat.erase (ins4Nat.getD i.val 0)) (Nat.xor 0xfee8 0xffff) 0xfee8 = false := by decide +kernel

theorem allSep_mono_sub {W m0 m1 : Nat} (h0 : m0 < 2 ^ W) (h1 : m1 < 2 ^ W) {xs ys : List Nat}
    (hsub : ∀ w ∈ xs, w ∈ ys) (h : allSep (2 ^ W - 1) xs m0 m1 = true) :
    allSep (2 ^ W - 1) ys m0 m1 = true := by
  by_contra hf
  obtain ⟨i, hi, j, hj, hti, htj, hall⟩ := allSep_false ys m0 m1 h0 h1 (Bool.eq_false_iff.2 hf)
  have hall' : ∀ w ∈ xs, w.testBit i = w.testBit j := fun w hw => hall w (hsub w hw)
  have hcontra : ∀ (zs : List Nat) (a b : Nat), a.testBit i = true → b.testBit j = true →
      (∀ w ∈ zs, w.testBit i = w.testBit j) → allSep (2 ^ W - 1) zs a b = false := by
    intro zs; induction zs with
    | nil =>
      intro a b ha hb _
      have ha0 : a ≠ 0 := fun e => by subst e; simp at ha
      have hb0 : b ≠ 0 := fun e => by subst e; simp at hb
      simp [allSep, nat_beq_false_iff.2 ha0, nat_beq_false_iff.2 hb0]
    | cons w zs ihz =>
      intro a b ha hb hsame
      have ha0 : a ≠ 0 := fun e => by subst e; simp at ha
      have hb0 : b ≠ 0 := fun e => by subst e; simp at hb
      have hwi := hsame w (by simp)
      have hrest : ∀ u ∈ zs, u.testBit i = u.testBit j := fun u hu => hsame u (by simp [hu])
      simp only [allSep, nat_beq_false_iff.2 ha0, nat_beq_false_iff.2 hb0, Bool.or_false,
        Bool.false_or, Bool.and_eq_false_iff]
      cases hwv : w.testBit i
      · right
        apply ihz _ _ _ _ hrest
        · simp [Nat.land_eq, Nat.xor_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hi, ha, hwv]
        · simp [Nat.land_eq, Nat.xor_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hj, hb, ← hwi, hwv]
      · left
        apply ihz _ _ _ _ hrest
        · simp [Nat.land_eq, Nat.testBit_and, ha, hwv]
        · simp [Nat.land_eq, Nat.testBit_and, hb, ← hwi, hwv]
  have hbad := hcontra xs m0 m1 hti htj hall'
  rw [h] at hbad; cases hbad

theorem no_build_H5 : ∀ t : BitVec 32, (t = 0xe8888880#32 ∨ t = ~~~0xe8888880#32) →
    ¬ build basicOps t 8 ins5BV.toFinset := by
  intro t ht hb
  have het : eBV t = 0xe8888880 := by
    rcases ht with rfl | rfl <;> decide
  have hnb := build_to_nbuild (W := 32) (by omega) hb (by rw [het]; decide)
  rw [het, ins5_img] at hnb
  obtain ⟨s, hs, hlive⟩ := compress hnb
  have hrun := live_to_nrun hlive s.toList s.nodup_toList (Finset.toList_toFinset s)
  have hsep := nrun_allSep (W := 32) (by decide) hrun
  have hfull : s = ins5Nat.toFinset := by
    apply Finset.Subset.antisymm hs
    intro x hx
    by_contra hxn
    have hsub : ∀ w ∈ s.toList, w ∈ ins5Nat.erase x := by
      intro w hw
      have hws : w ∈ s := Finset.mem_toList.1 hw
      have hwx : w ≠ x := fun e => hxn (e ▸ hws)
      exact (List.Nodup.mem_erase_iff (by decide : ins5Nat.Nodup)).2 ⟨hwx, List.mem_toFinset.1 (hs hws)⟩
    have hidx : ∃ i : Fin 5, ins5Nat.getD i.val 0 = x := by
      have hx' : x ∈ ins5Nat := List.mem_toFinset.1 hx
      simp only [ins5Nat, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
    obtain ⟨i, rfl⟩ := hidx
    have hbad : allSep 0xffffffff (ins5Nat.erase (ins5Nat.getD i.val 0)) (Nat.xor 0xe8888880 0xffffffff) 0xe8888880 = true :=
      allSep_mono_sub (W := 32) (by decide) (by decide) hsub hsep
    rw [sub5_sep i] at hbad; cases hbad
  have hperm : s.toList.Perm ins5Nat := by
    refine (List.perm_ext_iff_of_nodup s.nodup_toList (by decide)).2 ?_
    intro x; rw [Finset.mem_toList, hfull, List.mem_toFinset]
  have hrun_root := NRun.perm (hperm.trans (isPermFast_sound s5_root)) hrun
  exact bar_sound (W := 32) (by decide) S5 N5 idx5 ori5 (fun h => ori5_nrun h) checked5 8 (by omega) le_rfl 0 (by decide) hrun_root

theorem no_build_K4 : ∀ t : BitVec 16, (t = 0xfee8#16 ∨ t = ~~~0xfee8#16) →
    ¬ build basicOps t 6 ins4BV.toFinset := by
  intro t ht hb
  have het : eBV t = 0xfee8 := by
    rcases ht with rfl | rfl <;> decide
  have hnb := build_to_nbuild (W := 16) (by omega) hb (by rw [het]; decide)
  rw [het, ins4_img] at hnb
  obtain ⟨s, hs, hlive⟩ := compress hnb
  have hrun := live_to_nrun hlive s.toList s.nodup_toList (Finset.toList_toFinset s)
  have hsep := nrun_allSep (W := 16) (by decide) hrun
  have hfull : s = ins4Nat.toFinset := by
    apply Finset.Subset.antisymm hs
    intro x hx
    by_contra hxn
    have hsub : ∀ w ∈ s.toList, w ∈ ins4Nat.erase x := by
      intro w hw
      have hws : w ∈ s := Finset.mem_toList.1 hw
      have hwx : w ≠ x := fun e => hxn (e ▸ hws)
      exact (List.Nodup.mem_erase_iff (by decide : ins4Nat.Nodup)).2 ⟨hwx, List.mem_toFinset.1 (hs hws)⟩
    have hidx : ∃ i : Fin 4, ins4Nat.getD i.val 0 = x := by
      have hx' : x ∈ ins4Nat := List.mem_toFinset.1 hx
      simp only [ins4Nat, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    obtain ⟨i, rfl⟩ := hidx
    have hbad : allSep 0xffff (ins4Nat.erase (ins4Nat.getD i.val 0)) (Nat.xor 0xfee8 0xffff) 0xfee8 = true :=
      allSep_mono_sub (W := 16) (by decide) (by decide) hsub hsep
    rw [sub4_sep i] at hbad; cases hbad
  have hperm : s.toList.Perm ins4Nat := by
    refine (List.perm_ext_iff_of_nodup s.nodup_toList (by decide)).2 ?_
    intro x; rw [Finset.mem_toList, hfull, List.mem_toFinset]
  have hrun_root := NRun.perm (hperm.trans (isPermFast_sound s4_root)) hrun
  exact bar_sound (W := 16) (by decide) S4 N4 idx4 ori4 (fun h => ori4_nrun h) checked4 6 (by omega) le_rfl 0 (by decide) hrun_root

def F6_bv : W64 := 0xfee8e8e8e8e8e800#64
def x6 : Fin 6 → W64
  | 0 => 0xaaaaaaaaaaaaaaaa#64
  | 1 => 0xcccccccccccccccc#64
  | 2 => 0xf0f0f0f0f0f0f0f0#64
  | 3 => 0xff00ff00ff00ff00#64
  | 4 => 0xffff0000ffff0000#64
  | 5 => 0xffffffff00000000#64

def ins6BV : List W64 := [x6 0, x6 1, x6 2, x6 3, x6 4, x6 5]

def selRows (idx : ℕ → Fin 64) (v : W64) : (M : ℕ) → BitVec M
  | 0 => 0#0
  | m + 1 => BitVec.cons (v[(idx m).val]) (selRows idx v m)

theorem selRows_and (idx : ℕ → Fin 64) (a b : W64) : ∀ M,
    selRows idx (a &&& b) M = selRows idx a M &&& selRows idx b M
  | 0 => Subsingleton.elim _ _
  | m + 1 => by
    simp only [selRows, BitVec.getElem_and]
    rw [selRows_and idx a b m]
    apply BitVec.eq_of_getElem_eq; intro k hk
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [BitVec.getElem_cons, hkm]

theorem selRows_or (idx : ℕ → Fin 64) (a b : W64) : ∀ M,
    selRows idx (a ||| b) M = selRows idx a M ||| selRows idx b M
  | 0 => Subsingleton.elim _ _
  | m + 1 => by
    simp only [selRows, BitVec.getElem_or]
    rw [selRows_or idx a b m]
    apply BitVec.eq_of_getElem_eq; intro k hk
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [BitVec.getElem_cons, hkm]

theorem selRows_not (idx : ℕ → Fin 64) (a : W64) : ∀ M,
    selRows idx (~~~a) M = ~~~(selRows idx a M)
  | 0 => Subsingleton.elim _ _
  | m + 1 => by
    simp only [selRows, BitVec.getElem_not]
    rw [selRows_not idx a m]
    apply BitVec.eq_of_getElem_eq; intro k hk
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [BitVec.getElem_cons, hkm]

def idxA0 (i : Fin 3) (k : ℕ) : Fin 64 :=
  let v := k % 32
  let b0 := v % 2
  let b1 := (v / 2) % 2
  let hi := v / 4
  let lo3 :=
    if i.val = 0 then b0 * 2 + b1 * 4
    else if i.val = 1 then b0 * 1 + b1 * 4
    else b0 * 1 + b1 * 2
  ⟨lo3 + hi * 8, by
    have hv : v < 32 := Nat.mod_lt k (by omega)
    dsimp only [lo3, b0, b1, hi]
    split_ifs <;> omega⟩

def idxB1 (p : Fin 3) (k : ℕ) : Fin 64 :=
  let v := k % 16
  let lo3 := v % 8
  let b3 := v / 8
  let hi3 :=
    if p.val = 0 then 1 + 2 + b3 * 4
    else if p.val = 1 then 1 + b3 * 2 + 4
    else b3 * 1 + 2 + 4
  ⟨lo3 + hi3 * 8, by
    have hv : v < 16 := Nat.mod_lt k (by omega)
    dsimp only [hi3, lo3, b3]
    split_ifs <;> omega⟩

theorem resA0_target (i : Fin 3) : selRows (idxA0 i) F6_bv 32 = 0xe8888880#32 := by
  fin_cases i <;> decide +kernel

theorem resA0_xi (i : Fin 3) : selRows (idxA0 i) (x6 ⟨i.val, by omega⟩) 32 = 0 := by
  fin_cases i <;> decide +kernel

theorem resA0_holds (i : Fin 3) (k : Fin 6) :
    selRows (idxA0 i) (x6 k) 32 = 0 ∨ selRows (idxA0 i) (x6 k) 32 ∈ ins5BV := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem resB1_target (p : Fin 3) : selRows (idxB1 p) F6_bv 16 = 0xfee8#16 := by
  fin_cases p <;> decide +kernel

theorem resB1_holds (p : Fin 3) (k : Fin 6) :
    selRows (idxB1 p) (x6 k) 16 = ~~~0 ∨ selRows (idxB1 p) (x6 k) 16 ∈ ins4BV := by
  fin_cases p <;> fin_cases k <;> decide +kernel

theorem resB1_const_0 : selRows (idxB1 0) (x6 3) 16 = ~~~0 ∧ selRows (idxB1 0) (x6 4) 16 = ~~~0 := by decide +kernel
theorem resB1_const_1 : selRows (idxB1 1) (x6 3) 16 = ~~~0 ∧ selRows (idxB1 1) (x6 5) 16 = ~~~0 := by decide +kernel
theorem resB1_const_2 : selRows (idxB1 2) (x6 4) 16 = ~~~0 ∧ selRows (idxB1 2) (x6 5) 16 = ~~~0 := by decide +kernel

def applyOp64 (op : Fin 4) (a b : W64) : W64 :=
  match op.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

theorem basicOps_eq_applyOp64 (a b z : W64) (hz : z ∈ basicOps a b) :
    ∃ op : Fin 4, z = applyOp64 op a b := by
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def sepPair64 (p q : Fin 64) (w : W64) : Prop := w[p.val] ≠ w[q.val]

theorem sepPair64_basicOps (p q : Fin 64) (a b z : W64) (hz : z ∈ basicOps a b)
    (h : sepPair64 p q z) : sepPair64 p q a ∨ sepPair64 p q b := by
  by_contra hnot
  have ha : a[p.val] = a[q.val] := by
    by_contra hne; exact hnot (.inl hne)
  have hb : b[p.val] = b[q.val] := by
    by_contra hne; exact hnot (.inr hne)
  apply h
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha, hb]

def flip6 (i : Fin 6) (p : Fin 64) : Fin 64 :=
  ⟨(Nat.xor p.val (1 <<< i.val)) % 64, Nat.mod_lt _ (by omega)⟩

theorem f6_all_ess : ∀ i : Fin 6, ∃ p : Fin 64,
    F6_bv[p.val] ≠ F6_bv[(flip6 i p).val] ∧ ∀ k : Fin 6, k ≠ i → (x6 k)[p.val] = (x6 k)[(flip6 i p).val] := by
  decide +kernel

theorem f6_forced_live : ∀ (i j : Fin 6), i ≠ j → ∀ (op : Fin 4), ∃ p : Fin 64,
    F6_bv[p.val] ≠ F6_bv[(flip6 i p).val] ∧
    (∀ k : Fin 6, k ≠ i → (x6 k)[p.val] = (x6 k)[(flip6 i p).val]) ∧
    (applyOp64 op (x6 i) (x6 j))[p.val] = (applyOp64 op (x6 i) (x6 j))[(flip6 i p).val] := by
  decide +kernel

theorem x6_inj : ∀ i j : Fin 6, x6 i = x6 j → i = j := by decide +kernel

theorem x6_mem_ins6 (k : Fin 6) : x6 k ∈ ins6BV.toFinset := by
  fin_cases k <;> simp only [ins6BV, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] <;> tauto

theorem no_build_F6 : ∀ t : W64, (t = F6_bv ∨ t = ~~~F6_bv) →
    ¬ build basicOps t 10 ins6BV.toFinset := by
  intro t ht hb
  obtain ⟨s, hs, hlive⟩ := compress hb
  have hfull : s = ins6BV.toFinset := by
    apply Finset.Subset.antisymm hs
    intro w hw
    have hmem : ∃ i : Fin 6, w = x6 i := by
      simp only [ins6BV, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    obtain ⟨i, rfl⟩ := hmem
    obtain ⟨p, hfpq, hother⟩ := f6_all_ess i
    let q := flip6 i p
    have ht_sep : sepPair64 p q t := by
      rcases ht with rfl | rfl
      · exact hfpq
      · simp [sepPair64, q, hfpq]
    obtain ⟨u, hus, husep⟩ := live_separates (sepPair64 p q) ht_sep (sepPair64_basicOps p q) hlive
    have hu6 := hs hus
    simp only [ins6BV, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu6
    have hu_eq : u = x6 i := by
      by_contra hne
      rcases hu6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact husep (hother 0 (fun e => hne (e ▸ rfl)))
      · exact husep (hother 1 (fun e => hne (e ▸ rfl)))
      · exact husep (hother 2 (fun e => hne (e ▸ rfl)))
      · exact husep (hother 3 (fun e => hne (e ▸ rfl)))
      · exact husep (hother 4 (fun e => hne (e ▸ rfl)))
      · exact husep (hother 5 (fun e => hne (e ▸ rfl)))
    exact hu_eq ▸ hus
  subst hfull
  rcases first_live hlive with hsing | ⟨a, ha, b, hb', hab, z, hz, hzout, rest, hins_eq, htail⟩
  · have hc := congrArg Finset.card hsing
    have h6 : ins6BV.toFinset.card = 6 := by decide
    simp [h6] at hc
  · have to_idx : ∀ u ∈ ins6BV.toFinset, ∃ i : Fin 6, u = x6 i := by
      intro u hu
      simp only [ins6BV, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    obtain ⟨i, rfl⟩ := to_idx a ha
    obtain ⟨j, rfl⟩ := to_idx b hb'
    have hij : i ≠ j := fun e => hab (e ▸ rfl)
    obtain ⟨op, hzop⟩ := basicOps_eq_applyOp64 (x6 i) (x6 j) z hz
    have hkeep : ∀ (i0 j0 : Fin 6), i0 ≠ j0 → z ∈ basicOps (x6 i0) (x6 j0) → x6 i0 ∈ insert z rest := by
      intro i0 j0 hne hz0
      obtain ⟨op0, hop0⟩ := basicOps_eq_applyOp64 (x6 i0) (x6 j0) z hz0
      obtain ⟨p, hfpq, hother, hzsame⟩ := f6_forced_live i0 j0 hne op0
      let q := flip6 i0 p
      have ht_sep : sepPair64 p q t := by
        rcases ht with rfl | rfl
        · exact hfpq
        · simp [sepPair64, q, hfpq]
      obtain ⟨u, hus, husep⟩ := live_separates (sepPair64 p q) ht_sep (sepPair64_basicOps p q) htail
      rcases Finset.mem_insert.mp hus with rfl | hur
      · exact False.elim (husep (hop0.symm ▸ hzsame))
      · have hu6 : u ∈ ins6BV.toFinset := by rw [hins_eq]; simp [hur]
        obtain ⟨k, rfl⟩ := to_idx u hu6
        by_cases hki : k = i0
        · subst hki; exact hus
        · exact False.elim (husep (hother k hki))
    have hi_in : x6 i ∈ rest := by
      rcases Finset.mem_insert.mp (hkeep i j hij hz) with h | h
      · exact False.elim (hzout (h ▸ ha))
      · exact h
    have hz_sym : z ∈ basicOps (x6 j) (x6 i) := by
      simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl | rfl | rfl
      · exact .inl (by apply BitVec.eq_of_getElem_eq; intro k hk; simp [Bool.and_comm])
      · exact .inr (.inl (by apply BitVec.eq_of_getElem_eq; intro k hk; simp [Bool.or_comm]))
      · exact .inr (.inr (.inr rfl))
      · exact .inr (.inr (.inl rfl))
    have hj_in : x6 j ∈ rest := by
      rcases Finset.mem_insert.mp (hkeep j i hij.symm hz_sym) with h | h
      · exact False.elim (hzout (h ▸ hb'))
      · exact h
    have hrest_eq : rest = ins6BV.toFinset := by
      rw [hins_eq, Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hi_in), Finset.insert_eq_of_mem hj_in]
    rw [hrest_eq] at htail
    have kill_A : ∀ (i0 : Fin 3) (j0 : Fin 6), z ∈ basicOps (x6 ⟨i0.val, by omega⟩) (x6 j0) → False := by
      intro i0 j0 hz0
      let f : W64 → BitVec 32 := fun v => selRows (idxA0 i0) v 32
      have hf_and : ∀ u v, f (u &&& v) = f u &&& f v := fun u v => selRows_and (idxA0 i0) u v 32
      have hf_or : ∀ u v, f (u ||| v) = f u ||| f v := fun u v => selRows_or (idxA0 i0) u v 32
      have hf_not : ∀ u, f (~~~u) = ~~~(f u) := fun u => selRows_not (idxA0 i0) u 32
      have hft : f t = 0xe8888880#32 ∨ f t = ~~~0xe8888880#32 := by
        rcases ht with rfl | rfl
        · exact .inl (resA0_target i0)
        · exact .inr (by rw [hf_not]; exact congrArg (~~~·) (resA0_target i0))
      have hnc : ¬ IsConst (f t) := by
        rcases hft with h | h <;> rw [h] <;> unfold IsConst <;> decide
      have hholds_ins : ∀ w ∈ ins6BV.toFinset, holds ins5BV.toFinset (f w) := by
        intro w hw
        obtain ⟨k, rfl⟩ := to_idx w hw
        rcases resA0_holds i0 k with h0 | hmem
        · exact .inl h0
        · exact .inr (.inr ⟨f (x6 k), List.mem_toFinset.2 hmem, .inl rfl⟩)
      have hholds_s : ∀ w ∈ insert z ins6BV.toFinset, holds ins5BV.toFinset (f w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · rw [hw]
          have hfxi : f (x6 ⟨i0.val, by omega⟩) = 0 := resA0_xi i0
          have hfz : f z ∈ basicOps (f (x6 ⟨i0.val, by omega⟩)) (f (x6 j0)) := by
            simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz0 ⊢
            rcases hz0 with hz0 | hz0 | hz0 | hz0 <;> rw [hz0]
            · exact .inl (hf_and _ _)
            · exact .inr (.inl (hf_or _ _))
            · exact .inr (.inr (.inl (by rw [hf_and, hf_not])))
            · exact .inr (.inr (.inr (by rw [hf_and, hf_not])))
          have hxj := hholds_ins (x6 j0) (x6_mem_ins6 j0)
          rcases bv_const_basic _ _ (.inl (.inl hfxi)) (f z) hfz with h | h | h | h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inl (h.trans hfxi)
          · exact .inr (.inl (by rw [h, hfxi]))
          · rw [h]; exact hxj
          · rw [h]; exact holds_not hxj
        · exact hholds_ins w hw
      obtain ⟨m, hm, t', ht', hbld⟩ := live_kill_card f hf_and hf_or hf_not hnc htail ins5BV.toFinset hholds_s
      have hxi_in : x6 ⟨i0.val, by omega⟩ ∈ (insert z ins6BV.toFinset).filter (fun w => isConstBool (f w) = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem (x6_mem_ins6 ⟨i0.val, by omega⟩),
          (isConstBool_iff _).2 (.inl (resA0_xi i0))⟩
      have hc1 : 1 ≤ ((insert z ins6BV.toFinset).filter (fun w => isConstBool (f w) = true)).card :=
        Finset.one_le_card.2 ⟨_, hxi_in⟩
      have hm8 : m ≤ 8 := Nat.le_of_add_le_add_left (le_trans (Nat.add_le_add_right hc1 m) hm)
      have ht'2 : t' = 0xe8888880#32 ∨ t' = ~~~0xe8888880#32 := by
        rcases hft with h | h <;> rcases ht' with rfl | rfl
        · exact .inl h
        · exact .inr (by rw [h])
        · exact .inr h
        · exact .inl (by rw [h, BitVec.not_not])
      exact no_build_H5 t' ht'2 (build_mono hm8 hbld)
    by_cases hi3 : i.val < 3
    · exact kill_A ⟨i.val, hi3⟩ j hz
    · by_cases hj3 : j.val < 3
      · exact kill_A ⟨j.val, hj3⟩ i hz_sym
      · have kill_B : ∀ (p : Fin 3) (u v : Fin 6), u ≠ v →
            selRows (idxB1 p) (x6 u) 16 = ~~~0 → selRows (idxB1 p) (x6 v) 16 = ~~~0 →
            z ∈ basicOps (x6 u) (x6 v) → False := by
          intro p u v huv hfu hfv hzuv
          let f : W64 → BitVec 16 := fun w => selRows (idxB1 p) w 16
          have hf_and : ∀ a1 b1, f (a1 &&& b1) = f a1 &&& f b1 := fun a1 b1 => selRows_and (idxB1 p) a1 b1 16
          have hf_or : ∀ a1 b1, f (a1 ||| b1) = f a1 ||| f b1 := fun a1 b1 => selRows_or (idxB1 p) a1 b1 16
          have hf_not : ∀ a1, f (~~~a1) = ~~~(f a1) := fun a1 => selRows_not (idxB1 p) a1 16
          have hft : f t = 0xfee8#16 ∨ f t = ~~~0xfee8#16 := by
            rcases ht with rfl | rfl
            · exact .inl (resB1_target p)
            · exact .inr (by rw [hf_not]; exact congrArg (~~~·) (resB1_target p))
          have hnc : ¬ IsConst (f t) := by
            rcases hft with h | h <;> rw [h] <;> unfold IsConst <;> decide
          have hfz_const : IsConst (f z) := by
            have hfz : f z ∈ basicOps (f (x6 u)) (f (x6 v)) := by
              simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hzuv ⊢
              rcases hzuv with hzuv | hzuv | hzuv | hzuv <;> rw [hzuv]
              · exact .inl (hf_and _ _)
              · exact .inr (.inl (hf_or _ _))
              · exact .inr (.inr (.inl (by rw [hf_and, hf_not])))
              · exact .inr (.inr (.inr (by rw [hf_and, hf_not])))
            have hfu' : f (x6 u) = ~~~0 := hfu
            have hfv' : f (x6 v) = ~~~0 := hfv
            rcases bv_const_basic _ _ (.inl (.inr hfu')) (f z) hfz with h | h | h | h | h | h
            · exact .inl h
            · exact .inr h
            · exact .inr (h.trans hfu')
            · exact .inl (by rw [h, hfu', BitVec.not_not])
            · exact .inr (h.trans hfv')
            · exact .inl (by rw [h, hfv', BitVec.not_not])
          have hholds_s : ∀ w ∈ insert z ins6BV.toFinset, holds ins4BV.toFinset (f w) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · rcases hfz_const with h | h
              · exact .inl h
              · exact .inr (.inl h)
            · obtain ⟨k, rfl⟩ := to_idx w hw
              rcases resB1_holds p k with h1 | hmem
              · exact .inr (.inl h1)
              · exact .inr (.inr ⟨f (x6 k), List.mem_toFinset.2 hmem, .inl rfl⟩)
          obtain ⟨m, hm, t', ht', hbld⟩ := live_kill_card f hf_and hf_or hf_not hnc htail ins4BV.toFinset hholds_s
          have hsub3 : ({z, x6 u, x6 v} : Finset W64) ⊆ (insert z ins6BV.toFinset).filter (fun w => isConstBool (f w) = true) := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            refine Finset.mem_filter.2 ⟨?_, ?_⟩
            · rcases hw with rfl | rfl | rfl
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (x6_mem_ins6 u)
              · exact Finset.mem_insert_of_mem (x6_mem_ins6 v)
            · rcases hw with rfl | rfl | rfl
              · exact (isConstBool_iff _).2 hfz_const
              · exact (isConstBool_iff _).2 (.inr hfu)
              · exact (isConstBool_iff _).2 (.inr hfv)
          have hne_zu : z ≠ x6 u := fun e => hzout (e ▸ x6_mem_ins6 u)
          have hne_zv : z ≠ x6 v := fun e => hzout (e ▸ x6_mem_ins6 v)
          have hne_uv : x6 u ≠ x6 v := fun e => huv (x6_inj u v e)
          have hc3 : 3 ≤ ((insert z ins6BV.toFinset).filter (fun w => isConstBool (f w) = true)).card := by
            have h1 := Finset.card_le_card hsub3
            rw [Finset.card_insert_of_notMem (by simp [hne_zu, hne_zv]),
                Finset.card_insert_of_notMem (by simp [hne_uv]), Finset.card_singleton] at h1
            exact h1
          have hm6 : m ≤ 6 := Nat.le_of_add_le_add_left (le_trans (Nat.add_le_add_right hc3 m) hm)
          have ht'2 : t' = 0xfee8#16 ∨ t' = ~~~0xfee8#16 := by
            rcases hft with h | h <;> rcases ht' with rfl | rfl
            · exact .inl h
            · exact .inr (by rw [h])
            · exact .inr h
            · exact .inl (by rw [h, BitVec.not_not])
          exact no_build_K4 t' ht'2 (build_mono hm6 hbld)
        fin_cases i <;> fin_cases j <;> simp at hi3 hj3 hij
        · exact kill_B 0 3 4 (by decide) resB1_const_0.1 resB1_const_0.2 hz
        · exact kill_B 1 3 5 (by decide) resB1_const_1.1 resB1_const_1.2 hz
        · exact kill_B 0 4 3 (by decide) resB1_const_0.2 resB1_const_0.1 hz
        · exact kill_B 2 4 5 (by decide) resB1_const_2.1 resB1_const_2.2 hz
        · exact kill_B 1 5 3 (by decide) resB1_const_1.2 resB1_const_1.1 hz
        · exact kill_B 2 5 4 (by decide) resB1_const_2.2 resB1_const_2.1 hz

def targetFn (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 3907577856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem sample64 : ∀ k : Fin 64,
    targetFn (fun i : Fin 6 => bit64 k (ins6BV.getD i.val 0)) = bit64 k F6_bv := by
  decide +kernel

theorem bound_F6 (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetFn x) :
    10 < binaryCost gs := by
  by_contra hlow
  have hle : binaryCost gs ≤ 10 := Nat.le_of_not_lt hlow
  have init : ∀ u ∈ ins6BV, holds ins6BV.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.2 hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step64 (ins6BV.map (bit64 k))).getD o false = bit64 k F6_bv := by
    let x (i : Fin 6) : Bool := bit64 k (ins6BV.getD i.val 0)
    have same : List.ofFn x = ins6BV.map (bit64 k) := by
      apply List.ext_getElem
      · simp [ins6BV]
      · intro i hi hj
        have hlt : i < ins6BV.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins6BV.map (bit64 k)) = bit64 k F6_bv
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, hrun⟩ := compile64 F6_bv (by decide) (by decide) gs o hg ins6BV ins6BV.toFinset init evaluate
  exact no_build_F6 t ht (build_mono hle hrun)

def wg : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 2]⟩,
   ⟨.or, [3, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [13, 5]⟩,
   ⟨.and, [9, 12]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [15, 16]⟩]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval : ∀ x : Fin 6 → Bool,
    Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = targetFn x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12300

theorem PEqualNP.Outside.L_meta_12300 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 3907577856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 3907577856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_12300.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_12300.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_12300.isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_12300.legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    have hb := PEqualNP.Outside.L_meta_12300.bound_F6 C.gates C.output hleg heval
    have hsz : C.size = C.gates.length := rfl
    have hl : (⟨PEqualNP.Outside.L_meta_12300.wg, 17⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 12 := rfl
    exact ⟨⟨PEqualNP.Outside.L_meta_12300.wg, 17⟩, PEqualNP.Outside.L_meta_12300.wfits, by omega, PEqualNP.Outside.L_meta_12300.weval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
