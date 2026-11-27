import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18717

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Fn := (Fin 6 → Bool) → Bool
def con (c : Bool) : Fn := fun _ => c
def lit (i : Fin 6) (s : Bool) : Fn := fun v => xor (v i) s
def sg (u : Fn) (s : Bool) : Fn := fun v => xor (u v) s
def An (a b : Fn) : Fn := fun v => a v && b v
def rs (x : Fin 6) (c : Bool) (u : Fn) : Fn := fun v => u (Function.update v x c)

/-- Available functions: constants, literals, earlier gates and their complements. -/
def Av (g : ℕ → Fn) (k : ℕ) : Set Fn := {h | (∃ c, h = con c) ∨ (∃ i s, h = lit i s) ∨ ∃ j, j < k ∧ ∃ s, h = sg (g j) s}
def AvE (g : ℕ → Fn) (k i : ℕ) : Set Fn := {h | (∃ c, h = con c) ∨ (∃ i s, h = lit i s) ∨ ∃ j, j < k ∧ j ≠ i ∧ ∃ s, h = sg (g j) s}
def Ch (g : ℕ → Fn) (k : ℕ) : Prop := ∀ i, i < k → ∃ a ∈ Av g i, ∃ b ∈ Av g i, g i = An a b
def Comp (f : Fn) (k : ℕ) : Prop := ∃ g, Ch g k ∧ f ∈ Av g k

theorem sg_sg (u : Fn) (s t : Bool) : sg (sg u s) t = sg u (xor s t) := by
  funext v; simp [sg]
theorem sg_con (c s : Bool) : sg (con c) s = con (xor c s) := rfl
theorem sg_lit (i : Fin 6) (s t : Bool) : sg (lit i s) t = lit i (xor s t) := by
  funext v; simp [sg, lit]
theorem sg_false (u : Fn) : sg u false = u := by funext v; simp [sg]
theorem An_comm (a b : Fn) : An a b = An b a := by funext v; simp [An, Bool.and_comm]

theorem Av_con (g : ℕ → Fn) (k : ℕ) (c : Bool) : con c ∈ Av g k := Or.inl ⟨c, rfl⟩
theorem Av_lit (g : ℕ → Fn) (k : ℕ) (i : Fin 6) (s : Bool) : lit i s ∈ Av g k := Or.inr (Or.inl ⟨i, s, rfl⟩)
theorem Av_gate (g : ℕ → Fn) (k j : ℕ) (h : j < k) (s : Bool) : sg (g j) s ∈ Av g k := Or.inr (Or.inr ⟨j, h, s, rfl⟩)

theorem Av_sg {g : ℕ → Fn} {k : ℕ} {h : Fn} (hh : h ∈ Av g k) (s : Bool) : sg h s ∈ Av g k := by
  rcases hh with ⟨c, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, hj, t, rfl⟩
  · rw [sg_con]; exact Av_con _ _ _
  · rw [sg_lit]; exact Av_lit _ _ _ _
  · rw [sg_sg]; exact Av_gate _ _ _ hj _

theorem Av_mono {g : ℕ → Fn} {k l : ℕ} (h : k ≤ l) : Av g k ⊆ Av g l := by
  rintro u (hc | hl | ⟨j, hj, hs⟩)
  · exact Or.inl hc
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr ⟨j, by omega, hs⟩)

theorem Av_congr {g g' : ℕ → Fn} {k : ℕ} (h : ∀ j, j < k → g j = g' j) : Av g k ⊆ Av g' k := by
  rintro u (hc | hl | ⟨j, hj, s, rfl⟩)
  · exact Or.inl hc
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr ⟨j, hj, s, by rw [h j hj]⟩)

/-- Drop redundant gates. -/
theorem prune (g : ℕ → Fn) : ∀ k, Ch g k → ∀ R : Finset ℕ, (∀ i ∈ R, i < k ∧ g i ∈ Av g i) →
    ∃ g' k', Ch g' k' ∧ k' + R.card = k ∧ Av g k ⊆ Av g' k' := by
  intro k
  induction k with
  | zero =>
    intro _ R hR
    have : R = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => absurd (hR i hi).1 (by omega)
    subst this
    exact ⟨g, 0, fun i hi => absurd hi (by omega), by simp, fun _ h => h⟩
  | succ k ih =>
    intro hC R hR
    have hC' : Ch g k := fun i hi => hC i (by omega)
    by_cases hk : k ∈ R
    · obtain ⟨g', k', h1, h2, h3⟩ := ih hC' (R.erase k) fun i hi => by
        have hiR := Finset.mem_of_mem_erase hi
        have := (hR i hiR).1
        have hne := Finset.ne_of_mem_erase hi
        exact ⟨by omega, (hR i hiR).2⟩
      have hc := Finset.card_erase_of_mem hk
      have hp : 0 < R.card := Finset.card_pos.2 ⟨k, hk⟩
      refine ⟨g', k', h1, by omega, ?_⟩
      rintro u (hc | hl | ⟨j, hj, s, rfl⟩)
      · exact Or.inl hc
      · exact Or.inr (Or.inl hl)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · exact h3 (Av_gate _ _ _ h _)
        · exact Av_sg (h3 (hR _ hk).2) s
    · obtain ⟨g', k', h1, h2, h3⟩ := ih hC' R fun i hi => by
        have := (hR i hi).1
        have : i ≠ k := fun h => hk (h ▸ hi)
        exact ⟨by omega, (hR i hi).2⟩
      let g2 : ℕ → Fn := fun i => if i < k' then g' i else g k
      have e : ∀ j, j < k' → g' j = g2 j := fun j hj => by simp only [g2, if_pos hj]
      have hlast : g2 k' = g k := by simp [g2]
      refine ⟨g2, k' + 1, ?_, by omega, ?_⟩
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · obtain ⟨a, ha, b, hb, hab⟩ := h1 i h
          have e' : ∀ j, j < i → g' j = g2 j := fun j hj => e j (by omega)
          exact ⟨a, Av_congr e' ha, b, Av_congr e' hb, by rw [← e i h]; exact hab⟩
        · obtain ⟨a, ha, b, hb, hab⟩ := hC k (by omega)
          exact ⟨a, Av_congr e (h3 ha), b, Av_congr e (h3 hb), by rw [hlast]; exact hab⟩
      · rintro u (hc | hl | ⟨j, hj, s, rfl⟩)
        · exact Or.inl hc
        · exact Or.inr (Or.inl hl)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
          · exact Av_mono (by omega) (Av_congr e (h3 (Av_gate _ _ _ h _)))
          · rw [← hlast]; exact Av_gate _ _ _ (by omega) _

theorem rs_sg (x : Fin 6) (c : Bool) (u : Fn) (s : Bool) : rs x c (sg u s) = sg (rs x c u) s := rfl
theorem rs_con (x : Fin 6) (c d : Bool) : rs x c (con d) = con d := rfl
theorem rs_An (x : Fin 6) (c : Bool) (a b : Fn) : rs x c (An a b) = An (rs x c a) (rs x c b) := rfl
theorem rs_lit_ne {x i : Fin 6} (h : i ≠ x) (c s : Bool) : rs x c (lit i s) = lit i s := by
  funext v; simp [rs, lit, Function.update_of_ne h]
theorem rs_lit_eq (x : Fin 6) (c s : Bool) : rs x c (lit x s) = con (xor c s) := by
  funext v; simp [rs, lit, con]

theorem rs_Av {g : ℕ → Fn} {k : ℕ} {h : Fn} (x : Fin 6) (c : Bool) (hh : h ∈ Av g k) : rs x c h ∈ Av (fun i => rs x c (g i)) k := by
  rcases hh with ⟨d, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, hj, t, rfl⟩
  · exact Av_con _ _ _
  · by_cases hi : i = x
    · subst hi; rw [rs_lit_eq]; exact Av_con _ _ _
    · rw [rs_lit_ne hi]; exact Av_lit _ _ _ _
  · exact Av_gate (fun i => rs x c (g i)) _ _ hj _

theorem rs_Ch {g : ℕ → Fn} {k : ℕ} (x : Fin 6) (c : Bool) (h : Ch g k) : Ch (fun i => rs x c (g i)) k := by
  intro i hi
  obtain ⟨a, ha, b, hb, hab⟩ := h i hi
  exact ⟨_, rs_Av x c ha, _, rs_Av x c hb, by show rs x c (g i) = _; rw [hab]; rfl⟩

/-- Restrict and drop. -/
theorem kill {g : ℕ → Fn} {k : ℕ} {f : Fn} (hC : Ch g k) (hf : f ∈ Av g k) (x : Fin 6) (c : Bool) (R : Finset ℕ)
    (hR : ∀ i ∈ R, i < k ∧ rs x c (g i) ∈ Av (fun i => rs x c (g i)) i) : ∃ k', k' + R.card = k ∧ Comp (rs x c f) k' := by
  obtain ⟨g', k', h1, h2, h3⟩ := prune _ k (rs_Ch x c hC) R hR
  exact ⟨k', h2, g', h1, h3 (rs_Av x c hf)⟩

def Min (f : Fn) (g : ℕ → Fn) (k : ℕ) : Prop := Ch g k ∧ f ∈ Av g k ∧ ∀ k', k' < k → ¬ Comp f k'

theorem min_exists {f : Fn} {k : ℕ} (h : Comp f k) : ∃ k0, k0 ≤ k ∧ ∃ g, Min f g k0 := by
  classical
  have hex : ∃ k, Comp f k := ⟨k, h⟩
  obtain ⟨g, h1, h2⟩ := Nat.find_spec hex
  exact ⟨Nat.find hex, Nat.find_min' hex h, g, h1, h2, fun k' hk' => Nat.find_min hex hk'⟩

theorem min_irr {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) {j : ℕ} (hj : j < k) : g j ∉ Av g j := by
  intro hm
  obtain ⟨g', k', h1, h2, h3⟩ := prune g k h.1 {j} (by intro i hi; rw [Finset.mem_singleton.1 hi]; exact ⟨hj, hm⟩)
  simp at h2
  exact h.2.2 k' (by omega) ⟨g', h1, h3 h.2.1⟩

theorem AvE_sub {g : ℕ → Fn} {j i : ℕ} {u : Fn} (h : u ∈ Av g j) : u ∈ AvE g j i ∨ ∃ s, u = sg (g i) s := by
  rcases h with hc | hl | ⟨l, hl, s, rfl⟩
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr (Or.inl hl))
  · by_cases e : l = i
    · exact Or.inr ⟨s, by rw [e]⟩
    · exact Or.inl (Or.inr (Or.inr ⟨l, hl, e, s, rfl⟩))

/-- Every gate of a least chain has a reader that cannot do without it. -/
theorem reader {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) {i : ℕ} (hi : i < k) (hf : ∀ s, f ≠ sg (g i) s) :
    ∃ j, i < j ∧ j < k ∧ ∀ a ∈ AvE g j i, ∀ b ∈ AvE g j i, g j ≠ An a b := by
  by_contra hno
  push Not at hno
  let g' : ℕ → Fn := fun m => if m < i then g m else g (m + 1)
  have conv : ∀ m u, u ∈ AvE g (m + 1) i → i ≤ m → u ∈ Av g' m := by
    rintro m u (hc | hl | ⟨l, hl, hne, s, rfl⟩) hm
    · exact Or.inl hc
    · exact Or.inr (Or.inl hl)
    · by_cases hli : l < i
      · have : g' l = g l := by simp only [g', if_pos hli]
        rw [← this]; exact Av_gate _ _ _ (by omega) _
      · have : g' (l - 1) = g l := by simp only [g']; rw [if_neg (by omega)]; congr 1; omega
        rw [← this]; exact Av_gate _ _ _ (by omega) _
  refine h.2.2 (k - 1) (by omega) ⟨g', ?_, ?_⟩
  · intro m hm
    by_cases hmi : m < i
    · obtain ⟨a, ha, b, hb, hab⟩ := h.1 m (by omega)
      have e : ∀ j, j < m → g j = g' j := fun j hj => by simp only [g']; rw [if_pos (by omega)]
      exact ⟨a, Av_congr e ha, b, Av_congr e hb, by simp only [g', if_pos hmi]; exact hab⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := hno (m + 1) (by omega) (by omega)
      exact ⟨a, conv m a ha (by omega), b, conv m b hb (by omega), by simp only [g', if_neg hmi]; exact hab⟩
  · rcases AvE_sub (i := i) h.2.1 with hu | ⟨s, hs⟩
    · have := conv (k - 1) f (by rwa [show k - 1 + 1 = k by omega]) (by omega)
      exact this
    · exact absurd hs (hf s)

theorem uses {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) {i j : ℕ} (hj : j < k) (hno : ∀ a ∈ AvE g j i, ∀ b ∈ AvE g j i, g j ≠ An a b) :
    ∃ s b, b ∈ Av g j ∧ g j = An (sg (g i) s) b := by
  obtain ⟨a, ha, b, hb, hab⟩ := h.1 j hj
  rcases AvE_sub (i := i) ha with h1 | ⟨s, rfl⟩
  · rcases AvE_sub (i := i) hb with h2 | ⟨s, rfl⟩
    · exact absurd hab (hno a h1 b h2)
    · exact ⟨s, a, ha, by rw [hab, An_comm]⟩
  · exact ⟨s, b, hb, hab⟩

theorem red_const {g : ℕ → Fn} {i : ℕ} (d : Bool) {b : Fn} (hb : b ∈ Av g i) : An (con d) b ∈ Av g i := by
  cases d
  · have : An (con false) b = con false := by funext v; simp [An, con]
    rw [this]; exact Av_con _ _ _
  · have : An (con true) b = b := by funext v; simp [An, con]
    rw [this]; exact hb

/-- A gate that reads a wire which is constant after the restriction is redundant. -/
theorem red_reader {g : ℕ → Fn} {i j : ℕ} {x : Fin 6} {c d : Bool} (hd : rs x c (g i) = con d) {s : Bool} {b : Fn} (hb : b ∈ Av g j)
    (hg : g j = An (sg (g i) s) b) : rs x c (g j) ∈ Av (fun i => rs x c (g i)) j := by
  rw [hg, rs_An, rs_sg, hd, sg_con]
  exact red_const _ (rs_Av x c hb)

def indep (u : Fn) (x : Fin 6) : Prop := rs x true u = rs x false u

theorem indep_An {a b : Fn} {x : Fin 6} (ha : indep a x) (hb : indep b x) : indep (An a b) x := by
  unfold indep at *; rw [rs_An, rs_An, ha, hb]
theorem indep_sg {a : Fn} {x : Fin 6} (ha : indep a x) (s : Bool) : indep (sg a s) x := by
  unfold indep at *; rw [rs_sg, rs_sg, ha]
theorem indep_lit {i x : Fin 6} (h : i ≠ x) (s : Bool) : indep (lit i s) x := by
  unfold indep; rw [rs_lit_ne h, rs_lit_ne h]
theorem indep_con (c : Bool) (x : Fin 6) : indep (con c) x := rfl

theorem rs_indep {u : Fn} {x : Fin 6} (h : indep u x) (c : Bool) : rs x c u = u := by
  funext v
  have h1 : ∀ c, rs x c u v = rs x (v x) u v := by
    intro c
    have := congrFun h v
    cases c <;> cases hv : v x <;> simp_all
  rw [h1 c]
  simp [rs, Function.update_eq_self]

/-- One input: some value removes two gates. -/
theorem R1 {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) (x : Fin 6) (hdep : ¬ indep f x) (hlit : ∀ s, f ≠ lit x s) :
    ∃ c, ((∃ k', k' + 2 = k ∧ Comp (rs x c f) k') ∨ ∃ d, rs x c f = con d) ∧ ∃ k', k' + 1 = k ∧ Comp (rs x (!c) f) k' := by
  classical
  have avdep : ∀ j u, (∀ i, i < j → indep (g i) x) → u ∈ Av g j → indep u x ∨ ∃ s, u = lit x s := by
    rintro j u hj (⟨c, rfl⟩ | ⟨i, s, rfl⟩ | ⟨l, hl, s, rfl⟩)
    · exact Or.inl (indep_con _ _)
    · by_cases hi : i = x
      · exact Or.inr ⟨s, by rw [hi]⟩
      · exact Or.inl (indep_lit hi s)
    · exact Or.inl (indep_sg (hj l hl) s)
  have hex : ∃ i, i < k ∧ ¬ indep (g i) x := by
    by_contra hno
    push Not at hno
    rcases avdep k f hno h.2.1 with h1 | ⟨s, hs⟩
    · exact hdep h1
    · exact hlit s hs
  obtain ⟨hik, hid⟩ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → indep (g j) x := by
    intro j hj
    by_contra hc
    exact Nat.find_min hex hj ⟨by omega, hc⟩
  set i := Nat.find hex
  obtain ⟨s, b, hb, hg⟩ : ∃ s b, b ∈ Av g i ∧ g i = An (lit x s) b := by
    obtain ⟨a, ha, b, hb, hab⟩ := h.1 i hik
    rcases avdep i a hmin ha with h1 | ⟨s, rfl⟩
    · rcases avdep i b hmin hb with h2 | ⟨s, rfl⟩
      · exact absurd (hab ▸ indep_An h1 h2) hid
      · exact ⟨s, a, ha, by rw [hab, An_comm]⟩
    · exact ⟨s, b, hb, hab⟩
  have z : rs x s (g i) = con false := by
    rw [hg, rs_An, rs_lit_eq]; funext v; simp [An, con]
  have zr : rs x s (g i) ∈ Av (fun i => rs x s (g i)) i := by rw [z]; exact Av_con _ _ _
  refine ⟨s, ?_, ?_⟩
  · by_cases hout : ∃ t, f = sg (g i) t
    · obtain ⟨t, rfl⟩ := hout
      exact Or.inr ⟨_, by rw [rs_sg, z, sg_con]⟩
    · push Not at hout
      obtain ⟨j, hij, hjk, hno⟩ := reader h hik hout
      obtain ⟨t, b', hb', hg'⟩ := uses h hjk hno
      obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s {i, j} (by
        intro l hl
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact ⟨hik, zr⟩
        · rw [Finset.mem_singleton.1 hl]
          exact ⟨hjk, red_reader z hb' hg'⟩)
      rw [Finset.card_pair (by omega)] at h1
      exact Or.inl ⟨k', h1, h2⟩
  · obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x (!s) {i} (by
      intro j hj
      rw [Finset.mem_singleton.1 hj]
      refine ⟨hik, ?_⟩
      rw [hg, rs_An, rs_lit_eq]
      exact red_const _ (rs_Av x _ hb))
    exact ⟨k', by simpa using h1, h2⟩

def AvX (g : ℕ → Fn) (k : ℕ) (x : Fin 6) : Set Fn := {h | (∃ c, h = con c) ∨ (∃ i s, i ≠ x ∧ h = lit i s) ∨ ∃ j, j < k ∧ ∃ s, h = sg (g j) s}

/-- What a first gate `(x = s) and (y = t)` gives for `x`. -/
def Q (f : Fn) (k : ℕ) (x : Fin 6) (s : Bool) (y : Fin 6) (t : Bool) : Prop :=
  (∃ k', k' + 2 = k ∧ Comp (rs x (s) f) k') ∧ (∃ k', k' + 1 = k ∧ Comp (rs x (!s) f) k') ∧
  (¬ indep (rs y t f) x → ((∃ k', k' + 4 = k ∧ Comp (rs x s f) k') ∧ ∃ k', k' + 2 = k ∧ Comp (rs x (!s) f) k') ∨
    ((∃ k', k' + 3 = k ∧ Comp (rs x s f) k') ∧ ∃ k', k' + 3 = k ∧ Comp (rs x (!s) f) k'))

theorem first {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) (x y : Fin 6) (s t : Bool) (hxy : x ≠ y) (hk : 0 < k)
    (hg0 : g 0 = An (lit x s) (lit y t)) (hcon : ∀ c d, rs x c f ≠ con d) : Q f k x s y t := by
  classical
  have notsg : ∀ (i : ℕ) (c d : Bool), rs x c (g i) = con d → ∀ e, f ≠ sg (g i) e := by
    intro i c d hd e he
    exact hcon c (xor d e) (by rw [he, rs_sg, hd, sg_con])
  have z0 : rs x s (g 0) = con false := by
    rw [hg0, rs_An, rs_lit_eq]; funext v; simp [An, con]
  have zr0 : rs x s (g 0) ∈ Av (fun i => rs x s (g i)) 0 := by rw [z0]; exact Av_con _ _ _
  obtain ⟨r, hr0, hrk, hrno⟩ := reader h hk (notsg 0 s false z0)
  obtain ⟨e, br, hbr, hgr⟩ := uses h hrk hrno
  have zr : rs x s (g r) ∈ Av (fun i => rs x s (g i)) r := red_reader z0 hbr hgr
  have z1 : rs x (!s) (g 0) ∈ Av (fun i => rs x (!s) (g i)) 0 := by
    rw [hg0, rs_An, rs_lit_eq]
    exact red_const _ (rs_Av (g := g) (k := 0) x (!s) (Av_lit g 0 y t))
  refine ⟨?_, ?_, fun hdep => ?_⟩
  rotate_left
  · obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x (!s) {0} (by
      intro l hl
      rw [Finset.mem_singleton.1 hl]; exact ⟨hk, z1⟩)
    exact ⟨k', by simpa using h1, h2⟩
  rotate_left
  · obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s {0, r} (by
      intro l hl
      rcases Finset.mem_insert.1 hl with rfl | hl
      · exact ⟨hk, zr0⟩
      · rw [Finset.mem_singleton.1 hl]; exact ⟨hrk, zr⟩)
    rw [Finset.card_pair (by omega)] at h1
    exact ⟨k', h1, h2⟩
  · -- another gate reads x
    obtain ⟨j, hj0, hjk, hjno⟩ : ∃ j, 0 < j ∧ j < k ∧ ∀ a ∈ AvX g j x, ∀ b ∈ AvX g j x, g j ≠ An a b := by
      by_contra hno
      push Not at hno
      have avx : ∀ j u, (∀ i, i < j → indep (rs y t (g i)) x) → u ∈ AvX g j x → indep (rs y t u) x := by
        rintro j u hj (⟨c, rfl⟩ | ⟨i, s', hi, rfl⟩ | ⟨l, hl, s', rfl⟩)
        · exact indep_con _ _
        · by_cases hiy : i = y
          · subst hiy; rw [rs_lit_eq]; exact indep_con _ _
          · rw [rs_lit_ne hiy]; exact indep_lit hi _
        · rw [rs_sg]; exact indep_sg (hj l hl) _
      have all : ∀ n j, j < n → j < k → indep (rs y t (g j)) x := by
        intro n
        induction n with
        | zero => intro j hj; omega
        | succ n ih =>
          intro j hjn hjk
          rcases Nat.eq_zero_or_pos j with rfl | hp
          · rw [hg0, rs_An, rs_lit_eq]
            have : An (rs y t (lit x s)) (con (xor t t)) = con false := by funext v; simp [An, con]
            rw [this]; exact indep_con _ _
          · obtain ⟨a, ha, b, hb, hab⟩ := hno j hp hjk
            rw [hab, rs_An]
            exact indep_An (avx j a (fun i hi => ih i (by omega) (by omega)) ha) (avx j b (fun i hi => ih i (by omega) (by omega)) hb)
      apply hdep
      rcases h.2.1 with hc | ⟨i, s', rfl⟩ | hg
      · exact avx k f (fun i hi => all (i + 1) i (by omega) hi) (Or.inl hc)
      · by_cases hi : i = x
        · subst hi
          exact absurd (rs_lit_eq i true s') (hcon true _)
        · exact avx k _ (fun i hi => all (i + 1) i (by omega) hi) (Or.inr (Or.inl ⟨i, s', hi, rfl⟩))
      · exact avx k f (fun i hi => all (i + 1) i (by omega) hi) (Or.inr (Or.inr hg))
    obtain ⟨s', b, hb, hgj⟩ : ∃ s' b, b ∈ Av g j ∧ g j = An (lit x s') b := by
      have sub : ∀ u, u ∈ Av g j → u ∈ AvX g j x ∨ ∃ s', u = lit x s' := by
        rintro u (hc | ⟨i, s', rfl⟩ | hg)
        · exact Or.inl (Or.inl hc)
        · by_cases hi : i = x
          · exact Or.inr ⟨s', by rw [hi]⟩
          · exact Or.inl (Or.inr (Or.inl ⟨i, s', hi, rfl⟩))
        · exact Or.inl (Or.inr (Or.inr hg))
      obtain ⟨a, ha, b, hb, hab⟩ := h.1 j hjk
      rcases sub a ha with h1 | ⟨s', rfl⟩
      · rcases sub b hb with h2 | ⟨s', rfl⟩
        · exact absurd hab (hjno a h1 b h2)
        · exact ⟨s', a, ha, by rw [hab, An_comm]⟩
      · exact ⟨s', b, hb, hab⟩
    have hrj : r ≠ j := by
      rintro rfl
      have hb0 : ∃ e, b = sg (g 0) e := by
        rcases AvE_sub (i := 0) hb with h1 | h1
        · exact absurd hgj (hrno _ (Or.inr (Or.inl ⟨x, s', rfl⟩)) _ h1)
        · exact h1
      obtain ⟨e', rfl⟩ := hb0
      have hgr' : g r = An (lit x s') (sg (An (lit x s) (lit y t)) e') := by rw [hgj, hg0]
      have irr := min_irr h hrk
      by_cases hs : s' = s
      · subst hs
        cases e'
        · apply irr
          have : g r = sg (g 0) false := by rw [hgr', hg0]; funext v; simp [An, sg, lit]
          rw [this]; exact Av_gate _ _ _ hr0 _
        · refine hrno (lit x s') (Or.inr (Or.inl ⟨x, s', rfl⟩)) (lit y (!t)) (Or.inr (Or.inl ⟨y, _, rfl⟩)) ?_
          rw [hgr']; funext v
          simp only [An, sg, lit]
          cases v x <;> cases v y <;> cases s' <;> cases t <;> rfl
      · have hs' : s' = !s := by cases s <;> cases s' <;> simp_all
        subst hs'
        cases e'
        · apply irr
          have : g r = con false := by
            rw [hgr']; funext v; simp only [An, sg, lit, con]
            cases v x <;> cases v y <;> cases s <;> cases t <;> rfl
          rw [this]; exact Av_con _ _ _
        · apply irr
          have : g r = lit x (!s) := by
            rw [hgr']; funext v; simp only [An, sg, lit]
            cases v x <;> cases v y <;> cases s <;> cases t <;> rfl
          rw [this]; exact Av_lit _ _ _ _
    by_cases hs : s' = s
    · -- both gates die at x = s
      subst hs
      left
      have more : ∃ k', k' + 2 = k ∧ Comp (rs x (!s') f) k' := by
        obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x (!s') {0, j} (by
          intro l hl
          rcases Finset.mem_insert.1 hl with rfl | hl
          · exact ⟨hk, z1⟩
          · rw [Finset.mem_singleton.1 hl]
            refine ⟨hjk, ?_⟩
            rw [hgj, rs_An, rs_lit_eq]
            exact red_const _ (rs_Av x (!s') hb))
        rw [Finset.card_pair (by omega)] at h1
        exact ⟨k', h1, h2⟩
      refine ⟨?_, more⟩
      have zj : rs x s' (g j) = con false := by
        rw [hgj, rs_An, rs_lit_eq]; funext v; simp [An, con]
      have zrj : rs x s' (g j) ∈ Av (fun i => rs x s' (g i)) j := by rw [zj]; exact Av_con _ _ _
      obtain ⟨q, hq0, hqk, hqno⟩ := reader h hjk (notsg j s' false zj)
      obtain ⟨e2, bq, hbq, hgq⟩ := uses h hqk hqno
      have zq : rs x s' (g q) ∈ Av (fun i => rs x s' (g i)) q := red_reader zj hbq hgq
      by_cases hqr : q = r
      · subst hqr
        have hb0 : ∃ e, bq = sg (g 0) e := by
          rcases AvE_sub (i := 0) hbq with h1 | h1
          · exact absurd hgq (hrno _ (Or.inr (Or.inr ⟨j, hq0, by omega, e2, rfl⟩)) _ h1)
          · exact h1
        obtain ⟨e3, rfl⟩ := hb0
        have zc : ∃ d, rs x s' (g q) = con d := by
          exact ⟨(xor false e2) && (xor false e3), by rw [hgq, rs_An, rs_sg, rs_sg, zj, z0]; rfl⟩
        obtain ⟨d, zc⟩ := zc
        obtain ⟨p, hp0, hpk, hpno⟩ := reader h hqk (notsg q s' d zc)
        obtain ⟨e4, bp, hbp, hgp⟩ := uses h hpk hpno
        obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s' {0, j, q, p} (by
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl | rfl
          · exact ⟨hk, zr0⟩
          · exact ⟨hjk, zrj⟩
          · exact ⟨hqk, zq⟩
          · exact ⟨hpk, red_reader zc hbp hgp⟩)
        have hc : ({0, j, q, p} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;> simp <;> omega
        rw [hc] at h1
        exact ⟨k', h1, h2⟩
      · obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s' {0, j, r, q} (by
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl | rfl
          · exact ⟨hk, zr0⟩
          · exact ⟨hjk, zrj⟩
          · exact ⟨hrk, zr⟩
          · exact ⟨hqk, zq⟩)
        have hc : ({0, j, r, q} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair] <;> simp <;> omega
        rw [hc] at h1
        exact ⟨k', h1, h2⟩
    · have hs' : s' = !s := by cases s <;> cases s' <;> simp_all
      subst hs'
      right
      constructor
      · obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s {0, j, r} (by
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl
          · exact ⟨hk, zr0⟩
          · refine ⟨hjk, ?_⟩
            rw [hgj, rs_An, rs_lit_eq]
            exact red_const _ (rs_Av x s hb)
          · exact ⟨hrk, zr⟩)
        have hc : ({0, j, r} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair] <;> simp <;> omega
        rw [hc] at h1
        exact ⟨k', h1, h2⟩
      · have zj : rs x (!s) (g j) = con false := by
          rw [hgj, rs_An, rs_lit_eq]; funext v; simp [An, con]
        obtain ⟨q, hq0, hqk, hqno⟩ := reader h hjk (notsg j (!s) false zj)
        obtain ⟨e2, bq, hbq, hgq⟩ := uses h hqk hqno
        obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x (!s) {0, j, q} (by
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl
          · refine ⟨hk, ?_⟩
            rw [hg0, rs_An, rs_lit_eq]
            exact red_const _ (rs_Av (g := g) (k := 0) x (!s) (Av_lit g 0 y t))
          · refine ⟨hjk, ?_⟩
            rw [zj]; exact Av_con _ _ _
          · exact ⟨hqk, red_reader zj hbq hgq⟩)
        have hc : ({0, j, q} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair] <;> simp <;> omega
        rw [hc] at h1
        exact ⟨k', h1, h2⟩

theorem R2 {f : Fn} {g : ℕ → Fn} {k : ℕ} (h : Min f g k) (hk : 0 < k) (hcon : ∀ x, ¬ indep f x → ∀ c d, rs x c f ≠ con d) :
    ∃ x y s t, x ≠ y ∧ ¬ indep f x ∧ ¬ indep f y ∧ Q f k x s y t ∧ Q f k y t x s := by
  have irr := min_irr h hk
  obtain ⟨a, ha, b, hb, hab⟩ := h.1 0 hk
  have nc : ∀ u, u ∈ Av g 0 → (∃ c, u = con c) ∨ ∃ i s, u = lit i s := by
    rintro u (hc | hl | ⟨j, hj, _⟩)
    · exact Or.inl hc
    · exact Or.inr hl
    · omega
  rcases nc a ha with ⟨c, rfl⟩ | ⟨x, s, rfl⟩
  · exact absurd (hab ▸ red_const c hb) irr
  rcases nc b hb with ⟨c, rfl⟩ | ⟨y, t, rfl⟩
  · exact absurd (by rw [hab, An_comm]; exact red_const c ha) irr
  have hxy : x ≠ y := by
    rintro rfl
    apply irr
    by_cases hst : s = t
    · subst hst
      have : g 0 = lit x s := by rw [hab]; funext v; simp [An]
      rw [this]; exact Av_lit _ _ _ _
    · have : g 0 = con false := by
        rw [hab]; funext v; simp only [An, lit, con]
        cases v x <;> cases s <;> cases t <;> simp_all
      rw [this]; exact Av_con _ _ _
  have rel : ∀ (x y : Fin 6) (s t : Bool), g 0 = An (lit x s) (lit y t) → ¬ indep f x := by
    intro x y s t hg hi
    obtain ⟨k', h1, h2⟩ := kill h.1 h.2.1 x s {0} (by
      intro l hl
      rw [Finset.mem_singleton.1 hl]
      refine ⟨hk, ?_⟩
      rw [hg, rs_An, rs_lit_eq]
      exact red_const _ (rs_Av (g := g) (k := 0) x s (Av_lit g 0 y t)))
    rw [rs_indep hi] at h2
    simp at h1
    exact h.2.2 k' (by omega) h2
  have hab' : g 0 = An (lit y t) (lit x s) := by rw [hab, An_comm]
  have hx := rel x y s t hab
  have hy := rel y x t s hab'
  exact ⟨x, y, s, t, hxy, hx, hy, first h x y s t hxy hk hab (hcon x hx), first h y x t s hxy.symm hk hab' (hcon y hy)⟩

def LB (f : Fn) (n : ℕ) : Prop := ∀ k, Comp f k → n ≤ k

/-! Tables. -/
def ix (v : Fin 6 → Bool) : ℕ := ∑ i : Fin 6, if v i then 2 ^ (i : ℕ) else 0
def fn (t : ℕ) : Fn := fun v => Nat.testBit t (ix v)
def Mk (x : Fin 6) : ℕ := [0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0, 0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000, 0xFFFFFFFF00000000].getD x.val 0
def Nk (x : Fin 6) : ℕ := [0x5555555555555555, 0x3333333333333333, 0x0F0F0F0F0F0F0F0F, 0x00FF00FF00FF00FF, 0x0000FFFF0000FFFF, 0x00000000FFFFFFFF].getD x.val 0
def rt (t : ℕ) (x : Fin 6) (c : Bool) : ℕ :=
  if c then (t &&& Mk x) ||| ((t &&& Mk x) >>> (2 ^ x.val)) else (t &&& Nk x) ||| ((t &&& Nk x) <<< (2 ^ x.val))

theorem tab1 : ∀ (x : Fin 6) (v : Fin 6 → Bool), Nat.testBit (Mk x) (ix v) = v x ∧ Nat.testBit (Nk x) (ix v) = !(v x) ∧
    ix (Function.update v x true) = (if v x then ix v else 2 ^ x.val + ix v) ∧ ix (Function.update v x false) = (if v x then ix v - 2 ^ x.val else ix v) ∧
    (v x = true → Nat.testBit (Mk x) (2 ^ x.val + ix v) = false ∧ 2 ^ x.val ≤ ix v ∧ Nat.testBit (Nk x) (ix v - 2 ^ x.val) = true) ∧
    (v x = false → Nat.testBit (Mk x) (2 ^ x.val + ix v) = true ∧ (2 ^ x.val ≤ ix v → Nat.testBit (Nk x) (ix v - 2 ^ x.val) = false)) := by decide +kernel

theorem rs_fn (t : ℕ) (x : Fin 6) (c : Bool) : rs x c (fn t) = fn (rt t x c) := by
  funext v
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tab1 x v
  cases c
  · simp only [rs, fn, rt, Bool.false_eq_true, if_false]
    rw [h4, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and, h2]
    cases hv : v x
    · rw [if_neg (by simp)]
      by_cases hle : 2 ^ x.val ≤ ix v
      · simp [(h6 hv).2 hle]
      · simp [hle]
    · rw [if_pos rfl]
      simp [(h5 hv).2.1, (h5 hv).2.2]
  · simp only [rs, fn, rt, if_true]
    rw [h3, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and, h1]
    cases hv : v x
    · rw [if_neg (by simp)]; simp [(h6 hv).1]
    · rw [if_pos rfl]; simp [(h5 hv).1]

def pt (j : ℕ) : Fin 6 → Bool := fun i => Nat.testBit j i.val
theorem ix_pt : ∀ j : Fin 64, ix (pt j.val) = j.val := by decide +kernel

/-- Some of the 64 bits differ. -/
def df (a b : ℕ) : Bool := (List.range 64).any fun j => Nat.testBit a j != Nat.testBit b j
theorem df_ne {a b : ℕ} (h : df a b = true) : fn a ≠ fn b := by
  intro e
  obtain ⟨j, hj, hd⟩ := List.any_eq_true.1 h
  have hj := List.mem_range.1 hj
  have := congrFun e (pt j)
  simp only [fn] at this
  rw [ix_pt ⟨j, hj⟩] at this
  simp [this] at hd

def full : ℕ := 0xFFFFFFFFFFFFFFFF
theorem con_fn : ∀ c : Bool, con c = fn (if c then full else 0) := by
  intro c; funext v
  revert c v; decide +kernel
def lt6 (i : Fin 6) (s : Bool) : ℕ := if s then Nk i else Mk i
theorem lit_fn : ∀ (i : Fin 6) (s : Bool), lit i s = fn (lt6 i s) := by
  intro i s; funext v
  revert i s v; decide +kernel

def dp (t : ℕ) (x : Fin 6) : Bool := df (rt t x true) (rt t x false)
theorem dp_true {t : ℕ} {x : Fin 6} (h : dp t x = true) : ¬ indep (fn t) x := by
  unfold indep; rw [rs_fn, rs_fn]; exact df_ne h
theorem dp_false {t : ℕ} {x : Fin 6} (h : rt t x true = rt t x false) : indep (fn t) x := by
  unfold indep; rw [rs_fn, rs_fn, h]

def nc (a : ℕ) : Bool := df a 0 && df a full
theorem nc_con {a : ℕ} (h : nc a = true) (d : Bool) : fn a ≠ con d := by
  rw [con_fn]
  simp only [nc, Bool.and_eq_true] at h
  cases d
  · exact df_ne h.1
  · exact df_ne h.2

def lk (T : List (ℕ × ℕ)) (t : ℕ) : ℕ := match T.find? (fun p => p.1 == t) with | some p => p.2 | none => 0
theorem lk_LB {T : List (ℕ × ℕ)} (hT : ∀ p ∈ T, LB (fn p.1) p.2) (t : ℕ) : LB (fn t) (lk T t) := by
  unfold lk
  split
  · rename_i p hp
    have h1 := List.find?_some hp
    have h2 := List.mem_of_find?_eq_some hp
    have : p.1 = t := by simpa using h1
    rw [← this]; exact hT p h2
  · exact fun k _ => Nat.zero_le k

def nl (t : ℕ) : Bool := nc t && (List.finRange 6).all fun i => df t (lt6 i true) && df t (lt6 i false)
theorem nl_lit {t : ℕ} (h : nl t = true) (i : Fin 6) (s : Bool) : fn t ≠ lit i s := by
  simp only [nl, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 i (List.mem_finRange i)
  rw [lit_fn]
  cases s
  · exact df_ne this.2
  · exact df_ne this.1
theorem nl_pos {t : ℕ} (h : nl t = true) {g : ℕ → Fn} {k : ℕ} (hm : fn t ∈ Av g k) : 0 < k := by
  rcases hm with ⟨c, hc⟩ | ⟨i, s, hs⟩ | ⟨j, hj, _⟩
  · simp only [nl, Bool.and_eq_true] at h
    exact absurd hc (nc_con h.1 c)
  · exact absurd hs (nl_lit h i s)
  · omega

def ok1 (T : List (ℕ × ℕ)) (t k : ℕ) (x : Fin 6) : Bool :=
  dp t x && nl t && [true, false].all fun c =>
    decide (k ≤ max (if nc (rt t x c) then lk T (rt t x c) + 2 else 0) (lk T (rt t x (!c)) + 1))

def vl (T : List (ℕ × ℕ)) (t : ℕ) (x : Fin 6) (s : Bool) (y : Fin 6) (b : Bool) : ℕ :=
  if dp (rt t y b) x then min (max (lk T (rt t x s) + 4) (lk T (rt t x (!s)) + 2)) (max (lk T (rt t x s)) (lk T (rt t x (!s))) + 3) else max (lk T (rt t x s) + 2) (lk T (rt t x (!s)) + 1)

def ok2 (T : List (ℕ × ℕ)) (t k : ℕ) : Bool :=
  nl t && (List.finRange 6).all fun x => (rt t x true == rt t x false) ||
    ([true, false].all fun c => nc (rt t x c)) && (List.finRange 6).all fun y => x == y || (rt t y true == rt t y false) ||
      [true, false].all fun s => [true, false].all fun b => decide (k ≤ max (vl T t x s y b) (vl T t y b x s))

theorem ok1_LB {T : List (ℕ × ℕ)} (hT : ∀ p ∈ T, LB (fn p.1) p.2) {t k : ℕ} {x : Fin 6} (h : ok1 T t k x = true) : LB (fn t) k := by
  intro l hl
  obtain ⟨l0, hl0, g, hm⟩ := min_exists hl
  simp only [ok1, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨c, hc⟩ := R1 hm x (dp_true h1) (fun s => nl_lit h2 x s)
  have hcc := of_decide_eq_true (h3 c (by cases c <;> simp))
  obtain ⟨hc1, k2, e2, hk2⟩ := hc
  rw [rs_fn] at hk2
  have b2 := lk_LB hT _ _ hk2
  rcases hc1 with ⟨k', e, hk'⟩ | ⟨d, hd⟩
  · rw [rs_fn] at hk'
    have b1 := lk_LB hT _ _ hk'
    refine le_trans (le_trans hcc (max_le ?_ ?_)) hl0
    · split <;> omega
    · omega
  · rw [rs_fn] at hd
    rw [if_neg (fun hn => nc_con hn d hd)] at hcc
    refine le_trans (le_trans hcc (max_le ?_ ?_)) hl0 <;> omega

theorem vl_le {T : List (ℕ × ℕ)} (hT : ∀ p ∈ T, LB (fn p.1) p.2) {t l : ℕ} {x y : Fin 6} {s b : Bool} (h : Q (fn t) l x s y b) : vl T t x s y b ≤ l := by
  obtain ⟨⟨k', e, hk'⟩, ⟨k1, e1, hk1⟩, h2⟩ := h
  rw [rs_fn] at hk' hk1
  have b1 := lk_LB hT _ _ hk'
  have b2 := lk_LB hT _ _ hk1
  unfold vl
  split
  · rename_i hd
    rw [rs_fn] at h2
    rcases h2 (dp_true hd) with ⟨⟨k2, e2, hk2⟩, k3, e3, hk3⟩ | ⟨⟨k2, e2, hk2⟩, k3, e3, hk3⟩
    · rw [rs_fn] at hk2 hk3
      have := lk_LB hT _ _ hk2
      have := lk_LB hT _ _ hk3
      exact (min_le_left _ _).trans (max_le (by omega) (by omega))
    · rw [rs_fn] at hk2 hk3
      have := lk_LB hT _ _ hk2
      have := lk_LB hT _ _ hk3
      exact (min_le_right _ _).trans (by omega)
  · exact max_le (by omega) (by omega)

theorem ok2_LB {T : List (ℕ × ℕ)} (hT : ∀ p ∈ T, LB (fn p.1) p.2) {t k : ℕ} (h : ok2 T t k = true) : LB (fn t) k := by
  intro l hl
  obtain ⟨l0, hl0, g, hm⟩ := min_exists hl
  simp only [ok2, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hpos := nl_pos h1 hm.2.1
  have rel : ∀ x, ¬ indep (fn t) x → (∀ c ∈ [true, false], nc (rt t x c) = true) ∧ ∀ y ∈ List.finRange 6, (x = y ∨ rt t y true = rt t y false) ∨
      ∀ s ∈ [true, false], ∀ b ∈ [true, false], decide (k ≤ max (vl T t x s y b) (vl T t y b x s)) = true := by
    intro x hx
    rcases h2 x (List.mem_finRange x) with he | he
    · exact absurd (dp_false he) hx
    · exact he
  obtain ⟨x, y, s, b, hxy, hx, hy, q1, q2⟩ := R2 hm hpos (by
    intro x hx c d
    rw [rs_fn]
    exact nc_con ((rel x hx).1 c (by cases c <;> simp)) d)
  rcases (rel x hx).2 y (List.mem_finRange y) with (he | he) | he
  · exact absurd he hxy
  · exact absurd (dp_false he) hy
  · have hb := of_decide_eq_true (he s (by cases s <;> simp) b (by cases b <;> simp))
    have v1 := vl_le hT q1
    have v2 := vl_le hT q2
    have := max_le v1 v2
    omega

def okr (T : List (ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : Bool :=
  if e.2.2 = 7 then decide (e.2.1 ≤ 1) && nl e.1 else if e.2.2 = 6 then ok2 T e.1 e.2.1 else ok1 T e.1 e.2.1 (Fin.ofNat 6 e.2.2)

theorem okr_LB {T : List (ℕ × ℕ)} (hT : ∀ p ∈ T, LB (fn p.1) p.2) {e : ℕ × ℕ × ℕ} (h : okr T e = true) : LB (fn e.1) e.2.1 := by
  unfold okr at h
  split at h
  · rw [Bool.and_eq_true] at h
    rintro l ⟨g, _, hm⟩
    have := nl_pos h.2 hm
    have := of_decide_eq_true h.1
    omega
  · split at h
    · exact ok2_LB hT h
    · exact ok1_LB hT h

def chk : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], _ => true
  | e :: es, T => okr T e && chk es ((e.1, e.2.1) :: T)

theorem chk_LB : ∀ (es : List (ℕ × ℕ × ℕ)) (T : List (ℕ × ℕ)), (∀ p ∈ T, LB (fn p.1) p.2) → chk es T = true → ∀ e ∈ es, LB (fn e.1) e.2.1 := by
  intro es
  induction es with
  | nil => intro T _ _ e he; simp at he
  | cons a es ih =>
    intro T hT h e he
    rw [chk, Bool.and_eq_true] at h
    have ha := okr_LB hT h.1
    rcases List.mem_cons.1 he with rfl | he
    · exact ha
    · refine ih _ ?_ h.2 e he
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ha
      · exact hT p hp

/-! From circuits to chains. -/
theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) : (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def isN (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem chain (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∃ g k, Ch g k ∧ k + gs.countP isN ≤ gs.length ∧ ∀ w, (fun x : Fin 6 → Bool => ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD w false) ∈ Av g k := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => con false, 0, fun i hi => absurd hi (by omega), by simp, fun w => ?_⟩
    by_cases hw : w < 6
    · have : (fun x : Fin 6 → Bool => ((⟨[], 0⟩ : Circuit).wires (List.ofFn x)).getD w false) = lit ⟨w, hw⟩ false := by
        funext x
        show (List.ofFn x).getD w false = xor (x ⟨w, hw⟩) false
        rw [getD_ofFn x w hw, Bool.xor_false]
      rw [this]; exact Av_lit _ _ _ _
    · have : (fun x : Fin 6 → Bool => ((⟨[], 0⟩ : Circuit).wires (List.ofFn x)).getD w false) = con false := by
        funext x
        show (List.ofFn x).getD w false = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_ofFn]; omega)]; rfl
      rw [this]; exact Av_con _ _ _
  | append_singleton gs a ih =>
    obtain ⟨g, k, h1, h2, h3⟩ := ih fun u hu => hg u (by simp [hu])
    obtain ⟨hop, hlen⟩ := hg a (by simp)
    set W : (Fin 6 → Bool) → List Bool := fun x => (⟨gs, 0⟩ : Circuit).wires (List.ofFn x) with hW
    have hWl : ∀ x, (W x).length = 6 + gs.length := by
      intro x
      have : ∀ (l : List Gate) (w : List Bool), (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + l.length := by
        intro l
        induction l with
        | nil => intro w; rfl
        | cons c l ih => intro w; rw [List.foldl_cons, ih]; simp; omega
      have := this gs (List.ofFn x)
      simpa [hW, Circuit.wires] using this
    have hW' : ∀ x, (⟨gs ++ [a], 0⟩ : Circuit).wires (List.ofFn x) = W x ++ [a.op.eval (a.inputs.map fun i => (W x).getD i false)] := by
      intro x; simp [Circuit.wires, hW]
    -- the new wire
    obtain ⟨g', k', c1, c2, c3, c4⟩ : ∃ g' k', Ch g' k' ∧ Av g k ⊆ Av g' k' ∧ k' + (if isN a then 1 else 0) ≤ k + 1 ∧ (fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false)) ∈ Av g' k' := by
      have two : ∀ p q : ℕ, ∀ s t e : Bool, isN a = false → (fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false)) = sg (An (sg (fun x => (W x).getD p false) s) (sg (fun x => (W x).getD q false) t)) e →
          ∃ g' k', Ch g' k' ∧ Av g k ⊆ Av g' k' ∧ k' + (if isN a then 1 else 0) ≤ k + 1 ∧ (fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false)) ∈ Av g' k' := by
        intro p q s t e hn he
        let g2 : ℕ → Fn := fun i => if i < k then g i else An (sg (fun x => (W x).getD p false) s) (sg (fun x => (W x).getD q false) t)
        have e2 : ∀ j, j < k → g j = g2 j := fun j hj => by simp only [g2, if_pos hj]
        refine ⟨g2, k + 1, ?_, (Av_congr e2).trans (Av_mono (by omega)), by rw [hn]; exact le_refl _, ?_⟩
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
          · obtain ⟨u, hu, v, hv, huv⟩ := h1 i h
            have e' : ∀ j, j < i → g j = g2 j := fun j hj => e2 j (by omega)
            exact ⟨u, Av_congr e' hu, v, Av_congr e' hv, by rw [← e2 i h]; exact huv⟩
          · exact ⟨_, Av_congr e2 (Av_sg (h3 p) s), _, Av_congr e2 (Av_sg (h3 q) t), if_neg (Nat.lt_irrefl _)⟩
        · rw [he]
          have : An (sg (fun x => (W x).getD p false) s) (sg (fun x => (W x).getD q false) t) = g2 k := (if_neg (Nat.lt_irrefl k)).symm
          rw [this]; exact Av_gate _ _ _ (by omega) _
      have one : (fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false)) ∈ Av g k →
          ∃ g' k', Ch g' k' ∧ Av g k ⊆ Av g' k' ∧ k' + (if isN a then 1 else 0) ≤ k + 1 ∧ (fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false)) ∈ Av g' k' :=
        fun h => ⟨g, k, h1, fun _ h => h, by split <;> omega, h⟩
      obtain ⟨op, I⟩ := a
      simp only at hop hlen
      rcases hop with rfl | rfl | rfl
      · match I, hlen with
        | [], _ => exact one (Or.inl ⟨true, by funext x; simp [GateOp.eval, con]⟩)
        | [p], _ =>
          refine one ?_
          have := h3 p
          convert this using 1
          funext x; simp [GateOp.eval, hW]
        | [p, q], _ =>
          exact two p q false false false rfl (by funext x; simp [GateOp.eval, sg, An])
      · match I, hlen with
        | [], _ => exact one (Or.inl ⟨false, by funext x; simp [GateOp.eval, con]⟩)
        | [p], _ =>
          refine one ?_
          have := h3 p
          convert this using 1
          funext x; simp [GateOp.eval, hW]
        | [p, q], _ =>
          refine two p q true true true rfl ?_
          funext x
          simp only [GateOp.eval, sg, An, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
          cases (W x).getD p false <;> cases (W x).getD q false <;> rfl
      · match I, hlen with
        | [], _ => exact one (Or.inl ⟨true, by funext x; simp [GateOp.eval, con]⟩)
        | p :: r, _ =>
          refine one ?_
          have := Av_sg (h3 p) true
          convert this using 1
          funext x; simp [GateOp.eval, hW, sg]
    refine ⟨g', k', c1, ?_, fun w => ?_⟩
    · rw [List.countP_append, List.length_append]
      simp only [List.countP_singleton, List.length_singleton]
      split at c3 <;> simp_all <;> omega
    · by_cases hw : w < 6 + gs.length
      · have : (fun x : Fin 6 → Bool => ((⟨gs ++ [a], 0⟩ : Circuit).wires (List.ofFn x)).getD w false) = fun x => (W x).getD w false := by
          funext x
          rw [hW' x, List.getD_append _ _ _ _ (by rw [hWl]; exact hw)]
        rw [this]; exact c2 (h3 w)
      · by_cases hw2 : w = 6 + gs.length
        · have : (fun x : Fin 6 → Bool => ((⟨gs ++ [a], 0⟩ : Circuit).wires (List.ofFn x)).getD w false) = fun x => a.op.eval (a.inputs.map fun i => (W x).getD i false) := by
            funext x
            rw [hW' x, List.getD_append_right _ _ _ _ (by rw [hWl]; omega), hWl, hw2]
            simp
          rw [this]; exact c4
        · have : (fun x : Fin 6 → Bool => ((⟨gs ++ [a], 0⟩ : Circuit).wires (List.ofFn x)).getD w false) = con false := by
            funext x
            rw [hW' x, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hWl]; omega)]; rfl
          rw [this]; exact Av_con _ _ _

theorem finish (t m : ℕ) (hlb : LB (fn t) m) (W : Circuit) (hW : Monotone2 W) (hWs : W.size ≤ m + 1) (hWf : ∀ x : Fin 6 → Bool, W.eval (List.ofFn x) = fn t x)
    (s : ℕ) (h : HasCircuitSize 6 (fn t) s) : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = fn t x := by
  obtain ⟨C, hC, hs, hf⟩ := h
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa using this
  by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, k, h1, h2, h3⟩ := chain C.gates hg
    have hmem : fn t ∈ Av g k := by
      have := h3 C.output
      convert this using 1
      funext x; exact (hf x).symm
    have := hlb k ⟨g, h1, hmem⟩
    obtain ⟨u, hu, huo⟩ := hn
    have hpos : 0 < C.gates.countP isN := List.countP_pos_iff.2 ⟨u, hu, by simp [isN, huo]⟩
    have hsz : C.gates.length ≤ s := hs
    exact ⟨W, hW, by omega, hWf⟩
  · refine ⟨C, ?_, hs, hf⟩
    intro g hgm
    obtain ⟨ho, hl⟩ := hg g hgm
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · simp [h]
    · simp [h]
    · exact absurd ⟨g, hgm, h⟩ hn

def ents : List (ℕ × ℕ × ℕ) := [(18446462598732840960, 1, 7), (18446462603011031040, 2, 3), (18446742978476179200, 2, 3), (18446726485801758720, 4, 2), (18446727516609638640, 3, 2), (18446727310448062656, 5, 1), (18446744073709486080, 1, 7), (18446744073692774400, 2, 3), (18446744073692839680, 1, 7), (18446744073692835840, 3, 2), (18446744073706208460, 4, 1), (18446738211062476800, 5, 0), (18446738554676247290, 4, 0), (18446650250132193280, 4, 0), (18446650250143378090, 3, 0), (18446650250141141128, 5, 1), (18446743854662877132, 3, 1), (18446744073706209228, 2, 1), (18446744000691765196, 4, 0), (18446650245854003200, 2, 0), (18446650248717314730, 2, 0), (18446650248144652424, 4, 1), (18446687778714209484, 2, 1), (18446744072850558156, 1, 7), (18446725308138441932, 3, 0), (18446720892844689608, 5, 2), (18446727516610621680, 1, 7), (18446744073709547760, 2, 2), (18446744073709550844, 3, 1), (18446738554676574456, 4, 0), (12297829381900372104, 2, 0), (17216961134889585868, 2, 0), (16927600443537279176, 4, 2), (18446744073456906480, 1, 7), (18446744073659022588, 2, 1), (18085043209485482232, 3, 0), (18080539541135489224, 5, 3), (18446744073708568560, 2, 2), (18446744073705422784, 3, 1), (18446744073705947080, 4, 0), (18374686483949813760, 1, 7), (18374950366740541440, 2, 2), (18442505391958978800, 2, 2), (18428994386915291328, 4, 1), (18432385332315749580, 3, 1), (18431255017182263496, 5, 0), (18446742978492890880, 1, 7), (18446726485818470400, 2, 2), (18446727310452191424, 3, 1), (18446738485957098218, 4, 0), (18446738485953493192, 8, 6)]

theorem low : LB (fn 18446738485953493192) 8 :=
  chk_LB ents [] (by simp) (by decide +kernel) (18446738485953493192, 8, 6) (by simp [ents])

theorem lb_all (t m : ℕ) (hlb : LB (fn t) m) (C : Circuit) (hC : FanInTwo C) (hf : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = fn t x) : m ≤ C.size := by
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa using this
  obtain ⟨g, k, h1, h2, h3⟩ := chain C.gates hg
  have hmem : fn t ∈ Av g k := by
    have := h3 C.output
    convert this using 1
    funext x; exact (hf x).symm
  have := hlb k ⟨g, h1, hmem⟩
  have : C.gates.length = C.size := rfl
  omega

theorem feq : ∀ x1 : Fin 6 → Bool, (x1 (0 : Fin (6 : ℕ)) && x1 (1 : Fin (6 : ℕ)) || x1 (1 : Fin (6 : ℕ)) && x1 (2 : Fin (6 : ℕ)) || x1 (2 : Fin (6 : ℕ)) && x1 (3 : Fin (6 : ℕ)) || x1 (3 : Fin (6 : ℕ)) && x1 (4 : Fin (6 : ℕ)) || x1 (4 : Fin (6 : ℕ)) && x1 (5 : Fin (6 : ℕ)) || x1 (5 : Fin (6 : ℕ)) && x1 (0 : Fin (6 : ℕ))) = fn 18446738485953493192 x1 := by decide

end PEqualNP.Outside.L_meta_18717

theorem PEqualNP.Outside.L_meta_18717 : ¬PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ) (fun (x1 : Fin (6 : ℕ) → Bool) => x1 (0 : Fin (6 : ℕ)) && x1 (1 : Fin (6 : ℕ)) || x1 (1 : Fin (6 : ℕ)) && x1 (2 : Fin (6 : ℕ)) || x1 (2 : Fin (6 : ℕ)) && x1 (3 : Fin (6 : ℕ)) || x1 (3 : Fin (6 : ℕ)) && x1 (4 : Fin (6 : ℕ)) || x1 (4 : Fin (6 : ℕ)) && x1 (5 : Fin (6 : ℕ)) || x1 (5 : Fin (6 : ℕ)) && x1 (0 : Fin (6 : ℕ))) (7 : ℕ) := by
  rintro ⟨C, hC, hs, hf⟩
  have := PEqualNP.Outside.L_meta_18717.lb_all 18446738485953493192 8 PEqualNP.Outside.L_meta_18717.low C hC (fun x => (hf x).trans (PEqualNP.Outside.L_meta_18717.feq x))
  omega
