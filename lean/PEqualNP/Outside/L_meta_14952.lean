import PEqualNP.Defs

-- The signed-circuit search and its five-vertex certificate are adapted from
-- Jonathan Nanhu's checked L-meta-10754 in this project's Apache-2.0 repository.
-- Pinning both extra vertices gives the bowtie. It needs eight binary gates,
-- so any circuit on these seven vertices needs ten binary gates.
namespace PEqualNP.Outside.L_meta_14952_aux.Signed

open PEqualNP.CircuitLowerBounds

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

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
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
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
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

end Live

section FreeNot

def ops {n : ℕ} (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps {n : ℕ} (a b : BitVec n) : Finset (BitVec n) := (ops a b).toFinset

theorem ops_swap {n : ℕ} (a b : BitVec n) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem index_of_op {n : ℕ} (a b z : BitVec n) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

def holds {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {n : ℕ} {av : Finset (BitVec n)} {z a : BitVec n} (h : holds av z) :
    holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_mono {n : ℕ} {av av' : Finset (BitVec n)} (sub : av ⊆ av') {x : BitVec n}
    (h : holds av x) : holds av' x := by
  rcases h with h | h | ⟨a, ha, e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a, sub ha, e⟩)

theorem holds_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable {n : ℕ} (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : reachable av z) :
    reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem bv_zero_and {n : ℕ} (x : BitVec n) : (0 : BitVec n) &&& x = 0 := BitVec.zero_and
theorem bv_and_zero {n : ℕ} (x : BitVec n) : x &&& (0 : BitVec n) = 0 := BitVec.and_zero
theorem bv_zero_or {n : ℕ} (x : BitVec n) : (0 : BitVec n) ||| x = x := BitVec.zero_or
theorem bv_or_zero {n : ℕ} (x : BitVec n) : x ||| (0 : BitVec n) = x := BitVec.or_zero
theorem bv_not_zero_and {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) &&& x = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_and_not_zero {n : ℕ} (x : BitVec n) : x &&& ~~~(0 : BitVec n) = x := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_not_zero_or {n : ℕ} (x : BitVec n) : ~~~(0 : BitVec n) ||| x = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp
theorem bv_or_not_zero {n : ℕ} (x : BitVec n) : x ||| ~~~(0 : BitVec n) = ~~~0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi; simp

set_option maxRecDepth 5000 in
theorem and_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x &&& y) := by
  have const0 : holds av (0 : BitVec n) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [bv_zero_and]; exact .inl const0
  · rw [bv_not_zero_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [bv_and_zero]; exact .inl const0
  · rw [bv_and_not_zero]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const0 | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : BitVec n) (hw : w ∈ basicOps a b) (z : BitVec n) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops]) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops]) _ (.inr BitVec.not_or.symm)

theorem or_reach {n : ℕ} {av : Finset (BitVec n)} {x y : BitVec n}
    (hx : holds av x) (hy : holds av y) : reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using
    reachable_not (and_reach (holds_not hx) (holds_not hy))

theorem mem_ops_reach {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y) (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

theorem mem_ops_const {n : ℕ} {av : Finset (BitVec n)} {x y z : BitVec n}
    (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0))
    (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : BitVec n) := .inl rfl
  have h1 : holds av (~~~(0 : BitVec n)) := .inr (.inl rfl)
  have hnx : holds av (~~~x) := holds_not hx
  have hny : holds av (~~~y) := holds_not hy
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl
  · rw [bv_zero_and]; exact h0
  · rw [bv_zero_or]; exact hy
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hy
  · rw [bv_not_zero_and]; exact hy
  · rw [bv_not_zero_or]; exact h1
  · rw [bv_not_zero_and]; exact hny
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_and_zero]; exact h0
  · rw [bv_or_zero]; exact hx
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_zero_and]; exact h0
  · rw [bv_and_not_zero]; exact hx
  · rw [bv_or_not_zero]; exact h1
  · rw [BitVec.not_not, bv_and_zero]; exact h0
  · rw [bv_not_zero_and]; exact hnx

def SignedBuild {n : ℕ} (k : ℕ) (av : Finset (BitVec n)) (z : BitVec n) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} (h : holds av z) :
    SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k : ℕ}
    (h : SignedBuild k av z) : SignedBuild (k + 1) av z := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {n : ℕ} {av : Finset (BitVec n)} {z : BitVec n} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuild k av z) : SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {n : ℕ} {av : Finset (BitVec n)} {t a b z : BitVec n} {k : ℕ}
    (ha : a ∈ av) (hb : b ∈ av) (hne : a ≠ b) (hz : z ∈ basicOps a b)
    (h : SignedBuild k (insert z av) t) : SignedBuild (k + 1) av t := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a, ha, b, hb, hne, z, hz, h⟩)))

theorem sb_advance {n : ℕ} {av : Finset (BitVec n)} {z t : BitVec n} {k : ℕ}
    (hz : reachable av z)
    (next : ∀ av' : Finset (BitVec n), av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem ops_map_of {n m : ℕ} {f : BitVec n → BitVec m}
    (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b))
    (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hAnd, hOr, hNot]

theorem live_transport {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem live_transport_save_const {n m : ℕ} {f : BitVec n → BitVec m}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : BitVec n} {k : ℕ} {s : Finset (BitVec n)} {av : Finset (BitVec m)}
    (run : live basicOps g k s)
    (hp : p ∈ s) (hconst : f p = 0 ∨ f p = ~~~0)
    (hng : f g ≠ 0 ∧ f g ≠ ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) :
    1 ≤ k ∧ SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    have hpg : p = g := by simpa [run] using hp
    subst hpg
    rcases hconst with h | h
    · exact (hng.1 h).elim
    · exact (hng.2 h).elim
  | succ k ih =>
    simp only [Nat.add_sub_cancel]
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · obtain ⟨hk, hsb⟩ := ih skip hp hav
      exact ⟨by omega, sb_le (by omega) hsb⟩
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) hc mapped
        refine ⟨by omega, live_transport hm tail ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact collapsed
        · exact inOld u hr
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        refine ⟨by omega, ?_⟩
        rcases mem_ops_reach (hav a ha) (hav b hb) mapped with hok | ⟨x, hx, y, hy, hxy, w, hw, hok⟩
        · obtain ⟨hk, hsb⟩ := ih tail pt (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact inOld u hr)
          exact sb_le (by omega) hsb
        · obtain ⟨hk, hsb⟩ := ih tail pt (av := insert w av) (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact holds_insert (inOld u hr))
          have hstep := sb_step hx hy hxy hw hsb
          exact sb_le (by omega) hstep

def selectRows {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) : BitVec m :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin m => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit {n m : ℕ} (rows : Fin m → Fin n) (w : BitVec n) (j : Fin m) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor {n m : ℕ} (rows : Fin m → Fin n) (u v : BitVec n) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg {n m : ℕ} (rows : Fin m → Fin n) (u : BitVec n) :
    selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin m := ⟨j, hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

def bitDiff {n : ℕ} (a b : Fin n) (w : BitVec n) : Prop :=
  w[a.val] ≠ w[b.val]

theorem ops_bitDiff {n : ℕ} (a b : Fin n) (x y z : BitVec n) (hz : z ∈ basicOps x y)
    (hd : bitDiff a b z) : bitDiff a b x ∨ bitDiff a b y := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨hx, hy⟩ := fail
  apply hd
  unfold bitDiff at hx hy
  simp only [not_not] at hx hy
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, hx, hy]

theorem bitDiff_not {n : ℕ} {a b : Fin n} {w : BitVec n} (h : bitDiff a b w) :
    bitDiff a b (~~~w) := by
  intro heq
  apply h
  simp only [BitVec.getElem_not] at heq
  cases ha : w[a.val] <;> cases hb : w[b.val] <;> simp_all

theorem live_has_unique_sep {n : ℕ} {g p : BitVec n} {k : ℕ}
    {s : Finset (BitVec n)} {ls : List (BitVec n)}
    (hs : s ⊆ ls.toFinset) (hl : live basicOps g k s)
    (a b : Fin n) (hd : bitDiff a b g)
    (huniq : ∀ w ∈ ls, bitDiff a b w → w = p) : p ∈ s := by
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) hl
  have hwp : w = p := huniq w (List.mem_toFinset.mp (hs hw)) hdw
  exact hwp ▸ hw

theorem sep_of_all {n : ℕ} (a b : Fin n) (ls : List (BitVec n)) (p : BitVec n)
    (h : ls.all (fun w => !(w[a.val] != w[b.val]) || w == p) = true) :
    ∀ w ∈ ls, bitDiff a b w → w = p := by
  intro w hw hdiff
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_iff_eq] at h1
  exact h1.resolve_left hdiff

theorem map_holds_list {n m : ℕ} (f : BitVec n → BitVec m) (src : List (BitVec n)) (dst : List (BitVec m))
    (h : src.all (fun w => f w == 0 || f w == ~~~0 || dst.any (fun d => f w == d)) = true) :
    ∀ w ∈ src, holds dst.toFinset (f w) := by
  intro w hw
  have h1 := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with (h0 | h1) | ⟨d, hd, hwd⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl hwd⟩)

theorem unwrap_sb {n : ℕ} {k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h0 : z ≠ 0) (h1 : z ≠ ~~~0) (h : SignedBuild k av z) :
    ∃ t, (t = z ∨ t = ~~~z) ∧ build basicOps t k av := by
  rcases h with hz | hz | hb | hb
  · exact (h0 hz).elim
  · exact (h1 hz).elim
  · exact ⟨z, .inl rfl, hb⟩
  · exact ⟨~~~z, .inr rfl, hb⟩

theorem not_const_of_neg {n : ℕ} {w : BitVec n} (h : w ≠ 0 ∧ w ≠ ~~~0) :
    ~~~w ≠ 0 ∧ ~~~w ≠ ~~~0 := by
  refine ⟨fun heq => h.2 ?_, fun heq => h.1 ?_⟩
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq
  · simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) heq

end FreeNot

section SearchP

abbrev WP (P : ℕ) := BitVec (P + P)
def sepP {P : ℕ} (x : WP P) : BitVec P := ((x >>> P) ^^^ x).setWidth P
def cutsP {P : ℕ} (ws : List (WP P)) : BitVec P := ws.foldr (fun w v => sepP w ||| v) 0
def goalP (P : ℕ) : WP P := BitVec.allOnes P ++ (0 : BitVec P)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differsP {P : ℕ} (i : Fin P) (w : WP P) : Prop :=
  w.getLsbD (P + i.val) ≠ w.getLsbD i.val

theorem goalP_differs {P : ℕ} (i : Fin P) : differsP i (goalP P) := by
  unfold differsP goalP
  have hi : i.val < P := i.isLt
  have hlo : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD i.val = false := by
    rw [BitVec.getLsbD_append]
    simp [hi]
  have hhi : (BitVec.allOnes P ++ (0 : BitVec P)).getLsbD (P + i.val) = true := by
    rw [BitVec.getLsbD_append]
    have hnot : ¬ (P + i.val < P) := by omega
    simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes]
  rw [hlo, hhi]
  decide

theorem ngoalP_differs {P : ℕ} (i : Fin P) : differsP i (~~~goalP P) := by
  have h := goalP_differs i
  unfold differsP at h ⊢
  have h1 : P + i.val < P + P := by omega
  have h2 : i.val < P + P := by omega
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  intro heq
  apply h
  cases a : (goalP P).getLsbD (P + i.val) <;> cases b : (goalP P).getLsbD i.val <;> simp_all

theorem ops_differsP {P : ℕ} (i : Fin P) (a b z : WP P) (hz : z ∈ basicOps a b)
    (hd : differsP i z) : differsP i a ∨ differsP i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differsP at ha hb
  simp only [not_not] at ha hb
  have hi : P + i.val < P + P := by omega
  have hi' : i.val < P + P := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cutsP_spec {P : ℕ} (ws : List (WP P)) (i : Fin P) :
    (cutsP ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differsP i w := by
  induction ws with
  | nil => simp [cutsP]
  | cons a rest ih =>
    change (sepP a ||| cutsP rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sepP, i.isLt, differsP, Nat.add_comm, bx]

theorem cutsP_full {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) {k : ℕ} {ws : List (WP P)}
    (h : live basicOps g k ws.toFinset) : cutsP ws = BitVec.allOnes P := by
  have hd : ∀ i, differsP i g := by
    intro i; rcases hg with rfl | rfl
    · exact goalP_differs i
    · exact ngoalP_differs i
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differsP ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differsP ⟨j, hj⟩) h
  have hbit := (cutsP_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) :=
  [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {α : Type} [DecidableEq α] {goal : α} {ws : List α} (hn : ws.Nodup)
    (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchP (P : ℕ) (extra : ℕ) (next : ℕ → List (WP P) → Bool) (a b : WP P) (r : List (WP P)) : Bool :=
  let base := cutsP r
  let full := BitVec.allOnes P
  (ops a b).any fun w =>
    let v := sepP w ||| base
    ((v == full) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepP a == full) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepP b == full) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepP a ||| sepP b == full) && next (extra - 2) (w :: a :: b :: r))

def optimizedP (P : ℕ) : ℕ → ℕ → List (WP P) → Bool
  | 0, _, ws => (ws == [goalP P] || ws == [~~~goalP P])
  | k + 1, extra, ws => (ws == [goalP P] || ws == [~~~goalP P]) ||
    (pairs ws).any (fun (a, b, r) => dispatchP P extra (optimizedP P k) a b r)

theorem dispatchP_complete {P k extra : ℕ} {a b z : WP P} {r kept : List (WP P)}
    (next : ℕ → List (WP P) → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsP (z :: kept) = BitVec.allOnes P) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatchP P extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cutsP, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimizedP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (ws : List (WP P)) (extra : ℕ) (hn : ws.Nodup) (room : extra + ws.length = n + 1)
    (h : live basicOps g n ws.toFinset) : optimizedP P n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimizedP, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : WP P} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatchP P extra (optimizedP P k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatchP_complete (k := k) (extra := extra) (optimizedP P k) hop hk (by omega)
          (by omega) (cutsP_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimizedP, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def searchP (P : ℕ) (n : ℕ) (inputs : List (WP P)) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsP ws == BitVec.allOnes P) && optimizedP P n (n + 1 - ws.length) ws

theorem searchP_complete {P : ℕ} {g : WP P} (hg : g = goalP P ∨ g = ~~~goalP P) (n : ℕ)
    (inputs : List (WP P)) (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchP P n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cutsP_full hg hl',
      optimizedP_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

theorem goalP_ne_const {P : ℕ} (hP : 0 < P) :
    goalP P ≠ 0 ∧ goalP P ≠ ~~~0 ∧ ~~~goalP P ≠ 0 ∧ ~~~goalP P ≠ ~~~0 := by
  have hd := goalP_differs ⟨0, hP⟩
  have hdn := ngoalP_differs ⟨0, hP⟩
  have h0 : ¬ differsP ⟨0, hP⟩ (0 : WP P) := by unfold differsP; simp
  have h1 : ¬ differsP ⟨0, hP⟩ (~~~(0 : WP P)) := by
    unfold differsP
    have hb : 0 < P + P := by omega
    simp [hb]
    omega
  exact ⟨fun e => h0 (e ▸ hd), fun e => h1 (e ▸ hd), fun e => h0 (e ▸ hdn), fun e => h1 (e ▸ hdn)⟩

theorem signed_rejectP {P k : ℕ} (hP : 0 < P) {ws : List (WP P)} (hn : ws.Nodup)
    (hf : searchP P k ws = false) {t : WP P} (ht : t = goalP P ∨ t = ~~~goalP P)
    (h : SignedBuild k ws.toFinset t) : False := by
  have nt := goalP_ne_const hP
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (searchP_complete (by simp) k ws hn h))

end SearchP

section BowtieBase

def bow_32_vars : List (BitVec 32) :=
  [0xaaaaaaaa#32, 0xcccccccc#32, 0xf0f0f0f0#32, 0xff00ff00#32, 0xffff0000#32]
def bowv32 (i : Fin 5) : BitVec 32 := bow_32_vars.getD i.val 0
def bow_tt32 : BitVec 32 := 0xfffef888#32

def bw0 : WP 76 := 0x77770c30c30c30c30c30f0f000fc003f000fc0#152
def bw1 : WP 76 := 0xbbbb145145145145145f0f003f000fc003f000#152
def bw2 : WP 76 := 0xdddd61861861861861800ff000000ffffc0000#152
def bw3 : WP 76 := 0xeeeea28a28a28a28a28ff0003ffff000000000#152
def bw4 : WP 76 := 0xdb6db6db6db6db60000fc0000000000000#152
def bow152 : List (WP 76) := [bw0, bw1, bw2, bw3, bw4]

def bowBase152 : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5,
    6, 6, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 16, 16, 16, 16, 16, 16,
    5, 5, 5, 5, 6, 6, 6, 6, 9, 9, 9, 9, 10, 10, 10, 10,
    3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24,
    3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24,
    3, 17, 18, 12, 20, 24, 3, 17, 18, 12, 20, 24, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14, 7, 11, 13, 14]

def bowAuts : Array (List ℕ) :=
  #[[0, 1, 2, 3, 4], [1, 0, 2, 3, 4], [0, 1, 3, 2, 4], [1, 0, 3, 2, 4],
    [2, 3, 0, 1, 4], [3, 2, 0, 1, 4], [2, 3, 1, 0, 4], [3, 2, 1, 0, 4]]

def permBits5 (p : List ℕ) (y : ℕ) : Fin 32 :=
  let m := (if y.testBit 0 then 1 <<< (p.getD 0 0) else 0) |||
           (if y.testBit 1 then 1 <<< (p.getD 1 0) else 0) |||
           (if y.testBit 2 then 1 <<< (p.getD 2 0) else 0) |||
           (if y.testBit 3 then 1 <<< (p.getD 3 0) else 0) |||
           (if y.testBit 4 then 1 <<< (p.getD 4 0) else 0)
  ⟨m % 32, Nat.mod_lt _ (by decide)⟩

def bowRowMap (ai : Fin 8) (k : Fin 152) : Fin 32 :=
  permBits5 (bowAuts[ai.val]!) (bowBase152[k.val]!)

def bowProj (ai : Fin 8) : BitVec 32 → WP 76 := selectRows (bowRowMap ai)

def bowAutFor (i j : Fin 5) : Fin 8 :=
  match i.val, j.val with
  | 0, 1 => 0 | 1, 0 => 1 | 2, 3 => 4 | 3, 2 => 5
  | 0, 2 => 0 | 0, 3 => 2 | 1, 2 => 1 | 1, 3 => 3
  | 2, 0 => 4 | 2, 1 => 6 | 3, 0 => 5 | 3, 1 => 7
  | 0, 4 => 0 | 1, 4 => 1 | 2, 4 => 4 | 3, 4 => 5
  | _, _ => 0

def bowOrbit (i j : Fin 5) : Fin 3 :=
  if j.val == 4 then 2
  else if (i.val / 2) == (j.val / 2) then 0
  else 1

def checkBowProj : Bool :=
  (List.finRange 8).all (fun ai =>
    (bowProj ai bow_tt32 == goalP 76) &&
    bow_32_vars.all fun w => bow152.any fun d => bowProj ai w == d) &&
  (List.finRange 5).all (fun i =>
    (List.finRange 5).all fun j =>
      if i == j || i.val == 4 then true else
        let ai := bowAutFor i j
        let orb := bowOrbit i j
        let expI := bw0
        let expJ := if orb.val == 0 then bw1 else if orb.val == 1 then bw2 else bw4
        (bowProj ai (bowv32 i) == expI) && (bowProj ai (bowv32 j) == expJ))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bowProj_ok : checkBowProj = true := by decide +kernel

theorem bow_32_cover {w : BitVec 32} (hw : w ∈ bow_32_vars.toFinset) : ∃ i : Fin 5, bowv32 i = w := by
  rw [List.mem_toFinset] at hw
  simp only [bow_32_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

theorem bow_32_not_target : ∀ i : Fin 5, bowv32 i ≠ bow_tt32 ∧ bowv32 i ≠ ~~~bow_tt32 := by decide

theorem bow_nd01_0 : ((bw0 &&& bw1) :: bow152).Nodup := by decide +kernel
theorem bow_nd01_1 : ((bw0 ||| bw1) :: bow152).Nodup := by decide +kernel
theorem bow_nd01_2 : ((bw0 &&& ~~~bw1) :: bow152).Nodup := by decide +kernel
theorem bow_nd02_0 : ((bw0 &&& bw2) :: bow152).Nodup := by decide +kernel
theorem bow_nd02_1 : ((bw0 ||| bw2) :: bow152).Nodup := by decide +kernel
theorem bow_nd02_2 : ((bw0 &&& ~~~bw2) :: bow152).Nodup := by decide +kernel
theorem bow_nd04_0 : ((bw0 &&& bw4) :: bow152).Nodup := by decide +kernel
theorem bow_nd04_1 : ((bw0 ||| bw4) :: bow152).Nodup := by decide +kernel
theorem bow_nd04_2 : ((bw0 &&& ~~~bw4) :: bow152).Nodup := by decide +kernel
theorem bow_nd04_3 : ((bw4 &&& ~~~bw0) :: bow152).Nodup := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s01_0 : searchP 76 6 ((bw0 &&& bw1) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s01_1 : searchP 76 6 ((bw0 ||| bw1) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s01_2 : searchP 76 6 ((bw0 &&& ~~~bw1) :: bow152) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s02_0 : searchP 76 6 ((bw0 &&& bw2) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s02_1 : searchP 76 6 ((bw0 ||| bw2) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s02_2 : searchP 76 6 ((bw0 &&& ~~~bw2) :: bow152) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s04_0 : searchP 76 6 ((bw0 &&& bw4) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s04_1 : searchP 76 6 ((bw0 ||| bw4) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s04_2 : searchP 76 6 ((bw0 &&& ~~~bw4) :: bow152) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem bow_s04_3 : searchP 76 6 ((bw4 &&& ~~~bw0) :: bow152) = false := by decide +kernel

theorem bow_step_aux (i j : Fin 5) (hij : i ≠ j) (hi4 : i.val ≠ 4) {t z : BitVec 32}
    (ht : t = bow_tt32 ∨ t = ~~~bow_tt32)
    (hz : z = bowv32 i &&& bowv32 j ∨ z = bowv32 i ||| bowv32 j ∨
          z = bowv32 i &&& ~~~bowv32 j ∨ (j.val = 4 ∧ z = bowv32 j &&& ~~~bowv32 i))
    (rest : Finset (BitVec 32)) (hsub : rest ⊆ bow_32_vars.toFinset)
    (tail : live basicOps t 6 (insert z rest)) : False := by
  have hallP := (Bool.and_eq_true _ _).mp bowProj_ok
  let ai := bowAutFor i j
  have h1 := List.all_eq_true.mp hallP.1 ai (List.mem_finRange ai)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨hg, hall⟩ := h1
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp hallP.2 i (List.mem_finRange i)) j (List.mem_finRange j)
  have hcond : (i == j || i.val == 4) = false := by
    simp [beq_false_of_ne hij, beq_false_of_ne hi4]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨hi, hj⟩ := h2
  let f := bowProj ai
  have hi' : f (bowv32 i) = bw0 := hi
  have hAnd : ∀ u v, f (u &&& v) = f u &&& f v := selectRows_land (bowRowMap ai)
  have hOr : ∀ u v, f (u ||| v) = f u ||| f v := selectRows_lor (bowRowMap ai)
  have hNot : ∀ u, f (~~~u) = ~~~f u := selectRows_neg (bowRowMap ai)
  have hm := ops_map_of hAnd hOr hNot
  have hft : f t = goalP 76 ∨ f t = ~~~goalP 76 := by
    rcases ht with rfl | rfl
    · exact .inl hg
    · exact .inr ((hNot bow_tt32).trans (congrArg (fun u : WP 76 => ~~~u) hg))
  have hrest : ∀ u ∈ rest, holds bow152.toFinset (f u) := by
    intro u hu
    have hallu := List.all_eq_true.mp hall u (List.mem_toFinset.mp (hsub hu))
    obtain ⟨d, hd, heq⟩ := List.any_eq_true.mp hallu
    exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl (beq_iff_eq.mp heq)⟩)
  have run_with (w0 : WP 76) (hfw : f z = w0) (hnd : (w0 :: bow152).Nodup)
      (hsch : searchP 76 6 (w0 :: bow152) = false) : False := by
    apply signed_rejectP (by decide) hnd hsch hft
    apply live_transport hm tail
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact .inr (.inr ⟨w0, List.mem_toFinset.mpr (List.mem_cons_self ..), .inl hfw⟩)
    · exact holds_mono (by intro x hx; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))) (hrest u hr)
  match horb : (bowOrbit i j).val with
  | 0 =>
    have hj1 : f (bowv32 j) = bw1 := by simpa [horb] using hj
    have hj4 : j.val ≠ 4 := by
      intro h4; simp [bowOrbit, h4] at horb
    rcases hz with rfl | rfl | rfl | ⟨h4, _⟩
    · exact run_with (bw0 &&& bw1) (by rw [hAnd, hi', hj1]) bow_nd01_0 bow_s01_0
    · exact run_with (bw0 ||| bw1) (by rw [hOr, hi', hj1]) bow_nd01_1 bow_s01_1
    · exact run_with (bw0 &&& ~~~bw1) (by rw [hAnd, hNot, hi', hj1]) bow_nd01_2 bow_s01_2
    · exact (hj4 h4).elim
  | 1 =>
    have hj2 : f (bowv32 j) = bw2 := by simpa [horb] using hj
    have hj4 : j.val ≠ 4 := by
      intro h4; simp [bowOrbit, h4] at horb
    rcases hz with rfl | rfl | rfl | ⟨h4, _⟩
    · exact run_with (bw0 &&& bw2) (by rw [hAnd, hi', hj2]) bow_nd02_0 bow_s02_0
    · exact run_with (bw0 ||| bw2) (by rw [hOr, hi', hj2]) bow_nd02_1 bow_s02_1
    · exact run_with (bw0 &&& ~~~bw2) (by rw [hAnd, hNot, hi', hj2]) bow_nd02_2 bow_s02_2
    · exact (hj4 h4).elim
  | 2 =>
    have hj4 : f (bowv32 j) = bw4 := by simpa [horb] using hj
    rcases hz with rfl | rfl | rfl | ⟨_, rfl⟩
    · exact run_with (bw0 &&& bw4) (by rw [hAnd, hi', hj4]) bow_nd04_0 bow_s04_0
    · exact run_with (bw0 ||| bw4) (by rw [hOr, hi', hj4]) bow_nd04_1 bow_s04_1
    · exact run_with (bw0 &&& ~~~bw4) (by rw [hAnd, hNot, hi', hj4]) bow_nd04_2 bow_s04_2
    · exact run_with (bw4 &&& ~~~bw0) (by rw [hAnd, hNot, hi', hj4]) bow_nd04_3 bow_s04_3
  | n + 3 =>
    have := (bowOrbit i j).isLt
    omega

theorem bow_no7_32 (t : BitVec 32) (ht : t = bow_tt32 ∨ t = ~~~bow_tt32)
    (hb : build basicOps t 7 bow_32_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 6) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := bow_32_cover mt
    rcases ht with rfl | rfl
    · exact (bow_32_not_target i).1 hi
    · exact (bow_32_not_target i).2 hi
  · obtain ⟨i, rfl⟩ := bow_32_cover (hs ha)
    obtain ⟨j, rfl⟩ := bow_32_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg bowv32 e)
    have hsub : rest ⊆ bow_32_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases hi4 : i.val = 4
    · have hj4 : j.val ≠ 4 := fun h => hij (Fin.ext (hi4.trans h.symm))
      rcases hz with rfl | rfl | rfl | rfl
      · rw [BitVec.and_comm] at tail
        exact bow_step_aux j i hij.symm hj4 ht (.inl rfl) rest hsub tail
      · rw [BitVec.or_comm] at tail
        exact bow_step_aux j i hij.symm hj4 ht (.inr (.inl rfl)) rest hsub tail
      · exact bow_step_aux j i hij.symm hj4 ht (.inr (.inr (.inr ⟨hi4, rfl⟩))) rest hsub tail
      · exact bow_step_aux j i hij.symm hj4 ht (.inr (.inr (.inl rfl))) rest hsub tail
    · rcases hz with rfl | rfl | rfl | rfl
      · exact bow_step_aux i j hij hi4 ht (.inl rfl) rest hsub tail
      · exact bow_step_aux i j hij hi4 ht (.inr (.inl rfl)) rest hsub tail
      · exact bow_step_aux i j hij hi4 ht (.inr (.inr (.inl rfl))) rest hsub tail
      · by_cases hj4 : j.val = 4
        · exact bow_step_aux i j hij hi4 ht (.inr (.inr (.inr ⟨hj4, rfl⟩))) rest hsub tail
        · exact bow_step_aux j i hij.symm hj4 ht (.inr (.inr (.inl rfl))) rest hsub tail

end BowtieBase

section Compile128

abbrev W128 := BitVec 128

def bit128 (k : Fin 128) (z : W128) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit128 (w : List W128) (i : ℕ) (k : Fin 128) :
    (w.map (bit128 k)).getD i false = bit128 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit128]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W128) (g : Gate) : W128 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W128) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit128 k)) g = (w ++ [action w g]).map (bit128 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W128)[k.val] = false := by change (0#128)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit128, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit128, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W128} {w : List W128} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W128, x ||| (0 : W128) = x from fun x => BitVec.or_zero,
    show ∀ x : W128, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W128) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W128) (av : Finset W128) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit128 k))).getD out false = bit128 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit128, bit128] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W128 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit128 k))).getD out false = bit128 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W128) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

end Compile128

def edges11733 : List ℕ := [0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6]

def edgeValue (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edges11733.length / 2,
    (List.ofFn x).getD (edges11733.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges11733.getD (2 * i + 1) 0) false = true)

def v0 : W128 := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#128
def v1 : W128 := 0xcccccccccccccccccccccccccccccccc#128
def v2 : W128 := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#128
def v3 : W128 := 0xff00ff00ff00ff00ff00ff00ff00ff00#128
def v4 : W128 := 0xffff0000ffff0000ffff0000ffff0000#128
def v5 : W128 := 0xffffffff00000000ffffffff00000000#128
def v6 : W128 := 0xffffffffffffffff0000000000000000#128

def rows7 : List W128 := [v0, v1, v2, v3, v4, v5, v6]
def rows6 : List W128 := [v0, v1, v3, v4, v5, v6]
def target7 : W128 := 0xfffffffffffefefefffefefeffaaaa00#128
def target6 : W128 := 0xffffffffffeeeeeeffeeeeeeffaaaa00#128

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sample7 : ∀ k : Fin 128,
    edgeValue (fun i => (rows7.getD i.val 0)[k.val]) = target7[k.val] := by
  decide +kernel

def fixBit (i : Fin 7) (val : Bool) (k : Fin 128) : Fin 128 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (127 - bit)
  ⟨m % 128, Nat.mod_lt _ (by decide)⟩

-- The lowest two positive pairs involving vertices 1 and 2 distinguish their
-- input wires from all others. Fixing either such wire to false saves a gate.
theorem pinInput {n m k : ℕ} (mp : Fin m → Fin n)
    (src : List (BitVec n)) (dst : List (BitVec m))
    (p g : BitVec n) (projected : BitVec m) (a b : Fin n)
    (diff : bitDiff a b g) (unique : ∀ w ∈ src, bitDiff a b w → w = p)
    (pin : selectRows mp p = 0) (goal : selectRows mp g = projected)
    (nonconstant : projected ≠ 0 ∧ projected ≠ ~~~0)
    (read : ∀ w ∈ src, holds dst.toFinset (selectRows mp w))
    (t : BitVec n) (ht : t = g ∨ t = ~~~g)
    (hb : build basicOps t (k + 1) src.toFinset) :
    ∃ u, (u = projected ∨ u = ~~~projected) ∧ build basicOps u k dst.toFinset := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff a b t := by
    rcases ht with rfl | rfl
    · exact diff
    · exact bitDiff_not diff
  have active := live_has_unique_sep hs hl a b hd unique
  have hm := ops_map_of (selectRows_land mp) (selectRows_lor mp) (selectRows_neg mp)
  have ht' : selectRows mp t = projected ∨ selectRows mp t = ~~~projected := by
    rcases ht with rfl | rfl
    · exact .inl goal
    · exact .inr ((selectRows_neg mp g).trans (congrArg (fun z : BitVec m => ~~~z) goal))
  have hn : selectRows mp t ≠ 0 ∧ selectRows mp t ≠ ~~~0 := by
    rcases ht' with he | he <;> rw [he]
    · exact nonconstant
    · exact not_const_of_neg nonconstant
  obtain ⟨_, hsb⟩ := live_transport_save_const hm hl active (.inl pin) hn
    (fun w hw => read w (List.mem_toFinset.mp (hs hw)))
  obtain ⟨u, hu, hrun⟩ := unwrap_sb hn.1 hn.2 hsb
  refine ⟨u, ?_, hrun⟩
  rcases ht' with he | he <;> rcases hu with rfl | rfl <;> rw [he]
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl
  · exact .inl BitVec.not_not

-- The order on the five remaining inputs is 3, 4, 5, 6, 0.
def bowMap (k : Fin 32) : Fin 128 :=
  ⟨(((k.val &&& 15) <<< 3) ||| (k.val >>> 4)) % 128, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
theorem noNineBinary (t : W128) (ht : t = target7 ∨ t = ~~~target7)
    (hb : build basicOps t 9 rows7.toFinset) : False := by
  obtain ⟨t6, ht6, hb6⟩ := pinInput (k := 8) (fixBit 2 false) rows7 rows6
    v2 target7 target6 32 36 (by unfold bitDiff; decide +kernel)
    (sep_of_all 32 36 rows7 v2 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (map_holds_list _ rows7 rows6 (by decide +kernel)) t ht hb
  obtain ⟨t5, ht5, hb5⟩ := pinInput (k := 7) bowMap rows6 bow_32_vars
    v1 target6 bow_tt32 32 34 (by unfold bitDiff; decide +kernel)
    (sep_of_all 32 34 rows6 v1 (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide)
    (map_holds_list _ rows6 bow_32_vars (by decide +kernel)) t6 ht6 hb6
  exact bow_no7_32 t5 ht5 hb5

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeValue x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows7, holds rows7.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (rows7.map (bit128 k))).getD o false = bit128 k target7 := by
    let x (i : Fin 7) : Bool := bit128 k (rows7.getD i.val 0)
    have width : rows7.length = 7 := rfl
    have same : List.ofFn x = rows7.map (bit128 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < rows7.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows7.map (bit128 k)) = bit128 k target7
    rw [← same, he]
    exact sample7 k
  obtain ⟨t, ht, run⟩ := compile target7 (by decide) (by decide) gs o hg rows7 rows7.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rows7.toFinset) :
      build basicOps t b rows7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact noNineBinary t ht (lift low run)

end PEqualNP.Outside.L_meta_14952_aux.Signed

namespace PEqualNP.Outside.L_meta_14952_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_14952_aux.Signed (legal isBinary binaryCost)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_legal (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

theorem isBinary_and (l : List ℕ) : isBinary ⟨GateOp.and, l⟩ = true := rfl
theorem isBinary_or (l : List ℕ) : isBinary ⟨GateOp.or, l⟩ = true := rfl
theorem isBinary_not (l : List ℕ) : isBinary ⟨GateOp.not, l⟩ = false := rfl

theorem simplify_binCost_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    binaryCost (simplify op m ins).1.toList ≤ if isBinary ⟨op, []⟩ then 1 else 0 := by
  have hlen : ∀ o : Option Gate, binaryCost o.toList ≤ 1 := by
    intro o
    cases o with
    | none => simp [binaryCost]
    | some g => exact (List.length_filter_le _ _).trans (by simp)
  cases op
  · exact hlen _
  · exact hlen _
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simplify, simpNot, binaryCost, isBinary_not]
  · simp [simplify, binaryCost]
  · simp [simplify, binaryCost]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem binaryCost_append (l1 l2 : List Gate) :
    binaryCost (l1 ++ l2) = binaryCost l1 + binaryCost l2 := by
  simp [binaryCost, List.filter_append]

theorem binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = (if isBinary g then 1 else 0) + binaryCost gs := by
  simp only [binaryCost, List.filter_cons]
  cases isBinary g <;> simp [Nat.add_comm]

theorem elim_legal (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → (∀ g ∈ (elim n gs acc).2, legal g) := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_legal _ _ _ g' hg'

theorem elim_binCost_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs with
  | nil => intro acc; simp [elim, binaryCost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq] at hb
      omega
    rw [elim_cons, binaryCost_cons]
    omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def AgreeNonConst (st : List Stat) (w1 w2 : List Bool) : Prop :=
  st.length = w1.length ∧ st.length = w2.length ∧
  ∀ i : ℕ, (∃ j : ℕ, st.getD i (Sum.inl false) = Sum.inr j) → w1.getD i false = w2.getD i false

theorem elim_agree_of_eq_binCost (n : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, legal g) →
      AgreeNonConst acc.1 w1 w2 →
      binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs →
      AgreeNonConst (elim n gs acc).1 (wiresFrom gs w1) (wiresFrom gs w2) := by
  induction gs with
  | nil => intro w1 w2 acc _ hag _; exact hag
  | cons g gs ih =>
    intro w1 w2 acc hok hag heq
    have hstep_le : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq' : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq'] at hb; omega
    have htail_le := elim_binCost_le n gs (elimStep n acc g)
    rw [elim_cons, binaryCost_cons] at heq
    have hstep_eq : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + (if isBinary g then 1 else 0) := by omega
    have htail_eq : binaryCost (elim n gs (elimStep n acc g)).2 = binaryCost (elimStep n acc g).2 + binaryCost gs := by omega
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
             (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
             (elimStep n acc g)
             (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ htail_eq
    obtain ⟨hl1, hl2, hwi⟩ := hag
    refine ⟨by simp [elimStep, hl1], by simp [elimStep, hl2], ?_⟩
    intro i hi
    by_cases hil : i = acc.1.length
    · subst hil
      simp only [elimStep] at hi ⊢
      rw [getD_snoc_eq] at hi
      rw [hl1, getD_snoc_eq, ← hl1, hl2, getD_snoc_eq]
      have hgok := hok g List.mem_cons_self
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hlen⟩ := hgok
      dsimp only [elimStep] at hi hstep_eq
      rw [binaryCost_append] at hstep_eq
      rcases hop with rfl | rfl | rfl
      · rw [isBinary_and] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpAnd, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpAnd, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rw [isBinary_or] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpOr, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpOr, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rcases args with _ | ⟨k1, l⟩
        · simp [simplify, simpNot] at hi
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, h1] at hi
            simp [simplify, simpNot] at hi
          · have e1 := hwi k1 ⟨a, h1⟩
            simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 ⊢
            rw [e1]
    · simp only [elimStep] at hi ⊢
      rw [getD_snoc_ne _ _ _ _ hil] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hwi i hi

def insAt {α : Type} {n : ℕ} (idx : Fin (n + 1)) (v : α) (y : Fin n → α) (k : Fin (n + 1)) : α :=
  if h1 : k.val < idx.val then y ⟨k.val, by omega⟩
  else if h2 : k.val = idx.val then v
  else y ⟨k.val - 1, by omega⟩

theorem drop_one_var {n : ℕ} (idx : Fin (n + 1)) (v : Bool) (F : (Fin (n + 1) → Bool) → Bool)
    (y_diff y0 y1 : Fin n → Bool)
    (hdiff : F (insAt idx false y_diff) ≠ F (insAt idx true y_diff))
    (hnc : F (insAt idx v y0) ≠ F (insAt idx v y1))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin (n + 1) → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', legal g) ∧ binaryCost gs' < binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn y) = F (insAt idx v y) := by
  let initFn : Fin (n + 1) → Stat := insAt idx (Sum.inl v) (fun i : Fin n => Sum.inr i.val)
  let initSt : List Stat := List.ofFn initFn
  let res := elim n gs (initSt, [])
  have hgetFn : ∀ {α : Type} (f : Fin (n + 1) → α) (d : α) (i : ℕ) (hi : i < n + 1),
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    intro α f d i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]), Option.getD_some,
      List.getElem_ofFn]
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (List.ofFn (insAt idx v y)) (initSt, []) := by
    intro y
    refine ⟨by simp [initSt], ?_⟩
    intro i
    by_cases hi : i < n + 1
    · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi,
          hgetFn (insAt idx v y) false i hi]
      dsimp only [initFn, insAt]
      by_cases h1 : i < idx.val
      · simp only [h1, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
        refine ⟨by omega, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
          Option.getD_some, List.getElem_ofFn]
      · by_cases h2 : i = idx.val
        · simp [h2, statValid, statVal]
        · simp only [h1, h2, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
          refine ⟨by omega, ?_⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
            Option.getD_some, List.getElem_ofFn]
    · have h1 : initSt.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [initSt]; omega)
      have h2 : (List.ofFn (insAt idx v y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [h1, h2]; simp [statValid, statVal]
  have heval : ∀ y : Fin n → Bool,
      statVal (wiresFrom res.2 (List.ofFn y)) (res.1.getD o (Sum.inl false)) =
        F (insAt idx v y) := by
    intro y
    have hi := inv_elim n (List.ofFn y) (by simp) gs (List.ofFn (insAt idx v y)) (initSt, []) hg (hinv y)
    have h2 := (hi.2 o).2
    have h3 : (wiresFrom gs (List.ofFn (insAt idx v y))).getD o false =
        F (insAt idx v y) := he (insAt idx v y)
    exact h2.trans h3
  have hout_inr : ∃ o', res.1.getD o (Sum.inl false) = Sum.inr o' := by
    cases hst : res.1.getD o (Sum.inl false) with
    | inl c =>
      have e0 := heval y0; rw [hst] at e0
      have e1 := heval y1; rw [hst] at e1
      exact (hnc (e0.symm.trans e1)).elim
    | inr o' => exact ⟨o', rfl⟩
  obtain ⟨o', ho'⟩ := hout_inr
  have hlt : binaryCost res.2 < binaryCost gs := by
    have hle : binaryCost res.2 ≤ binaryCost ([] : List Gate) + binaryCost gs :=
      elim_binCost_le n gs (initSt, [])
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    by_contra hnot
    have heq : binaryCost res.2 = binaryCost ([] : List Gate) + binaryCost gs := by omega
    have hag0 : AgreeNonConst initSt
        (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff)) := by
      refine ⟨by simp [initSt], by simp [initSt], ?_⟩
      intro i ⟨j, hj⟩
      by_cases hi : i < n + 1
      · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi] at hj
        rw [hgetFn (insAt idx false y_diff) false i hi, hgetFn (insAt idx true y_diff) false i hi]
        dsimp only [initFn, insAt] at hj ⊢
        by_cases h1 : i < idx.val
        · simp [h1]
        · by_cases h2 : i = idx.val
          · simp [h2] at hj
          · simp [h1, h2]
      · rw [List.getD_eq_default _ _ (by simp [initSt]; omega)] at hj
        cases hj
    have hag := elim_agree_of_eq_binCost n gs
      (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff))
      (initSt, []) hg hag0 heq
    have hsame := hag.2.2 o ⟨o', ho'⟩
    have hf0 : (wiresFrom gs (List.ofFn (insAt idx false y_diff))).getD o false =
        F (insAt idx false y_diff) := he _
    have hf1 : (wiresFrom gs (List.ofFn (insAt idx true y_diff))).getD o false =
        F (insAt idx true y_diff) := he _
    exact hdiff (hf0.symm.trans (hsame.trans hf1))
  refine ⟨res.2, o', elim_legal n gs (initSt, []) (by simp), hlt, ?_⟩
  intro y
  have h := heval y
  rw [ho'] at h
  exact h

def edges : List ℕ := [0,4,0,5,4,5,0,6,1,6,2,6,3,6,0,7,1,7,2,7,3,7,6,7]
def target (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧ (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)
-- Pin vertex 3 to false to obtain the seven-vertex graph from L-meta-11733.
theorem binary_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) : 11 ≤ binaryCost gs := by
  obtain ⟨g7,o7,h7,l7,e7⟩ := drop_one_var (3 : Fin 8) false target (fun i => decide (i = 5))
    (fun _ => false) (fun _ => true) (by decide +kernel) (by decide +kernel) gs o hg he
  have eqf : ∀ y : Fin 7 → Bool, target (insAt (3 : Fin 8) false y) = Signed.edgeValue y := by decide +kernel
  have low := Signed.cost_bound g7 o7 h7 (fun y => (e7 y).trans (eqf y))
  omega

def witness : Circuit := ⟨[
  ⟨.or,[4,5]⟩,⟨.and,[0,8]⟩,⟨.and,[4,5]⟩,⟨.or,[9,10]⟩,
  ⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[12,13]⟩,⟨.or,[6,7]⟩,
  ⟨.and,[14,15]⟩,⟨.and,[6,7]⟩,⟨.or,[16,17]⟩,⟨.or,[11,18]⟩],19⟩
theorem witness_mono : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
set_option maxRecDepth 10000 in
theorem witness_eval : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by decide +kernel
end PEqualNP.Outside.L_meta_14952_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_14952_aux in
theorem PEqualNP.Outside.L_meta_14952 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ he
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · have bound := binary_bound gs o legal he
    obtain ⟨g,mem,hop⟩ := hn
    have lt : Signed.binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr ⟨g,mem,by simp [Signed.isBinary,hop]⟩
    refine ⟨witness.gates,witness.output,witness_mono,?_,witness_eval⟩
    change 12 ≤ gs.length
    omega
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g mem
    obtain ⟨hop,cap⟩ := legal g mem
    rcases hop with a | b | c
    · exact ⟨Or.inl a,cap⟩
    · exact ⟨Or.inr b,cap⟩
    · exact (hn ⟨g,mem,c⟩).elim
