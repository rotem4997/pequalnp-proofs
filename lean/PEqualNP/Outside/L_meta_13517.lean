import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13517

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
    simp only [hnot, ↓reduceIte, Nat.add_sub_cancel_left]
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
    simp [sepP, i.isLt, differsP, bx]

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

section F5Base

def f5_32_vars : List (BitVec 32) :=
  [0xaaaaaaaa#32, 0xcccccccc#32, 0xf0f0f0f0#32, 0xff00ff00#32, 0xffff0000#32]
def f5v32 (i : Fin 5) : BitVec 32 := f5_32_vars.getD i.val 0
def f5_tt32 : BitVec 32 := 0xeee0eac0#32

def gw0 : WP 40 := (0x7957799656#40 ++ 0x311531aacc#40)
def gw1 : WP 40 := (0xb6abb669a9#40 ++ 0x322a3255cc#40)
def gw2 : WP 40 := (0xd65dd69959#40 ++ 0xc445c4aa33#40)
def gw3 : WP 40 := (0xe9aee966a6#40 ++ 0xc88ac85533#40)
def gw4 : WP 40 := (0xfff000f0f0#40 ++ 0xfff00000ff#40)
def f5inputs : List (WP 40) := [gw0, gw1, gw2, gw3, gw4]
def f5w (i : Fin 5) : WP 40 := f5inputs.getD i.val 0

def f5Base80 : Array ℕ :=
  #[28, 28, 19, 19, 28, 28, 19, 19, 10, 5, 10, 5, 10, 5, 10, 5, 1, 2, 4, 8, 3, 3, 12, 12, 5, 10, 5, 10, 17, 18, 20, 24, 17, 18, 20, 24, 19, 19, 28, 28, 6, 9, 9, 6, 21, 26, 21, 26, 6, 9, 9, 6, 21, 26, 26, 21, 9, 6, 6, 9, 7, 11, 13, 14, 7, 11, 13, 14, 21, 26, 21, 26, 25, 22, 22, 25, 23, 27, 29, 30]

def f5Auts : Array (List ℕ) :=
  #[[0, 1, 2, 3, 4], [1, 0, 3, 2, 4], [2, 3, 0, 1, 4], [3, 2, 1, 0, 4]]

def permBits5 (p : List ℕ) (y : ℕ) : Fin 32 :=
  let m := (if y.testBit 0 then 1 <<< (p.getD 0 0) else 0) |||
           (if y.testBit 1 then 1 <<< (p.getD 1 0) else 0) |||
           (if y.testBit 2 then 1 <<< (p.getD 2 0) else 0) |||
           (if y.testBit 3 then 1 <<< (p.getD 3 0) else 0) |||
           (if y.testBit 4 then 1 <<< (p.getD 4 0) else 0)
  ⟨m % 32, Nat.mod_lt _ (by decide)⟩

def f5RowMap (ai : Fin 4) (k : Fin 80) : Fin 32 :=
  permBits5 (f5Auts[ai.val]!) (f5Base80[k.val]!)

def f5Proj (ai : Fin 4) : BitVec 32 → WP 40 := selectRows (f5RowMap ai)

def autIdx (ai : Fin 4) (i : Fin 5) : Fin 5 :=
  ⟨(f5Auts[ai.val]!).getD i.val 0 % 5, Nat.mod_lt _ (by decide)⟩

def checkF5Proj : Bool :=
  (List.finRange 4).all fun ai =>
    (f5Proj ai f5_tt32 == goalP 40) &&
    (List.finRange 5).all (fun i => f5Proj ai (f5v32 i) == f5w (autIdx ai i)) &&
    f5_32_vars.all fun w => f5inputs.any fun d => f5Proj ai w == d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem f5Proj_ok : checkF5Proj = true := by decide +kernel

theorem f5_32_cover {w : BitVec 32} (hw : w ∈ f5_32_vars.toFinset) : ∃ i : Fin 5, f5v32 i = w := by
  rw [List.mem_toFinset] at hw
  simp only [f5_32_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

theorem f5_32_not_target : ∀ i : Fin 5, f5v32 i ≠ f5_tt32 ∧ f5v32 i ≠ ~~~f5_tt32 := by decide

theorem f5_nd_0_1_0 : ((gw0 &&& gw1) :: f5inputs).Nodup := by decide
theorem f5_nd_0_1_1 : ((gw0 ||| gw1) :: f5inputs).Nodup := by decide
theorem f5_nd_0_1_2 : ((gw0 &&& ~~~gw1) :: f5inputs).Nodup := by decide
theorem f5_nd_0_2_0 : ((gw0 &&& gw2) :: f5inputs).Nodup := by decide
theorem f5_nd_0_2_1 : ((gw0 ||| gw2) :: f5inputs).Nodup := by decide
theorem f5_nd_0_2_2 : ((gw0 &&& ~~~gw2) :: f5inputs).Nodup := by decide
theorem f5_nd_0_3_0 : ((gw0 &&& gw3) :: f5inputs).Nodup := by decide
theorem f5_nd_0_3_1 : ((gw0 ||| gw3) :: f5inputs).Nodup := by decide
theorem f5_nd_0_3_2 : ((gw0 &&& ~~~gw3) :: f5inputs).Nodup := by decide
theorem f5_nd_0_4_0 : ((gw0 &&& gw4) :: f5inputs).Nodup := by decide
theorem f5_nd_0_4_1 : ((gw0 ||| gw4) :: f5inputs).Nodup := by decide
theorem f5_nd_0_4_2 : ((gw0 &&& ~~~gw4) :: f5inputs).Nodup := by decide
theorem f5_nd_0_4_3 : ((gw4 &&& ~~~gw0) :: f5inputs).Nodup := by decide

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_1_0 : searchP 40 5 ((gw0 &&& gw1) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_1_1 : searchP 40 5 ((gw0 ||| gw1) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_1_2 : searchP 40 5 ((gw0 &&& ~~~gw1) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_2_0 : searchP 40 5 ((gw0 &&& gw2) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_2_1 : searchP 40 5 ((gw0 ||| gw2) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_2_2 : searchP 40 5 ((gw0 &&& ~~~gw2) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_3_0 : searchP 40 5 ((gw0 &&& gw3) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_3_1 : searchP 40 5 ((gw0 ||| gw3) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_3_2 : searchP 40 5 ((gw0 &&& ~~~gw3) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_4_0 : searchP 40 5 ((gw0 &&& gw4) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_4_1 : searchP 40 5 ((gw0 ||| gw4) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_4_2 : searchP 40 5 ((gw0 &&& ~~~gw4) :: f5inputs) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem f5_s_0_4_3 : searchP 40 5 ((gw4 &&& ~~~gw0) :: f5inputs) = false := by decide +kernel

theorem f5_run (ai : Fin 4) {t z : BitVec 32} (ht : t = f5_tt32 ∨ t = ~~~f5_tt32)
    (rest : Finset (BitVec 32)) (hsub : rest ⊆ f5_32_vars.toFinset)
    (tail : live basicOps t 5 (insert z rest))
    (w0 : WP 40) (hfw : f5Proj ai z = w0) (hnd : (w0 :: f5inputs).Nodup)
    (hsch : searchP 40 5 (w0 :: f5inputs) = false) : False := by
  have h1 := List.all_eq_true.mp f5Proj_ok ai (List.mem_finRange ai)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨hg, _⟩, hall⟩ := h1
  let f := f5Proj ai
  have hm := ops_map_of (selectRows_land (f5RowMap ai)) (selectRows_lor (f5RowMap ai)) (selectRows_neg (f5RowMap ai))
  have hft : f t = goalP 40 ∨ f t = ~~~goalP 40 := by
    rcases ht with rfl | rfl
    · exact .inl hg
    · exact .inr ((selectRows_neg (f5RowMap ai) f5_tt32).trans (congrArg (fun u : WP 40 => ~~~u) hg))
  have hrest : ∀ u ∈ rest, holds f5inputs.toFinset (f u) := by
    intro u hu
    have hallu := List.all_eq_true.mp hall u (List.mem_toFinset.mp (hsub hu))
    obtain ⟨d, hd, heq⟩ := List.any_eq_true.mp hallu
    exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl (beq_iff_eq.mp heq)⟩)
  apply signed_rejectP (by decide) hnd hsch hft
  apply live_transport hm tail
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hr
  · exact .inr (.inr ⟨w0, List.mem_toFinset.mpr (List.mem_cons_self ..), .inl hfw⟩)
  · exact holds_mono (by intro x hx; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))) (hrest u hr)

theorem f5Proj_var (ai : Fin 4) (i : Fin 5) : f5Proj ai (f5v32 i) = f5w (autIdx ai i) := by
  have h1 := List.all_eq_true.mp f5Proj_ok ai (List.mem_finRange ai)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact beq_iff_eq.mp (List.all_eq_true.mp h1.1.2 i (List.mem_finRange i))

theorem f5_step_ord (i j : Fin 5) (hij : i.val < j.val) {t z : BitVec 32}
    (ht : t = f5_tt32 ∨ t = ~~~f5_tt32)
    (hz : z ∈ basicOps (f5v32 i) (f5v32 j))
    (rest : Finset (BitVec 32)) (hsub : rest ⊆ f5_32_vars.toFinset)
    (tail : live basicOps t 5 (insert z rest)) : False := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hAnd : ∀ ai u v, f5Proj ai (u &&& v) = f5Proj ai u &&& f5Proj ai v := fun ai => selectRows_land (f5RowMap ai)
  have hOr : ∀ ai u v, f5Proj ai (u ||| v) = f5Proj ai u ||| f5Proj ai v := fun ai => selectRows_lor (f5RowMap ai)
  have hNot : ∀ ai u, f5Proj ai (~~~u) = ~~~f5Proj ai u := fun ai => selectRows_neg (f5RowMap ai)
  fin_cases i <;> fin_cases j <;> simp at hij
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_0 f5_s_0_1_0
    · exact f5_run 0 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_1 f5_s_0_1_1
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_2 f5_s_0_1_2
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_2 f5_s_0_1_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_0 f5_s_0_2_0
    · exact f5_run 0 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_1 f5_s_0_2_1
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_2 f5_s_0_2_2
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_2 f5_s_0_2_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_0 f5_s_0_3_0
    · exact f5_run 0 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_1 f5_s_0_3_1
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_2 f5_s_0_3_2
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_2 f5_s_0_3_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_0 f5_s_0_4_0
    · exact f5_run 0 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_1 f5_s_0_4_1
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_2 f5_s_0_4_2
    · exact f5_run 0 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_3 f5_s_0_4_3
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_0 f5_s_0_3_0
    · exact f5_run 1 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_1 f5_s_0_3_1
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_2 f5_s_0_3_2
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_3_2 f5_s_0_3_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_0 f5_s_0_2_0
    · exact f5_run 1 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_1 f5_s_0_2_1
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_2 f5_s_0_2_2
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_2_2 f5_s_0_2_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_0 f5_s_0_4_0
    · exact f5_run 1 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_1 f5_s_0_4_1
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_2 f5_s_0_4_2
    · exact f5_run 1 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_3 f5_s_0_4_3
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_0 f5_s_0_1_0
    · exact f5_run 2 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_1 f5_s_0_1_1
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_2 f5_s_0_1_2
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_1_2 f5_s_0_1_2
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_0 f5_s_0_4_0
    · exact f5_run 2 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_1 f5_s_0_4_1
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_2 f5_s_0_4_2
    · exact f5_run 2 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_3 f5_s_0_4_3
  · rcases hz with rfl | rfl | rfl | rfl
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_0 f5_s_0_4_0
    · exact f5_run 3 ht rest hsub tail _ (by rw [hOr, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_1 f5_s_0_4_1
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_2 f5_s_0_4_2
    · exact f5_run 3 ht rest hsub tail _ (by rw [hAnd, hNot, f5Proj_var, f5Proj_var]; rfl) f5_nd_0_4_3 f5_s_0_4_3

theorem f5_no6_32 (t : BitVec 32) (ht : t = f5_tt32 ∨ t = ~~~f5_tt32)
    (hb : build basicOps t 6 f5_32_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 5) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := f5_32_cover mt
    rcases ht with rfl | rfl
    · exact (f5_32_not_target i).1 hi
    · exact (f5_32_not_target i).2 hi
  · obtain ⟨i, rfl⟩ := f5_32_cover (hs ha)
    obtain ⟨j, rfl⟩ := f5_32_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg f5v32 e)
    have hsub : rest ⊆ f5_32_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    rcases Nat.lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with hlt | hgt
    · exact f5_step_ord i j hlt ht hz rest hsub tail
    · exact f5_step_ord j i hgt ht (ops_swap (f5v32 i) (f5v32 j) ▸ hz) rest hsub tail

end F5Base


section Compile64

abbrev W64 := BitVec 64

def bit64 (k : Fin 64) (z : W64) : Bool := z[k.val]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit64 (w : List W64) (i : ℕ) (k : Fin 64) :
    (w.map (bit64 k)).getD i false = bit64 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit64]

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W64) (g : Gate) : W64 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W64) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit64 k)) g = (w ++ [action w g]).map (bit64 k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W64)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit64, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit64, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

theorem available_read {av : Finset W64} {w : List W64} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W64) (av : Finset W64) (hw : ∀ u ∈ w, holds av u)
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
    show ∀ x : W64, x ||| (0 : W64) = x from fun x => BitVec.or_zero,
    show ∀ x : W64, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (target : W64) (hnt0 : target ≠ 0) (hnt1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W64) (av : Finset W64) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit64 k))).getD out false = bit64 k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit64, bit64] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hnt0 zero)
    · exact False.elim (hnt1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun u : W64 => ~~~u) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit64 k))).getD out false = bit64 k target := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W64) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
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

end Compile64

section Lower13517

def targetFn (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4007717568 * 2 ^ 32 + 3969908736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def v0 : W64 := 0xaaaaaaaaaaaaaaaa#64
def v1 : W64 := 0xcccccccccccccccc#64
def v2 : W64 := 0xf0f0f0f0f0f0f0f0#64
def v3 : W64 := 0xff00ff00ff00ff00#64
def v4 : W64 := 0xffff0000ffff0000#64
def v5 : W64 := 0xffffffff00000000#64

def rows6 : List W64 := [v0, v1, v2, v3, v4, v5]
def rows5 : List W64 := [v0, v1, v2, v3, v4]

def target6 : W64 := 0xeee0eac0eca00000#64
def target5 : W64 := 0xeee0eac0eee0eac0#64

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sample6 : ∀ k : Fin 64,
    targetFn (fun i => (rows6.getD i.val 0)[k.val]) = target6[k.val] := by
  decide +kernel

def fixBit (i : Fin 6) (val : Bool) (k : Fin 64) : Fin 64 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (63 - bit)
  ⟨m % 64, Nat.mod_lt _ (by decide)⟩

def r5 : W64 → W64 := selectRows (fixBit 5 true)

theorem t6_nc : target6 ≠ 0 ∧ target6 ≠ ~~~0 := by decide
theorem t5_nc : target5 ≠ 0 ∧ target5 ≠ ~~~0 := by decide
theorem r5_t6 : r5 target6 = target5 := by decide +kernel
theorem r5_v5 : r5 v5 = ~~~0 := by decide +kernel

theorem sep6 : bitDiff ⟨6, by decide⟩ ⟨38, by decide⟩ target6 ∧
    ∀ w ∈ rows6, bitDiff ⟨6, by decide⟩ ⟨38, by decide⟩ w → w = v5 :=
  ⟨by unfold bitDiff; decide +kernel,
   sep_of_all ⟨6, by decide⟩ ⟨38, by decide⟩ rows6 v5 (by decide +kernel)⟩

theorem hold_rows5 : ∀ w ∈ rows6, holds rows5.toFinset (r5 w) :=
  map_holds_list r5 rows6 rows5 (by decide +kernel)

def f5Map64 (k : Fin 32) : Fin 64 := ⟨k.val, by omega⟩
def projF5_32 : W64 → BitVec 32 := selectRows f5Map64

theorem proj_f5_t : projF5_32 target5 = f5_tt32 := by decide +kernel

theorem hold_f5_32 : ∀ w ∈ rows5, holds f5_32_vars.toFinset (projF5_32 w) :=
  map_holds_list projF5_32 rows5 f5_32_vars (by decide +kernel)

theorem f5_64_false (t : W64) (ht : t = target5 ∨ t = ~~~target5)
    (hb : build basicOps t 6 rows5.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hm := ops_map_of (selectRows_land f5Map64) (selectRows_lor f5Map64) (selectRows_neg f5Map64)
  have hsb := live_transport hm hl (fun w hw => hold_f5_32 w (List.mem_toFinset.mp (hs hw)))
  have hft : projF5_32 t = f5_tt32 ∨ projF5_32 t = ~~~f5_tt32 := by
    rcases ht with rfl | rfl
    · exact .inl proj_f5_t
    · exact .inr ((selectRows_neg f5Map64 target5).trans (congrArg (fun u : BitVec 32 => ~~~u) proj_f5_t))
  have hnc : f5_tt32 ≠ 0 ∧ f5_tt32 ≠ ~~~0 := by decide
  have hng : projF5_32 t ≠ 0 ∧ projF5_32 t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact hnc
    · exact not_const_of_neg hnc
  obtain ⟨t32, ht32, hb32⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht32' : t32 = f5_tt32 ∨ t32 = ~~~f5_tt32 := by
    rcases hft with h | h <;> rcases ht32 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact f5_no6_32 t32 ht32' hb32

theorem no_seven_t6 (t : W64) (ht : t = target6 ∨ t = ~~~target6)
    (hb : build basicOps t 7 rows6.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff ⟨6, by decide⟩ ⟨38, by decide⟩ t := by
    rcases ht with rfl | rfl
    · exact sep6.1
    · exact bitDiff_not sep6.1
  have hp : v5 ∈ s := live_has_unique_sep hs hl ⟨6, by decide⟩ ⟨38, by decide⟩ hd sep6.2
  have hm := ops_map_of (selectRows_land (fixBit 5 true)) (selectRows_lor (fixBit 5 true)) (selectRows_neg (fixBit 5 true))
  have hft : r5 t = target5 ∨ r5 t = ~~~target5 := by
    rcases ht with rfl | rfl
    · exact .inl r5_t6
    · exact .inr ((selectRows_neg (fixBit 5 true) target6).trans (congrArg (fun u : W64 => ~~~u) r5_t6))
  have hng : r5 t ≠ 0 ∧ r5 t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact t5_nc
    · exact not_const_of_neg t5_nc
  obtain ⟨_, hsb⟩ := live_transport_save_const hm hl hp (.inr r5_v5) hng
    (fun w hw => hold_rows5 w (List.mem_toFinset.mp (hs hw)))
  obtain ⟨t5, ht5, hb5⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht5' : t5 = target5 ∨ t5 = ~~~target5 := by
    rcases hft with h | h <;> rcases ht5 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact f5_64_false t5 ht5' hb5

theorem binary_lower (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFn x) : 8 ≤ binaryCost C.gates := by
  have hleg : ∀ g ∈ C.gates, legal g := by
    intro g hg
    obtain ⟨hop, hcap⟩ := hfan g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hcap⟩
  by_contra! low
  have init : ∀ u ∈ rows6, holds rows6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (C.gates.foldl step (rows6.map (bit64 k))).getD C.output false = bit64 k target6 := by
    let x (i : Fin 6) : Bool := bit64 k (rows6.getD i.val 0)
    have width : rows6.length = 6 := rfl
    have same : List.ofFn x = rows6.map (bit64 k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < rows6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change C.eval (rows6.map (bit64 k)) = bit64 k target6
    rw [← same, he]
    exact sample6 k
  obtain ⟨t, ht, run⟩ := compile target6 t6_nc.1 t6_nc.2 C.gates C.output hleg rows6 rows6.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rows6.toFinset) :
      build basicOps t b rows6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_seven_t6 t ht (lift (Nat.le_of_lt_succ low) run)

def witnessCircuit : Circuit :=
  ⟨[⟨.and, [0, 2]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [8, 4]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [12, 5]⟩,
    ⟨.or, [9, 13]⟩], 14⟩

theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 witnessCircuit := by
  intro g hg
  simp only [witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witnessCircuit.eval (List.ofFn x) = targetFn x := by
  decide +kernel

end Lower13517

end PEqualNP.Outside.L_meta_13517

theorem PEqualNP.Outside.L_meta_13517 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717568 * 2 ^ 32 + 3969908736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717568 * 2 ^ 32 + 3969908736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, hfan, hsize, he⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hasNot
    have hlt : PEqualNP.Outside.L_meta_13517.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_13517.isBinary)).mpr
        ⟨g, hmem, by simp [PEqualNP.Outside.L_meta_13517.isBinary, hop]⟩
    have h8 := PEqualNP.Outside.L_meta_13517.binary_lower C hfan he
    have hlen : PEqualNP.Outside.L_meta_13517.witnessCircuit.size = 9 := rfl
    have hcs : C.gates.length = C.size := rfl
    exact ⟨PEqualNP.Outside.L_meta_13517.witnessCircuit,
      PEqualNP.Outside.L_meta_13517.witness_mono,
      by omega,
      PEqualNP.Outside.L_meta_13517.witness_eval⟩
  · refine ⟨C, ?_, hsize, he⟩
    intro g hg
    obtain ⟨hop, hcap⟩ := hfan g hg
    have hop' : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    refine ⟨?_, hcap⟩
    rcases hop' with h | h | h
    · simp [h]
    · simp [h]
    · exact (hasNot ⟨g, hg, h⟩).elim
