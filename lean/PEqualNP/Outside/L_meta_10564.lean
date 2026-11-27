import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10564

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

section K4Base

def k4_16_vars : List (BitVec 16) := [0xaaaa#16, 0xcccc#16, 0xf0f0#16, 0xff00#16]
def k4v16 (i : Fin 4) : BitVec 16 := k4_16_vars.getD i.val 0
def k4_tt16 : BitVec 16 := 0xfee8#16

def k4a : WP 30 := 0x2cb2cb2c0000fc0#60
def k4b : WP 30 := 0x55555554003f000#60
def k4c : WP 30 := 0x9a69a6980fc0000#60
def k4d : WP 30 := 0xe38e38e3f000000#60
def k4inputs : List (WP 30) := [k4a, k4b, k4c, k4d]

def k4Base60 : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8,
    3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12, 3, 5, 6, 9, 10, 12]

def permBits4 (p0 p1 p2 p3 : ℕ) (y : ℕ) : Fin 16 :=
  let m := (if y.testBit 0 then 1 <<< p0 else 0) |||
           (if y.testBit 1 then 1 <<< p1 else 0) |||
           (if y.testBit 2 then 1 <<< p2 else 0) |||
           (if y.testBit 3 then 1 <<< p3 else 0)
  ⟨m % 16, Nat.mod_lt _ (by decide)⟩

def k4RowMap (i j : Fin 4) (k : Fin 60) : Fin 16 :=
  let rem := (List.finRange 4).filter (fun q => q != i && q != j)
  permBits4 i.val j.val (rem.getD 0 0).val (rem.getD 1 0).val (k4Base60[k.val]!)

def k4Proj (i j : Fin 4) : BitVec 16 → WP 30 := selectRows (k4RowMap i j)

def checkK4Proj : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).all fun j =>
      if i == j then true else
        (k4Proj i j k4_tt16 == goalP 30) &&
        (k4Proj i j (k4v16 i) == k4a) &&
        (k4Proj i j (k4v16 j) == k4b) &&
        k4_16_vars.all fun w => k4inputs.any fun d => k4Proj i j w == d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem k4Proj_ok : checkK4Proj = true := by decide +kernel

theorem k4_16_cover {w : BitVec 16} (hw : w ∈ k4_16_vars.toFinset) : ∃ i : Fin 4, k4v16 i = w := by
  rw [List.mem_toFinset] at hw
  simp only [k4_16_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

theorem k4_16_not_target : ∀ i : Fin 4, k4v16 i ≠ k4_tt16 ∧ k4v16 i ≠ ~~~k4_tt16 := by decide

theorem k4_nd0 : ((k4a &&& k4b) :: k4inputs).Nodup := by decide
theorem k4_nd1 : ((k4a ||| k4b) :: k4inputs).Nodup := by decide
theorem k4_nd2 : ((k4a &&& ~~~k4b) :: k4inputs).Nodup := by decide

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s0 : searchP 30 5 ((k4a &&& k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s1 : searchP 30 5 ((k4a ||| k4b) :: k4inputs) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4_s2 : searchP 30 5 ((k4a &&& ~~~k4b) :: k4inputs) = false := by decide +kernel

theorem k4_step_aux (i j : Fin 4) (hij : i ≠ j) {t z : BitVec 16}
    (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hz : z = k4v16 i &&& k4v16 j ∨ z = k4v16 i ||| k4v16 j ∨ z = k4v16 i &&& ~~~k4v16 j)
    (rest : Finset (BitVec 16)) (hsub : rest ⊆ k4_16_vars.toFinset)
    (tail : live basicOps t 5 (insert z rest)) : False := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp k4Proj_ok i (List.mem_finRange i)) j (List.mem_finRange j)
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨hg, hi⟩, hj⟩, hall⟩ := h1
  let f := k4Proj i j
  have hi' : f (k4v16 i) = k4a := hi
  have hj' : f (k4v16 j) = k4b := hj
  have hAnd : ∀ u v, f (u &&& v) = f u &&& f v := selectRows_land (k4RowMap i j)
  have hOr : ∀ u v, f (u ||| v) = f u ||| f v := selectRows_lor (k4RowMap i j)
  have hNot : ∀ u, f (~~~u) = ~~~f u := selectRows_neg (k4RowMap i j)
  have hm := ops_map_of hAnd hOr hNot
  have hft : f t = goalP 30 ∨ f t = ~~~goalP 30 := by
    rcases ht with rfl | rfl
    · exact .inl hg
    · exact .inr ((hNot k4_tt16).trans (congrArg (fun u : WP 30 => ~~~u) hg))
  have hrest : ∀ u ∈ rest, holds k4inputs.toFinset (f u) := by
    intro u hu
    have hallu := List.all_eq_true.mp hall u (List.mem_toFinset.mp (hsub hu))
    obtain ⟨d, hd, heq⟩ := List.any_eq_true.mp hallu
    exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, .inl (beq_iff_eq.mp heq)⟩)
  have run_with (w0 : WP 30) (hfw : f z = w0) (hnd : (w0 :: k4inputs).Nodup)
      (hsch : searchP 30 5 (w0 :: k4inputs) = false) : False := by
    apply signed_rejectP (by decide) hnd hsch hft
    apply live_transport hm tail
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact .inr (.inr ⟨w0, List.mem_toFinset.mpr (List.mem_cons_self ..), .inl hfw⟩)
    · exact holds_mono (by intro x hx; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hx))) (hrest u hr)
  rcases hz with rfl | rfl | rfl
  · exact run_with (k4a &&& k4b) (by rw [hAnd, hi', hj']) k4_nd0 k4_s0
  · exact run_with (k4a ||| k4b) (by rw [hOr, hi', hj']) k4_nd1 k4_s1
  · exact run_with (k4a &&& ~~~k4b) (by rw [hAnd, hNot, hi', hj']) k4_nd2 k4_s2

theorem k4_no6_16 (t : BitVec 16) (ht : t = k4_tt16 ∨ t = ~~~k4_tt16)
    (hb : build basicOps t 6 k4_16_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 5) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := k4_16_cover mt
    rcases ht with rfl | rfl
    · exact (k4_16_not_target i).1 hi
    · exact (k4_16_not_target i).2 hi
  · obtain ⟨i, rfl⟩ := k4_16_cover (hs ha)
    obtain ⟨j, rfl⟩ := k4_16_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg k4v16 e)
    have hsub : rest ⊆ k4_16_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact k4_step_aux i j hij ht (.inl rfl) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inl rfl)) rest hsub tail
    · exact k4_step_aux i j hij ht (.inr (.inr rfl)) rest hsub tail
    · exact k4_step_aux j i hij.symm ht (.inr (.inr rfl)) rest hsub tail

end K4Base

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

section ConstrainedBar

abbrev W64 := BitVec 64

def w64_vars : List W64 :=
  [0xaaaaaaaaaaaaaaaa#64, 0xcccccccccccccccc#64, 0xf0f0f0f0f0f0f0f0#64,
   0xff00ff00ff00ff00#64, 0xffff0000ffff0000#64, 0xffffffff00000000#64]

def w64v (i : Fin 6) : W64 := w64_vars.getD i.val 0

def dropVar6 (d : Fin 6) : List W64 :=
  w64_vars.filter (fun w => w != w64v d)

def fixBit6 (i : Fin 6) (k : Fin 64) : Fin 64 :=
  let bit := 1 <<< i.val
  let m := k.val &&& (63 - bit)
  ⟨m % 64, Nat.mod_lt _ (by decide)⟩

def restrict6 (i : Fin 6) : W64 → W64 := selectRows (fixBit6 i)

theorem restrict6_self : ∀ d : Fin 6, restrict6 d (w64v d) = 0 := by decide +kernel

theorem w64_cover {w : W64} (hw : w ∈ w64_vars.toFinset) : ∃ i : Fin 6, w64v i = w := by
  rw [List.mem_toFinset] at hw
  simp only [w64_vars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩

theorem w64_vars_nd : w64_vars.Nodup := by decide +kernel

theorem sb_not {n k : ℕ} {av : Finset (BitVec n)} {z : BitVec n}
    (h : SignedBuild k av (~~~z)) : SignedBuild k av z := by
  rcases h with h0 | h1 | hb | hnb
  · exact .inr (.inl (by simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) h0))
  · exact .inl (by simpa only [BitVec.not_not] using congrArg (fun u : BitVec n => ~~~u) h1)
  · exact .inr (.inr (.inr hb))
  · exact .inr (.inr (.inl (by simpa only [BitVec.not_not] using hnb)))

theorem no7_of_bow64 (mp : Fin 32 → Fin 64) (rs : List W64) (tgt : W64)
    (hproj : selectRows mp tgt = bow_tt32)
    (hhold : ∀ w ∈ rs, holds bow_32_vars.toFinset (selectRows mp w))
    (t : W64) (ht : t = tgt ∨ t = ~~~tgt)
    (hb : build basicOps t 7 rs.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hm := ops_map_of (selectRows_land mp) (selectRows_lor mp) (selectRows_neg mp)
  have hsb := live_transport hm hl (fun w hw => hhold w (List.mem_toFinset.mp (hs hw)))
  have hft : selectRows mp t = bow_tt32 ∨ selectRows mp t = ~~~bow_tt32 := by
    rcases ht with rfl | rfl
    · exact .inl hproj
    · exact .inr ((selectRows_neg mp tgt).trans (congrArg (fun u : BitVec 32 => ~~~u) hproj))
  have hnc : bow_tt32 ≠ 0 ∧ bow_tt32 ≠ ~~~0 := by decide
  have hng : selectRows mp t ≠ 0 ∧ selectRows mp t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact hnc
    · exact not_const_of_neg hnc
  obtain ⟨t32, ht32, hb32⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht32' : t32 = bow_tt32 ∨ t32 = ~~~bow_tt32 := by
    rcases hft with h | h <;> rcases ht32 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact bow_no7_32 t32 ht32' hb32

theorem no7_of_k4p64 (a b : Fin 64) (p : W64) (mp : Fin 16 → Fin 64) (rs : List W64) (tgt : W64)
    (hdiff : bitDiff a b tgt)
    (huniq : ∀ w ∈ rs, bitDiff a b w → w = p)
    (hfp0 : selectRows mp p = 0)
    (hproj : selectRows mp tgt = k4_tt16)
    (hhold : ∀ w ∈ rs, holds k4_16_vars.toFinset (selectRows mp w))
    (t : W64) (ht : t = tgt ∨ t = ~~~tgt)
    (hb : build basicOps t 7 rs.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff a b t := by
    rcases ht with rfl | rfl
    · exact hdiff
    · exact bitDiff_not hdiff
  have hp : p ∈ s := live_has_unique_sep hs hl a b hd huniq
  have hm := ops_map_of (selectRows_land mp) (selectRows_lor mp) (selectRows_neg mp)
  have hft : selectRows mp t = k4_tt16 ∨ selectRows mp t = ~~~k4_tt16 := by
    rcases ht with rfl | rfl
    · exact .inl hproj
    · exact .inr ((selectRows_neg mp tgt).trans (congrArg (fun u : BitVec 16 => ~~~u) hproj))
  have hnc : k4_tt16 ≠ 0 ∧ k4_tt16 ≠ ~~~0 := by decide
  have hng : selectRows mp t ≠ 0 ∧ selectRows mp t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact hnc
    · exact not_const_of_neg hnc
  obtain ⟨_, hsb⟩ := live_transport_save_const hm hl hp (.inl hfp0) hng
    (fun w hw => hhold w (List.mem_toFinset.mp (hs hw)))
  obtain ⟨t16, ht16, hb16⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht16' : t16 = k4_tt16 ∨ t16 = ~~~k4_tt16 := by
    rcases hft with h | h <;> rcases ht16 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact k4_no6_16 t16 ht16' hb16

def liveP (P : W64 → W64 → W64 → Finset W64 → Prop) (goal : W64) : ℕ → Finset W64 → Prop
  | 0, s => s = {goal}
  | k + 1, s => liveP P goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ s ∧
      ∃ rest : Finset W64, s = insert a (insert b rest) ∧ P a b z rest ∧ liveP P goal k (insert z rest)

theorem liveP_of_live {goal : W64} {k : ℕ} {s : Finset W64} (h : live basicOps goal k s) :
    liveP (fun _ _ _ _ => True) goal k s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, he, tail⟩
    · exact .inl (ih skip)
    · exact .inr ⟨a, ha, b, hb, hab, z, hz, hout, r, he, trivial, ih tail⟩

theorem live_of_liveP {P : W64 → W64 → W64 → Finset W64 → Prop} {goal : W64} {k : ℕ} {s : Finset W64}
    (h : liveP P goal k s) : live basicOps goal k s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, he, _, tail⟩
    · exact .inl (ih skip)
    · exact .inr ⟨a, ha, b, hb, hab, z, hz, hout, r, he, ih tail⟩

theorem liveP_mono {P Q : W64 → W64 → W64 → Finset W64 → Prop}
    (hPQ : ∀ a b z r, P a b z r → Q a b z r)
    {goal : W64} {k : ℕ} {s : Finset W64} (h : liveP P goal k s) : liveP Q goal k s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, he, hp, tail⟩
    · exact .inl (ih skip)
    · exact .inr ⟨a, ha, b, hb, hab, z, hz, hout, r, he, hPQ a b z r hp, ih tail⟩

theorem first_liveP {P : W64 → W64 → W64 → Finset W64 → Prop} {goal : W64} {k : ℕ} {s : Finset W64}
    (h : liveP P goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ s ∧
      ∃ rest : Finset W64, s = insert a (insert b rest) ∧ P a b z rest ∧ liveP P goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, hp, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, hp, .inl tail⟩
    · exact .inr step

def pSafe (p a b z : W64) (rest : Finset W64) : Prop :=
  (p = a → p ∉ rest ∧ z ≠ a &&& b ∧ z ≠ a &&& ~~~b) ∧
  (p = b → p ∉ rest ∧ z ≠ a &&& b ∧ z ≠ b &&& ~~~a)

theorem pSafe_swap {p a b z : W64} {r : Finset W64} (h : pSafe p a b z r) : pSafe p b a z r := by
  refine ⟨fun hpb => ?_, fun hpa => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.2 hpb
    exact ⟨h1, by rwa [BitVec.and_comm], h3⟩
  · obtain ⟨h1, h2, h3⟩ := h.1 hpa
    exact ⟨h1, by rwa [BitVec.and_comm], h3⟩

def cSafe (c0 c1 c2 a b z : W64) (rest : Finset W64) : Prop :=
  pSafe c0 a b z rest ∧ pSafe c1 a b z rest ∧ pSafe c2 a b z rest

theorem cSafe_swap {c0 c1 c2 a b z : W64} {r : Finset W64}
    (h : cSafe c0 c1 c2 a b z r) : cSafe c0 c1 c2 b a z r :=
  ⟨pSafe_swap h.1, pSafe_swap h.2.1, pSafe_swap h.2.2⟩

theorem liveP_enforce {P : W64 → W64 → W64 → Finset W64 → Prop}
    {f : W64 → W64}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    (hAnd : ∀ a b, f (a &&& b) = f a &&& f b)
    (hNot : ∀ a, f (~~~a) = ~~~f a)
    {g p : W64} (hfp : f p = 0) (hng : f g ≠ 0 ∧ f g ≠ ~~~0)
    {k : ℕ} {s av : Finset W64}
    (h : liveP P g k s)
    (hav : ∀ w ∈ s, holds av (f w))
    (hno : ∀ n, n + 2 ≤ k → ¬ SignedBuild n av (f g)) :
    liveP (fun a b z r => P a b z r ∧ pSafe p a b z r) g k s := by
  induction k generalizing s av with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, he, hP, tail⟩
    · exact .inl (ih skip hav (fun n hn => hno n (by omega)))
    · have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have hc : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (.inl (h ▸ hfp))) (fun h => .inr (.inl (h ▸ hfp)))
        have hfz : holds av (f z) := mem_ops_const (hav a ha) (hav b hb) hc (hm a b z hz)
        have htail_av : ∀ u ∈ insert z r, holds av (f u) := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact hfz
          · exact inOld u hr
        have hnr : p ∉ r := by
          intro hpr
          obtain ⟨hk, hsb⟩ := live_transport_save_const hm (live_of_liveP tail)
            (Finset.mem_insert_of_mem hpr) (.inl hfp) hng htail_av
          exact hno (k - 1) (by omega) hsb
        have hnz0 : f z ≠ 0 := by
          intro hfz0
          obtain ⟨hk, hsb⟩ := live_transport_save_const hm (live_of_liveP tail)
            (Finset.mem_insert_self z r) (.inl hfz0) hng htail_av
          exact hno (k - 1) (by omega) hsb
        have hsafe : pSafe p a b z r := by
          refine ⟨fun hpa => ⟨hnr, fun e => hnz0 ?_, fun e => hnz0 ?_⟩,
                  fun hpb => ⟨hnr, fun e => hnz0 ?_, fun e => hnz0 ?_⟩⟩
          · rw [e, hAnd, ← hpa, hfp, bv_zero_and]
          · rw [e, hAnd, hNot, ← hpa, hfp, bv_zero_and]
          · rw [e, hAnd, ← hpb, hfp, bv_and_zero]
          · rw [e, hAnd, hNot, ← hpb, hfp, bv_zero_and]
        exact .inr ⟨a, ha, b, hb, hab, z, hz, hout, r, he, ⟨hP, hsafe⟩,
          ih tail htail_av (fun n hn => hno n (by omega))⟩
      · have hpa : p ≠ a := (not_or.mp touches).1
        have hpb : p ≠ b := (not_or.mp touches).2
        have hsafe : pSafe p a b z r := ⟨fun e => (hpa e).elim, fun e => (hpb e).elim⟩
        refine .inr ⟨a, ha, b, hb, hab, z, hz, hout, r, he, ⟨hP, hsafe⟩, ?_⟩
        rcases mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz) with hok | ⟨x, hx, y, hy, hxy, w, hw, hok⟩
        · exact ih tail (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact inOld u hr) (fun n hn => hno n (by omega))
        · exact ih tail (av := insert w av) (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact hok
            · exact holds_insert (inOld u hr)) (fun n hn hsb =>
            hno (n + 1) (by omega) (sb_step hx hy hxy hw hsb))

theorem liveP_map_inj {φ : W64 → W64} (hφ : Function.Injective φ)
    (hAnd : ∀ a b, φ (a &&& b) = φ a &&& φ b)
    (hOr : ∀ a b, φ (a ||| b) = φ a ||| φ b)
    (hNot : ∀ a, φ (~~~a) = ~~~φ a)
    {c0 c1 c2 t : W64} (hc0 : φ c0 = c0) (hc1 : φ c1 = c1) (hc2 : φ c2 = c2) (ht : φ t = t)
    {k : ℕ} {s : Finset W64} (h : liveP (cSafe c0 c1 c2) t k s) :
    liveP (cSafe c0 c1 c2) t k (s.image φ) := by
  have hm := ops_map_of hAnd hOr hNot
  have hps {c a b z : W64} {r : Finset W64} (hc : φ c = c) (hp : pSafe c a b z r) :
      pSafe c (φ a) (φ b) (φ z) (r.image φ) := by
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have hca : c = a := hφ (hc.trans he)
      obtain ⟨hnr, h1, h2⟩ := hp.1 hca
      refine ⟨fun hm' => ?_, fun e => h1 (hφ (e.trans (hAnd a b).symm)),
              fun e => h2 (hφ (e.trans (by rw [hAnd, hNot])))⟩
      rcases Finset.mem_image.mp hm' with ⟨u, hu, hu'⟩
      exact hnr ((hφ (hu'.trans hc.symm)) ▸ hu)
    · have hcb : c = b := hφ (hc.trans he)
      obtain ⟨hnr, h1, h2⟩ := hp.2 hcb
      refine ⟨fun hm' => ?_, fun e => h1 (hφ (e.trans (hAnd a b).symm)),
              fun e => h2 (hφ (e.trans (by rw [hAnd, hNot])))⟩
      rcases Finset.mem_image.mp hm' with ⟨u, hu, hu'⟩
      exact hnr ((hφ (hu'.trans hc.symm)) ▸ hu)
  induction k generalizing s with
  | zero =>
    change s = {t} at h
    change s.image φ = {t}
    rw [h, Finset.image_singleton, ht]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, he, hcs, tail⟩
    · exact .inl (ih skip)
    · refine .inr ⟨φ a, Finset.mem_image_of_mem φ ha, φ b, Finset.mem_image_of_mem φ hb,
        fun e => hab (hφ e), φ z, hm a b z hz, fun hm' => ?_, r.image φ, ?_,
        ⟨hps hc0 hcs.1, hps hc1 hcs.2.1, hps hc2 hcs.2.2⟩, ?_⟩
      · rcases Finset.mem_image.mp hm' with ⟨u, hu, hu'⟩
        exact hout ((hφ hu') ▸ hu)
      · rw [he, Finset.image_insert, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih tail

theorem singles_map {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a, r) => (f a, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, singles, ih, List.map_map]
    congr 1

theorem pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    simp only [List.map_cons, pairs, singles_map, ih, List.map_append, List.map_map]
    congr 1

theorem bv_getLsbD_toNat {n : ℕ} (w : BitVec n) (i : ℕ) : w.getLsbD i = w.toNat.testBit i := rfl

def mask64 : ℕ := 0xffffffffffffffff

theorem toNat_and_not (a b : W64) : (a &&& ~~~b).toNat = a.toNat &&& (mask64 ^^^ b.toNat) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_and, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor]
  by_cases hi : i < 64
  · have hm : mask64.testBit i = true := by
      have : mask64 = 2 ^ 64 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi
    rw [hm, Bool.true_xor]
    congr 1
    rw [← bv_getLsbD_toNat, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and, bv_getLsbD_toNat]
  · have ha : a.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    simp [ha]

def cov1 (d sm : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: r => ((w ^^^ (w >>> d)) &&& sm) ||| cov1 d sm r

def cover6 (d0 d1 d2 d3 d4 d5 : ℕ) (ws : List ℕ) : Bool :=
  (d0 &&& cov1 1 0x7fffffffffffffff ws == d0) &&
  (d1 &&& cov1 2 0x3fffffffffffffff ws == d1) &&
  (d2 &&& cov1 4 0x0fffffffffffffff ws == d2) &&
  (d3 &&& cov1 8 0x00ffffffffffffff ws == d3) &&
  (d4 &&& cov1 16 0x0000ffffffffffff ws == d4) &&
  (d5 &&& cov1 32 0x00000000ffffffff ws == d5)

theorem cov1_mem_bit {d sm i : ℕ} {ns : List ℕ} {w : ℕ} (hw : w ∈ ns)
    (hb : ((w ^^^ (w >>> d)) &&& sm).testBit i = true) : (cov1 d sm ns).testBit i = true := by
  induction ns with
  | nil => simp at hw
  | cons a r ih =>
    simp only [cov1, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | hr
    · exact .inl hb
    · exact .inr (ih hr)

theorem cov1_ok {d sm : ℕ} (hsm : ∀ i, sm.testBit i = true → i + d < 64)
    {tgt t : W64} (ht : t = tgt ∨ t = ~~~tgt) {k : ℕ} {ws : List W64}
    (hl : live basicOps t k ws.toFinset) :
    let dt := (tgt.toNat ^^^ (tgt.toNat >>> d)) &&& sm
    dt &&& cov1 d sm (ws.map BitVec.toNat) = dt := by
  intro dt
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases hdt : dt.testBit i
  · simp
  · simp only [Bool.true_and]
    have h1 : (tgt.toNat ^^^ (tgt.toNat >>> d)).testBit i = true ∧ sm.testBit i = true := by
      simpa [dt, Nat.testBit_and, Bool.and_eq_true] using hdt
    have hid : i + d < 64 := hsm i h1.2
    have hi : i < 64 := by omega
    have hne : tgt.toNat.testBit i ≠ tgt.toNat.testBit (i + d) := by
      have hx := h1.1
      rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm] at hx
      intro heq
      rw [heq, Bool.xor_self] at hx
      exact Bool.false_ne_true hx
    have hbd_tgt : bitDiff ⟨i, hi⟩ ⟨i + d, hid⟩ tgt := by
      unfold bitDiff
      simpa only [← BitVec.getLsbD_eq_getElem hi, ← BitVec.getLsbD_eq_getElem hid,
        bv_getLsbD_toNat] using hne
    have hbd_t : bitDiff ⟨i, hi⟩ ⟨i + d, hid⟩ t := by
      rcases ht with rfl | rfl
      · exact hbd_tgt
      · exact bitDiff_not hbd_tgt
    obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff ⟨i, hi⟩ ⟨i + d, hid⟩) hbd_t
      (ops_bitDiff ⟨i, hi⟩ ⟨i + d, hid⟩) hl
    have hwn : w.toNat.testBit i ≠ w.toNat.testBit (i + d) := by
      unfold bitDiff at hdw
      simpa only [← BitVec.getLsbD_eq_getElem hi, ← BitVec.getLsbD_eq_getElem hid,
        bv_getLsbD_toNat] using hdw
    have hwb : ((w.toNat ^^^ (w.toNat >>> d)) &&& sm).testBit i = true := by
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm, h1.2, Bool.and_true]
      cases ha : w.toNat.testBit i <;> cases hb : w.toNat.testBit (i + d) <;> simp_all
    exact cov1_mem_bit (List.mem_map_of_mem (List.mem_toFinset.mp hw)) hwb

theorem sm_lt (d : ℕ) (hd : d < 64) (sm : ℕ) (hsm : sm = 2 ^ (64 - d) - 1) :
    ∀ i, sm.testBit i = true → i + d < 64 := by
  intro i hi
  rw [hsm, Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hi
  omega

def fld (T w i : ℕ) : ℕ := (T >>> (w * i)) &&& ((1 <<< w) - 1)

def bsrF (H : ℕ → ℕ) (h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      if H ((lo + hi) / 2) ≤ h then bsrF H h f ((lo + hi) / 2) hi
      else bsrF H h f lo ((lo + hi) / 2)
    else lo

def hw (w : ℕ) : ℕ :=
  let x := w % 11400714819323198549 + 317
  ((x * x % 11400714819323198549) * x % 11400714819323198549) + 1

def hz : List ℕ → ℕ
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List ℕ) : ℕ := hz zs % 4294967291

def ori (swNat : ℕ → ℕ) (zs : List ℕ) : List ℕ :=
  let zs' := zs.map swNat
  if hk zs' < hk zs then zs' else zs

def memN (w : ℕ) : List ℕ → Bool
  | [] => false
  | u :: r => u == w || memN w r

theorem memN_iff (w : ℕ) (ns : List ℕ) : memN w ns = true ↔ w ∈ ns := by
  induction ns with
  | nil => simp [memN]
  | cons a r ih =>
    simp only [memN, Bool.or_eq_true, beq_iff_eq, List.mem_cons, ih]
    exact or_congr_left eq_comm

def found (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ) (idx : ℕ → List ℕ → ℕ)
    (s : ℕ) (zs : List ℕ) : Bool :=
  let i := idx s zs
  decide (i < N s) && zs.isPerm (S s i)

def checkNext (d0 d1 d2 d3 d4 d5 : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ) (idx : ℕ → List ℕ → ℕ) (oriF : List ℕ → List ℕ)
    (s : ℕ) (zs : List ℕ) : Bool :=
  !(decide (zs.length ≤ s + 1) && cover6 d0 d1 d2 d3 d4 d5 zs && !(found S N idx s (oriF zs)))

def stepOne (d0 d1 d2 d3 d4 d5 : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ) (idx : ℕ → List ℕ → ℕ) (oriF : List ℕ → List ℕ)
    (s : ℕ) (ca cb : Bool) (a b : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  if w == a || w == b || memN w r then true else
  checkNext d0 d1 d2 d3 d4 d5 S N idx oriF s (w :: r) &&
  (ca || checkNext d0 d1 d2 d3 d4 d5 S N idx oriF s (w :: a :: r)) &&
  (cb || checkNext d0 d1 d2 d3 d4 d5 S N idx oriF s (w :: b :: r)) &&
  (ca || cb || checkNext d0 d1 d2 d3 d4 d5 S N idx oriF s (w :: a :: b :: r))

def stepPair (c0 c1 c2 d0 d1 d2 d3 d4 d5 : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ) (idx : ℕ → List ℕ → ℕ) (oriF : List ℕ → List ℕ)
    (s : ℕ) (a b : ℕ) (r : List ℕ) : Bool :=
  let ca := a == c0 || a == c1 || a == c2
  let cb := b == c0 || b == c1 || b == c2
  stepOne d0 d1 d2 d3 d4 d5 S N idx oriF s ca cb a b r (a ||| b) &&
  (ca || cb || stepOne d0 d1 d2 d3 d4 d5 S N idx oriF s ca cb a b r (a &&& b)) &&
  (ca || stepOne d0 d1 d2 d3 d4 d5 S N idx oriF s ca cb a b r (a &&& (mask64 ^^^ b))) &&
  (cb || stepOne d0 d1 d2 d3 d4 d5 S N idx oriF s ca cb a b r (b &&& (mask64 ^^^ a)))

def bar (c0 c1 c2 d0 d1 d2 d3 d4 d5 : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ) (idx : ℕ → List ℕ → ℕ) (oriF : List ℕ → List ℕ)
    : ℕ → ℕ → Bool
  | 0, _ => false
  | s + 1, i =>
    let ws := S (s + 1) i
    (ws.length != 1) && (pairs ws).all (fun (a, b, r) =>
      stepPair c0 c1 c2 d0 d1 d2 d3 d4 d5 S N idx oriF s a b r)

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f : ℕ → Bool} {n o : ℕ} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f : ℕ → Bool} {a o b : ℕ}
    (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def Live64 (c0 c1 c2 tgt : W64) (s : ℕ) (ns : List ℕ) : Prop :=
  ∃ (ws : List W64) (t : W64), (t = tgt ∨ t = ~~~tgt) ∧ ws.Nodup ∧ ws.map BitVec.toNat = ns ∧
    liveP (cSafe c0 c1 c2) t s ws.toFinset

theorem Live64_perm {c0 c1 c2 tgt : W64} {s : ℕ} {ns ms : List ℕ}
    (hp : ns.Perm ms) (h : Live64 c0 c1 c2 tgt s ns) : Live64 c0 c1 c2 tgt s ms := by
  obtain ⟨ws, t, ht, hnd, hmap, hrun⟩ := h
  let ms' := ms.map (BitVec.ofNat 64)
  have hof : ∀ l : List W64, l.map (BitVec.ofNat 64 ∘ BitVec.toNat) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a r ih => simp [Function.comp, BitVec.ofNat_toNat, ih]
  have hpw : ws.Perm ms' := by
    have h1 : (ns.map (BitVec.ofNat 64)).Perm ms' := hp.map _
    rw [← hmap, List.map_map, hof ws] at h1
    exact h1
  have hmap_aux : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ 64) → (l.map (BitVec.ofNat 64)).map BitVec.toNat = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a r ih =>
      intro hl
      simp only [List.map_cons, BitVec.toNat_ofNat]
      congr 1
      · exact Nat.mod_eq_of_lt (hl a (List.mem_cons_self ..))
      · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  have hlt : ∀ x ∈ ms, x < 2 ^ 64 := by
    intro x hx
    have hx' : x ∈ ws.map BitVec.toNat := hmap.symm ▸ (hp.mem_iff.mpr hx)
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx'
    exact w.isLt
  have hms_map : ms'.map BitVec.toNat = ms := hmap_aux ms hlt
  have hfin : ms'.toFinset = ws.toFinset := by
    ext u; simp [hpw.mem_iff]
  exact ⟨ms', t, ht, hpw.nodup_iff.mp hnd, hms_map, hfin.symm ▸ hrun⟩

theorem Live64_ori {c0 c1 c2 tgt : W64} {swMap : Fin 64 → Fin 64} {swNat : ℕ → ℕ}
    (hinv : ∀ j, swMap (swMap j) = j)
    (hnat : ∀ w : W64, (selectRows swMap w).toNat = swNat w.toNat)
    (htgt : selectRows swMap tgt = tgt)
    (hc0 : selectRows swMap c0 = c0) (hc1 : selectRows swMap c1 = c1) (hc2 : selectRows swMap c2 = c2)
    {s : ℕ} {ns : List ℕ} (h : Live64 c0 c1 c2 tgt s ns) :
    Live64 c0 c1 c2 tgt s (ori swNat ns) := by
  unfold ori
  dsimp only
  split
  · obtain ⟨ws, t, ht, hnd, hmap, hrun⟩ := h
    let sw := selectRows swMap
    have hsw_inv : ∀ w : W64, sw (sw w) = w := by
      intro w; apply BitVec.eq_of_getElem_eq; intro j hj
      let k : Fin 64 := ⟨j, hj⟩
      change (sw (sw w))[k.val] = w[k.val]
      simp [sw, selectRows_bit, hinv k]
    have hinj : Function.Injective sw := fun u v e => by
      have := congrArg sw e; simpa [hsw_inv] using this
    have hft : sw t = t := by
      rcases ht with rfl | rfl
      · exact htgt
      · simp only [sw, selectRows_neg, htgt]
    have hrun' := liveP_map_inj hinj (selectRows_land swMap) (selectRows_lor swMap)
      (selectRows_neg swMap) hc0 hc1 hc2 hft hrun
    have hmap' : (ws.map sw).map BitVec.toNat = ns.map swNat := by
      rw [← hmap, List.map_map, List.map_map]
      apply List.map_congr_left
      intro w _; exact hnat w
    have hfin : (ws.map sw).toFinset = ws.toFinset.image sw := by
      ext u; simp
    refine ⟨ws.map sw, t, ht, hnd.map hinj, hmap', hfin.symm ▸ hrun'⟩
  · exact h

theorem bar_sound {c0 c1 c2 tgt : W64} {d0 d1 d2 d3 d4 d5 : ℕ}
    (hd0 : d0 = (tgt.toNat ^^^ (tgt.toNat >>> 1)) &&& 0x7fffffffffffffff)
    (hd1 : d1 = (tgt.toNat ^^^ (tgt.toNat >>> 2)) &&& 0x3fffffffffffffff)
    (hd2 : d2 = (tgt.toNat ^^^ (tgt.toNat >>> 4)) &&& 0x0fffffffffffffff)
    (hd3 : d3 = (tgt.toNat ^^^ (tgt.toNat >>> 8)) &&& 0x00ffffffffffffff)
    (hd4 : d4 = (tgt.toNat ^^^ (tgt.toNat >>> 16)) &&& 0x0000ffffffffffff)
    (hd5 : d5 = (tgt.toNat ^^^ (tgt.toNat >>> 32)) &&& 0x00000000ffffffff)
    {swMap : Fin 64 → Fin 64} {swNat : ℕ → ℕ}
    (hinv : ∀ j, swMap (swMap j) = j)
    (hnat : ∀ w : W64, (selectRows swMap w).toNat = swNat w.toNat)
    (htgt : selectRows swMap tgt = tgt)
    (hc0 : selectRows swMap c0 = c0) (hc1 : selectRows swMap c1 = c1) (hc2 : selectRows swMap c2 = c2)
    {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ} {idx : ℕ → List ℕ → ℕ} {s i : ℕ}
    (hb : bar c0.toNat c1.toNat c2.toNat d0 d1 d2 d3 d4 d5 S N idx (ori swNat) s i = true)
    (h : Live64 c0 c1 c2 tgt s (S s i)) :
    ∃ q < s, ∃ j < N q, Live64 c0 c1 c2 tgt q (S q j) := by
  cases s with
  | zero => simp [bar] at hb
  | succ s =>
    simp only [bar, Bool.and_eq_true, bne_iff_ne, List.all_eq_true] at hb
    obtain ⟨hlen1, hall⟩ := hb
    obtain ⟨ws, t, ht, hnd, hmap, hrun⟩ := h
    rcases first_liveP hrun with done | ⟨a, ha, b, hb', hab, z, hz, hout, needed, hs, hcs, tail⟩
    · have hsing := singleton_list hnd done
      rw [hsing] at hmap
      simp [← hmap] at hlen1
    · obtain ⟨r, hpair, hperm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb') hab
      have go {a b : W64} (r : List W64)
          (hmem : (a, b, r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed))
          (hop : z ∈ basicOps a b) (hcs' : cSafe c0 c1 c2 a b z needed) :
          ∃ q < s + 1, ∃ j < N q, Live64 c0 c1 c2 tgt q (S q j) := by
        have hm' : (a.toNat, b.toNat, r.map BitVec.toNat) ∈ pairs (S (s + 1) i) := by
          rw [← hmap, pairs_map]
          exact List.mem_map.mpr ⟨(a, b, r), hmem, rfl⟩
        have hsp := hall _ hm'
        let ca := a.toNat == c0.toNat || a.toNat == c1.toNat || a.toNat == c2.toNat
        let cb := b.toNat == c0.toNat || b.toNat == c1.toNat || b.toNat == c2.toNat
        have hca_imp : ca = true → a ∉ needed ∧ z ≠ a &&& b ∧ z ≠ a &&& ~~~b := by
          intro hca
          simp only [ca, Bool.or_eq_true, beq_iff_eq] at hca
          rcases hca with (e | e) | e
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.1.1 e'
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.2.1.1 e'
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.2.2.1 e'
        have hcb_imp : cb = true → b ∉ needed ∧ z ≠ a &&& b ∧ z ≠ b &&& ~~~a := by
          intro hcb
          simp only [cb, Bool.or_eq_true, beq_iff_eq] at hcb
          rcases hcb with (e | e) | e
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.1.2 e'
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.2.1.2 e'
          · have e' := BitVec.eq_of_toNat_eq e.symm; simpa [e'] using hcs'.2.2.2 e'
        have hso : stepOne d0 d1 d2 d3 d4 d5 S N idx (ori swNat) s ca cb a.toNat b.toNat
            (r.map BitVec.toNat) z.toNat = true := by
          simp only [stepPair, Bool.and_eq_true] at hsp
          obtain ⟨⟨⟨h_or, h_and⟩, h_an⟩, h_bn⟩ := hsp
          simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hop
          rcases hop with rfl | rfl | rfl | rfl
          · have hcaf : ca = false := by cases h : ca; rfl; exact ((hca_imp h).2.1 rfl).elim
            have hcbf : cb = false := by cases h : cb; rfl; exact ((hcb_imp h).2.1 rfl).elim
            rw [BitVec.toNat_and]
            simpa [ca, cb, hcaf, hcbf] using h_and
          · rw [BitVec.toNat_or]; exact h_or
          · have hcaf : ca = false := by cases h : ca; rfl; exact ((hca_imp h).2.2 rfl).elim
            rw [toNat_and_not]
            simpa [ca, hcaf] using h_an
          · have hcbf : cb = false := by cases h : cb; rfl; exact ((hcb_imp h).2.2 rfl).elim
            rw [toNat_and_not]
            simpa [cb, hcbf] using h_bn
        have hcond : (z.toNat == a.toNat || z.toNat == b.toNat || memN z.toNat (r.map BitVec.toNat)) = false := by
          cases hc : (z.toNat == a.toNat || z.toNat == b.toNat || memN z.toNat (r.map BitVec.toNat))
          · rfl
          · exfalso
            simp only [Bool.or_eq_true, beq_iff_eq, memN_iff, List.mem_map] at hc
            apply hout
            rw [List.mem_toFinset, perm.mem_iff]
            rcases hc with (e | e) | ⟨u, hu, e⟩
            · rw [BitVec.eq_of_toNat_eq e]; simp
            · rw [BitVec.eq_of_toNat_eq e]; simp
            · rw [BitVec.eq_of_toNat_eq e.symm]; simp [hu]
        simp only [stepOne, hcond, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hso
        obtain ⟨⟨⟨hc0', hc1'⟩, hc2'⟩, hc3'⟩ := hso
        obtain ⟨kept, hk_mem, hnk, hfin⟩ := recover_kept perm hnd hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd' : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have htail' : liveP (cSafe c0 c1 c2) t s (z :: kept).toFinset := by simpa [hfin] using tail
        have hcn : checkNext d0 d1 d2 d3 d4 d5 S N idx (ori swNat) s ((z :: kept).map BitVec.toNat) = true := by
          simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk_mem
          rcases hk_mem with rfl | rfl | rfl | rfl
          · exact hc0'
          · have ha_need : a ∈ needed := hfin ▸ List.mem_toFinset.mpr (List.mem_cons_self ..)
            have hcaf : ca = false := by cases h : ca; rfl; exact ((hca_imp h).1 ha_need).elim
            simpa [hcaf] using hc1'
          · have hb_need : b ∈ needed := hfin ▸ List.mem_toFinset.mpr (List.mem_cons_self ..)
            have hcbf : cb = false := by cases h : cb; rfl; exact ((hcb_imp h).1 hb_need).elim
            simpa [hcbf] using hc2'
          · have ha_need : a ∈ needed := hfin ▸ List.mem_toFinset.mpr (List.mem_cons_self ..)
            have hb_need : b ∈ needed := hfin ▸ List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            have hcaf : ca = false := by cases h : ca; rfl; exact ((hca_imp h).1 ha_need).elim
            have hcbf : cb = false := by cases h : cb; rfl; exact ((hcb_imp h).1 hb_need).elim
            simpa [hcaf, hcbf] using hc3'
        have hlen_zk : ((z :: kept).map BitVec.toNat).length ≤ s + 1 := by
          rw [List.length_map, ← List.toFinset_card_of_nodup hnd']
          exact live_card (live_of_liveP htail')
        have hcov_zk : cover6 d0 d1 d2 d3 d4 d5 ((z :: kept).map BitVec.toNat) = true := by
          have hl' := live_of_liveP htail'
          simp only [cover6, Bool.and_eq_true, beq_iff_eq]
          refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
          · rw [hd0]; exact cov1_ok (sm_lt 1 (by decide) _ (by decide)) ht hl'
          · rw [hd1]; exact cov1_ok (sm_lt 2 (by decide) _ (by decide)) ht hl'
          · rw [hd2]; exact cov1_ok (sm_lt 4 (by decide) _ (by decide)) ht hl'
          · rw [hd3]; exact cov1_ok (sm_lt 8 (by decide) _ (by decide)) ht hl'
          · rw [hd4]; exact cov1_ok (sm_lt 16 (by decide) _ (by decide)) ht hl'
          · rw [hd5]; exact cov1_ok (sm_lt 32 (by decide) _ (by decide)) ht hl'
        simp only [checkNext, hlen_zk, decide_true, hcov_zk, Bool.true_and, Bool.not_not] at hcn
        simp only [found, Bool.and_eq_true, decide_eq_true_eq] at hcn
        obtain ⟨hj, hp_ori⟩ := hcn
        have hlive_zk : Live64 c0 c1 c2 tgt s ((z :: kept).map BitVec.toNat) :=
          ⟨z :: kept, t, ht, hnd', rfl, htail'⟩
        have hlive_ori := Live64_ori hinv hnat htgt hc0 hc1 hc2 hlive_zk
        have hlive_S := Live64_perm (List.isPerm_iff.mp hp_ori) hlive_ori
        exact ⟨s, Nat.lt_succ_self s, idx s (ori swNat ((z :: kept).map BitVec.toNat)), hj, hlive_S⟩
      rcases hpair with direct | swp
      · exact go r direct hperm hs hz hcs
      · exact go r swp (hperm.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (ops_swap a b ▸ hz) (cSafe_swap hcs)

theorem bar_all {c0 c1 c2 tgt : W64} {d0 d1 d2 d3 d4 d5 : ℕ}
    (hd0 : d0 = (tgt.toNat ^^^ (tgt.toNat >>> 1)) &&& 0x7fffffffffffffff)
    (hd1 : d1 = (tgt.toNat ^^^ (tgt.toNat >>> 2)) &&& 0x3fffffffffffffff)
    (hd2 : d2 = (tgt.toNat ^^^ (tgt.toNat >>> 4)) &&& 0x0fffffffffffffff)
    (hd3 : d3 = (tgt.toNat ^^^ (tgt.toNat >>> 8)) &&& 0x00ffffffffffffff)
    (hd4 : d4 = (tgt.toNat ^^^ (tgt.toNat >>> 16)) &&& 0x0000ffffffffffff)
    (hd5 : d5 = (tgt.toNat ^^^ (tgt.toNat >>> 32)) &&& 0x00000000ffffffff)
    {swMap : Fin 64 → Fin 64} {swNat : ℕ → ℕ}
    (hinv : ∀ j, swMap (swMap j) = j)
    (hnat : ∀ w : W64, (selectRows swMap w).toNat = swNat w.toNat)
    (htgt : selectRows swMap tgt = tgt)
    (hc0 : selectRows swMap c0 = c0) (hc1 : selectRows swMap c1 = c1) (hc2 : selectRows swMap c2 = c2)
    {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ} {idx : ℕ → List ℕ → ℕ} {cap : ℕ}
    (hc : ∀ s ≤ cap, ∀ i < N s, bar c0.toNat c1.toNat c2.toNat d0 d1 d2 d3 d4 d5 S N idx (ori swNat) s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ Live64 c0 c1 c2 tgt s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h'⟩ := bar_sound hd0 hd1 hd2 hd3 hd4 hd5 hinv hnat htgt hc0 hc1 hc2 (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h'

theorem enforce_drop6 {P : W64 → W64 → W64 → Finset W64 → Prop} (d : Fin 6) (tgt : W64)
    (hnc : restrict6 d tgt ≠ 0 ∧ restrict6 d tgt ≠ ~~~0)
    (hno7 : ∀ t5, (t5 = restrict6 d tgt ∨ t5 = ~~~restrict6 d tgt) → build basicOps t5 7 (dropVar6 d).toFinset → False)
    {t : W64} (ht : t = tgt ∨ t = ~~~tgt) (h : liveP P t 9 w64_vars.toFinset) :
    liveP (fun a b z r => P a b z r ∧ pSafe (w64v d) a b z r) t 9 w64_vars.toFinset := by
  let f := restrict6 d
  have hAnd := selectRows_land (fixBit6 d)
  have hOr := selectRows_lor (fixBit6 d)
  have hNot := selectRows_neg (fixBit6 d)
  have hm := ops_map_of hAnd hOr hNot
  have hfp : f (w64v d) = 0 := by fin_cases d <;> decide +kernel
  have hhold : ∀ w ∈ w64_vars.toFinset, holds (dropVar6 d).toFinset (f w) := by
    have hall : ∀ d' : Fin 6, w64_vars.all (fun w => restrict6 d' w == 0 || restrict6 d' w == ~~~0 || (dropVar6 d').any (fun u => restrict6 d' w == u)) = true := by
      decide +kernel
    intro w hw
    exact map_holds_list (restrict6 d) w64_vars (dropVar6 d) (hall d) w (List.mem_toFinset.mp hw)
  have hft : f t = f tgt ∨ f t = ~~~f tgt := by
    rcases ht with rfl | rfl
    · exact .inl rfl
    · exact .inr (hNot tgt)
  have hng : f t ≠ 0 ∧ f t ≠ ~~~0 := by
    rcases hft with h' | h' <;> rw [h']
    · exact hnc
    · exact not_const_of_neg hnc
  apply liveP_enforce hm hAnd hNot hfp hng h hhold
  intro n hn hsb
  have hsb7 : SignedBuild 7 (dropVar6 d).toFinset (f t) := sb_le (by omega) hsb
  obtain ⟨t5, ht5, hb5⟩ := unwrap_sb hng.1 hng.2 hsb7
  have ht5' : t5 = f tgt ∨ t5 = ~~~f tgt := by
    rcases hft with h' | h' <;> rcases ht5 with rfl | rfl <;> rw [h']
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact hno7 t5 ht5' hb5

theorem bar_refute64 {c0 c1 c2 tgt : W64} {d0 d1 d2 d3 d4 d5 : ℕ}
    {swMap : Fin 64 → Fin 64} {swNat : ℕ → ℕ}
    {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ} {idx : ℕ → List ℕ → ℕ}
    (hd0 : d0 = (tgt.toNat ^^^ (tgt.toNat >>> 1)) &&& 0x7fffffffffffffff)
    (hd1 : d1 = (tgt.toNat ^^^ (tgt.toNat >>> 2)) &&& 0x3fffffffffffffff)
    (hd2 : d2 = (tgt.toNat ^^^ (tgt.toNat >>> 4)) &&& 0x0fffffffffffffff)
    (hd3 : d3 = (tgt.toNat ^^^ (tgt.toNat >>> 8)) &&& 0x00ffffffffffffff)
    (hd4 : d4 = (tgt.toNat ^^^ (tgt.toNat >>> 16)) &&& 0x0000ffffffffffff)
    (hd5 : d5 = (tgt.toNat ^^^ (tgt.toNat >>> 32)) &&& 0x00000000ffffffff)
    (hinv : ∀ j, swMap (swMap j) = j)
    (hnat : ∀ w : W64, (selectRows swMap w).toNat = swNat w.toNat)
    (htgt : selectRows swMap tgt = tgt)
    (hc0 : selectRows swMap c0 = c0) (hc1 : selectRows swMap c1 = c1) (hc2 : selectRows swMap c2 = c2)
    (hroot : S 9 0 = w64_vars.map BitVec.toNat)
    (hN9 : 0 < N 9)
    (hprop : w64_vars.sublists.all (fun ws => (ws.length == 6) || !(cover6 d0 d1 d2 d3 d4 d5 (ws.map BitVec.toNat))) = true)
    (hchk : ∀ s ≤ 9, ∀ i < N s, bar c0.toNat c1.toNat c2.toNat d0 d1 d2 d3 d4 d5 S N idx (ori swNat) s i = true)
    (he0 : ∀ t, (t = tgt ∨ t = ~~~tgt) → liveP (fun _ _ _ _ => True) t 9 w64_vars.toFinset →
      liveP (fun a b z r => True ∧ pSafe c0 a b z r) t 9 w64_vars.toFinset)
    (he1 : ∀ t, (t = tgt ∨ t = ~~~tgt) → liveP (fun a b z r => True ∧ pSafe c0 a b z r) t 9 w64_vars.toFinset →
      liveP (fun a b z r => (True ∧ pSafe c0 a b z r) ∧ pSafe c1 a b z r) t 9 w64_vars.toFinset)
    (he2 : ∀ t, (t = tgt ∨ t = ~~~tgt) → liveP (fun a b z r => (True ∧ pSafe c0 a b z r) ∧ pSafe c1 a b z r) t 9 w64_vars.toFinset →
      liveP (fun a b z r => ((True ∧ pSafe c0 a b z r) ∧ pSafe c1 a b z r) ∧ pSafe c2 a b z r) t 9 w64_vars.toFinset)
    (t : W64) (ht : t = tgt ∨ t = ~~~tgt) (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := w64_vars.filter (· ∈ s)
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hl' : live basicOps t 9 ws.toFinset := heq.symm ▸ hl
  have hcov : cover6 d0 d1 d2 d3 d4 d5 (ws.map BitVec.toNat) = true := by
    simp only [cover6, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hd0]; exact cov1_ok (sm_lt 1 (by decide) _ (by decide)) ht hl'
    · rw [hd1]; exact cov1_ok (sm_lt 2 (by decide) _ (by decide)) ht hl'
    · rw [hd2]; exact cov1_ok (sm_lt 4 (by decide) _ (by decide)) ht hl'
    · rw [hd3]; exact cov1_ok (sm_lt 8 (by decide) _ (by decide)) ht hl'
    · rw [hd4]; exact cov1_ok (sm_lt 16 (by decide) _ (by decide)) ht hl'
    · rw [hd5]; exact cov1_ok (sm_lt 32 (by decide) _ (by decide)) ht hl'
  have hsub : ws.Sublist w64_vars := List.filter_sublist
  have hlen := List.all_eq_true.mp hprop ws (List.mem_sublists.mpr hsub)
  simp only [hcov, Bool.not_true, Bool.or_false, beq_iff_eq] at hlen
  have hws : ws = w64_vars := hsub.eq_of_length (by simpa [w64_vars] using hlen)
  rw [hws] at hl'
  have hp0 := he0 t ht (liveP_of_live hl')
  have hp1 := he1 t ht hp0
  have hp2 := he2 t ht hp1
  have hcs : liveP (cSafe c0 c1 c2) t 9 w64_vars.toFinset :=
    liveP_mono (fun _ _ _ _ ⟨⟨⟨_, h0⟩, h1⟩, h2⟩ => ⟨h0, h1, h2⟩) hp2
  have hlive : Live64 c0 c1 c2 tgt 9 (S 9 0) :=
    ⟨w64_vars, t, ht, w64_vars_nd, hroot.symm, hcs⟩
  exact bar_all hd0 hd1 hd2 hd3 hd4 hd5 hinv hnat htgt hc0 hc1 hc2 hchk 9 le_rfl 0 hN9 hlive

def swap02Map (j : Fin 64) : Fin 64 :=
  let m := if j.val.testBit 0 != j.val.testBit 2 then j.val ^^^ 5 else j.val
  ⟨m % 64, Nat.mod_lt _ (by decide)⟩

def swap02Nat (w : ℕ) : ℕ :=
  (w &&& 0xa5a5a5a5a5a5a5a5) ||| ((w &&& 0x0a0a0a0a0a0a0a0a) <<< 3) ||| ((w &&& 0x5050505050505050) >>> 3)

theorem swap02_inv : ∀ j : Fin 64, swap02Map (swap02Map j) = j := by decide

theorem swap02_bits : ∀ j : Fin 64,
    ((0xa5a5a5a5a5a5a5a5 : ℕ).testBit j.val = true ∧ (j.val < 3 ∨ (0x0a0a0a0a0a0a0a0a : ℕ).testBit (j.val - 3) = false) ∧ (0x5050505050505050 : ℕ).testBit (j.val + 3) = false ∧ (swap02Map j).val = j.val) ∨
    ((0xa5a5a5a5a5a5a5a5 : ℕ).testBit j.val = false ∧ 3 ≤ j.val ∧ (0x0a0a0a0a0a0a0a0a : ℕ).testBit (j.val - 3) = true ∧ (0x5050505050505050 : ℕ).testBit (j.val + 3) = false ∧ (swap02Map j).val = j.val - 3) ∨
    ((0xa5a5a5a5a5a5a5a5 : ℕ).testBit j.val = false ∧ (j.val < 3 ∨ (0x0a0a0a0a0a0a0a0a : ℕ).testBit (j.val - 3) = false) ∧ (0x5050505050505050 : ℕ).testBit (j.val + 3) = true ∧ (swap02Map j).val = j.val + 3) := by
  decide

theorem swap02_nat (w : W64) : (selectRows swap02Map w).toNat = swap02Nat w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have hlhs : (selectRows swap02Map w).toNat.testBit i = w.toNat.testBit (swap02Map ⟨i, hi⟩).val := by
      rw [← bv_getLsbD_toNat, BitVec.getLsbD_eq_getElem hi]
      change (selectRows swap02Map w)[(⟨i, hi⟩ : Fin 64).val] = _
      rw [selectRows_bit, ← BitVec.getLsbD_eq_getElem (swap02Map ⟨i, hi⟩).isLt, bv_getLsbD_toNat]
    rw [hlhs]
    unfold swap02Nat
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and]
    rcases swap02_bits ⟨i, hi⟩ with ⟨h1, h2, h3, heq⟩ | ⟨h1, hge, h2, h3, heq⟩ | ⟨h1, h2, h3, heq⟩
    · dsimp only at h1 h2 h3 heq
      have ht2 : (decide (3 ≤ i) && (w.toNat.testBit (i - 3) && (0x0a0a0a0a0a0a0a0a : ℕ).testBit (i - 3))) = false := by
        rcases h2 with hlt | hf
        · have : ¬ (3 ≤ i) := by omega
          simp [this]
        · simp [hf]
      have ht3 : (0x5050505050505050 : ℕ).testBit (3 + i) = false := by simpa [Nat.add_comm] using h3
      simp [heq, h1, ht2, ht3]
    · dsimp only at h1 hge h2 h3 heq
      have ht3 : (0x5050505050505050 : ℕ).testBit (3 + i) = false := by simpa [Nat.add_comm] using h3
      simp [heq, h1, hge, h2, ht3]
    · dsimp only at h1 h2 h3 heq
      have ht2 : (decide (3 ≤ i) && (w.toNat.testBit (i - 3) && (0x0a0a0a0a0a0a0a0a : ℕ).testBit (i - 3))) = false := by
        rcases h2 with hlt | hf
        · have : ¬ (3 ≤ i) := by omega
          simp [this]
        · simp [hf]
      rw [Nat.add_comm 3 i]
      simp [heq, h1, ht2, h3]
  · have hlhs : (selectRows swap02Map w).toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (selectRows swap02Map w).isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    have hge : 64 ≤ i := Nat.le_of_not_gt hi
    have hw : w.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) hge))
    have hm2 : (0x0a0a0a0a0a0a0a0a : ℕ).testBit (i - 3) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 0x0a0a0a0a0a0a0a0a < 2 ^ 61) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hm3 : (0x5050505050505050 : ℕ).testBit (3 + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 0x5050505050505050 < 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlhs]
    unfold swap02Nat
    simp [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hw, hm2, hm3]

def swap01Map (j : Fin 64) : Fin 64 :=
  let m := if j.val.testBit 0 != j.val.testBit 1 then j.val ^^^ 3 else j.val
  ⟨m % 64, Nat.mod_lt _ (by decide)⟩

def swap01Nat (w : ℕ) : ℕ :=
  (w &&& 0x9999999999999999) ||| ((w &&& 0x2222222222222222) <<< 1) ||| ((w &&& 0x4444444444444444) >>> 1)

theorem swap01_inv : ∀ j : Fin 64, swap01Map (swap01Map j) = j := by decide

theorem swap01_bits : ∀ j : Fin 64,
    ((0x9999999999999999 : ℕ).testBit j.val = true ∧ (j.val < 1 ∨ (0x2222222222222222 : ℕ).testBit (j.val - 1) = false) ∧ (0x4444444444444444 : ℕ).testBit (j.val + 1) = false ∧ (swap01Map j).val = j.val) ∨
    ((0x9999999999999999 : ℕ).testBit j.val = false ∧ 1 ≤ j.val ∧ (0x2222222222222222 : ℕ).testBit (j.val - 1) = true ∧ (0x4444444444444444 : ℕ).testBit (j.val + 1) = false ∧ (swap01Map j).val = j.val - 1) ∨
    ((0x9999999999999999 : ℕ).testBit j.val = false ∧ (j.val < 1 ∨ (0x2222222222222222 : ℕ).testBit (j.val - 1) = false) ∧ (0x4444444444444444 : ℕ).testBit (j.val + 1) = true ∧ (swap01Map j).val = j.val + 1) := by
  decide

theorem swap01_nat (w : W64) : (selectRows swap01Map w).toNat = swap01Nat w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have hlhs : (selectRows swap01Map w).toNat.testBit i = w.toNat.testBit (swap01Map ⟨i, hi⟩).val := by
      rw [← bv_getLsbD_toNat, BitVec.getLsbD_eq_getElem hi]
      change (selectRows swap01Map w)[(⟨i, hi⟩ : Fin 64).val] = _
      rw [selectRows_bit, ← BitVec.getLsbD_eq_getElem (swap01Map ⟨i, hi⟩).isLt, bv_getLsbD_toNat]
    rw [hlhs]
    unfold swap01Nat
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and]
    rcases swap01_bits ⟨i, hi⟩ with ⟨h1, h2, h3, heq⟩ | ⟨h1, hge, h2, h3, heq⟩ | ⟨h1, h2, h3, heq⟩
    · dsimp only at h1 h2 h3 heq
      have ht2 : (decide (1 ≤ i) && (w.toNat.testBit (i - 1) && (0x2222222222222222 : ℕ).testBit (i - 1))) = false := by
        rcases h2 with hlt | hf
        · have : ¬ (1 ≤ i) := by omega
          simp [this]
        · simp [hf]
      have ht3 : (0x4444444444444444 : ℕ).testBit (1 + i) = false := by simpa [Nat.add_comm] using h3
      simp [heq, h1, ht2, ht3]
    · dsimp only at h1 hge h2 h3 heq
      have ht3 : (0x4444444444444444 : ℕ).testBit (1 + i) = false := by simpa [Nat.add_comm] using h3
      simp [heq, h1, hge, h2, ht3]
    · dsimp only at h1 h2 h3 heq
      have ht2 : (decide (1 ≤ i) && (w.toNat.testBit (i - 1) && (0x2222222222222222 : ℕ).testBit (i - 1))) = false := by
        rcases h2 with hlt | hf
        · have : ¬ (1 ≤ i) := by omega
          simp [this]
        · simp [hf]
      rw [Nat.add_comm 1 i]
      simp [heq, h1, ht2, h3]
  · have hlhs : (selectRows swap01Map w).toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (selectRows swap01Map w).isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    have hge : 64 ≤ i := Nat.le_of_not_gt hi
    have hw : w.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) hge))
    have hm2 : (0x2222222222222222 : ℕ).testBit (i - 1) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 0x2222222222222222 < 2 ^ 63) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hm3 : (0x4444444444444444 : ℕ).testBit (1 + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 0x4444444444444444 < 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlhs]
    unfold swap01Nat
    simp [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hw, hm2, hm3]

end ConstrainedBar


section Drops64

def k4m_0245Arr : Array ℕ := #[0, 1, 4, 5, 16, 17, 20, 21, 32, 33, 36, 37, 48, 49, 52, 53]
def k4m_0245 (k : Fin 16) : Fin 64 := ⟨k4m_0245Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def k4m_1345Arr : Array ℕ := #[0, 2, 8, 10, 16, 18, 24, 26, 32, 34, 40, 42, 48, 50, 56, 58]
def k4m_1345 (k : Fin 16) : Fin 64 := ⟨k4m_1345Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def k4m_0145Arr : Array ℕ := #[0, 1, 2, 3, 16, 17, 18, 19, 32, 33, 34, 35, 48, 49, 50, 51]
def k4m_0145 (k : Fin 16) : Fin 64 := ⟨k4m_0145Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def k4m_0135Arr : Array ℕ := #[0, 1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43]
def k4m_0135 (k : Fin 16) : Fin 64 := ⟨k4m_0135Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def bowm_02135Arr : Array ℕ := #[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 32, 33, 36, 37, 34, 35, 38, 39, 40, 41, 44, 45, 42, 43, 46, 47]
def bowm_02135 (k : Fin 32) : Fin 64 := ⟨bowm_02135Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def bowm_02134Arr : Array ℕ := #[0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 16, 17, 20, 21, 18, 19, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31]
def bowm_02134 (k : Fin 32) : Fin 64 := ⟨bowm_02134Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def bowm_13245Arr : Array ℕ := #[0, 2, 8, 10, 4, 6, 12, 14, 16, 18, 24, 26, 20, 22, 28, 30, 32, 34, 40, 42, 36, 38, 44, 46, 48, 50, 56, 58, 52, 54, 60, 62]
def bowm_13245 (k : Fin 32) : Fin 64 := ⟨bowm_13245Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩
def bowm_04135Arr : Array ℕ := #[0, 1, 16, 17, 2, 3, 18, 19, 8, 9, 24, 25, 10, 11, 26, 27, 32, 33, 48, 49, 34, 35, 50, 51, 40, 41, 56, 57, 42, 43, 58, 59]
def bowm_04135 (k : Fin 32) : Fin 64 := ⟨bowm_04135Arr[k.val]! % 64, Nat.mod_lt _ (by decide)⟩

end Drops64

section G0Bar

def g0_tt64 : W64 := 0xfffffffefefeeca0#64
def g0_dt0 : ℕ := 0x181819af0
def g0_dt1 : ℕ := 0x141415788
def g0_dt2 : ℕ := 0x11111026a
def g0_dt3 : ℕ := 0x10000124c
def g0_dt4 : ℕ := 0x10100125e
def g0_dt5 : ℕ := 0x101135e
def g0_bChunk (i : ℕ) : ℕ := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x00000000fafafafa00000000f0f0f0f000000000ecececec00000000cccccccc00000000aaaaaaaa00000000a0a0a0a0000000005a5a5a5a000000005555000000000000505050500000000030303030000000000f0f0000000000000a0a0a0a0000000000f000f0000000000000f0f0000000000000aaaa0000000000000000 else (if i < 2 then 0x00005a5afafafafa00005a5a00005a5a0000555500000000000055000000ff0000005050f0f0f0f0000050500000f0f000000f0f0000f0f000000f000000ff0000000a0aaaaaaaaa00000a0a0a0aaaaa00000a0a0000aaaa00000a0a00000a0a00000000ffffa0a000000000ffff000000000000ffa0ffa000000000ff00ff00 else 0x050500000505000005000500ff00ff0004040404cccccccc03030303000000000202020222222222020202020202020200ff00ff00ec00ec00ff00ff00cc00cc005f005fffa0ffa0005f005f000000000050005000500050000f000f00000000000a000aaaaaaaaa000a000a00aa00aa00005f5f0000000000005f0000005f00)) else (if i < 4 then 0x0a0a0a0a5a5a5a5a0a0a0a0a0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a0000000005055f5f0000000005055a5a05055a5a05050505fafafafa05050505f0f0f0f005050505aaaaaaaa050505055a5a5a5a0505050550505050050505050a0a0a0a0505050505050000050505050000000005050000ffffa0a005050000ffff0000 else (if i < 5 then 0x0f0f0a0a0f0f00000f0f0000ffffa0a00f0f0000ffff00000f0f00000f0f00000f0a0f0a0f000f000f000f00ffa0ffa00f000f00ff00ff000f000f005f005f000f000f000f000f000e0e0e0e0c0c0c0c0c0c0c0ccccccccc0c0c0c0c4c4c4c4c0c0c0c0c0c0c0c0c0a0a0a0af0f0f0f00a0a0a0aaaaaaaaa0a0a0a0aa0a0a0a0 else 0x1313131300000000121212121212121210101010f0f0f0f0101010103030303010101010101010100f5a0f5a0ff00ff00f0f5f5f000000000f0f5a5a0f0ff0f00f0f0f0ffafafafa0f0f0f0ff0f0f0f00f0f0f0f5a5a5a5a0f0f0f0f505050500f0f0f0f0f0f00000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0a0affff0000))) else (if i < 9 then (if i < 7 then 0x545454544444444450505050fafafafa50505050f0f0f0f050505050aaaaaaaa505050505a5a5a5a505050505050f0f0505050505050505050505050000000004e4e4e4e4c4c4c4c4c4c4c4cecececec4c4c4c4ccccccccc4c4c4c4c4c4c4c4c44444444ecececec44444444cccccccc444444444444444413131313ecececec else (if i < 8 then 0x555555555a5a5a5a55555555555550505555555550505050555555550a0a0a0a555555550000000055555500ffffff00555550505f5f00005555505055555050555550505555000055550000ffff0000555500005f5f0000555500005555000055505550ff00ff00555055505500550055005500ff00ff0054545454cccccccc else 0x5e5e5e5e5e5e5e5e5c5c5c5ccccccccc5c5c5c5c5c5c5c5c5a5a5a5afafafafa5a5a5a5af0f0f0f05a5a5a5aaaaaaaaa5a5a5a5a5a5a5a5a5a5a5a5a505050505a5a5a5a0a0a0a0a5a5a5a5a0000000055555f5f5050f0f055555f5f0000000055555555fafafafa55555555f0f0f0f055555555aaaaaaaa55555555a0a0a0a0)) else (if i < 11 then (if i < 10 then 0x5f5f5f5f5a5a5a5a5f5f5f5f0a0a0a0a5f5f5f5f000000005f5f5f005f5f5f005f5f5050ffff00005f5f50505f5f00005f5f0a0affff00005f5f0a0a5f5f00005f5f0000ffffa0a05f5f0000ffff00005f5f00005f5f00005f505f50ff00ff005f505f505f005f005f005f00ffa0ffa05f005f00ff00ff005f005f005f005f00 else 0xa5a5a5a5f0f0f0f0a5a5a5a5aaaaaaaaa5a5a5a5a0a0a0a0a5a5a5a55a5a5a5aa5a5a5a500000000a2a2a2a2a2a2a2a2a0a0a0a0f0f0f0f0a0a0a0a0aaaaaaaaa0a0a0a0a2a2a2a2a0a0a0a0a0a0a0a0a0a0a0a050505050a0a0a0a0000000008c8c8c8ccccccccc5f5f5f5ff0f0f0f05f5f5f5faaaaaaaa5f5f5f5fa0a0a0a0) else (if i < 12 then 0xafafafaf00000000afa0afa0ff00ff00aeaeaeaeaeaeaeaeacacacacccccccccaafaaafaaafaaafaaaaafafafafafafaaaaaaaaafafafafaaaaaaaaaf0f0f0f0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa0a0aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa0a0a0a0aaaaaaaaa00000000aaa0aaa0aaa0aaa0a8a8a8a8a8a8a8a8 else 0xdcdcdcdccccccccccececececcccccccccdcccdcccfcccfcccceccceccceccceccccccccececececcccccccccceecceecccccccccccccccccccccccc4c4c4c4cbbbbbbbbaaaaaaaab2b2b2b2b2b2b2b2afafffffaaaaaaaaafafafaffafafafaafafafaff0f0f0f0afafafafaaaaaaaaafafafafa0a0a0a0afafafaf50505050)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0xf0a0f0a0f0a0f0a0f0a0f0a0f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeeeececeeeeeeeeececececeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000eeeeececeeeeececececececececececececececccccccccecececec4c4c4c4cecececec00000000e0e0e0e0c0c0c0c0dedededeccccccccdcdcdcdcecececec else (if i < 15 then 0xf0f0fffff0f0f0f0f0f0fafaf0f0fafaf0f0f0f0fafafafaf0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0aaaaaaaaf0f0f0f0a0a0a0a0f0f0f0f05a5a5a5af0f0f0f050505050f0f0f0f00a0a0a0af0f0f0f000000000f0f0a0a0f0f0a0a0f0f0a0a0f0f00000 else 0xfafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafaa0fafafaa0fafafaa0a0fafaa0a0f5f5f5f5fafafafaf5f5f5f5f0f0f0f0f5f5f5f5aaaaaaaaf5f5f5f5a0a0a0a0f5f5f5f500000000f5f5a0a0ffff0000f5f50000ffff0000f500f500ff00ff00f4f4f4f4f4f4f4f4f2f2f2f2f2f2f2f2f0fff0fff0f0f0f0)) else (if i < 17 then 0xfcfcfcfcfcfcccccfcfcfcfcf0f0f0f0fcfcfcfcececececfcfcfcfcccccccccfcfcfcfc00000000fcfcececfcfcccccfafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafaa0a0fafafafaf0f0f0f0fafafafaaaaaaaaafafafafaa0a0a0a0fafafafa5a5a5a5afafafafa50505050fafafafa0a0a0a0a else (if i < 18 then 0xff00ff00ffffff00ff00ff00ffa0ffa0ff00ff00ff55ff00ff00ff00ff22ff22ff00ff00ff00ff00ff00ff005f005f00fefefefefefefefefefefefefefeececfefefefefcfcfcfcfefefefef0f0f0f0fefefefeececececfefefefeccccccccfefeecfefefeecfefefeececfefeececfcfcfcfcfcfcfcfcfcfcfcfcfcfcecec else 0xffa0ffa05f005f00ffa0ffa000000000ff5fff00ff5fff00ff5aff5aff00ff00ff55ff50ff55ff00ff55ff00ff55ff00ff50ff50ffa0ffa0ff50ff50ff00ff00ff10ff10ff30ff30ff10ff10ff10ff10ff0fff0aff0fff00ff0fff00ffffff00ff0fff00ff0fff00ff0aff0aff00ff00ff05ff00ff05ff00ff00ff00ffffffa0))) else (if i < 22 then (if i < 20 then 0xfff0fff000000000fff0ffa0fff0ffa0fff0ffa0fff0ff00ffeeffeeff00ff00ffeeffeeccccccccffecffecff00ff00ffecffecccccccccffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaffa0ffa0ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaffa0ffaaff00ffa0ffa0ffa0ffa0ffa0ffa0ff00ff00 else (if i < 21 then 0xffff0a0affffa0a0ffff0a0affff0000ffff0000ffffa0a0ffff0000ffff0000ffff00005f5f0000fffcfffcff00ff00fffcfffcccccccccfffafffafff0fff0fffafffaffa0ffa0fffafffaff00ff00fffafffaaaaaaaaafffaffa0fffaffa0fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0ffa0ffa0fff0fff0ff00ff00 else 0xfffff0f0f0f00000fffff0f000000000ffffeeeeeeeeccccffffececffff0000ffffececccccccccffffaaaaffffaaaaffffaaaaffffa0a0ffffaaaaffff0000ffffaaaaaaaaaaaaffffaaaa00000000ffffa0a0ffffa0a0ffffa0a0ffff0000ffffa0a05f5f0000ffffa0a000000000ffff5a5affff0000ffff5050ffff0000)) else (if i < 24 then (if i < 23 then 0xffffff00ffffffa0fffffcfcffff0000fffffcfcccccccccfffffafafffffafafffffafafffff0f0fffffafaffffaaaafffffafaffffa0a0fffffafaffff0000fffffafafafafafafffffafafafaaaaafffffafaf0f0f0f0fffffafaaaaaaaaafffff0f0fffff0f0fffff0f0ffffa0a0fffff0f0ffff0000fffff0f0f0f0f0f0 else 0xffffffff00aa00aaffffffff0000f0f0ffffffff00000000fffffffaffffff00fffffff0ffffff00fffffff0ffff0000fffffff0ff00ff00ffffffaaffffffa0ffffffaaffffff00ffffffaaffff0000ffffffaaffaaff00ffffffa0ffffffa0ffffffa0ffffff00ffffffa0ffff0000ffffffa0ff00ff00ffffff50ffffff00) else (if i < 25 then 0xfffffffffafaa0a0fffffffff0f0f0f0fffffffff0f0a0a0fffffffff0f00000ffffffffececececffffffffccccccccffffffffb0b0b0b0ffffffffaaaaaaaaffffffffaaaaa0a0ffffffffaaaa0000ffffffffa0a0a0a0ffffffff5a5a5a5affffffff50505050ffffffff22222222ffffffff0a0aaaaaffffffff0a0a0a0a else 0xffffffffffffaaaaffffffffffffa0a0ffffffffffff0000ffffffffffa0ffa0ffffffffff00ff00fffffffffafafafafffffffffafaf0f0fffffffffafaaaaa)))))
def g0_bW (i : ℕ) : ℕ := fld (g0_bChunk (i / 16)) 64 (i % 16)
def g0_decAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => g0_bW (x &&& 1023) :: g0_decAux n (x >>> 10)
def g0_decSt (x : ℕ) : List ℕ := g0_decAux (x &&& 15) (x >>> 4)
def g0_l2C (_ : ℕ) : ℕ := 0x00000000000017d5d113300000000000017d5d1183
def g0_l2S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l2C (i / 8)) 84 (i % 8))
def g0_l2HC (_ : ℕ) : ℕ := 0x4771601e2d6ec890
def g0_l2H (i : ℕ) : ℕ := fld (g0_l2HC (i / 32)) 32 (i % 32)
def g0_l3C (i : ℕ) : ℕ := (if i < 1 then 0x00000000005551b324394000000000063d6c46cc9400000000005311b32436400000000005891b32483400000000005f574418c9400000000006211b32458400000000005611b32455400000000006496946cc94 else (if i < 2 then 0x00000000006116846cc94000000000053d1b324c4400000000006115146cc9400000000005f51b3243a400000000005a11b3249f400000000005f55546d18400000000006416b46cc9400000000005651b324c44 else 0x00000000005f57444909400000000005311b324ac400000000005f5743f0c94000000000063d74424c94))
def g0_l3S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l3C (i / 8)) 84 (i % 8))
def g0_l3HC (_ : ℕ) : ℕ := 0xfa32bcf8d9fcf7ddd715433ad5be5294c2393dc6be7fd5c2bd48efedb982fe09a68d3784a4a748e2920c87f28d64943572931d4b72539c316b43c9df688855536293506f4d9581dc40dad03333a9b948
def g0_l3H (i : ℕ) : ℕ := fld (g0_l3HC (i / 32)) 32 (i % 32)
def g0_l4C (i : ℕ) : ℕ := (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0x000000017d55546424c95000000018e53145500c95000000017d5d15532489500000001885611b3b0d55000000018e5b91b430b75000000017d5311b408c9500000001895311b430b75000000017d5891b324b95 else (if i < 2 then 0x000000014c500ec324815000000017b584c92dc565000000017d5b11b3ecc95000000014c4c4c92dc565000000016146cc92dc565000000018e5b56146cb75000000018e5311b410cf5000000018e54140324b75 else 0x000000017d5551b324ba500000001855311b408c95000000014c46cf73b4c95000000014c46cc92d057500000001885a11b450ec500000001855311b324895000000014c46cc92bc0b5000000018553131424d65)) else (if i < 4 then 0x000000018853140414c95000000014c46d0c3b081500000001855311b3c4d650000000188561353246d5000000017d5551b464d65000000018e5411b430b75000000018e53128430b7500000001855311b455095 else (if i < 5 then 0x000000018e5a51b410c95000000014c46ce33247d5000000014c46cf83b0c95000000017d5551b424d75000000018e53104324495000000018e5314043041500000001885611b3b0c95000000018553141424c95 else 0x000000014c46cc9308b85000000014c46cc9310b450000000188560ec3247a5000000018e5851b2dc455000000015046cc92dc565000000014c4a0c92dc565000000018e58540410c9500000001885651b3b0c95))) else (if i < 9 then (if i < 7 then 0x000000014c46cce2dc56500000001885311b431055000000014c500c9158415000000018e5851b324165000000018b5711b3b0b75000000014c478ec324815000000014d46cec32481500000001885651b324695 else (if i < 8 then 0x000000018e5851b431045000000017d55509324205000000014c46cc9274895000000014c4d505324815000000014c4c5093589d5000000018c5ad1b324b7500000001885391b3b0ce5000000017d55530424c95 else 0x000000017d531413243f5000000017d5551b444dd500000001885651b424c95000000014c46d0c158415000000017d5511b324895000000014c46d023249d5000000011b3b0c9204765000000018e53146410c95)) else (if i < 11 then (if i < 10 then 0x000000018e5851b33cb7500000001935313b3b0b75000000017d58941424c95000000018e6214c46d145000000018553140424c95000000016146d04324565000000014c4a4ec324815000000017d55521424c95 else 0x00000001885611b3686d5000000017d46d09324975000000014c46cc9294345000000014c46cdb2dc5650000000188561253b0c95000000014c46ccf30cb75000000018846d0532476500000001925851b324b45) else (if i < 12 then 0x00000001855311b3248c5000000017d5311b358895000000015846cec324a15000000017d55520424c9500000001885311b451055000000017d5351b424c95000000014c46d04324a250000000194531393b0b75 else 0x000000014c46cec340815000000018e53130410c95000000017d5e159424c95000000017d53135324895000000017d5311b408d65000000015546cec324815000000017d5311b22464500000001855311b431095)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x00000001855351b424c9500000001885955846cc95000000014c46d05368815000000018e584c92dc495000000018e46cc92dc9a5000000018e5314a430b75000000014c46cec204625000000015546d093243b5 else (if i < 15 then 0x000000017d5551b424d5500000001885a1463b0c95000000018d58d1b324b75000000018e5312833cb7500000001855311b358895000000014c46cc92a437500000001885391b414c9500000001855311e424c95 else 0x00000001885611d3b0c95000000017d5314143509500000001885611b420c9500000001885311b41462500000001835311b400c95000000018e5851b3247e5000000018e5c150324b7500000001885551b414c95)) else (if i < 17 then 0x00000001855311b451095000000017d53131324895000000017d5851b32489500000001885611b3b0d650000000188539223b0c95000000018e5996146cc9500000001885dd583b0da5000000014c488c92dc565 else (if i < 18 then 0x000000014c4d4f83b0c95000000018e5611b410c95000000014c46cec32c815000000017d53131408c95000000017d5d109324135000000015846cc92046d5000000014c4d8c92dc5650000000188561353b0c95 else 0x000000017d531313c4d6500000001885611b434ec5000000017d5451b324895000000014c46cc930c415000000017d55509324905000000018e5851b32441500000001885611f3b0c95000000017d5551b424c95))) else (if i < 22 then (if i < 20 then 0x000000014c46cc9308425000000014c46cd6274895000000018553131324895000000017d5312c324895000000015546d09324845000000014d46d093249d5000000018e5651b410c95000000018e5ed61324415 else (if i < 21 then 0x000000017d5312832489500000001855551b424c95000000018e53147410c95000000014e46cc93080e5000000017d5a11b324895000000017d5891b440b75000000018e53140430b75000000017d5311b368895 else 0x000000014c46cc92b40f5000000015946cec3247c500000001915851b324b750000000188561313b0c95000000018e5311b410d55000000014c46cc90d4045000000014c46ce53247b5000000017d5411b324895)) else (if i < 24 then (if i < 23 then 0x000000017d5351b424d65000000018f5551b424c95000000018e5411b324415000000017d5d109324205000000018e6214c518c95000000018e58530324b75000000017d5311b338895000000014c500c92dc565 else 0x00000001885611b3b0da5000000017d5a51b424c95000000017d5551b3585e5000000016146cc92dc855000000014c46d0c2dc565000000011b424c9084135000000018e46cc91dc155000000017d5311e424d65) else (if i < 25 then 0x00000001885311b458da5000000015546d093249d500000001885dd58414c95000000014c46cf83b0da5000000018e5311b410c95000000017d56d5546d095000000014c46cc92046d5000000014c4c4c9274895 else 0x000000015846cec324c55000000018b5313a3b0b7500000001855a51b424c95000000017d5551b420c95000000014c4c0ec32481500000001885755846cec500000001965f574424c9500000001855311b424cb5))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then 0x000000014d46ced3247b5000000017d53131358895000000017d53531424c9500000001885d9353b0c95000000014c46cc91f0695000000018e53140431045000000014c46cc92fc3f5000000017d5ad1b3f4c95 else (if i < 28 then 0x000000017d46d093244e5000000018d5891b324b75000000014c46ced324805000000016846cec324375000000017d5bd4d424c95000000014c3b0c9204715000000018553146424c95000000017d5651b3246b5 else 0x000000017d5551b424645000000014c46cc91ec6b5000000018e5314033cb75000000014c46cc9310405000000017d5551b424d65000000017d5d1093ecc9500000001835891b324b75000000014c46cc90c8095)) else (if i < 30 then 0x00000001855311b464d65000000016146cc91f404500000001885a11b3b0c95000000018c58d1b324b7500000001885651b3b0db5000000014e46cc92dc565000000017d55535424c95000000017d5553e424c95 else (if i < 31 then 0x000000014c46cc90e00b5000000017d5551b449095000000018e5891b410c9500000001925a11b324a6500000001855551b424d65000000018a5313c3b0b75000000017d5311b3588f5000000018a5b91b3b0b75 else 0x000000014c46d053e0c95000000014c46d09324a05000000018e5ed61324b75000000018e5851b32417500000001885611b414c9500000001925551b3fcc95000000015946d093247b5000000018e5511b410c95))) else (if i < 35 then (if i < 33 then 0x000000017d5691b420c9500000001885613d3b0c95000000017d46d09324315000000014c46cec354815000000014c46ccf2dc565000000018546d09324955000000018553130424c95000000011b324b7064055 else (if i < 34 then 0x0000000188561413b0c95000000015546ced3247b50000000188561223b0c9500000001885ad1b380c950000000188560ec3241c500000001885313b4d4ec500000001815611b3b0c95000000017d55531424c95 else 0x000000018e5311b410d6500000001805391b324695000000018e58540430b75000000014c46cc929839500000001855311b444dd5000000014c488f83b0c95000000017d5d1093241e5000000017d5691b3f8c95)) else (if i < 37 then (if i < 36 then 0x00000001885612a3b0c95000000014c46cec324815000000017d5551b424da5000000018e5411b324b75000000015546d093589d5000000018e5311b3248a5000000018555531424c95000000017d5651b424c95 else 0x00000001855611b424c95000000018e5311b435045000000018853146450ec500000001885d5583b0c95000000018d5851b324b75000000014c46cec2dc6050000000161500c92dc5650000000188565363b0c95) else (if i < 38 then 0x000000017d5351b324895000000016146d0c2dc56500000001885611b3246a5000000017d53131424cb500000001855651b424c95000000015846cc93080e5000000017d55523424c9500000001835311b324875 else 0x000000017d5351b408c95000000018e53131410c9500000001885611b428ec5000000018553147424c950000000188561403b0c95000000018846cec324505000000014c46cc93003d5000000017d5311e324895)))) else (if i < 46 then (if i < 42 then (if i < 40 then 0x000000017d5311b450895000000018e46cc92dc9b500000001885611b430ec5000000016846cec324c2500000001855311b424d5500000001554c5093249d500000001875551b424c95000000017d5311e408c95 else (if i < 41 then 0x000000017d53131464d65000000016246cec32481500000001855311b424c95000000017d5651b420c95000000018e53128410c9500000001885611b3acc95000000017d5d155424c95000000018e5a11b410c95 else 0x000000017d46cc90bc1e500000001855d155424c95000000018e5a11b3240b5000000017d55531424d65000000017d530c92dc5a5000000015446cec324815000000018e58542324b75000000018553109324905)) else (if i < 44 then (if i < 43 then 0x000000018e5851b43cb750000000195621773b0c95000000014c46ce23247f500000001925311b40cc95000000017d5551b408c95000000017d5551b3b0dc5000000017d5551b3241f5000000017d5551b324895 else 0x000000017d5c555424c95000000014c46cec358815000000017d5311b1905e500000001855551b324895000000017d5311b344895000000018e58524324b75000000014c46cc92ac095000000017d5551b3c4d65) else (if i < 45 then 0x000000014c46cff3249f5000000017d5551b32433500000001855311b3585e5000000014e46cf83b0c95000000017d53131444dd5000000015846cc92dc565000000018e5311b410db5000000016146cc930cb75 else 0x000000018e5e561324b7500000001835851b3243d5000000017d5311b408cb500000001885f1683b0c95000000018853135414c95000000017d5311b32c8950000000174555093249d5000000017d5351e424c95))) else (if i < 49 then (if i < 47 then 0x000000018e53141410c95000000017d53146324895000000018e5311b455045000000017d46cc92dc585000000015546cc9274895000000014c46ce43247c500000001855511b424c9500000001885e1593b0c95 else (if i < 48 then 0x000000018e46cc92dc795000000014c3b0c92dc275000000015546cc90c80f5000000017d5311b358c6500000001855311b424d65000000018e53136410c95000000017d5551b3248c5000000017d5d155424d65 else 0x000000017d5552d424c9500000001855311b43509500000001845311b3fcc95000000017d5551b358895000000017d5551e424c95000000018e6216846cc9500000001845311b32486500000001855311b424645)) else (if i < 51 then (if i < 50 then 0x00000001925651b388c95000000017d5551b451095000000018e53141434b75000000017d46cc9254895000000017d53130324895000000017d5311b36c6b5000000014c5010c2dc56500000001885311b414da5 else 0x000000014f46cc92dc56500000001885a51b3b0c95000000017d55531324895000000017d5311e424cb5000000017d5351b424cb5000000017d5651b424db5000000018553131424c95000000017d5551b418c95) else (if i < 52 then 0x000000017d5551b424cb5000000017d5311b354895000000017d55544424c95000000018e5ecc92dc185000000017d531313585e5000000017d59d5546cc9500000001855a11b424c95000000014c46d04324565 else 0x000000017d530c9240895000000017d5311b324895000000017d53131424d65000000017d555093249c5))))))
def g0_l4S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l4C (i / 8)) 84 (i % 8))
def g0_l4HC (i : ℕ) : ℕ := (if i < 7 then (if i < 3 then (if i < 1 then 0x0d2743d40c4d2b3d0c2a36650bf046160b8930010b0c0c540ac8e3000a0a6ca20961771609417e1008f581d206d5d17206bd4c0d062bed1105ab65a504abc7b804a358270482a3a30474afb703f8d6ec03c8527903a6b7180375c1870362393e032435a40317449002fe751a019f83a50186416300b8bc7d002c8e580010eeaf else (if i < 2 then 0x1911ec80190f2c33177dce88166293d715fda92f15d6f37d15d4fa521563c90c1537d6f514d116ea1473120313afc06713a43eed12c9f58012c283d312bd6295125b2e77121d7c5b12063b2311fb765411f08e3a11ad64e61168196a10ee314b10b7d2ff108529fe0ff5a98c0f7786b30ef0df570d8e901d0d861d980d528eb7 else 0x27fe15c027ce30632781006c268fdb4326725f9b26113da524b8d47f23eb7d2023d815b223b895e223b04e65237725002362ba6922e44c8722c8170922a96705227e6af521bb6633212c09eb20e52018207ad38c1ff66e661ff632c11da183df1d90bc381ccec0b41c2304641c1ce5191ace680a1a935f871a442b5c1a2f4f7b)) else (if i < 5 then (if i < 4 then 0x368885a53617748f35e7d15d35cb387b34cfcd273497a845342e1f4d32fa118731de45b931702bb230ca2e4830637d623056f1f62f409c612efe42302ea170e52e99ff382e7e86602e4a63732df988c52d9e131f2d7791412d474cce2cb59c442c8122092c6ee2e32c1600b12af430002ae3c1622a7625da2a039e132824a6a2 else 0x424bb81541a8d36d419336df40cfeb633ff2237a3febe0af3fc7d33b3f131e793f08bea03ed3c5033ecd5bcc3ebeaee13e75bf153e58cd4f3de07ae53dc4dfac3d46ae0e3c5fbf883c3b47273c20064b3c10fcf33beae79c3b9d01fb3ad7221a39c5ef53390a754c38d9f0d937b1227d37297bc636f5bdfc36ced38b368c5869) else (if i < 6 then 0x52bef1b6527890e9526356d851b16c64519cbabb5169752d515639c15043b437503c428a4cf6d2eb4c8109104b9884cf4b97ffbd4b778c514a49755549f2e7a549eb49a6497c90a44939c0a248ed676648e95f9048e921e64806bcc047022c9a46bf0346464da13f45bd543d45a506f743bda9a54349bd8c430e65bf42dbff9c else 0x66f3e43566bf4ae566ae7e9165b73eae65b2e275650473786478cef86450072863d9147063357a3161788773605dd1f66053e8365f3c81ac5e0185c25be728555ba896475b89a1575b01527c5af1c0585ae0e6fb5a24901a594a57365812c28c57c86b9f579f82b657659122552e7daa54cff98354bef42f545b219752e51856))) else (if i < 10 then (if i < 8 then 0x75c53b41755757bd7492f41b73ee0d7e7355af4d72e275b4722a442e71fb360f716d4707716b3d4f7132364a70ab725b7078a6246e73f9116e16b36d6da226f56cddc9556c9774196c10d5ba6bf655a76bd3c92d6bc9e6016b15e42e6ac0af8c6a25524169f9e07968a900216804c90a67efe49167df661a67cf1c4a6726bdd8 else (if i < 9 then 0x834314078341fd9b82fdb3ca8200deb281ca879b81b9869a81b4eb0d818891257efafe687e6b9f0a7e452b1a7e2e09747e235a087df074d77dedde037d8873077bbf334a7b8cb6777b80e8e37ad2cee87a49ea8979e557667987a7f6792c297a78ade51077f3a6db77846eb9775b63a87737551d76f64eec76b86260766e6c6d else 0x984fa1cc96e5f6b896914b35943bd7829332df0d9306cc8490515a2f9040b45d903942b0903743519008e5379006d3ba8ee7781f8e79b35d8d4731858d2b235e8d23b1b18cd380168c2148eb8af14ac78a1152b889fc7414891df826873683ae86a93f05861da0ee860223d985aee3668593d379855769ac8529ad0083f9a628)) else (if i < 12 then (if i < 11 then 0xae3054abad6d0280ad649c49ad60154bacd4ce9aacc833ddab36986daad59d0caabf5348a8d78293a8bf0dbea7f8a870a7ece4b7a67dd346a59982c3a4d753b8a476d54ca474c29ca4404920a3572e5fa1610b8aa06d3a27a049fbb19fca58699fbc51909fa43a629f1979009eb571d19debd14b9c24a7ac9bec01099aea77aa else 0xcafdea9bca9b0708ca3ed7a0c9d78371c9447de5c7db6e60c6a97c67c61705eec3090f35c3028171bfc0ed20bfbcf75abeb1f6c2be8789fcbc44b58cbb7ba0d2ba7a7e94ba6bb686b9b20604b9237312b916edcab69c7505b5c6a413b5993585b45f2706b406414bb3b7f02cb32e026fb101e243b021531eafb59165af7549de) else (if i < 13 then 0xf6be2933f1bc9186ef818346ea12f9afe6967867e5e37afee533f727e4bfa906e4a4a85ee1de310ae03e9d86df11f8d9df0a872cdc6e2907da80c2ced9cbd0c1d94fc277d87155fad8289ab3d5800165d54214d9d43dc552d2fe1542d0febd66d07535e5d067206bd00b2d48cf02589dcd4cd78ccc5327eccbf8a102cb79eb95 else 0xfe540ae2fda32b79fc230620f9f5cbd3))))
def g0_l4H (i : ℕ) : ℕ := fld (g0_l4HC (i / 32)) 32 (i % 32)
def g0_l5C (i : ℕ) : ℕ := (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x000005f54c46cec114416000000017d5311b408c95000006154c46ce4324b76000005f5614d4ec324b76000006215a5611b3b0c96000005f51b3b0c92dc506000005f56146cfe324b76000005f51b324b71d86d6 else (if i < 2 then 0x000005f54c46d0932ca66000005f55846d0a3b0b76000006214c500ec324b26000005f54c46cec3247f6000005f54c525403b0b76000006355546cec324b76000006398853141324b76000005311b324b71440e6 else 0x000006154c46d093240e6000005311b324b71a0566000006394c46cc9158416000005f54c46cec3680b6000006397d53140430b76000006394c46d0c388416000005f52d3b0c92dc956000006214c46d05388c96)) else (if i < 5 then (if i < 4 then 0x000005f55946cec3247460000063961500ec324b76000005f54c46cc92243c6000005851b410ec324516000000016146cc92dc565000005f56846cec3240b6000005f56147cec324b76000005f54c46cc92cc696 else 0x000005f54c46d09324b46000006154c4c4ec358b7600000001855311b324895000005f54c488ec324b76000006157d5551b424c96000005f54c46cec2dc446000005f54e46cec324416000006394c46d043247b6) else (if i < 6 then 0x000006394c46d04324a66000005f55346cec324b76000005f54c46cc91f4526000005f55546cc92dc536000005f55855d1b3b0c96000006396146d04388c96000006154c46d05324b76000005f54c504ec324b76 else 0x000005f54c4c509358b76000005f56246cc92dc0e6000005f55846d0c3b0b76000006214c4d8ec324b46000006195846cec324b76000005f54c46d043240e6000005f5613b0c92dc186000005f54c46cec2dc636))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x000005f55546cec324416000006214e46cec3243d6000005f54c500c92dc566000005311b388c9158416000006214c46d0c3b0b26000005f54c4c4c91a43d6000005311b324b71583d6000005f56146cc91a43d6 else 0x000005f54c4d4ec368b76000005f56146d073b0c96000005551b424c92989d6000005f54c46cc92dc896000005f54c46cec3380b6000005f56146d0f3b0b76000006394c46ce236cb76000005f5555491b424c96) else (if i < 10 then 0x000005f561490ec324b76000005f54c46cc92dc386000006017d5311b324896000005311b3b0c920432600000531353b0c92c8816000005f54c3b0da2dc286000005f55846d053240b6000006214c4d4ec324816 else 0x00000001885611b3b0c95000005f54c46d02324b76000006217d5891b424c96000005f54c46cec368d96000006396146cc92dca46000006396146d0c3b0b76000005f54e46cc92dc6d6000005f54c46cc9224046)) else (if i < 13 then (if i < 12 then 0x00000639855311b424c96000006154c504ec324b76000006154c46d09324b46000005f54c51909324a66000005f5614c4ec324b7600000639885311b324326000005f54c500ec354b76000005f54c46d05324a86 else 0x000006498e5311b410c96000005f54c4d5343b0c96000005f54c46cf1358b76000006396146cc92dc196000000014c46cf83b0c95000006154c4c4ec3243d6000006215846cec324006000005f54c46cc9224696) else (if i < 14 then 0x000005f54d46d093240a6000005311b3b0c91f40f6000005f55546d09324146000005311b3d8c91a4046000005f54c46d0c2dc566000005f54c46cec33c416000005f55546cec35cb7600000001885651b3b0c95 else 0x000006154c46cc92dc896000005f5584d505324b76000006217d5611b3b0da6000005f54c46d02324696000005f54c46cec368bd6000005f55546d09324516000005f54c4d4ec338b76000005f54c479093240a6)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0x000005311b398c92dc546000006214c4d505324b26000005851b3b0c92dc566000005f5773b0c92dc766000005f54c46d0c3b0aa6000006217d531353b0c96000005311b3b0e6324816000005f54c46cda1a43d6 else 0x000006397d5311b410c96000006398853140324b76000006215846cec3243c6000005f54c46cc92046d6000005311b414c91ec0b6000006394c46cc92dc576000006214c46d05324326000005f56146cef324b76) else (if i < 18 then 0x000005311b3e0ec3243c6000005f54c488ec324a86000005f57b3b0c92dc126000006154c46d09388c96000005f54c4e5313b0b76000006397d5891b324b76000005f54c3b0c92dc926000006214c46d143fcec6 else 0x000000014c46cc9274895000005f55546d093249d6000005f54c4c4ec330b76000005f54c46d19358a66000005f55046cc91a43d6000005f5554c0ec324b76000006014c46d093240b6000005f54c4a0c91a43d6)) else (if i < 21 then (if i < 20 then 0x000005f54c4c4ec368b76000005f54c46d09324896000005f54c46cec36c0b6000005f54c4c4ec3582a6000005f54c46ccf2dc6d6000005311b414c92dc9d6000006211b3b0c92c876600000531313b0d62dc9d6 else 0x000005f5553b0c92dc206000005f54c46cce1a43d6000006215846cec324b76000005f573550ec324b76000005f54c46d05410c96000005f579584ec324b76000005f54c4d4ec334b76000005f54c500ec324b76) else (if i < 22 then 0x000005f54c46d09408c96000005f54c46cec32c4160000064d4c4fcec324b76000006214c46d05398c96000005f55446d05324b76000006557d5dcec324b76000005f55546d09358a66000006394c46d0c42cb76 else 0x000005f54c3b0c9124416000005311b3e0ec324b76000005f54c3b0c92dc4a6000005f5614a0ec324b76000005311b3b0c9290816000005311b324b314407600000639885311b430b760000053135414c92dc7b6))) else (if i < 27 then (if i < 25 then (if i < 24 then 0x000005f54c4d1313b0c96000006394c500c92dc0e6000005f54c4f0ec368b76000006394c500c92dc496000006215946cec324b76000005311b3d8ec324a86000005f51b3b0c92dc996000005f55546d093240f6 else 0x000005f54c46cc9224096000005311b324b714438600000531223b0c92dc9d6000006394c46cc9310b76000005f561500ec324416000006215846cec324696000006396146cc92dc126000005f56148cec324b76) else (if i < 26 then 0x000005f54c505043b0c96000006394c4d8e2324b76000006154c500ec324b76000006394c46ccf2dc686000005f51b424c9298956000006154c46d09324896000005f54c46d0c3b0b76000005f54c4c109324a66 else 0x000006396146cc92dc7b6000006214e46cec324b26000006215846cec324076000005311b324b72c8566000005311b3b0da2c8816000006214c46cc92dc566000006214c46cec368816000005f562504ec324b76)) else (if i < 29 then (if i < 28 then 0x000005f54c3b0d62dc296000006394c46d0c2dc0e6000005f51b3b0c92dc976000006214c46d05324a46000005311b324b82dc32600000621585591b3b0c96000005311b324c32dc7b6000005311b324b7274896 else 0x000005f54d46cec324b76000005f5403b0c92dc4d6000006154c46d09324326000005f56146d0c3b0416000006396146cc92dca66000006394c46ce3324b76000005f55846cec324786000000017d5351b424c95) else (if i < 30 then 0x000005f57b584c92dc0e6000005f555480ec324b76000005f54c46d05358b76000000017d5311b358895000006215546cec324b26000005f54c478ec324b76000006214c4d4ec324516000005f56146cc92dc0e6 else 0x000006397d5311b434b76000005f55546d093240a6000005f54d46cc92dc696000006394c46d04324516000005f54c500c92dca96000005f96146cec324b76000006215846d093b0c96000005f54c46d11374a66))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then 0x000006214c46cec2c8626000005f5504a0ec324b76000005f55846cec324816000005311b324c12dc076000005fd4c4d4ec324b76000005f54c470ec368b76000005f55846cec2dc626000006154c46d0c3b0b76 else (if i < 33 then 0x000006217d5a11b3b0c96000006214c46d05368b26000005f54c488ec3240b6000005f57c5a0ec324b76000005f54c4d505324b76000005311b358b71440e6000006217d5311b3b0da6000005f55846d05368b76 else 0x000006214c46cec3243c6000005311b3e4e23240b6000005311b3e0ec324a86000006394c46d04324416000005f51b324b713c1a6000005f5554c509324a66000005391b3b0c92dc7b6000005f51b3d4ec324b76)) else (if i < 36 then (if i < 35 then 0x000005311b3b0c92043460000053135324b71440e6000005f5645851b3b0c96000005f578564ec324b76000005f54c46cd62dc8d6000006214c4d4ec324106000005f56346cea324b76000005311b324b71580e6 else 0x000006154d46cec324b76000005f54c46cc92240b6000006498e5851b324b76000005311b324b71f4566000005f55546d09384c96000005f51b3b0c92dc766000005f51b430ec2dc4d6000006394c46d00324b76) else (if i < 37 then 0x000005f55a5551b424c96000005f54c46d0c2dca96000005311b324b92dc566000005f54c4d8ec3240b6000006394c500e2324b76000006294c46cec360b76000006154c478ec324b76000005f54c4d4ec3680b6 else 0x000006395046cc92dc7b6000006217d5311b3b0ce6000006497d5651b3b0c96000006215846cec324526000006394c4a0c92dc7b6000006396146cea324b76000005f54c4c4ec3583d6000005f55846d09324a66))) else (if i < 42 then (if i < 40 then (if i < 39 then 0x000005311b3d8ec3240b6000006217d5611b414c96000005f54c46d023240b6000005f54c46cf6324896000005f54d46d09324b76000005f54c46d143b0b76000005311b424c9274896000005f54c4c4ec374d66 else 0x000005f54c498ec358b76000005f54c46cc930cb76000005311b414da2dc7b6000005f54c46cc91b4416000005311b3b0c92047b6000006397d5851b324b76000005f55546cec354b7600000531403b0c92dc9d6) else (if i < 41 then 0x000005f554500ec324b76000005f54c46cec2dc456000005311b3b0c9298816000006014c46cc92c8696000005f55046cc92dc0e6000005f577560c92dc6d6000005f54c46cd62dc896000006397d5ed61324b76 else 0x000006394c46cc92dc566000005f54c500c91040e6000006394c46d0c388b76000006154c46d09324a46000005f54c5050d3b0b76000005f5614c8ec324b76000005311b430ec1ec0b6000006214c46d05324346)) else (if i < 44 then (if i < 43 then 0x000005311b424e63245160000000188561353b0c95000005f55546cd62dc5b6000005f54c4c0ec324416000005f54c4c505324b76000006215846cc92c86d6000005f56146d05324b76000000017d53131324895 else 0x000005f54c46cec2dca36000005851b324b71440e6000006215846cec324086000005f54c46d0932c0a6000005f54e46cec324b76000005f54c46d093249f6000005f54c4d4ec324c26000005311b430ec2dc9d6) else (if i < 45 then 0x000006394c46cc91a0416000000017d5551b424c95000005351b3b0c91ec0b6000005f54c46cec324ae6000005f5743b0c92dc136000005f54c46d09354a66000005f54c46d0c410ec60000053131324b71440e6 else 0x000006494c46cec324816000005311b388c92dc566000005f54c46ce63243f6000005311b324b72cc566000006014c46ced324b76000000018e5851b324415000005f55446d0c3b0b76000005311e3b0c91ec0b6)))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then 0x000006215846cec3240b6000005311b3b0c9294816000005f55546d09324006000006214c46cec368516000005f55546cec324176000005f55546cec324b76000006214c518ff3b0c96000005f55846cc92dc1b6 else 0x000006558e5851b324b76000005f57a500ec324b76000005311b3b0c92000b6000005f54c4c4ec324bb6000005f5553b0c92dc906000005f54c46d0c1040e6000005f51b3b0c92dc306000006214c46d09324046) else (if i < 49 then 0x000005311b3e0ec3240b6000006397d5411b324b76000005311e3b0c92dc9d6000005551b3b0c92dc846000006397d53128324b76000005351b3b0c92dc9d6000005611b324b71ec6d6000005f55546cc92dc696 else 0x000006394c46d0c2dc456000006214c46d05324816000005f56246ceb324b76000000018e53140430b75000005f54c46cec324816000005f54c46d09358896000005f56246d09398c96000005f54c500f0324b76)) else (if i < 52 then (if i < 51 then 0x000005f54c46cc92dc8b6000006396157d1b324b76000005311b3e0f63b0c96000006397d53140324416000005f56846d05324b76000005f55546d09324956000005311b414c92c8816000005f54c500ec358b76 else 0x000005f51b3d0ec324b76000005f5614acec324b76000006214c46cec338516000005f54c46cec33cb7600000001855551b424c95000006215846cec3241a6000005f54c4c4c92dc896000005f54c46d09324ad6) else (if i < 53 then 0x000000014c500c92dc565000006155546cc92dc696000005f57b3b0c92dc186000005f54c46d09324a66000006014c46cec324b46000005311b324c32dc516000006396146cc92dc516000006155546cec324b76 else 0x000005311b324c22dc566000005f54e46cec324a860000062d4c46cec34cb76000005f54c46d05338b76000005f55546d09324b76000005f55846cec324416000005f54c424c9298906000005311b3e8ec324816))) else (if i < 58 then (if i < 56 then (if i < 55 then 0x000005f54c46cc9224866000005f5743b0c92dc206000006214c4d5333b0c960000062177560ec324b26000006014c46d05324b76000006397d5311b430416000005f54c488ec368b76000006396146cc92dc416 else 0x000005f54c500c91a43d6000005f54c46d14410ec6000005f57455509324a66000005f54c4d50c3b0b76000005f54c49cec368b76000006396146cec324416000006215846cec3243d6000005311b338b71440e6) else (if i < 57 then 0x000005f54c46d112dc646000005311b324b2148076000005f55846cc92dc6d6000005f54c4d5053240b6000005f54c46cec368a76000005311b3e0ec3243d6000006154c46d093247b6000005f55546d09324696 else 0x000005f56146cc92dc6a6000006154c46d09324a66000005f54c478ec358b76000005f54d46cec358b76000006214c46cc92c86d6000000014c46d0c2dc565000005f54c46cff324896000005f54c46cec32cb76)) else (if i < 60 then (if i < 59 then 0x000005f54c46cec368c26000006155546d09324b760000046cec324b7084136000006394c5010c3b0b7600000001885611b3b0da5000005f54c488ec338b76000005f54c46d043b0456000005f54c3b0c92dc496 else 0x000000018e5311b410c95000005f561500ec324b76000005dd583b0c92dc7b6000000014c46cc92046d5000005f54c4c509324896000005f5584dcec324b76000005f56c5551b424c96000005f54c46ced324b46) else (if i < 61 then 0x000006214c46d033b0c96000005f54c46d0c3b0bd6000005f54c3b0c91c8226000005f54c468ec324b76000005551b3b0c91ec0b6000005f54c4e0ec324b16000005391b3b0c92dc9d6000005311b3b0c91ec6c6 else 0x000006154c46d11358b76000005f5584c0ec324b76000006117d5311b424c96000005f54c3b0c92dc946000005f54c46cec354416000006394c46d04324006000005f54c46ccf2dca96000005f55b5551b3b0b76)))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then 0x000005f54c46d143b00b6000005f54c46cc92c8896000006214c4c0ec324b26000006217d5311b324896000005f55546cc9298896000000015546d093249d5000005311b3b0c9204516000005f54c46d0d424e66 else (if i < 64 then 0x000005f54c46cf2358b76000006154c46cec32cb76000005551b3b0c92dc9d6000005f54c46d0536cb76000006217d531363b0c96000005f54c46cec2dc8e600000530ec324b7098116000005f54d46d093240b6 else 0x000006196146cec324b76000005f55546d043b0c9600000649855311b424c96000005551b324b7274696000006597d5d0ec324b76000005f54c46cec338c26000006214c4d4ec3243c600000531403b0c92dc566)) else (if i < 67 then (if i < 66 then 0x000006394c46cc93087b6000005f54c46d01324046000006494c46ce2324b46000005f54c46cd62985e6000006394c46ce233cb76000005f54c518ec324b76000005f57b5850c3b0b76000005f56146d0c3b0b76 else 0x000005311b324b72046d6000005f56e46d0c3b0b76000005311b3b0cf2dc9d6000005f56346ce1324b76000005f54c46cd62dc5d6000005f51b3b0c92dc986000006157d5311b424c96000005f55546cee324b76) else (if i < 68 then 0x000005f54c46cec324416000005f54c515403b0c96000006214c3b0c92c8716000005f56146ceb324b76000006394c46d04324b76000005f54c46ce4324b36000005311b430ec2dc566000005f5583b0c92dc716 else 0x000005f54c4c0ec354b76000005f577560ec324b76000006394c46d04324046000005311b424c92989d6000005f56d5851b3b0b76000005f54d4c4ec324b76000005311b410ec324bf6000005f550500ec324b76))) else (if i < 73 then (if i < 71 then (if i < 70 then 0x000005f54c46cec350b76000005f55446d09324a66000006394c46d04324696000005f54c46cec2f0b76000006394c46d043b0c96000005551b424c92dc9d6000005311b3b0c92046d6000005f54c46ce5324b76 else 0x00000585403b0c92dc516000005f54c46cec2dc656000005f54c46d053680b6000005f51b3b0c92dc4e6000006215846cec324b26000000017d5551b424d65000005f56f534ec324b76000005311b3b0cb1ec0b6) else (if i < 72 then 0x000006154c46cec324416000005311b3b0cb2dc9d6000006394c46d04324076000005311b3e0ec324b26000005f55046d0c3b0b76000006214c46cf83b0c96000005f55546cec358b76000005311b3b0c9300b76 else 0x000005f54c46d043e4c96000005f5554f8ec324b7600000001885a11b3b0c95000005f54c48905324b760000063961500e2324b76000005f55546cec2dc646000005f55546cd62dc696000005311b3b0c92dc7c6)) else (if i < 75 then (if i < 74 then 0x0000053122324b71440e6000005f54c3b0c92dc736000005f55546cec324b66000005f54c410ec324496000005f54c500c92dc0e6000005f54c5010c3b0416000005f5554d4ec324b76000005f55546cfe324b76 else 0x000005f54c4d505368b76000005611b3b0c92dc7b6000005f55546d093240b6000005f51b3b0c92dc956000006394c46d09410c96000005f54c4c0ec324b76000005f54c4d4ec2dc626000005311b3b0c92040a6) else (if i < 76 then 0x00000001885611b414c95000006155546cec358b76000006214c46cec3683c6000006215846cec3240e6000005f55546d09324216000005851b430ec2dc516000005311b324b82dc516000005f54c46d02390c96 else 0x000000018e5ed61324b75000006396146cc92dc566000005f55846cec354b76000005651b3b0c92dc7b6000005f54c46d09358a66000005311b3fcec324376000006396146d0c388b76000005f54c3ccec324b76)))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then 0x000005f55846cc91b40b6000005f55c46cec358b76000005f54c46d09298646000006396146cc92dc026000005f54c46cec2dc676000005f55546cc91a43d6000005f55546d09358b76000006214c46cec354b26 else 0x000006216846cec324b76000006154c46d093249d6000006151b3b0c92dc956000005311b324c12dc0e6000006154c4c0ec324b76000005311b3b0c92dca06000005f54c4d509324a66000005f55546d093244c6) else (if i < 80 then 0x000005f54c46cda2dc5d6000006214c46cec324376000006214c46cff3b0c96000005f54c519043b0c96000005f54c4d909324b46000000017d55531424c95000005f56846d143b0b76000006217d53135414c96 else 0x000005f54c4c509324906000006154c46d09358a66000005f54c488ec324c26000005f54c46d093dcc96000005f5554c4ec324b76000005f54c3b0c92dc916000006396a5851b324b76000005851b388c92dc566)) else (if i < 83 then (if i < 82 then 0x000006214c4d4c92c86d6000006494c46cff324a66000005f54c4c4ec324236000006154c46d093240f6000005f54c4d4ec328b7600000639885611b3b0c96000005f5554c4c92dc696000005311b3b0c9274416 else 0x000006215846d05324b76000005f54d46ced324b76000005f55446cec324416000005f55846cec324b76000005311b3247b1b40b6000005f54c50105324b76000005f54c46cec368c76000005311b388c92dca26) else (if i < 84 then 0x000000018e5411b324b75000005851b3b0c92fcb76000005f56146cec33cb76000000017d5651b424c9500000639885651b3b0c96000006215946cec324b46000006214c46cec324b26000006217d5311b450ec6 else 0x000000014c46cec324815000006215846d053b0c96000005f55946cec324b76000005f54c518ec3240b6000005f54c46d093240a60000053140324b71440e6000005f54c46cec320b76000005f54c3b0c92dc936))) else (if i < 89 then (if i < 87 then (if i < 86 then 0x000005f54c4c509324a66000005f55546cec368b76000006397b584ec324b76000005f5583b0c92dc7a6000006215846cec388c96000005551b3b0d62dc9d6000005f54c46d0032469600000615554c4ec324b76 else 0x000005f54c46cc92dc6b6000005f5554c509324b76000005f54c46cc9224326000005f54c46d043246d6000005311b3b0c9204006000005f55946cec324046000006394c46d0440cc96000005f55946cc92dc696) else (if i < 88 then 0x000006155846cec324b76000006094c46cec368b76000005f54e46cec338b76000005f54d46ce4324b76000005311b3b4c92987b6000006216846d093b0c96000006394c46d043240b6000005f54c46d0c414b76 else 0x000006154c46d093240a6000005f55548cec324b76000005f54c3b0c92f8b76000005311b430b71440e60000046cec324b727495600000531303b0c92dc9d6000006014e46cec324b76000006157d5311b424d66)) else (if i < 91 then (if i < 90 then 0x000005f5544c0ec324b76000005f54c46cec358416000005311b3247b1a4046000005f54c4c4ec32cb76000005f54c46cec354b76000005f54c4c1043b0c96000006155946cec324b76000005f56146cf9324b76 else 0x000005f55846cec324a86000005f54c3b0c92dc486000005f54c46d09368a66000006394c46ce7324b76000005f55946d09324b76000005311b324b7158406000005311b424d62989d6000006154c4c509324a66) else (if i < 92 then 0x000005f55946d093b0c96000005311b3b0c91f00b6000006217d5311b414da6000005411b3b0c92fcb76000005311b3b0c92dc816000005f54c4d4ec324416000005f56846d09324a66000006394c46d04324686 else 0x000005f54c46d093246b6000006214c46cec3680c6000005f570540ec324b76000005f54c46cb7170466000005f51b3b0c92dc756000005311b3b0c9204046000006395046cec324b76000005f55546d093fcc96))))) else (if i < 108 then (if i < 100 then (if i < 96 then (if i < 94 then 0x000005f54c4d4c92dc6d60000060d6146cec324b76000005311b324a90c80b6000006214c46cec324b46000006394c46d043243d6000005f51b414c92dc766000006154c46cec354b7600000555313b0c92dc9d6 else (if i < 95 then 0x000005311b3b0c92a07b6000005f55546d09324b26000005f54c46cec324b76000006217d5551b424c96000005f55546ced324b76000006214c46cc92d0696000006395846ce2324b76000005f54c46cc9290896 else 0x000006157d53131424c96000006395946ce2324b76000005f51b3b0d62dc956000005f54c4c0ec358b76000005611b3b0c92dc9d6000005f55046cf9324b76000005311b3b0c9204076000005f54c3b0c92dc906)) else (if i < 98 then (if i < 97 then 0x000005f574554ec324b76000006215846cec398c96000005f51b3b0c92dc966000006215846cec324746000005311b424c92740a6000006154c46cd62dc5b6000000017d5d155424c95000006214c488ec3243c6 else 0x000005f574554c92dc69600000001855311b424c950000053131424c92989d6000006217d5611b3246d6000005311b424ec324816000005f55546cec374d66000005f54c4c4ec324416000006215446cec324b26) else (if i < 99 then 0x00000639885311b424c96000005f54e46d05324b76000006154c46d09324006000006214c46d09324b46000005f54c46cec2dc706000006154c46cec324b76000005f54c46d0e358b76000005f55546ce4324b76 else 0x000005f54c46d04324566000005391b324b71440e6000005f568518ec324b76000005311b3b0c92a4816000006154c46cc92dc696000005311b3fcec324c26000005f54c46cc92203d6000006154c3b0c92dc906))) else (if i < 104 then (if i < 102 then (if i < 101 then 0x000005f54c46cec368416000006215846cec3244f6000005a11b3b0c92dc326000005311b3b0d52dc9d60000061574554ec324b76000006394c46cc92e4696000005f5554c4ec358b76000000017d5551b324895 else 0x000005f55446cec354b760000065d885611b3b0c96000006514c4b8ec324b76000005311b324c20f00e6000005f561500c92dc0e6000006394c46d043fcc96000005f57455509324b76000005f54c46d043b0d56) else (if i < 103 then 0x000006154c46d09324046000005f54c46d093580a6000006154c46d09324b76000005f54c4a0ec324416000005f5313b0c92dc956000006217d531463b0c96000006214c46cec358b26000005f55846cec358b76 else 0x000005f571554ec324b76000005f54c4bcec324b7600000639885311b410c96000005f54c4c509358a66000005f54c46cda2dc6d6000005f54c50ce9324b76000005f54c46cc92247b6000005f54c3b0c92dc2e6)) else (if i < 106 then (if i < 105 then 0x000006394c46cff3240b6000005311b3b0c92dc9d6000005f55546cc92dc896000006154c46d09324696000005f56146d0c2dc0e6000006214c46d05324526000005f54c46cc9298896000006396146cc92dc4d6 else 0x000006397d58540324b76000005f54c4c0ec368b76000005f54c46d043b0c96000005f54c46cec358aa6000005f54c46d02324a66000005f55546d0932413600000530ec324b7274906000005f54c4a0c92dc6d6) else (if i < 107 then 0x000005d1553b0c92dc9d60000053140430ec2dc516000005f54d478ec324b76000006394c46cc92dc356000005f54c46cf1358a66000005f54c46cec2a8646000005f56246cc92dc696000005f55446cec324b76 else 0x0000060d4c46cc91a03d6000005f54c46d09324096000006394c5010c388b76000006497d5311b324896000000018853135414c95000006154c46cc9298896000006394c46d043240e6000006214c46cec3247c6)))) else (if i < 116 then (if i < 112 then (if i < 110 then (if i < 109 then 0x000006117d5311b324896000005f54c4e8ec358b76000005311b3b0c9204686000005f54c4c5093240a6000006155446cec324b76000006395046cc92dc686000006214c4c4ec324b26000005f54c46cc91ac3d6 else 0x000005f54c3b0d62dc906000006154c46d09324096000005f54c46cec358b76000005f5605551b324b76000005311b3b4c91ec0a6000006216846cff3b0c96000005f55546d09324896000005f54c3b0da2dc716) else (if i < 111 then 0x000006157d5311b324896000005f55546d09324326000005f54c46cf9324c26000006214c4d505324b76000005f54c46cec2dc646000005f54c500ec32423600000639885311b434b76000005311b3b0c92043d6 else 0x000005f54c46d0d3b0b7600000001855311b424d65000006214c4d5053b0c96000005311b410ec324516000005f54b46cec324b76000005f574554ec358b76000005f54c4c4ec354b76000005f54c46d0940cc96)) else (if i < 114 then (if i < 113 then 0x000006154c46cd62dc696000006394c46d04388c96000006154c46cec358b76000005311b324a6274896000005611b3b0c92dc596000005f54c46d16368b76000005f54c46cc92ac896000005f57756105324b76 else 0x000006215846cec3241d6000006154c46d0940cc96000005511b3b0c92dc9d6000005a11b3b0c92dc7b6000005f555478ec324b76000005f5743b0c92dc956000005f54c46cc91a43d6000006154c46cec2dc646) else (if i < 115 then 0x000005f54c46cec2dc2d6000005f54c46cc92988c6000005f5554b4ec324b76000006154c46d0d3b0b7600000001885311b414da5000005f54c46d09358646000005f56246d043b0c96000006597d5551b424c96 else 0x000005f54c46cec2dc666000005f54d46d09324a66000005f54c46cc9274896000005f55546d09324a46000006154c46cc91a43d6000006154c46d09358b76000005311b324a60c80f6000005f54c4c4ec324b76))) else (if i < 120 then (if i < 118 then (if i < 117 then 0x000005311b3b0d62dc9d6000006154c4c4ec324b76000005f54c46cd6298896000000018553131424c95000006496846cec324b76000005311b324320380b600000639885311b3fcc96000005f54c47909324a66 else 0x000005f5243b0c92dc4d6000005311b3b0b7274646000005f56846cec324b76000005f55946cec36cb76000005f5615010c3b0b76000006214c46d05368b76000005f55546d093242f6000005f54c46cc92240f6) else (if i < 119 then 0x000006394c46d04398c96000005f54c46d14424a66000006215846cec380c96000006214c46d053b0da6000005f54c478ec32cb76000005f54d46cec32cb76000005f55446cec358b76000005f55546d093ecc96 else 0x000005611b324b71440e6000005311b3b0c92dc396000005311b3b0b717c0d6000005311b3249d1a43d6000005311b3b0c92040e6000006154c4c509324b76000005f55846d05324b76000000014c46d04324565)) else (if i < 122 then (if i < 121 then 0x000006214c46cec36cb46000006214c488ec324b2600000531313b0c92dc9d6000005f56b46ce0324b76000005f54c46d023240a6000005f54c4c4c9298896000005f5724c4ec324b76000005f54c46cc92240a6 else 0x000005f56146cec3243e6000005311b410ec324566000006154c46d093fcc96000005f54c478ec324416000005f54d46cec324416000005311b410c92dc566000005f5544c4ec324b76000005f55546d09324a66) else (if i < 123 then 0x000005f5553b0c92dc9c6000006497d5551b424c96000006155546d09324a66000006154c46ced324b76000005f55546cec32cb76000005f54c519143b0b76000005f54c46cd61a43d6000005f55546d093241e6 else 0x000005f54c4c4ec2dc646000005f54c46cc9224006000005f54c4c4ec358b76000000017d5311b324895000000017d53131424d65)))))))
def g0_l5S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l5C (i / 8)) 84 (i % 8))
def g0_l5HC (i : ℕ) : ℕ := (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then 0x051f902905112c63044a54fe04200d1e03c8527903bc38a003aeefbe034347a8033bfc9f03372449032b389402da8e9702cca77102c33e8902aaf93b025bf2400259156102305aba01f7060501be756301b3a3c5016865430133a8390106808a00c0cad200b8bc7d00a961b900a596f300a1e40400a128e00090d42d00391ece else (if i < 2 then 0x09d21fae09b8aae009b1295709a7c06f09a0d91b091c59d6091b878308ebd56308e4eee208cb5e9108b8c0b808b28e4e08a1d81808973db70874fde7082fdfbc079f0deb079e34ed0723992e0717967e06ccc632069cc7d60676205e0656e2c80641794b0638dd5c062bed1106189861060be2f105d9ae2e05d65057052fee3e else 0x0f32fa1d0edfa45b0eca3ade0ebf21cd0ebbdc3f0e5a6fdf0d988daa0d94d54d0d861d980d7aa53a0d4ba9250cfb62e60cd1ffac0cbaff790c6f49f50c5c54f20c44235d0ba79b560b699db40b63c3b50b3256080b2acadf0b0112330aebb70e0aa7a5b60a9e8f110a6e971e0a65143b0a4804500a3b42c80a1d7e700a07cfa5)) else (if i < 5 then (if i < 4 then 0x13c02ad613b641b5139f815f132fdca7130b7ad113059dc712f5fb4f12ede42612edd5ce12ce2952127d3368125f1cad125626ac1220801e12151b6f11f52cb211edbb0511a129c011785ac911716e02115afc6d1143bf7311049c5710ee314b10cb6593107b0dad10635d8f101d04a40ff5a98c0fd5ea1f0f6c2f3e0f498bae else 0x18bdeb0218af2d7d1887525b186384a917dcb91117c801d51797d93a178abed3177dce88175dc468174b256517241c2a1714112416f0deb016debe1616d0e7d0169cd30c15c00ee315b92bda15af81f8158b74c614c25c0f14ba43b9148f3b8f148e3b35145bed0e142d4718141963491412ff371400796e13e7af6213d5907e) else (if i < 6 then 0x1e9152f91e25bbbc1e01a97b1de5f6e41db01a081d5272831d3dbd631ce7553c1cbedd431cb792491cb09f921c706a391c3b5a561c13dd2c1c05c0241be016561bc4be7c1b9740fb1b861c321b79e6fc1b189b571afef8161abef8f91ab58dc21a9c41d71a5b59df1a4806551a31c22a1a1b7ab819f66e1419ef225d197f279d else 0x25e3751b25cf8ed22545ab8624bf460324bb269524a4ce43249e793e243fb745243897ac23ce0461235fb48c2330e104231a25a422ea420a22d386aa22b91f8f2284feb522435b6b2207e93021ed3cc5213ca1c12137ef102128fab320feb53520e1af802044fa161ff33b6b1f4824571f3617561f2c7dc81ee52a051eadaaeb))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x2a9afaac2a98a5fa2a9005522a2190f12a15d41129ca220929b2e24929b1bc4629adc6b329a15d0c296d8493292b99f5292303772894945f28921f972869acdd285a384f281cf0e7281863b027ce306327c9d3b827a5c4f627a2fc87279fe725279e534927511afa273b3f1a26dfea6c26a7b759267f824a265f008d26113da5 else 0x302714dc2fe9019e2fd40f012f729ea72f2e0a592f1ffad22efaee102ec6b3f72ec18bf42e57850c2e2f85cf2da316552cfa65ab2ccd9eea2cc484b02cb410b82c9d81132c7f6ee72c5f08cb2c120c9e2c05d3ad2bfb3de22bf7d9022bdfb4202bcf176c2b9e11512b9c85c42b4ae8952b3e634d2b31856f2aed6d632ab5f8ee) else (if i < 10 then 0x3413c6ca33fcc63533c7e5f233b71b6b33a1f2563396e4a3336b5b5d3359caa7332ee9643313f0ff32fe929d32ee9c1b32d3266232ca43643289d0873275bcca3260d36d325ae31c324f2a1c3243efca321daa1931e9694c31782d7130ef91da30e0a61830ccd68d30bb899330ad2f56309941153030786a302e8689302b9319 else 0x3c652ee63c3d45e53c229b023b667e593b5625f93b3cfd0e3b309f8f3b039dbd3ae213e13ad7221a3abfc1403a3ce0cf3954a899393e957a39242426390a754c38ab0e36384aa6af3843142b3812d5bb37a48a33375e8742374e9b1f374577a136aa64293640a0743611120335d29a0d35c822e634d698e734901920345135cd)) else (if i < 13 then (if i < 12 then 0x40d5659640b4ed9140995dd64002fd2f4002d4b93ff479c53fe5622c3fe454203fcbf3b83fac49eb3faaf1523f8acc233f675fdd3f51f5503f421b343f3dfd8f3f3d69ab3f2796113f0ba4353ea9bf233e80f4753e58cd4f3e54373f3dcb65623dc79f1f3dc4dfac3dc3f3b53db6d1713d9e12973d7931e23d5716a03c6dca58 else 0x47b8bd514770b30146f841dc46c39515464da13f45e68a9245cc5e09459317c7457235644541933f45411a294441a42d4407dcf243cd2f0d43b0e33b43aa2c8243a8ffef436a4441431e93f1430e65bf43003f4d42da326242a6f1e8425bd2dc423b7fac41bf206441806800417f391e417bf7104178f65341686a1b4121269a) else (if i < 14 then 0x4f166a8f4ef85f514ebb15714e79ff354e357fb44e2ffc354e1017fd4dacca614d7d0ce14d259a734d0cd0954c3553534bf58f4f4beb77434b516c7f4b1ab60c4b1543d24afd9c7b4a9655c84a93a8a24a86c8694a2dbd744a10ab3e4a0209b349f2e7a549a9e82d498ee92f495fcbd54914d6b6489a24f54834436347dab6e3 else 0x54cff98354b5ecf8545f27f4545b21975416774b53cfcebe538d4ca553679d0d53186f2b530f89fc52f68ad152e594a552bef1b652bee238526ebc61523eb2e551efbdc451e88d6851d0c9db51c9582e51aecf75519cbabb518f99275117169d510e8b6250fd30cd50c6b71250c250b050a59a4a507fa3f14f796dbb4f6b3fdc)))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then 0x59a7515e599fd830592c985a58d2f6ad58c00e2258a806135860a137585713c5584e30c758427f64583494d957fbe06a57a66820579f82b6579d9e0d57925c8c5761df45574c7c7656e9035056d886e556b75d7c56b60b29566770ef564c09d3562d20375628802b5612bbc055d76704557795bc556a82745530c903552c0331 else 0x629df76f6293340b6258215661f31c856191e2406176e96e6173e9a1617008f3611d0a54610230de609e381f601ce9025f4b0ac15f235d425ed7bab25ed3a9645ec3a0485e325ecb5e08aa9d5dfe43015dddae8d5d7d23095d1a11385c5fc00e5c48d76e5b80113d5b14e5105afbc9a45ad76cda5a85e4e459ee859559ca168b) else (if i < 18 then 0x6b26b9026af1b9a76aa990776a94fd726a87fbcf6a4e5e78697cfa3569564ec369534bb8693c943268aa204c6880f9d96825717e67efe491673ff819673cb70966d8822b668b0861667659b365d9364664a7286964616b736432507d6426f27463d61c7e63bd74eb638922f7633a6edf6322a69363059d1762f5c83f62de28b9 else 0x7355af4d7205bbc871d6553171a8a1327102baf570fd1ece70f500ed7092be737077376b704f461f700ab5cc6ffaa2fd6fdbfb826fbcb6716f7420c66f1e7afb6f014bd56eb987996ead90146e6cced26dca7c516d0a7f986ca2f9d26c8e370c6c51d62b6c4dc5306c10d5ba6be82a166bd006706bb267e56b4c2b7f6b469fa9)) else (if i < 21 then (if i < 20 then 0x7a58d9fa79f5757379e2c53c79ab3ef6794cee28792c297a78e4c18b78d52f7c78d2be7778b25dbc78836490786a7d977845780476e46d6176b0d057768c73de764aa47576033c9275c03e6a75a908897541bc9d74e9384274b1cd4e74af11867492f41b73e1d39173c6f92373b759d2738ad0ba73892e307379d98673730d3a else 0x8200deb281fe71ad81fa5a70818891258107b263809ef3248095ab7980610f938017980a7ff94a247fc933fb7fad93167f5c91797f4eb9527f23ef677f20c1857effd3f77e7d61dd7e50fe307e3bee907e0687a07d9f9eb07c8870687c789a797c6ab9977c13924d7bda66587b8d9fbd7ab93f1e7ab2d6917a9d42537a5e5b6c) else (if i < 22 then 0x883654a98829ab3f87fc6fd087a126598727a2a0871cd7b98715cfa386f88c68861a162d85ee123785c4f19385650cfa85280f41850ce7808506c22784e4d81384c715a3848ac96e846a2301842db0a1841c268b83579d3f834febff834200b18341fd9b832cde338315a6c98301106c826d34cd8267db11822addf0820662fd else 0x915fc00b90ca8d0c90bcff189026ad6e9003e6588feefbf18f7a49fc8f7590ae8f5509988ec37ad08e989ff38e4d34a38e4a79e28e299ba68d6573c48d4fd7368ce7f2fd8cc8fc548c85f21b8c7e606b8c37331e8bead25e8b9e685c8b5a7f998af5f6608aab0dca8a4709968a11ae2789d546078997597b895e567d8902bf97))) else (if i < 27 then (if i < 25 then (if i < 24 then 0x9a3f04809a2fc0419a25a7e299e7bb56998836209982bb5a991b948f98ceac7a9866f69c98643392981dcd11981d949897acec2b97764ab696c7ac8e969c88349687f58f967ad3c495a91ab695a7196c9559f3e894ef8c8794bff4b19493e22894642f6f9428583d93aa0ec8931680a792646be791fb270f91d80d9891b14d55 else 0xa47deab8a43ed96da397a130a2bd085ba275bfeea20dc704a1bcc37fa1576e0da144abc4a125b7aea0ff8aa6a0dbec85a0c41f93a0a68ea4a02e1c259f54c8609f4847f79f1979009ea1b8ad9e5d83419e4dff9a9e429b369e05413d9dc0e8059d7916ad9d3a1b479cd2b85f9c51efb09c47d7d79c145a949bec01099a984c5e) else (if i < 26 then 0xafbd6a4faf6b8c0eaf28ae6faef21a88ae6fc52bae537615ae032034adf8289cadd2a274ac9839b2abdb61bdabb9cf37ab61eccbab13ef38aac0b05ea9d897fba9626faaa91d1534a91afa76a913d78fa90141aca8bc672ca8ade9c6a8654f0ba7d6cb8da7105f90a69bcfa0a611d628a601d840a5b0517ea4e44403a4d753b8 else 0xb9da8856b9cf3b6fb9a46eb2b99e9789b916edcab8fb0174b8f27d1db8dd6bd8b753b9b7b727b3fab7264b29b70b6247b6708935b660bfc4b64f3b22b549099db4f83f2ab4f58a8fb44be8feb42b5214b387d0e0b3497d45b2a94f84b252c8d5b21238a2b1f8701bb1993c75b0bfd930b0ab14c2b083bb7ab0723fe1afd60fc3)) else (if i < 29 then (if i < 28 then 0xc96b747cc9447de5c8ee1cb0c8e947bec7ee3228c7a41b92c79e7cecc6c78011c5ea2ebec5e6a5c1c5e58835c5d8d687c47e3fa6c44b0ee9c44839edc3cbf800c2f9b15fc257fd02c248d1f6c04422dec0350b98bffd4363bfe355b7bf19170cbdfb775cbde89efcbde794c6bdd47e9bbdd1cb30bca675ddbbfcf547b9e227d5 else 0xd8e2cc37d8e05208d73c1035d6be3c62d63dd196d60666a2d5d9c3c9d38516dfd37e4c5ad2446890d2024b89d1f4360fd0febd66d0f55040d0ae25c5d082d788cfaa2c9ccf5041a4cf23aca7ced9fe41ced9ed30ce21c45acdb51003cd070139cca0c4d3cb660276cad19389ca4ce2ebca3b81a6c9efe11dc9d4cc28c98d06a0) else (if i < 30 then 0xe896468ae7f80cafe7d4054be78fb30de7648135e742ab8be57d24cbe4bfa906e483f732e40c4223e1ec05d3e0d5ec4ce09f0e7de0979cd0df740e82df17e66cdedf515ade58e2b0de384b38ddfb3eabddc11a95ddc0a623dd80fa51dcc5a109dc237500dc0dd872da9d44c6da80c2ceda757596da509390da25176ed8e7c3b5 else 0xffe58974ff893d1ffdb01bc4fda32b79fc230620fb82e177f9c04bb7f91cb5a2f901857ff84b3ed7f8299957f7e014e8f5265e55f4ba9e99f496d7ecf305e6a9f225ef4ff21e7da2f18191c3f0b0536bf093f40ff08cb14eee9076c4ed5fb9e9ecfa4466ec9539d8ebd989afeb5acd9de97fa8d9)))))
def g0_l5H (i : ℕ) : ℕ := fld (g0_l5HC (i / 32)) 32 (i % 32)
def g0_l6C (i : ℕ) : ℕ := (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x000005311b324b71440e6001885311b3b0c91443c70017d5311b3b0c91f4047001885f54c46d093b0c970014c46cff3b0c92dc5170017d5311b3b0da348b770017d5551b424ec324a670017d5311b3b0c92e4b77 else 0x000005f54c46cec3680b60017d5311b3b0d62dc3d70017d5311b3b0e2354b770014c46cec39cc92dc5170017d5311b3b0c92c8a870017d5311b324b72906d70017d5311b444d62dca670014c46cc92dc561440e7) else (if i < 3 then 0x001855311b3b0c92dc0e70017d5311b414c92dc3c70018e5311b424c92dc7b70017d5311b3b0cb2dca670017d5311b3b0dd358b77000005f54c46cc92cc6960017d5311b3d8c91a43d70014c46cc92dc51038007 else (if i < 4 then 0x000005f54c46d09324b46000005f54c488ec324b760017d531353b0c92dc3d70017d531313b0c92dc0b70018e6214c46cec324b470017d5851b3b0c92dc0b7001925f54c46d09324a670017d5311b3b0c92e4697 else 0x0017d561353b0c92dcb27001855f55546cec324b770017d5311b424c92dc0e7001885311b3b0c92dc5170017d5311b390c92dc0470017d5311b3b0c92fcb77000005f54c504ec324b760017d5311b3b0da2dc0c7))) else (if i < 7 then (if i < 6 then 0x001885311b3b0c91ec0b7000005f54c46d043240e60017d5311b324691a03d70017d5311b410ff3b0c970018e5f54c46cec324b770017d5311b3b0e4324b770017d5311b3b0c92dcb470014c46cc92dc510f00e7 else 0x0017d5311b3b0c92d00470017d5311b324b72d06970018e6214c46ce2324b770017d5311b424c90f40b70017d5311b3b0c92e40770017d5311b368b72c86d70014c46cec324b21ec0b70017d531303b0c92dca47) else (if i < 8 then 0x0017d5851b3b0c92dc4c70015546cec324b72989d7001835311b3b0c92dc7b70017d5555246cec324b77000005f54c4d4ec368b76000005f54c46cc92dc8960018e5f54c46cc92dc6970018e5311b388c92dcb27 else (if i < 9 then 0x0017d5311b414ec324b7700000001885611b3b0c950017d5311b424ec3247d70017d531223b0c92dc3c70017d5311b414c92dc0470014c46cec324b72c89d7001885311b3b0c92dc9d70017d5311b3b0da2dc617 else 0x0017d5851b3b0c92dc4d7000005f54c46cc92246960017d5311b410ec324b270017d5851b3b0c92dc777001885f56246cec324b770017d5311b3b0e2324b77001885f54c46d043b0c970017d5851b3b0c92dc687)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x0017d5311b424c9038077001855311b3b0c92dcb47001885311b3b0e6324b270017d5311b324b72cc6970017d5511b3b0c92dcb270017d5391b3b0c92dc5170017d5311b3b0da2dc0b70017d5311b414c92dc697 else 0x001885311b3b0c92dc0f7001855f54c46d09324a670017d5311b3fcec3240b7001885f54c46cc92c86d70017d5311b324b71480e70014c46cec324b71440e70018e6154c46cec324b770014c4d4ec324b72c87b7) else (if i < 13 then 0x0017d531353b0de324b770017d5311b3b0c92cc697000006217d531353b0c960017d5551b3b0c92dc1470017d5311b424c92dcb470017d5311b3b0c91ec4170014c46cc92dc691440e70014c46cec3247b0380b7 else (if i < 14 then 0x0017d5851b3b0e23244170014c46cf63b0c92dc3c70017d531313b0c92dc3d70017d5851b3b0c92dc3d70017d5551b3b0c92dc5170017d5311e3b0c92dc0a70017d5351b3b0c92dc0a70018e5311b388c92dc0e7 else 0x0017d5311b424ec324b47001885f54c46d093245270017d5311b3b0c92984170017d5311b410c92dc0e70014c46cf9324b71ec5170014c46cec324b92dc517000006397d5311b410c960017d5311b3b0c93083c7))) else (if i < 18 then (if i < 16 then 0x001855311b3b0e2324b770017d5311b3b0c92dc9e70014c46cc92dc510380770018a5f54c46cec368b770014c46ced3b0c91ec0b70017d5311b424ec390c970014c46cec324b72740e70018e5311b388c92dc7d7 else (if i < 17 then 0x0017d5311b42505324b770017d5551b3b0c92dc9d7000005f54c46d093248960017d5611b3b0c92dca470017d5311b410ec3240e7001805311b3b0c92dc0b70018e5f54c46d093246970017d5311b3b0c92c80b7 else 0x0017d5311b3b0c9308b77000006215846cec324b760017d5311b3b0c92dc8970017d5311b430ec2dc2b70017d5311b324b71ec6d7001885311b3b0c92c8a47000005f54c500ec324b760017d53140430ec388b77)) else (if i < 19 then 0x0017d531353b0c92dcb570017d5411b3b0c92dc6870014c46d09324b71440e70017d5311b324b72246970017d531403b0c92dc0070017d5311b3b0d62dc0d7001835f54c46cec324b77001885f54c46cf63b0c97 else (if i < 20 then 0x0018e5f54c46cc92dc5270017d5311b3b0d62dcb270017d531313b0c92dc117001885f54c46cec358b770018e5311b3b0c92e0b770017d46cec388c92dc4d70014c46cf63b0c92dc0470017d5551b3b0d62dca67 else 0x0017d5311b3b0c92246970017d5311b3b0dd368b770018e5311b3b0c91ec0b70014c46cec390c91ec0b70017d5311b3b0da2dc3d70017d5311b424c92985170014c46cc92dca81440e70017d531403b0c92dc247))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then 0x0017d531403b0c92dc0370018e5f54c46d04324b77000005f54c46d0c3b0b760017d5311b3b0c92dc327001885311b424ec3240f70017d531353b0c92dcb27001885f54c4d4ec324b770017d5611b3b0da2dcb27 else 0x0017d5855e46cec324b77001885f54c46d0d3b0b770017d53143500ec324b770014c46cec388c92dc5170017d5311b430ec2dc0070017d5311b424c92989d70017d46cec324b72989570017d531303b0c92dca67) else (if i < 24 then 0x0017d5311b3b0c92e40b70017d5311b424c92dc8970017d5311b3b0ce2dc3d70017d531313b0c92dc4770017d5311b3b0d52dca470014c46cec388c91ec0b70017d5311b3e4c92dc5170018e5f54c46d043b0c97 else (if i < 25 then 0x001885f54c46cc91a43d7001885f55846cec324b27000005f54c478ec324b76000005f56146cc92dc0e6000005f54d46cec324b760017d5311b324b71a00e70017d5311b3b0d62dc0e70017d5551b3b0c92983d7 else 0x0017d5611b3b0c92dc1270017d5311b398c92dc6970017d531353b0c92dc0e7001835f54c46d093b0c970017d5311b424ec324c270014c46cec368b72c87b70017d5311b424c92980f70017d5311b324b21a43d7))) else (if i < 29 then (if i < 27 then 0x0017d5311b3b0c92d00b70017d5311b424c90380b7000005311b324b71580e6000006214c46cec3243c6000005f54c4d505324b760017d5551b3b0c92dc0a7000006217d5311b3b0da60017d5311b410ec388c97 else (if i < 28 then 0x000005f51b3b0c92dc7660017d531313b0c92dcb270017d5851b3b0c92dcb27001885f54c4c4ec324b77001885f56146cec324b770018b5f54c46cec358b770017d555313b0c92dca670017d5311b388c91040e7 else 0x0017d5311b324690f40e70017d531313b0c92dc2570017d5311b3b0c92dca47001885311b3b0c92c87b70017d5551b3b0e1324b77000006394c500e2324b760017d5611b3b0c92dc7b70017d5311b324b72a4327)) else (if i < 30 then 0x001885311b3b0c92c8a67000005311b3d8ec3240b60018e5f54c46cc92dc687000005f54c46d143b0b760017d5311b3b0c91f43d70017d5611b3b0c92dca670017d5695546cec324b770017d5a11b3fcec324b77 else (if i < 31 then 0x0014c46cec3247b0c80b7000005f54c46cec2dc4560018e5f54c4d4ec324b770017d5311b424c92980a70017d53140424ec324b770017d5311b3b0c92cc0b7000005311b3b0c92047b6000006397d5851b324b76 else 0x0018e5f54c46d093240b7000006394c46cc92dc566000006394c46d0c388b76001885311b3b0c92c88170017d5311b3b0da2dcb270017d5311b430ec3a0b77001885f54c46cec368b770017d5851b3b0c92dc0e7)))) else (if i < 37 then (if i < 34 then (if i < 33 then 0x0017d531353b0e2324b77000005f54e46cec324b760017d53135414ec324b77001885311b3b0c91443d70017d531404fcec324b77001885f54c46cff3b0c97001855311b3b0c92dca47001885311b3b0c92dc3c7 else 0x000000017d5551b424c95000005f54c46d0c410ec60017d5311b3b0cb2dc0a7001926214c46cec324b270014c46cec324b71580e70014c46cec398c92dc5170017d5311b410ec3243270017d5311b431093b0b77) else (if i < 35 then 0x0014c46cec324b70c80f70014c46d043b0e23245170017d5311b3b0ce2dcb27000005f55546cec324b76000005311b388c92dc5660017d5311b3b0d52dca670017d5311b414c92dc3d70017d5ad5846cec324b77 else (if i < 36 then 0x0017d5551b3b0c92dc007000005f55546cc92dc696001805311b3b0c92dcb270018e531403b0e2324b770014c46cec324b72047b7001885f54c46cec324b270017d5611b414c92dcb270014c46cf63b0c92dc0b7 else 0x0018e5f54c46cc9304b770017d5311b410ec398c970018e5f56146cec324b77000005f54c46cec3248160017d5611b3b0c92dc1d70014c46cc92dc510f40e70017d5311b3b0da2dc0e7001885311b3b0c92dc047))) else (if i < 40 then (if i < 38 then 0x000005f54c46cec33cb760017d531223b0c92dc3d70018e6214c46cec3247b70017d5311b358b72985b70017d5311b3b0c90c80b70017d531353b0c92c80b70017d5551b3b0c92dc9570017d5891b3b0e6324b77 else (if i < 39 then 0x0017d5311b431043b0b770017d5851b3b0e2324b77000005f54c46d09324a660017d5311b430ec2dc6f70018e5311b3b0c92dc5670017d5311b3b0c92dc7b70018e5311b430ec388b77000006155546cec324b76 else 0x001805311b3b0c90f40b70017d530ec324b72989070017d5311b424c92980070014c46cec324b72909d70017d5311b3b0c92dca670017d531353b0c92dc4b70017d5ed613b0e2324b77000005f55546d09324b76)) else (if i < 41 then 0x0017d5311b3b0c93083d70017d5511b3b0c92dca47001885f54c46cec324b970017d5311b451093b0b770018e5f54c46cec368b770017d5311b410ec324a470017d5311b324b7298697001955f55846cec324b77 else (if i < 42 then 0x001835f54c46cc91a43d70017d5d1553b0c92dca670017d5311b324891a43d70017d5311b3b0c92dc817001885311b3b0c92dca870014c46cec388c92dc567001835f54c46cec3243d70017d5311b3b0c91040a7 else 0x000005f54c3b0c92dc496000006154c46d09324a66000006214c46cc92c86d6000005f54c46cec32cb76001855311b3b0c92dc7b70017d5551b3b0c92dc6970017d531353b0c92dc717000005f55846cc92dc6d6)))))) else (if i < 65 then (if i < 54 then (if i < 48 then (if i < 45 then (if i < 44 then 0x000005f561500ec324b760017d531403b0c92dc687001925f54c46cec324b770017d5611b3b0e0324b770017d5611b3b0c92dc5170017d5311b3b0e2368b77001855311b3b0c92dca670017d5311b3b0c92dc827 else 0x0017d531283b0e2324b770017d5311b3b4c90f40b70018e6014c46cec324b770017d5311b424c92dca67001885f54c46cec324b47001855311b324b7298697001885311b3b0c92c8517000000018e5311b410c95) else (if i < 46 then 0x0017d5551b424ec324b770017d531403b0c92dc3d70017d5311e3b0c92dc0b70017d5351b3b0c92dc0b7000005551b3b0c92dc9d60017d5311b434ec398b770017d5311b3b0c92a07b70017d5411b3b0e2324b77 else (if i < 47 then 0x0017d5311b3b0d62dc5f7000005f56146d0c3b0b760017d5311b430ec2dc687001885f54c46cec324b370017d5311b3b0d62dca470017d5311b424c92986970017d5311b324bf2dc0e70017d531403b0e2324417 else 0x0016146cec388c92dc517001885311b324b72c86d70017d531353b0c92dca470017d5311b390c90f40b7000005f54c518ec324b760017d5311b3b0da2c80b70014c46cec324b71ec5170017d5311b324b7158517))) else (if i < 51 then (if i < 49 then 0x0014c46cec324a61ec0b70018e6217d5311b424c97001885f54c504ec324b770017d5611b3b0c92dc6d7001855f54c46cec324b770018e5311b324b71a4077000006157d5311b424c96001855311b424c92dca67 else (if i < 50 then 0x000005311b424c92989d6000005f54c46cec3244160014c46cec324b72747b7001855f54c46cc92dc6970017d5311b414c92dc0e70017d5311b430ec2dc3d7000006394c46d04324b76001885311b3b0c92c86d7 else 0x0014c46cc92dca6274697001885311b3b0c92dc0b70014c46cec324b72989d70017d5311b410ec3247b7000006394c46d043b0c960017d5311b430ec2dc2c70017d5311b3b0c9104007000005f577560ec324b76)) else (if i < 52 then 0x0017d5311b3b0c91043c7001925f54c46cc92dc5270017d5311b3b0c9308b270014c46cf63b0c92dcb27000006215846cec324b260017d5511b3b0c92dca670014c46cec324b71ec0f70017d5311b410ec324a67 else (if i < 53 then 0x0017d531313b0c92dca470017d5311b3b0c92e0b770017d5311b404ec324b77001855f54c46d09324b770017d5311b3b0da2dc6270017d531403b0c92dc477000005f55546cec358b760017d5611b3b0c92dc017 else 0x0017d5311b3b0c92dc4170017d5311b324c22dc0e70017d5311b3b0c91ec0b7001885f54c46cec324327000005f54c500c92dc0e6001885f54c4d4ec324b27001885311b3b0c90f43c70014c46cc92dca91ec517)))) else (if i < 59 then (if i < 56 then (if i < 55 then 0x0018e5311b324b71ec327001835311b3b0c92dc077000005611b3b0c92dc7b60014c46d09324b72989d7000005f51b3b0c92dc9560017d5311b324b71b43c7000005f54c4c0ec324b760017d531484d4ec324b77 else 0x001925311b3b0c92dc0f7001885311b424ec3240b70017d5695846cec324b770017d5311b3b0d62dc7b70017d5551b3b0c92dc2170017d5311b3b0c92dc9d70017d5551b3b0c92dc0b70018e5311b410ec324b77) else (if i < 57 then 0x0014c46cf93b0c91ec0b70017d531353b0c92dc7b70017d5311b3b0c92040b70017d5311b3b0d62dca67001885611b3b0c92dcb270017d5311b3b0c91a44170014c46cf63b0c90f40b7000005f54c46d09358a66 else (if i < 58 then 0x0017d53146424ec324b770017d531353b0c92dca670017d5551b3b0c92dc4c70017d5311b3b0b72986470017d5311b3b0c92dc0f70017d5311b358b72986970018e5f54c46d09324b470017d5311b3b0da2dca47 else 0x0017d5311b324b71b46970017d531363b0c92dcb47000005f5554c4ec324b760017d5311b425013b0c97001855311b3b0c92dc9d70017d5311b4310b3b0b770017d531384c4ec324b77000006214c46cff3b0c96))) else (if i < 62 then (if i < 60 then 0x0018e5311b3d8ec324b770017d5311b424ec3244170017d531403b0c92dc0e7001855311b3b0d62dca670017d5311b3dcec324b770017d5391b3b0c92dc3d70017d5311b424c92980b70018e5f54c46cc9308b77 else (if i < 61 then 0x0017d5311b3b0cf2dc687000006214c46cec324b260017d5311b324a61a43d70017d5311b424d62dca67000005f55846cec324b760017d5311b3247b1a43d70017d5311b414c92c80b70017d531313b0c92dc907 else 0x0017d531313b0c92dc7b70017d5311b3b0cb2dc0b7000000014c46cec324815000005f55946cec324b760014c46cec3247b1440b7001885311b3b0c92c8007000005f54c46d093240a60017d5611b3b0c92dc007)) else (if i < 63 then 0x0017d5311b450ff3b0b77001885311b3fcec324b770017d531313b0c92dca670017d53135414c92dcb270017d5311b324b71a40a7001885f54c46cec368b27000005f54c4c509324a660017d5311b3b0c92dc0a7 else (if i < 64 then 0x000005f54c46cec354b760017d5311b410ec3244170018e5f54c46d04388c97001855f54c46cec358b770017d5311b410ec3245170017d53131324b7298697001885311b3b0c92c83c7001945f54c4c4ec324b77 else 0x0014c46cec324b71ec3c70017d5311b424c92dc0a70014c46cec358b72989d700185531313b0c92dca670017d5311b3b0da2dc7b70017d5311b430ec2dc067001885311b3b0c92dcb27001855311b3b0c92dc0a7))))) else (if i < 76 then (if i < 70 then (if i < 67 then (if i < 66 then 0x001885311b3b0c92c8697001935f54c4d4ec324b770017d531283b0c92dc7b70017d5311b404ec3240b70017d53131424c92dca670017d5851b3b0ea324b770017d5311b3b0da2dca67000005311b3b0c92dc816 else 0x000005f54c4d4c92dc6d6001885311b3b0c92c8077001885f54c46cec3247b70017d5311b3b0c9308327001835311b3b0c92dc687000006214c46cec324b46001885311b424ff3b0c970017d5311b3b0c91040b7) else (if i < 68 then 0x001885f55546cec324b77000005f54c3b0c92dc906001885311b3b0c90f40b7000005311b3b0c92a07b6000005f54c46cec324b760017d5311b3d8ec3244170014c46cec324b71ec0470017d531313b0df324b77 else (if i < 69 then 0x0017d5311b324b71b40b7001885311b3b4ec324b770017d531314b8ec324b770017d5611b424ec324b770014c46cec3247b02c0a70017d5311b3b0c92dc0070017d5551b3b0c92dcb270017d531353b0c92dc517 else 0x000005f574554ec324b76001885f54c46cec3248170017d5311b424ff324a670017d5311b45cec368b770017d5311b3b0b72c86270017d5311b3b0d62dc9d7001855f54c4c4ec324b77001885311b424ec324b27))) else (if i < 73 then (if i < 71 then 0x0014c4c4ec324b72989d700000001855311b424c950017d531353b0c92dc1070017d5311b3b0c92dc3c70017d5851b388c92dc0e70014c46cec324b72740a70017d5311b414da2dcb270017d5311b3b0c92c8817 else (if i < 72 then 0x0017d5311b3b4c92dca670018e6214c46cec324b770017d5311b3b0d62dcb07001855311b3b0c92dc007000006154c46cc92dc696001885311b3b0c92dcb4700000639885311b424c96000006154c46cec324b76 else 0x0017d5311b3b0c92dc6e70017d5311b3b0c92dc0470017d531353b0c92dc6d70014c46cec324b72a07b70018e6214c46cc92dc6970017d5311b424c92c8a67001885f54c46d09324a670017d5311b3b0d62dc5b7)) else (if i < 74 then 0x0017d531313b0c92dc9d70017d5311b3b0d634cb770017d531403b0c92dc227000006154c46d09324b760017d5311b390c92dca67001885311b3b0c91ec5170017d5311b3b0c92dc6970017d5311b324b71a4047 else (if i < 75 then 0x0017d5311b3dcec3243d70017d531313b0d62dca67000005f54c46cc9298896001855311b3b0c92dc047000005f54c46cda2dc6d60017d5311b3b0c92a03c70017d5311b3b0d62dc0a70018e6214c46d09324b77 else 0x0017d531313b0c92dc2670014c46cec324b72740070017d5311b424ec324b77001855311b3b0c92dc6970017d5311b424c92dc047000005311b3b0c92dc9d60017d5311b3b0da2dc5170017d531463fcec324b77)))) else (if i < 81 then (if i < 78 then (if i < 77 then 0x0017d5311b410ec324007000005f55446cec324b760017d5551b3b0c92dc1370017d5311b424c902c0a70017d5311b3b0c92dca870014c46cc92dcb21ec6d70014c46cff3b0c92dc327000005f54c46d043b0c96 else 0x001855311b424ec324b770017d5311b324b72a46970017d5311b3b0ce2dc5170014c46cec324b72743c70017d5311b424ec3246970017d5611b3b0c92dc1a70018e6214c46cc92dc527001925f54c46cec324b47) else (if i < 79 then 0x0018e5311b388c92dc6970017d5611b3b0c92dc3d70017d531313b0c92dc0a70017d5311b3b0da2dc6d70017d5311b3b0c92c84170017d5311b324b7298897001885f54c46cec3244170017d5311b3b0c92dc527 else (if i < 80 then 0x0017d530ec388c92dc497000005f54c46cec2dc6460017d5311b3b0d62dc0070017d5311b324b72c86d70014c46cec324b7274697001885f54c46cc92dc6d70017d5311b424c92dca97000005f54c46cec358b76 else 0x0014c46d093b0c92dc9d70017d5311b424c9298897000006394c46d04388c96000006154c46cec358b760017d5311b3b0c92dc0b70017d531303b0c92dcb27000005f54c46d0d3b0b76000005311b410ec324516))) else (if i < 84 then (if i < 82 then 0x000005f54c4c4ec324b760017d5311b3b0d62dc6470017d5311b3b0e4324417001965f55546cec324b770017d5311b424c92983270017d5311b324690f40070014c46cec324b72a09d7000005f54c46cc91a43d6 else (if i < 83 then 0x0018e5311b410ec388c970017d5311b324b71a43d70017d5311e3b0c92dca670017d5351b3b0c92dca670017d5551b3b0c92dca470018e5311b410e2324b770014c46d043b0c92dc5170017d531313b0c92dc007 else 0x0014c46cf63b0c92dc5170018e5311b388c92dc0b7000005f56846cec324b760017d5311b424ec358b770017d5311b324690f40470017d5311b3b4c92dc0a7000005311b3b0d62dc9d6000006154c4c4ec324b76)) else (if i < 85 then 0x0017d53131424ec324b7700000531313b0c92dc9d60017d5311b3fcec324b770017d5311b424c91a43d7001925311b3fcec324b77000005f55846d05324b760017d5311b390c92dc0a70017d5311b424c9298a47 else (if i < 86 then 0x000005f54c4c4ec358b76000000017d5311b324895001855551b3b0c92dca670017d5a11b424ec324b770017d5611b414ec324b770017d5551b3b0c92dca670017d5311b3b0d62dc437000005f55546d09324a66 else 0x0017d5311b324b71a40e7)))))))
def g0_l6S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l6C (i / 8)) 84 (i % 8))
def g0_l6HC (i : ℕ) : ℕ := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x0641794b0618986105f8cbfd05caed0405c09a89059a6891055b37e5052c40fe04c912430494884b040dd45003e62b0503d05bb9034347a8030080a502ec923002da8e9702d2cc6002cd3c16026682e30264977e02304dc801a8321a010fb12a0106808a00f9218500f61f5600c09b4400a7997f007db72a006b22fa0047c98b else 0x0c1c26a30bfbacc20ba403240b94e5490aa7a5b60a65143b0a067f7809d73a7409c5cfa6099dc03909909b7a096087f7095f77c2090f191608e2c16808b6132c089c226e08973db7085aa733083856ac08374e2e07f7cf0c07ce8eef07adaa0a079deb830798f895077523c90713e0c206d9c99a0685ee040656e2c8064fcdc0) else (if i < 3 then 0x11dab5e011a6cf1a118e2822116d11271126f3fc10ddaf7010c00fc110afd887108cd200105750821049a92d100530650fe85d880fb1c66b0f9c77540f93befb0f51ff430f498bae0eeb3ce90ed8fdbd0ed8bec90eb3d6090ea49def0dfa299c0dc48db10d861d980d48f7e10cbfc1e10ca6883f0c97c4060c51250c0c38a603 else (if i < 4 then 0x173c979c16ed1e8316e0177e169927f3167593431641e84e161af3ba1618f8171618a83115a73e90156d0bd71559267415210db914e5284b148e3b351486c48d146ac5c214522581140f114913de8cd613ad95c213824256137ad0a9135a6a28132adb1d131a768e13059dc71305706d1303620812fdec2a12ace0ba1265f11c else 0x1d1df17a1ce825e11cddba511ca186e71c8a107e1c85c9661c6425751c4c0e9d1c4a5ad61c22655d1c1282891c0b746b1b6539431b4fd2bc1b02501b1b0009e21aa183ca1a4806551a3c4321199f56511996e5c8198f0834197f279d19205e3218f960ca18eada0c18af2d7d18a6efd1186e6c9d186bd3ba185098ba18410e5f))) else (if i < 8 then (if i < 6 then 0x25cbb6ee2571163a254e11522535dd7425308fd924d97675247f5ab024656a1b245ca2ae23c4296d23bc9d9b235134c9230f0c5922f8b09122c9b765228bcad9221a3581215023f22128fab3203f932b2024cf22200e257e1fc786841f85bb1f1f20ba941ede2af21e5cee9a1e1d6f781de09b991dbb6c471d6fdfc91d48ddf8 else (if i < 7 then 0x2f1ffad22e246aca2df3e6572dddcbd02dad475d2dac3c412d8853862d7f551b2d527c522cf9112c2cb410b82c9d81132b3e634d2b2e72b02aed6d632ae1f1f62aba1a2a29a0fc0f29915532294c695d28eb9d0c2897a82328824165285463ee280dc4f427e3b33027a5c4f6279fe725279e5349270eb8f5266b559525e91b60 else 0x38f00eaa38ab0e363843142b383a067237f5f51a37e0dabe37af56203777160b366533973640a074358852b0353c4935348b299c33b9ec7e33a1f2563396e4a33364bfe1332ee9643305b67332ca436432c6f047327ca77e326dbbbc3224b8e631d793a23130baee311729cc30f5a03430bb1ffd30994115300d87d12fe36f05)) else (if i < 9 then 0x413806f64121269a40c5518040706ffb4063db134053ed2b401c78b63ff0d2213fa3c7093f7f50b63f636ad33f51f5503f2796113f0647863e7759303e26ca8b3dc4dfac3d5716a03cf393fd3c9117893c8b3f9e3c6f29853c6daf183c34fcb23c04da8b3b5625f93b1592333adbf26a39e7d8ed39a106ee399feb5f395f69d0 else (if i < 10 then 0x4c33e5624b9dc0e24b45dd7b4af1ccd64aece1794ae51cf74aa4ec8e4a86c8694a18ff5d49ea9b64495fcbd548bac27f48823d1c487dc1cc481a431147dab6e346c3951546a292c6466fcd66465aad6945c3808e459212e1455a44b14434078c441fbcc743ffe6b2436e138943003f4d41d1a21f41907aef417924ce417169c4 else 0x54b5ecf85424bec85419392154137b565409338853ecaa275375a30c528fd814523eb2e551e88d6851aecf755117169d5106835f50f8558050f3206350c6b7125099930d50482b154fd386134fc2280a4f219f8f4efec4f74eca61c34e7a74cf4e6995724e4266584dde95ba4dd645634d70224c4d4545b94cbc12c34caa55bb)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0x5e87fa245e70b8325e682e4e5e2e87ee5d7d23095d79e27d5d1b208c5cab6f3d5c8f6c7a5c5fc00e5bce91de5bcccb4a5b422eb15b062c055ad142b85a955aee5a5df74f5a09220259eb9b1659e42969592c985a591f72305825384e5812d72557cfadd15686abb9563f7eb25621b49255655b1e5544d45654f14beb54cff983 else 0x694520ef68ffdc6d687eeef3684a4fe76825717e68181e0567e1f5aa671afd666696b5cd64fe167064c7848364abddb964a7286964981b656484091563bd74eb633a6edf629df76f625864d6623401a0620fe26561b2f5186191e2406185fe5b611281e56102ed7660af97b4609de5f86064d0566021d4ba5ed7bab25eaa7625) else (if i < 14 then 0x737d6cff73482fb272c9598272a8c6b1728fd09971b6b1cd7197cb707169112671239866711da55d704f461f6ffc579c6ffaa2fd6fde1a8d6fbcb6716f9f5a266f5fe02c6eecd87e6e01af2f6dd65f5a6dca7c516da4f1ad6d277b786cbefc666c7e739a6c2ed1136c124cfa6b99a36f6b3511bb6b2fee2d697cfa35696a9d9d else (if i < 15 then 0x7dc47d197da9f96e7da1ab377da0a7f17d1ab5617be0205e7ba5a1f57ae3d5fc7add513d7ada03cc7ab93f1e7a5c663c7a3f73607a317d3d7a164fa379e2c53c78892508783de5fb78198982774d540e774042a176e717a8765afa63764ffdea7620899075cec64e7546156d7517e65e74e75a3b7444579f73b8e3c9738ad0ba else 0x8c37331e8b8dfc198b2444288a8fd53b88a7897088235c91873cd4f986cc83ac86b6b10d86a4adf986542b4785ddb73385c97bbb858cc14984c715a383fa4a7183e50b9a835cecbd8341fd9b8315a6c9829f0def827bbd1f826d34cd8193a4bc81692c408095ab798084246b804cb9777fad93167e1504be7e10a0147df7cf3b))) else (if i < 19 then (if i < 17 then 0x99aaaa3c98ceac7a98c628189866f69c981dcd1197e9680c9778a98e9714d2d09687f58f966f426d96148dfb9601612295e9a59495a7196c94eec73b94e3cd8f923c0ba991ee8a049199999491963a5d9188fe60916558c79025b5979003e6588f66a99a8f2f1d8a8ef289688edcecda8db695ea8d88521d8d5794368c830c04 else (if i < 18 then 0xa347d854a2d1c168a2b50f08a28ca04aa275bfeea2690229a144abc4a0a68ea4a02ece519f1979009ef514689ec4f6919e35f0189dd4ed7b9dc586cf9d9f93339d7916ad9d58f4399d4c397e9d0f45049cc2702a9be1b6b29bcc1a249ba1ad789b7cc72d9aea66119abaf21c9ab995159a1feadd9a03deb799f1493699ca7205 else 0xb3ef6238b3de81c1b329cf10b24ceed4b20bc99eb1f8701bb1b241a1b16990b2b0e2c709b07f302cb0723fe1af5fb818ae6fc52bae6c6d13ae254f56ae069481ad1dfb9bacf5536dac2f29b0abdb61bdaaefb489aab1ecbba9c42d41a8a627cfa7bec736a6d6f685a65f2475a528df59a4a0f2b2a3ff1fbba3b880c1a362c7e7)) else (if i < 20 then 0xc8d4bbd8c47e3fa6c42ee39cc3d644f3c39ed04bc38fa5f9c2cdaaeac248d1f6c0de46b9c0378d7bbf61943fbe46f411bd3d4b55bd34289ebcf6ac5bbcdb9f43bbb290a3b968091bb91fb75ab89f999bb80e4683b80e0010b7b864b4b708123db631faa4b549099db4d692e9b4b30aedb4872c50b477f7fcb46dbf22b44be8fe else (if i < 21 then 0xe2069c6ee17dbca9de384b38dd54d3f5dc6e3977dc55414cdc237500dc0dd872db3d315cda76f8c0da74d959da6d67acd84b5206d827eb33d5ab307bd56b2885d38516dfd28265e4d277f965d20fed2cd18191eacf9b21a9ce61cf5acdb51003cd04721acb7e41e0cb660276cad19389ca63a331ca5c0a57c96b747cc8e947be else 0xfe0f81f5fdb01bc4fda32b79faa9cb46f9444d37f55453b1f22109b3f1169e40f093f40fee9118deed5fb9e9ec0a3abae8c11202e8476518e57d24cbe3fd1d81e259288b)))))
def g0_l6H (i : ℕ) : ℕ := fld (g0_l6HC (i / 32)) 32 (i % 32)
def g0_l7C (i : ℕ) : ℕ := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x5f54c46d093fcec324b78001885311b3b0c92dc5170017d5311b3b0c92fcb775f54c46cec324b72c86986217d5311b3b0c92dc698000005311b324b71440e6001885f54c46d093b0c970017d5311b3b0c92e4b77 else 0x5f54c46cec324b70f40b86397d5311b3b0c92dc0080018e5f54c46cc92dc6976217d5311b3b0c92dc0780018e5f54c46cec324b770017d5311b3b0e4324b770017d5311b3b0c92dcb470017d5311b424c92dc0e7) else (if i < 3 then 0x0014c46cec324b71440e75f54c46cec388c92dc0085f54c46cf93b0c92dc7b80017d5311b3b0e2324b775f54c46cf63b0c92dc3d85f54c46d093b0c92dcb280017d5311b414ec324b776217d5311b424ec324b78 else 0x0017d5311b3b0c9308b776397d5311b3b0c92dc698000005f54c500ec324b760017d5311b3b0c92c80b75f54c46d093b0c92dc0e86217d5311b3b0c92dc5286157d5311b3b0c92dca685f54c46cec324b7038078)) else (if i < 6 then (if i < 5 then 0x0014c46cec388c92dc517000005f54c46d0c3b0b765f54c46cec388c92dc6980017d5311b3b0c92dc3270017d531353b0c92dcb275f54c46cec324b72985185f54c46cec324b71ec518001835f54c46cec324b77 else 0x5f54c46ced3b0c92dc0b80017d5311b3b0c92dca475f54c46cec324b70380b860d7d5311b3b0c92dc6980017d5311b410ec388c975f54c46cec324b72c80b86217d5311b3b0c92dc0b85f54c46cec324b72989d8) else (if i < 7 then 0x000005f55546cec324b765f54c46cec324b70f40e85f54c46d093b0c92dc3286397d5311b3b0c92dc0b85f54c46cec390c92dc0b80017d5311b3b0da2dcb275f54c46d043b0e2324b785f54c46cec324b72980a8 else (if i < 8 then 0x0017d5311b3b0c92dca675f54c46cec324b71ec0080017d5851b3b0e2324b77000005f54c46d09324a665f54c46cec388c92dc6880017d5311b3b0c92dc7b75f54c46cec388c92dc0b8001885f54c46cec324b27 else 0x5f54c46cec324b72986985f54c46cec324b71ec6980017d5311b424c92dca67001925f54c46cec324b77001855311b3b0c92dca676217d5311b3b0c92dcb285f54c46cec324b72980080017d5311b324b7298697)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0x001885311b3b0c92dc0b70014c46cec324b72989d75f54c46d093b0c92dc7b86397d5311b3b0c92dcb28000005f54c46cec324416639885f54c46cec324b78001855f54c46cec324b770014c46cec324b71ec517 else 0x5f54c46cec324b71443c80017d5311b3b0c92dc9d70017d5311b3b0c92dc4176497d5311b424ec324b780017d5311b3b0c91ec0b75f54c46cec388c92dcb285f54c46cec324b72a47b85f54c46d093b0c92dca68) else (if i < 12 then 0x000006214c46cec324b26000005f55846cec324b765f54c46cec324b71a45185f54c46cec324b72980b85f54c46cec324b71ec0b86397d5311b3b0c92dcb480017d5311b3b0c92dc0f70017d5311b3b0d62dca67 else 0x5f54c46cec324b71440b80017d5311b3b0c92dc007001885f54c46cec3247b75f54c46d093b0c92dc0f8001885311b3b0c92dcb275f54c46cec324b72c8a480017d531313b0c92dca670017d5311b3b0c92dc0a7)) else (if i < 15 then (if i < 14 then 0x0017d5311b3b0c92dc0475f54c46cec324b72c8a686217d5311b3b0c92dca685f54c46cec324b72c87b86217d5311b3b0c92dc7b80018e6214c46cec324b77000006154c46cec324b760017d5311b3b0c92dc3c7 else 0x5f54c46d093b0c92dc0080017d5311b3b0c92dca87000005f54c46d043b0c960017d5311b424ec324b77000005311b3b0c92dc9d6649885f54c46cec324b785f54c46cec324b71a40080017d5311b3b0c92dc697) else (if i < 16 then 0x0017d5311b324b72c86d7000005f54c46cec358b765f54c46cec324b71a40785f54c46cec388c92dc7b80017d5311b3b0c92dc5276397d5311b3b0c92dc7b80017d5311b424ec3246975f54c46cec324b702c0a8 else (if i < 17 then 0x0017d5311b324b71a43d75f54c46cec324b72c86d8000005f54c4c4ec324b765f54c46cec324b71ec328000005f54c46cc91a43d65f54c46cec324b702c0080017d5311b3b0c92dc0b75f54c46d093b0c92dc698 else 0x0017d5311b324b71a40e70017d5551b3b0c92dca670017d5311b3fcec324b775f54c46cec324b71a43d85f54c46cec324b7298a485f54c46cec324b70f43c8)))))
def g0_l7S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l7C (i / 8)) 84 (i % 8))
def g0_l7HC (i : ℕ) : ℕ := (if i < 2 then (if i < 1 then 0x1aa183ca19ddae5e197f279d18410e5f174c52af173454341333e4be1219e7a410ddaf701099e7af105adddf0eb3d6090df338180dc922fb0dc48db10d8284010aed9d9b0a1d5fd40a067f78085018f608374e2e07f7cf0c07ce8eef077523c907163cbe0713e0c20685ee040463812c041ce2320106808a00c09b440047c98b else 0x4aece1794a63d37249ea9b64495fcbd549596d34487dc1cc40f9ac294053ed2b3f51f5503cca4b153b4b952a3a7d244e3a3da52c37f5f51a37a3dab336c95ed93295c8f7311729cc2e8626d02ca8b04b2ae1f1f62502f71c24bc58222485c635235134c92128fab3205a3639203f932b200e257e1f4881eb1cd9623e1b02501b) else (if i < 3 then 0x8095ab797fad93167e1fcdb37d32b7997ac397ec77e81007774042a17517e65e7320970371b6b1cd6f5fe02c6f253b206e01af2f695329ef67f8cc8c65f8e37864fe167064c784836389c3cb62d6a214629df76f6290031a6064d0565d1b208c5c9341a95a2421fc5621b492541939215375a30c4d15d5e84cd2f31f4cbc12c3 else (if i < 4 then 0xc3d644f3c248d1f6bf9dc435bf13cabfbcdb9f43b89742e4b80e4683b6402091b50fe0b6b4872c50b44be8feb329cf10b1f8701bae71ee0dabaa3ee7a9c42d41a6d6f685a58c355fa5459665a31d15b2a2d676b8a2d1c168a0a68ea49ec4f6919ebf43a39a03deb796148dfb924c44a08d5794368bb67db286542b4783fa4a71 else 0xfe0f81f5f22109b3ec0a3abaea4e27a6e3e63e2fdf4ef0f6da76f8c0d3ad73d9d38516dfd09f87e1cdb51003cc49b4d7ca63a331c4d02f40)))
def g0_l7H (i : ℕ) : ℕ := fld (g0_l7HC (i / 32)) 32 (i % 32)
def g0_l8C (_ : ℕ) : ℕ := 0x0017d5311b3b0c92dc0b70017d5311b424ec324b770017d5311b3b0c92dc6970017d5311b3b0c92dca670017d5311b3b0c92dc7b70017d5311b3b0e2324b770018e5f54c46cec324b77
def g0_l8S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l8C (i / 8)) 84 (i % 8))
def g0_l8HC (_ : ℕ) : ℕ := 0xca63a331b329cf10a9c42d414aece179487dc1cc0eb3d60908374e2e
def g0_l8H (i : ℕ) : ℕ := fld (g0_l8HC (i / 32)) 32 (i % 32)
def g0_l9C (_ : ℕ) : ℕ := 0x000005f54c46cec324b76
def g0_l9S (i : ℕ) : List ℕ := g0_decSt (fld (g0_l9C (i / 8)) 84 (i % 8))
def g0_l9HC (_ : ℕ) : ℕ := 0x981dcd11
def g0_l9H (i : ℕ) : ℕ := fld (g0_l9HC (i / 32)) 32 (i % 32)
def g0_N : ℕ → ℕ
  | 2 => 2
  | 3 => 20
  | 4 => 420
  | 5 => 989
  | 6 => 689
  | 7 => 142
  | 8 => 7
  | 9 => 1
  | _ => 0
def g0_S : ℕ → ℕ → List ℕ
  | 2, i => g0_l2S i
  | 3, i => g0_l3S i
  | 4, i => g0_l4S i
  | 5, i => g0_l5S i
  | 6, i => g0_l6S i
  | 7, i => g0_l7S i
  | 8, i => g0_l8S i
  | 9, i => g0_l9S i
  | _, _ => []
def g0_idx : ℕ → List ℕ → ℕ
  | 2, zs => bsrF g0_l2H (hk zs) 12 0 2
  | 3, zs => bsrF g0_l3H (hk zs) 12 0 20
  | 4, zs => bsrF g0_l4H (hk zs) 12 0 420
  | 5, zs => bsrF g0_l5H (hk zs) 12 0 989
  | 6, zs => bsrF g0_l6H (hk zs) 12 0 689
  | 7, zs => bsrF g0_l7H (hk zs) 12 0 142
  | 8, zs => bsrF g0_l8H (hk zs) 12 0 7
  | _, _ => 0
def g0_bar : ℕ → ℕ → Bool := bar (w64v 1).toNat (w64v 3).toNat (w64v 4).toNat g0_dt0 g0_dt1 g0_dt2 g0_dt3 g0_dt4 g0_dt5 g0_S g0_N g0_idx (ori swap02Nat)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s2_0 : span (g0_bar 2) 2 0 = true := by decide +kernel
theorem g0_l2_all : span (g0_bar 2) 2 0 = true := g0_s2_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s3_0 : span (g0_bar 3) 20 0 = true := by decide +kernel
theorem g0_l3_all : span (g0_bar 3) 20 0 = true := g0_s3_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_0 : span (g0_bar 4) 65 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_1 : span (g0_bar 4) 65 65 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_2 : span (g0_bar 4) 65 130 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_3 : span (g0_bar 4) 65 195 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_4 : span (g0_bar 4) 65 260 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_5 : span (g0_bar 4) 65 325 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s4_6 : span (g0_bar 4) 30 390 = true := by decide +kernel
theorem g0_l4_all : span (g0_bar 4) 420 0 = true := (@span_join (g0_bar 4) 195 0 225 (@span_join (g0_bar 4) 65 0 130 g0_s4_0 (@span_join (g0_bar 4) 65 65 65 g0_s4_1 g0_s4_2)) (@span_join (g0_bar 4) 130 195 95 (@span_join (g0_bar 4) 65 195 65 g0_s4_3 g0_s4_4) (@span_join (g0_bar 4) 65 325 30 g0_s4_5 g0_s4_6)))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_0 : span (g0_bar 5) 65 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_1 : span (g0_bar 5) 65 65 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_2 : span (g0_bar 5) 65 130 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_3 : span (g0_bar 5) 65 195 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_4 : span (g0_bar 5) 65 260 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_5 : span (g0_bar 5) 65 325 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_6 : span (g0_bar 5) 65 390 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_7 : span (g0_bar 5) 65 455 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_8 : span (g0_bar 5) 65 520 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_9 : span (g0_bar 5) 65 585 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_10 : span (g0_bar 5) 65 650 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_11 : span (g0_bar 5) 65 715 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_12 : span (g0_bar 5) 65 780 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_13 : span (g0_bar 5) 65 845 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_14 : span (g0_bar 5) 65 910 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s5_15 : span (g0_bar 5) 14 975 = true := by decide +kernel
theorem g0_l5_all : span (g0_bar 5) 989 0 = true := (@span_join (g0_bar 5) 520 0 469 (@span_join (g0_bar 5) 260 0 260 (@span_join (g0_bar 5) 130 0 130 (@span_join (g0_bar 5) 65 0 65 g0_s5_0 g0_s5_1) (@span_join (g0_bar 5) 65 130 65 g0_s5_2 g0_s5_3)) (@span_join (g0_bar 5) 130 260 130 (@span_join (g0_bar 5) 65 260 65 g0_s5_4 g0_s5_5) (@span_join (g0_bar 5) 65 390 65 g0_s5_6 g0_s5_7))) (@span_join (g0_bar 5) 260 520 209 (@span_join (g0_bar 5) 130 520 130 (@span_join (g0_bar 5) 65 520 65 g0_s5_8 g0_s5_9) (@span_join (g0_bar 5) 65 650 65 g0_s5_10 g0_s5_11)) (@span_join (g0_bar 5) 130 780 79 (@span_join (g0_bar 5) 65 780 65 g0_s5_12 g0_s5_13) (@span_join (g0_bar 5) 65 910 14 g0_s5_14 g0_s5_15))))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_0 : span (g0_bar 6) 45 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_1 : span (g0_bar 6) 45 45 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_2 : span (g0_bar 6) 45 90 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_3 : span (g0_bar 6) 45 135 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_4 : span (g0_bar 6) 45 180 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_5 : span (g0_bar 6) 45 225 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_6 : span (g0_bar 6) 45 270 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_7 : span (g0_bar 6) 45 315 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_8 : span (g0_bar 6) 45 360 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_9 : span (g0_bar 6) 45 405 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_10 : span (g0_bar 6) 45 450 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_11 : span (g0_bar 6) 45 495 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_12 : span (g0_bar 6) 45 540 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_13 : span (g0_bar 6) 45 585 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_14 : span (g0_bar 6) 45 630 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s6_15 : span (g0_bar 6) 14 675 = true := by decide +kernel
theorem g0_l6_all : span (g0_bar 6) 689 0 = true := (@span_join (g0_bar 6) 360 0 329 (@span_join (g0_bar 6) 180 0 180 (@span_join (g0_bar 6) 90 0 90 (@span_join (g0_bar 6) 45 0 45 g0_s6_0 g0_s6_1) (@span_join (g0_bar 6) 45 90 45 g0_s6_2 g0_s6_3)) (@span_join (g0_bar 6) 90 180 90 (@span_join (g0_bar 6) 45 180 45 g0_s6_4 g0_s6_5) (@span_join (g0_bar 6) 45 270 45 g0_s6_6 g0_s6_7))) (@span_join (g0_bar 6) 180 360 149 (@span_join (g0_bar 6) 90 360 90 (@span_join (g0_bar 6) 45 360 45 g0_s6_8 g0_s6_9) (@span_join (g0_bar 6) 45 450 45 g0_s6_10 g0_s6_11)) (@span_join (g0_bar 6) 90 540 59 (@span_join (g0_bar 6) 45 540 45 g0_s6_12 g0_s6_13) (@span_join (g0_bar 6) 45 630 14 g0_s6_14 g0_s6_15))))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s7_0 : span (g0_bar 7) 40 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s7_1 : span (g0_bar 7) 40 40 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s7_2 : span (g0_bar 7) 40 80 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s7_3 : span (g0_bar 7) 22 120 = true := by decide +kernel
theorem g0_l7_all : span (g0_bar 7) 142 0 = true := (@span_join (g0_bar 7) 80 0 62 (@span_join (g0_bar 7) 40 0 40 g0_s7_0 g0_s7_1) (@span_join (g0_bar 7) 40 80 22 g0_s7_2 g0_s7_3))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s8_0 : span (g0_bar 8) 7 0 = true := by decide +kernel
theorem g0_l8_all : span (g0_bar 8) 7 0 = true := g0_s8_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g0_s9_0 : span (g0_bar 9) 1 0 = true := by decide +kernel
theorem g0_l9_all : span (g0_bar 9) 1 0 = true := g0_s9_0
theorem g0_chk : ∀ s ≤ 9, ∀ i < g0_N s, g0_bar s i = true := by
  intro s hs i hi
  match s with
  | 0 => simp [g0_N] at hi
  | 1 => simp [g0_N] at hi
  | 2 => exact span_ok g0_l2_all i (Nat.zero_le i) hi
  | 3 => exact span_ok g0_l3_all i (Nat.zero_le i) hi
  | 4 => exact span_ok g0_l4_all i (Nat.zero_le i) hi
  | 5 => exact span_ok g0_l5_all i (Nat.zero_le i) hi
  | 6 => exact span_ok g0_l6_all i (Nat.zero_le i) hi
  | 7 => exact span_ok g0_l7_all i (Nat.zero_le i) hi
  | 8 => exact span_ok g0_l8_all i (Nat.zero_le i) hi
  | 9 => exact span_ok g0_l9_all i (Nat.zero_le i) hi
  | _ + 10 => omega
theorem g0_root : g0_S 9 0 = w64_vars.map BitVec.toNat := by decide +kernel
theorem g0_prop : w64_vars.sublists.all (fun ws => (ws.length == 6) || !(cover6 g0_dt0 g0_dt1 g0_dt2 g0_dt3 g0_dt4 g0_dt5 (ws.map BitVec.toNat))) = true := by decide +kernel
theorem g0_no9_64 (t : W64) (ht : t = g0_tt64 ∨ t = ~~~g0_tt64)
    (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  apply bar_refute64 (c0 := w64v 1) (c1 := w64v 3) (c2 := w64v 4) (tgt := g0_tt64)
    (d0 := g0_dt0) (d1 := g0_dt1) (d2 := g0_dt2) (d3 := g0_dt3) (d4 := g0_dt4) (d5 := g0_dt5)
    (swMap := swap02Map) (swNat := swap02Nat) (S := g0_S) (N := g0_N) (idx := g0_idx)
    rfl rfl rfl rfl rfl rfl
    swap02_inv swap02_nat (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    g0_root (by decide) g0_prop g0_chk
    (fun t' ht' => enforce_drop6 1 g0_tt64 (by decide +kernel) (no7_of_k4p64 ⟨32, by decide⟩ ⟨40, by decide⟩ (w64v 3) k4m_0245 (dropVar6 1) (restrict6 1 g0_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨32, by decide⟩ ⟨40, by decide⟩ (dropVar6 1) (w64v 3) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 1) k4_16_vars (by decide +kernel))) ht')
    (fun t' ht' => enforce_drop6 3 g0_tt64 (by decide +kernel) (no7_of_k4p64 ⟨16, by decide⟩ ⟨18, by decide⟩ (w64v 1) k4m_0245 (dropVar6 3) (restrict6 3 g0_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨18, by decide⟩ (dropVar6 3) (w64v 1) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 3) k4_16_vars (by decide +kernel))) ht')
    (fun t' ht' => enforce_drop6 4 g0_tt64 (by decide +kernel) (no7_of_bow64 bowm_02135 (dropVar6 4) (restrict6 4 g0_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_02135) (dropVar6 4) bow_32_vars (by decide +kernel))) ht')
    t ht hb

end G0Bar

section G1Bar

def g1_tt64 : W64 := 0xfffffffefefeee88#64
def g1_dt0 : ℕ := 0x1818199cc
def g1_dt1 : ℕ := 0x14141552a
def g1_dt2 : ℕ := 0x111110060
def g1_dt3 : ℕ := 0x100001066
def g1_dt4 : ℕ := 0x101001076
def g1_dt5 : ℕ := 0x1011176
def g1_bChunk (i : ℕ) : ℕ := (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x000000005500550000000000545454540000000050505050000000004444444400000000333300000000000033003300000000003232323200000000303030300000000022222222000000000a0a0a0a00000000040404040000000000cc00cc0000000000aa00aa000000000000cccc000000000000aaaa0000000000000000 else (if i < 2 then 0x00000000ff00ff0000000000fefefefe00000000fcfcfcfc00000000fafafafa00000000f8f8f8f800000000f4f4f4f400000000f2f2f2f200000000f0f0f0f000000000eeeeeeee00000000cccccccc00000000aeaeaeae00000000aaaaaaaa00000000a8a8a8a8000000008888888800000000666666660000000055550000 else 0x00006666eeeeeeee00006666000066660000555500000000000055000000ff0000004444cccccccc000044440000cccc000033330000cccc0000333300000000000033000000ff0000002222aaaaaaaa000022222222aaaa000022220000aaaa000022220000222200000000ffff888800000000ffff000000000000ff88ff88)) else (if i < 4 then 0x00660066eeeeeeee0066006600660066005500550000000000440044cccccccc0044004444cc44cc0044004400cc00cc00440044004400440033003333cc33cc0033003300ee00ee0033003300cc00cc00220022aaaaaaaa0022002200aa00aa00220022002200220000ffff0000fefe00007777000000000000770000007700 else (if i < 5 then 0x03000300ff00ff0002020202cececece02020202aaaaaaaa020202020a0a0a0a0202020202020202020202020000000001010101fefefefe010101010000000000ff00ff00fe00fe00ff00ff00ee00ee00ff00ff0066006600dd00dd00ee00ee00bb00bb00ee00ee00770077ff88ff8800770077006600660077007700000000 else 0x08080808aaaaaaaa080808080808080807070707f8f8f8f8070707070000000005050505fafafafa05050505aaaaaaaa0505050550505050050505050000000005050000ffff000004040404cccccccc040404040404040403030303fcfcfcfc03030303cccccccc030303030202020203030303000000000303000003030000))) else (if i < 9 then (if i < 7 then 0x1010101032323232101010103030303010101010101010100f0f0f0f0f0f0c0c0f0f0f0f0f0f08080f0f0f0f0f0f00000f0f0f0f000000000d0d0d0d000000000c0c0c0ccccccccc0c0c0c0c0c0c0c0c0c0c0c0c040404040c0c0c0c000000000b0b0b0bf4f4f4f40b0b0b0b000000000a0a0a0a020202020a0a0a0a00000000 else (if i < 8 then 0x11111111cccccccc11111111aaaaaaaa111111116666666611111111444444441111111122222222111111110000000011110000ffff888811110000ffff0000111100001111000011001100ff88ff8811001100ff00ff00110011001100110010101010fefefefe10101010fcfcfcfc10101010f0f0f0f01010101050505050 else 0x303030300000000022222222eeeeeeee22222222cccccccc22222222aaaaaaaa222222226666666622222222323232322222222222aa22aa222222222222aaaa222222222222222222222222000000002020202020202020117711770000000011661166116611661111777700000000111166661111666611111111eeeeeeee)) else (if i < 10 then 0x32323232fefefefe32323232fafafafa32323232babababa323232327676767632323232727272723232323232323232323232323030303032323232101010103232323200000000313131313030303030303030fcfcfcfc30303030f8f8f8f830303030f0f0f0f0303030307474747430303030323232323030303030303030 else (if i < 11 then 0x3333333344444444333333333232323233333333303030303333333322222222333333330000000033333300ffffff0033332222ffff0000333322223333000033330000ffff888833330000ffff0000333300003333000033223322ff00ff00332233223300330033003300ff88ff8833003300ff00ff003300330033003300 else 0x444444444444cccc44444444444444444444444400000000404040405050505040404040404040403737373700000000363636363c3c3c3c363636363636363633773377000000003366336633cc33cc3333777700000000333366663333cccc33333333eeeeeeee33333333cccccccc33333333aaaaaaaa3333333366666666)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x50505050fafafafa50505050f2f2f2f250505050f0f0f0f050505050dcdcdcdc50505050d8d8d8d850505050d0d0d0d05050505070707070505050505454545450505050505050505050505010101010505050500000000044444444cccccccc44444444aaaaaaaa444444448888888844444444666666664444444444cc44cc else (if i < 14 then 0x55550000555500005544554477007700554455445500550055005500ff88ff8855005500ff00ff005500550077007700550055005500550054545454fcfcfcfc54545454f4f4f4f454545454f0f0f0f05454545454545454545454545050505054545454303030305454545410101010545454540000000050505050fcfcfcfc else 0x55555555eeeeeeee55555555cccccccc55555555aaaaaaaa555555558888888855555555666666665555555554545454555555555050505055555555444444445555555522222222555555550000000055555500ffffff0055554444ffff00005555444477770000555544445555000055550000ffff00005555000077770000)) else (if i < 16 then 0x70707070f0f0f0f0707070707676767670707070727272727070707070707070707070705050505066666666eeeeeeee66666666cccccccc6666666666666666666666664444444466666666000000005a5a5a5a5656565656565656565656565577557744cc44cc5577557700000000555577774444cccc5555777700000000 else (if i < 17 then 0x77227722ff00ff00772277227700770077007700ff88ff8877007700ff00ff0077007700770077007676767676767676757575753030303074747474f0f0f0f0747474747474747474747474707070707474747454545454747474743030303072727272fafafafa7272727272727272727272725050505070707070f8f8f8f8 else 0x8888888844444444888888880000000077777777cccccccc77777777aaaaaaaa7777777788888888777777776666666677777777222222227777777700000000777777007777770077774444ffff0000777744447777000077772222ffff000077770000ffff888877770000ffff000077770000777700007744774477007700))) else (if i < 21 then (if i < 19 then 0xa0a0a0a0a0a0a0a09a9a9a9a9a9a9a9a99999999cccccccc99999999aaaaaaaa999999998888888899999999666666669999999900000000989898989898989890909090909090908c8c8c8ccccccccc8c8c8c8c8c8c8c8c8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a88888888cccccccc88888888aaaaaaaa8888888888888888 else (if i < 20 then 0xaaaaaaaa44444444aaaaaaaa22222222aaaaaaaa02020202aaaaaaaa00000000aaaa8888aaaa8888aaaa8888aaaa0000aa88aa88aa88aa88aa88aa88aa00aa00a8a8a8a8fcfcfcfca8a8a8a8aaaaaaaaa8a8a8a8a8a8a8a8a8a8a8a8a0a0a0a0a8a8a8a800000000a2a2a2a2aaaaaaaaa2a2a2a2a2a2a2a2a0a0a0a0aaaaaaaa else 0xaaffaaffaaaaaaaaaaeeaaeeaaeeaaeeaaaaffffaaaaaaaaaaaaeeeeeeeeeeeeaaaaeeeeaaaaeeeeaaaaaaaafefefefeaaaaaaaafafafafaaaaaaaaaeeeeeeeeaaaaaaaaccccccccaaaaaaaaaeaeaeaeaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa8a8a8a8aaaaaaaa88888888aaaaaaaa66666666)) else (if i < 22 then 0xbabababaaaaaaaaababababa30303030b8b8b8b8b8b8b8b8b8b8b8b8b0b0b0b0b8b8b8b830303030b2b2b2b2b2b2b2b2b0b0b0b0b8b8b8b8b0b0b0b0b0b0b0b0b0b0b0b030303030afafafafaaaaaaaaafafafaf50505050afafafaf00000000aeaeaeaeaeaeaeaeaeaeaeaeaaaaaaaaababababaaaaaaaaabababab00000000 else (if i < 23 then 0xc0c0c0c0ccccccccc0c0c0c0c8c8c8c8bfbfbfbfaaaaaaaabbffbbffaaaaaaaabbbbbbbbeeeeeeeebbbbbbbbccccccccbbbbbbbbaaaaaaaabbbbbbbb88888888bbbbbbbb00000000bbbb0000ffff0000bb88bb88ff00ff00bb00bb00ff00ff00babababafefefefebabababafafafafababababababababababababab0b0b0b0 else 0xccccccccaaaaaaaacccccccc88888888cccccccc44444444cccccccc22222222cccccccc04040404cccccccc00000000cccc8888cccc8888cccc8888cccc0000cc88cc88cc88cc88cc88cc88cc00cc00c8c8c8c8fafafafac8c8c8c8ccccccccc8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c4c4c4c4ccccccccc4c4c4c4c4c4c4c4))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then 0xcfcfcfcfcccccccccfcfcfcf30303030cfcfcfcf00000000cececececececececececececccccccccdcdcdcd32323232cdcdcdcd00000000cceecceeeeeeeeeecccceeeecccceeeeccccccccfefefefeccccccccfcfcfcfccccccccceeeeeeeecccccccccccccccccccccccccccc0000cccccccccc00cc00ccccccccc0c0c0c0 else (if i < 26 then 0xdddddddd00000000dddd8888ffff0000dcdcdcdcdcdcdcdcdcdcdcdcccccccccdcdcdcdc54545454dcdcdcdc50505050d8d8d8d8fafafafad8d8d8d8f0f0f0f0d8d8d8d8d8d8d8d8d8d8d8d850505050d0d0d0d0f2f2f2f2d0d0d0d0f0f0f0f0d0d0d0d0dcdcdcdcd0d0d0d0d0d0d0d0d0d0d0d050505050cfcfcfcfcececece else 0xeeeeeeee22222222eeeeeeee00000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee8888eeee8888eecceecceecceecceeaaeeaaeeaaeeaaee88ee88ee88ee88ececececececececececececccccccccddddffffccccccccddddddddeeeeeeeeddddddddccccccccddddddddaaaaaaaadddddddd88888888dddddddd22222222)) else (if i < 28 then 0xf0f0f0f032323232f0f0f0f030303030f0f0f0f010101010f0f0f0f000000000efefefefaaaaaaaaef88ef88ef88ef88eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeaaeeaaeeeeeeeecccccccceeeeeeeeaeaeaeaeeeeeeeeeaaaaaaaaeeeeeeee88888888eeeeeeee66666666eeeeeeee44444444 else (if i < 29 then 0xf0f0f0f0fefefefef0f0f0f0fcfcfcfcf0f0f0f0fafafafaf0f0f0f0f8f8f8f8f0f0f0f0f6f6f6f6f0f0f0f0f4f4f4f4f0f0f0f0f2f2f2f2f0f0f0f0f0faf0faf0f0f0f0f0f0fcfcf0f0f0f0f0f0fafaf0f0f0f0f0f0f0f0f0f0f0f0d8d8d8d8f0f0f0f0d0d0d0d0f0f0f0f074747474f0f0f0f070707070f0f0f0f050505050 else 0xf3f3f3f300000000f2f2f2f2fefefefef2f2f2f2fafafafaf2f2f2f2f2f2f2f2f2f2f2f2f0f0f0f0f2f2f2f2d0d0d0d0f2f2f2f250505050f0f6f0f6f0f6f0f6f0f4f0f4f0fcf0fcf0f4f0f4f0f4f0f4f0f2f0f2f0faf0faf0f2f0f2f0f2f0f2f0f0f6f6f0f0f6f6f0f0f4f4f0f0fcfcf0f0f4f4f0f0f4f4f0f0f2f2f0f0f2f2))) else (if i < 33 then (if i < 31 then 0xf8f8f8f8f0f0f0f0f8f8f8f870707070f8f8f8f850505050f8f8f8f800000000f7f7f7f700000000f6f6f6f6f6f6f6f6f6f6f6f6f0f0f0f0f5f5f5f500000000f4f4f4f4fcfcfcfcf4f4f4f4f8f8f8f8f4f4f4f4f4f4f4f4f4f4f4f4f0f0f0f0f4f4f4f4b0b0b0b0f4f4f4f454545454f4f4f4f430303030f4f4f4f400000000 else (if i < 32 then 0xfafafafad8d8d8d8fafafafac8c8c8c8fafafafaaaaaaaaafafafafa72727272fafafafa50505050fafafafa32323232fafafafa10101010fafafafa00000000fafaf8f8fafaf8f8fafaf8f8fafaf0f0faf8faf8faf8faf8faf8faf8faf0faf0f8f8f8f8fcfcfcfcf8f8f8f8fafafafaf8f8f8f8f8f8f8f8f8f8f8f8f4f4f4f4 else 0xfcfcfcfc30303030fcfcfcfc10101010fcfcfcfc00000000fcfcf8f8fcfcf8f8fcf8fcf8fcf0fcf0fbfbfbfb00000000fafafafafefefefefafafafafcfcfcfcfafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafafaf0faf0fafafafaf8f8f8f8fafafafaf2f2f2f2fafafafaf0f0f0f0)) else (if i < 34 then 0xfdfdfdfdccccccccfdfdfdfd00000000fcfcfcfcfefefefefcfcfcfcfcfcfcfcfcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfcfcf0fcf0fcfcfcfcf8f8f8f8fcfcfcfcf4f4f4f4fcfcfcfcf0f0f0f0fcfcfcfcdcdcdcdcfcfcfcfcccccccccfcfcfcfcb8b8b8b8fcfcfcfca8a8a8a8fcfcfcfc54545454fcfcfcfc50505050 else (if i < 35 then 0xfefefefef6f6f6f6fefefefef2f2f2f2fefefefef0f0f0f0fefefefedcdcdcdcfefefefeccccccccfefefefebabababafefefefeaaaaaaaafefefefe76767676fefefefe54545454fefefefe36363636fefefefe32323232fefefefe10101010fefefefe00000000fefef8f8fefef8f8fef8fef8fef8fef8fdfdfdfdfcfcfcfc else 0xff0aff0aff00ff00ff08ff08ff08ff08ff04ff04ff00ff00ff00ff00ffffff88ff00ff00ffffff00ff00ff00ff88ff88ff00ff00ff55ff00ff00ff00ff00ff00ff00ff00ee00ee00ff00ff0077007700fefefefefefefefefefefefefefeccccfefefefefefeaaaafefefefefcfcfcfcfefefefefafafafafefefefef8f8f8f8)))) else (if i < 42 then (if i < 39 then (if i < 37 then 0xff77ff00ff77ff00ff66ff66ff00ff00ff55ff44ff55ff00ff55ff00ff55ff00ff54ff54ff00ff00ff44ff44ff88ff88ff44ff44ff00ff00ff33ff22ff33ff00ff33ff00ffffff00ff33ff00ff33ff00ff32ff32ff00ff00ff30ff30ff00ff00ff22ff22ff88ff88ff22ff22ff00ff00ff11ff00ff11ff00ff10ff10ff10ff10 else (if i < 38 then 0xffccff88ffccff88ffccff88ffccff00ffc8ffc8ff00ff00ffaaffaaffaaffaaffaaffaaffaaff00ffaaffaaff88ff88ffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaaaa00aa00ffaaffaa00000000ffaaff88ffaaff00ff88ff88ff88ff88ff88ff88ff00ff00ff88ff88ee88ee88ff88ff8877007700ff88ff8800000000 else 0xffeeffeeffccffccffeeffeeffaaffaaffeeffeeff88ff88ffeeffeeff00ff00ffeeffeeeeeeeeeeffeeffeeeecceeccffeeffeeccccccccffeeffeeaaaaaaaaffeeff88ffeeff88ffccffccffccffccffccffccffccff00ffccffccff88ff88ffccffccff00ff00ffccffccee00ee00ffccffccccccccccffccffcc00000000)) else (if i < 40 then 0xffff0808ffff0808ffff0202ffff0000ffff0000ffff8888ffff0000ffff0000ffff000077770000fffefffeff00ff00fffcfffcff00ff00fffcfffcf0f0f0f0fffafffaff00ff00fffafffafaf0faf0fffafffaf0f0f0f0fff8fff8ff00ff00fff8fff8f0f0f0f0fff4fff4ff00ff00fff0fff0ff00ff00ffeeffeeffeeffee else (if i < 41 then 0xffffaaaaaaaa0000ffffaa88ffffaa88ffffaa88ffffaa00ffffa8a8ffff0000ffff8888ffff8888ffff8888ffff0000ffff888877770000ffff888800000000ffff6666ffff0000ffff5454ffff0000ffff4444ffff8888ffff4444ffff0000ffff3232ffff0000ffff3030ffff0000ffff2222ffff0000ffff0a0affff0000 else 0xffffeeeeeeeeeeeeffffeeeeeeeeaaaaffffeeeeccccccccffffeeeeaaaaaaaaffffee88ffffee88ffffccccffffccccffffccccffffcc00ffffccccffff8888ffffccccffff0000ffffccccccccccccffffcccc00000000ffffcc88ffffcc88ffffaaaaffffaaaaffffaaaaffff8888ffffaaaaffff0000ffffaaaaaaaaaaaa))) else (if i < 45 then (if i < 43 then 0xfffffcfcfcfcf0f0fffffcfcf0f0f0f0fffffafaffffaaaafffffafaffff0000fffffafaf0f0f0f0fffff8f8ffff0000fffff8f8f0f0f0f0fffff4f4ffff0000fffff2f2ffff0000fffff0f0ffff0000ffffef88ffffef88ffffeeeeffffeeeeffffeeeeffffccccffffeeeeffffaaaaffffeeeeffff8888ffffeeeeffff0000 else (if i < 44 then 0xffffffaaffffee00ffffffaaffffaa00ffffffaaffff0000ffffffaaff00ff00ffffff88ffffff88ffffff88ffffff00ffffff88ffffee88ffffff88ffff0000ffffff88ff00ff00ffffff44ffffff00ffffff22ffffff00ffffff00ffffff88ffffff00ffffee00fffffefeffff0000fffffcfcffffccccfffffcfcffff0000 else 0xffffffff08080808ffffffff04040404ffffffff02020202ffffffff00cc00ccffffffff0000ccccffffffff0000aaaaffffffff00000000fffffffcffffff00fffffffaffffff00ffffffeeffffff00ffffffccffffff00ffffffccffff0000ffffffccffccff00ffffffccff00ff00ffffffaaffffff88ffffffaaffffff00)) else (if i < 46 then 0xffffffffaaaaaaaaffffffffaaaa0000ffffffffaa88aa88ffffffffaa00aa00ffffffffa8a8a8a8ffffffff88888888ffffffff66666666ffffffff54545454ffffffff50505050ffffffff44444444ffffffff32323232ffffffff30303030ffffffff22aa22aaffffffff2222aaaaffffffff22222222ffffffff0a0a0a0a else (if i < 47 then 0xfffffffffafa0000fffffffff8f8f8f8fffffffff4f4f4f4fffffffff2f2f2f2fffffffff0f0f0f0ffffffffeeeeeeeeffffffffeeeeccccffffffffeeee8888ffffffffeeaaeeaaffffffffee88ee88ffffffffccccccccffffffffcccc8888ffffffffcccc0000ffffffffcc00cc00ffffffffc8c8c8c8ffffffffaeaeaeae else 0xffffffffffffccccffffffffffffaaaaffffffffffff8888ffffffffffff0000ffffffffffaaffaaffffffffff88ff88ffffffffff00ff00fffffffffefefefefffffffffcfcfcfcfffffffffcfc0000fffffffffafafafafffffffffafaaaaa))))))
def g1_bW (i : ℕ) : ℕ := fld (g1_bChunk (i / 16)) 64 (i % 16)
def g1_decAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => g1_bW (x &&& 1023) :: g1_decAux n (x >>> 10)
def g1_decSt (x : ℕ) : List ℕ := g1_decAux (x &&& 15) (x >>> 4)
def g1_l2C (_ : ℕ) : ℕ := 0x0000000000002e5b223330000000000002c9ae63530000000000002c9a963530000000000002f0b1d833
def g1_l2S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l2C (i / 8)) 84 (i % 8))
def g1_l2HC (_ : ℕ) : ℕ := 0x61dbfc5d4cf57a294ac282ca20a5edda
def g1_l2H (i : ℕ) : ℕ := fld (g1_l2HC (i / 32)) 32 (i % 32)
def g1_l3C (i : ℕ) : ℕ := (if i < 3 then (if i < 1 then 0x0000000000baa8b9b1c540000000000b66a08e1c540000000000b7e38714b4400000000009f2437156b40000000000bda7c9adc540000000000b9a7c9c1c540000000000baa7c9b5c5400000000009f25a7156b4 else (if i < 2 then 0x0000000000b7e7c714b640000000000b96c88694540000000000a4638714b040000000000baa98965c5400000000009f263714eb40000000000baa91991c540000000000a82387151a400000000009f25a714b34 else 0x0000000000b66878e1c540000000000b267c7148340000000000ba6a28e1c540000000000b7ebf7158340000000000bc2ac8e18340000000000b7ec0a8e1c40000000000bde7c9a9c5400000000009f2387152a4)) else (if i < 5 then (if i < 4 then 0x0000000000a2e387148040000000000b667c939c540000000000a1638715a4400000000009f2387147d40000000000a4a387156b40000000000bcec8ac54540000000000b267c94a3540000000000b26c886d454 else 0x0000000000b267c8d5ba40000000000b7eac8e23440000000000b269b9523540000000000a4a38714b340000000000b26ad8e23440000000000b9a7c9523540000000000b9e7c9bdc540000000000bbead8e1834) else (if i < 6 then 0x0000000000bbec760d4540000000000b26c88cd8340000000000baaa0951c5400000000009f26c7151a40000000000b667c9b1c540000000000baaa18e1c5400000000009f25471480400000000009f1c5514384 else 0x0000000000ba2a48e1c540000000000b26b9715b9400000000009f1c56e44240000000000b26bba923540000000000b2638714814)))
def g1_l3S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l3C (i / 8)) 84 (i % 8))
def g1_l3HC (i : ℕ) : ℕ := (if i < 1 then 0x7825dd9f76334b73723dfed47007eefd6dffd7516ae09c006a7b8086621ae3c25f74d03a5f3943bd5b6fbfbe4e54d95547d9481e431af3823f633fb83cf2c0403cd5d43f3c161c673759a23d32dfca29309a398f2b06eb322a6a4f892788692627610fa42733e8922182aaec1f397c5f1e40502514571a5312ef18cb08972966 else 0xfe98ab5edfaee55eddd5894fddadb558d8f610b3cded5bedcc30d8a4c82b1ba8af54eee1ac1e87eaa8f03e829dda8900958b525b95571df6905f47778fba554f8cf1171188437bfe87f471987b2d17b57add753a)
def g1_l3H (i : ℕ) : ℕ := fld (g1_l3HC (i / 32)) 32 (i % 32)
def g1_l4C (i : ℕ) : ℕ := (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x00000002c99f2386e4fe500000002df9f23887147500000002c9a2e38715b1500000002da9f2386e4c7500000002c9a4e38715b85000000027c8e20f514b2500000002da9f2386e4d5500000002e598dc5514a65 else (if i < 2 then 0x00000002c9ab2388d145500000002e59f26375545500000002c99f1c53e046500000002e58e1c5514e3500000002df8e1c56d4e1500000002d39f25971583500000002df9f2598d583500000002818e1c5514b25 else 0x00000002dfb069271583500000002dfa465471583500000002df9f2598c983500000002e59f26471487500000002e5a5e3871545500000002dfa46388c9b5500000002c99f238568f8500000002df9f238795b55)) else (if i < 5 then (if i < 4 then 0x00000002c9a6264715b9500000002c9a2e38731b9500000002e5a5e38514d5500000002c9a2e387c4f85000000027c8e1c55ad41500000002a08e1c560c7e500000002da9f238714f8500000002e59f249715455 else 0x00000002f1ab23851456500000002e59f2637748c500000002858e1c560ced500000002e5b169a71545500000002c9ab23881583500000002e59f238839455000000027c8e1833b499500000002e5a5e38514c75) else (if i < 6 then 0x00000002f3ac6b08e145500000002f79f25771583500000002c9a2e388d46d500000002c9a2e38771b9500000002d69f26471545500000002e5a5e3871425500000002dfaca388d583500000002d2a4638715835 else 0x00000002e59f263865455000000027c8e145354b25000000027c8e21760ced500000002e59f27951490500000002df9f25981cc4500000002c9a4a3881db9500000002c99f638715b95000000027c8e1c5514b25))) else (if i < 10 then (if i < 8 then 0x00000002c99f253714f8500000002dfb01c560c10500000002df9f2388d409500000002e59f26372545500000002df8e1c52a02a500000002d19f242714be500000002da9f23881db95000000027c8e14531cb25 else (if i < 9 then 0x00000002e59f2497148c500000002e59f2388d5b35000000027c8e1f060ced500000002e59f25a715b35000000027c909c560ced500000002e59f238514d3500000002e5a5e387148c500000002c99f1c51d03e5 else 0x00000002dfa463860ccf500000002dfa8e3871578500000002da9f238714fa500000002c9a4a38809b9500000002df9f2388c1b5500000002978e1c56ccb2500000002c9a2e387bdb9500000002c99f2546e49a5)) else (if i < 12 then (if i < 11 then 0x00000002eab267c99207500000002da9f238809b9500000002c99f238514b8500000002e5a5e3881d45500000002cbac23887145500000002e5a5e3881c245000000027c8e1db514b2500000002c99f638714f85 else 0x00000002dfa463860cc7500000002da9f23881cf8500000002e59f24981d45500000002e5a823871414500000002dfa463860cd5500000002ea9f254715ae500000002df9f2388addc500000002c99f25473db95) else (if i < 13 then 0x00000002c9a2e38735b9500000002928e1c560ce7500000002c9a6a38715ac500000002e5a5e38859b35000000027c8e1c52c88c500000002f3ac238514905000000027c8e21c60ced5000000027c8e1be514b25 else 0x00000002da9f1c56e446500000002c99f238354b8500000002daa4a38715b9500000002e5a5e3880945500000002dfa45c560ce55000000027c8e1f35a945500000002dfab2388ae07500000002e5a3663715455)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x00000002c99f63881db9500000002bba2dc56e518500000002c99f23831cb8500000002e5a5e3881cc7500000002dfa463876d83500000002e59f2795141d500000002c99f238648f8500000002df9f23889d835 else (if i < 16 then 0x00000002c99f2546e507500000002918e1c53b4c4500000002e59f26351493500000002df9f24280183500000002daa2e387c5b9500000002c99f23a8d5b95000000027c8e1c55a48d5000000027c8e14516c565 else 0x00000002c99f264715485000000027c8e9c5610e6500000002df9f23879db5500000002c99f264715b95000000027c8e2166ccb2500000002df9f26c8d583500000002e9a5e3871545500000002eeaaa3860d455)) else (if i < 19 then (if i < 18 then 0x00000002e59f26271545500000002f1b1eac60d455000000027c8e202514b2500000002df9f24560c9a500000002e5a5dc551446500000002e59f2388a945500000002e5a5e3881c8c5000000027c9660060ced5 else 0x00000002df9f27760c9a500000002c9a2e63715b9500000002dfa463881d83500000002c9b169a871455000000027c8e1c5610ec500000002f1b7eac8e1835000000027c8e20731cb2500000002dfa463860cd85) else (if i < 20 then 0x00000002c99f2387948b5000000027c951c56e518500000002df9f25a715b5500000002dfafa5971583500000002c9a2e387ddb95000000027c8e1831641c5000000027c8e2316ccb2500000002e5a8238715b35 else 0x00000002da9f253715b9500000002df9f26a965c5500000002da9f2388d417500000002dfab2388d583500000002e69f254715b95000000027c8e1e560ced500000002e59f2638714550000000238715833b4e15))) else (if i < 25 then (if i < 23 then (if i < 22 then 0x000000027c715452c846500000002c99f2383e09a500000002928e1c5514b2500000002e5b7e928e21c500000002c99f259714f85000000027c8e2072c88c5000000027c98dc568c14500000002df9f2388c9b55 else 0x00000002c9aee8b7c5b9500000002da9f638715b9500000002c99f1c56e476500000002dfa4638800c45000000027c8e1c5688c4500000002918e1c52b00c500000002e5a623871545500000002dfa0e3860c9a5) else (if i < 24 then 0x00000002e5a5e5371545500000002c99f238894d55000000027c951c5460f8500000002dd9f25c71583500000002c9a2e38801b95000000027c8e1c55f0e8500000002ac8e1835145b500000002c9aedc56e4225 else 0x00000002c99f1c56e4a2500000002c9aedc56e4a5500000002c99f26481db9500000002c99f23842817500000002ea9f26371541500000002df9f25972183500000002dfa063871583500000002c99f26f715a95)) else (if i < 27 then (if i < 26 then 0x000000027c965c560d6c500000002dfa2e5971583500000002dd9f25481d835000000027c8e1c5504b3500000002c9a6e54715b9500000002dfa826c71583500000002df9f26d71583500000002f59f269715455 else 0x00000002f1ab23860ce9500000002c99f23841cf8500000002c99f2547c5b9500000002d4a0a38871455000000027c94dc5514b2500000002c99f2388bdb15000000027c8e1e45a9455000000028b8e1c5520ab5) else (if i < 28 then 0x00000002e59f27987145500000002df9f23860c5b5000000027c8e1831680d500000002dfa063876d83500000002e59f263795455000000027c952076e518500000002df9f259871b5500000002df9f259870165 else 0x00000002c9a2e386e490500000002c99f1c56e445500000002e5a623881d45500000002c99f23860cf55000000027d8e1c5514b2500000002c99f254715b1500000002df9f2388ae00500000002e59f23883d455))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then 0x00000002f39f27985145500000002e5b7e7c8e235500000002c99f254731b95000000027c8e1c5460f8500000002e5a666371545500000002eca9e3860d455000000027c8e1452c89e500000002dfa5e59715835 else (if i < 31 then 0x00000002c99f2548d46d500000002c99f254771b9500000002da9f259715b95000000027c8e18a60d45500000002da9f264715b9500000002e5b7e7c8e232500000002dfa063881d83500000002e5a12387148c5 else 0x00000002da9f23873db95000000027c8e1e760ced500000002f3ac2388a583500000002df9f2386d46e500000002e5a2e38715b3500000002c99f1c53e045500000002e29f26671545500000002e5a123881d455)) else (if i < 34 then (if i < 33 then 0x000000027c8e1c54b016500000002e5a5e59715455000000027c98dc55a945500000002c99f26c714f8500000002c9a2e4c715b95000000027c8e1ce5a945500000002dfaae918e1835000000027c8e21c488ed5 else 0x00000002df9f27781c56500000002df9f23860d01500000002df9f2597143c500000002918e1c560d1c500000002df9f25985983500000002c99f238715b1500000002c99f23a81d84500000002e5a5e38514d45) else (if i < 35 then 0x000000027c8e23260ced500000002b08e21c63d45500000002e5a5e38715b35000000027c8e1c5500ab500000002c99f2547bdb9500000002df9f25a715b95000000027c8e1833a45b5000000027c8e23560ced5 else 0x00000002f69f26171545500000002c99f264861b9500000002c99f2382e0145000000027c8e1835145d500000002e5a5e3881c14500000002e59f249715b3500000002c9acdc560d45500000002e5a5e3b715455))) else (if i < 39 then (if i < 37 then 0x000000027c8e1452c89a500000002e5aa238795455000000028b8e1c56e4b5500000002e5b1697871455000000027c965c5514b2500000002e5b7e7c9661c500000002c9a2e3a715b9500000002da9f2386e5075 else (if i < 38 then 0x00000002e5b7ea08e1c5500000002c99f2386e49c500000002e5b0a9771545500000002dfb0291715b5500000002dfa463971583500000002e5a5e6571545500000002a08e1c560d69500000002dfa4638819835 else 0x000000028b8e1f16e518500000002e59f23884d45500000002df9f1c560d0e5000000027c8e2072c8145000000027c8e2073b4c45000000027c715452c8435000000027c8e1c56ccb2500000002c99f254735b95)) else (if i < 41 then (if i < 40 then 0x00000002e59f238859b3500000002e4a2e38715b9500000002dfa465971583500000002e5a623886145500000002d8a1a3860d45500000002dfa466471583500000002da9f2547c5b9500000002c9aee9a715b95 else 0x00000002dfab27781d83500000002c99f238770f8500000002df9f2386d4cd500000002dea8a38715835000000027c715b910020500000002c9a2e54871b9500000002f19f2388adfd500000002dfab23860c1c5) else (if i < 42 then 0x00000002e59f238729b3500000002e5a5e385146c5000000027c8e18351463500000002e5a5e3881db3500000002e59f263715b65000000029798dc5514b25000000027c9661c60ced5000000027c8e145150165 else 0x00000002e5a5e5571545500000002dfa2a59715835000000027c951c56e4f2500000002e5a5e6385945500000002dfa5e38715b55000000027c8e1c547c7b500000002e58e1c5514e4500000002da9f26c715b95)))) else (if i < 50 then (if i < 46 then (if i < 44 then 0x00000002c99f266715b6500000002e59f2388a4085000000027c8e2076ccb2500000002c99f25a714c1500000002c99f238790f8500000002dfa625971583500000002988e1c56e4ab500000002c99f2387bcf85 else (if i < 45 then 0x00000002da9f2387c5b95000000027c8e21c639455000000027c8e1c54ac17500000002f3b967c8e2295000000027c715450d80a5000000027d8e1c56e518500000002c99f23854cb8500000002c9a2e387142f5 else 0x00000002dfad68171583500000002e5b15c5514a6500000002c9a2e38871b95000000027c98dc5514f3500000002df9f26f71576500000002dfa4a3881d83500000002c99f254801b9500000002df9f1c560c445)) else (if i < 48 then (if i < 47 then 0x00000002c99f25a8d5b9500000002da9f238715b1500000002d99f238714f6500000002df9f27a81d83500000002f59f25871583500000002c9a2e3887148500000002c9a2e38745b9500000002dfa465981d835 else 0x00000002df9f2598c9b5500000002e59f2798d5455000000027c8e1c539cbe500000002c99f2388a1b95000000027c909c55a416500000002c98e1c56e479500000002c99f2387a927500000002c99f2548d5a85) else (if i < 49 then 0x00000002da9f238731b95000000027c8e18316c59500000002da9f2387c4f8500000002e5a6264715455000000027c951c5520ab500000002df9f238859b5500000002e59f2388c470500000002e5a5e387c5455 else 0x00000002e5ac23885945500000002c9a2e38870f8500000002e59f238514d2500000002d1a4a38715835000000027c8e1452c895500000002e59f263871b3500000002e59f2388b5b3500000002e58e1c5515155))) else (if i < 54 then (if i < 52 then (if i < 51 then 0x00000002da9f2388d46d500000002df9f1c56d4db500000002df9f238729b5500000002da9f238771b9500000002e5a6238715b3500000002df9f2597143b500000002df9f25982d83500000002e5a2a38715b35 else 0x00000002e59f27a81d455000000027c8e1835585b500000002c99f2546e490500000002c99f6387c5b95000000027c8e1f1514b2500000002c9a7e8b8e1c5500000002df9f2388ae1c500000002dfa0659715835) else (if i < 53 then 0x00000002e5b15c551421500000002d4ac23887145500000002c99f638715b15000000027c8e145320b2500000002c99f254751b9500000002c0a45c560ced500000002e59f27279545500000002ea9f25a7157a5 else 0x00000002e59f238528d5500000002da9f2387bdb9500000002978e1c5514f1500000002e5a1238715b3500000002e5a6238715b9500000002df9f27780183500000002e5a5e3877145500000002e59f238785455)) else (if i < 56 then (if i < 55 then 0x000000028b8e1c560ced500000002df9f25971583500000002df9f26c8b583500000002e59f254715b3500000002df9f25960ccf500000002e5a7a978e1c5500000002c99f2384286d500000002c9a3a5481d835 else 0x00000002eab268b8e235500000002df9f25960cc7500000002df9f25960cd55000000027c8e1833b4cd5000000027c8e1c56e51b500000002c99f238800f8500000002c99f638731b95000000027c8e1cc514b25) else (if i < 57 then 0x00000002d6a5e3871487500000002e5a8a978e207500000002dfb029180183500000002c99f23872cf8500000002c99f23889945500000002da9f238735b9500000002e5a5e387bd45500000002e59f2388a4905 else 0x00000002df9f25976d83500000002c9a8a38715ad500000002c99f2387e8d5500000002978e1c560ced5000000027c8e1c51e811500000002e59f24979145500000002dfa76918e1c5500000002e5a5e38714885)))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then 0x000000027c8e1c55a148500000002dfa6238715b5500000002f39f2798a5835000000027c8e1c55e8eb500000002e59f26d715b35000000027c8e18355545500000002d8ac23860d455000000027c925c560ced5 else (if i < 60 then 0x000000027c8e1ef514b2500000002e5a5e3873545500000002daa2e38871b9500000002918e1c5689835000000027c965c53b4c4500000002e59f26471545500000002e29f26f71545500000002c9b22b1871455 else 0x00000002e59f238715b3500000002c99f2383e090500000002c99f238514b95000000027c8e1e4514b25000000027c8e21c5a945500000002dfb267c8e0b8500000002e5b7e978e207500000002dfa4638771835)) else (if i < 63 then (if i < 62 then 0x00000002e59f2388a41d5000000027c951f16e518500000002e59f2386ccc7500000002e59f2386ccd5500000002dfa463881db5500000002e5a5e38715b7500000002c9a2e548d5b9500000002df9f25960cd85 else 0x00000002df9f25a871835000000027c8e21660ced500000002df9f23881cb2500000002c99f638735b9500000002dfaf659715835000000027c8e1cd514b2500000002e5a5e4d71545500000002eaa62387153c5) else (if i < 64 then 0x000000027c9e58351454500000002df8e1c560d14500000002df9f259800c45000000027c965c52b00c500000002dfaca3881d83500000002e5a5dc5514a1500000002dfa463879cc4500000002e5a5e38739455 else 0x00000002c99f23a715b95000000027c715833b4db5000000027c8e1c51fc145000000027c8e1ca60ced500000002c9aee8b871b9500000002e59f238520d5500000002da9f238801b9500000002c9b16a281d835))) else (if i < 68 then (if i < 66 then 0x00000002c9ac63886945500000002d79f2387f583500000002da9f23872db95000000027c8e1ce514b25000000027c8e1c54887e5000000027c8e1e55a945500000002f3aca3860d45500000002df9f26c715835 else (if i < 67 then 0x00000002ea9f26c71520500000002e5a5e3880145500000002e59f23881db3500000002e1b7e7c8e235500000002e4a6a38715455000000027c98dc5514b2500000002e5b7e7c8e22d500000002c9a2e388d5b95 else 0x00000002918e1c560ced500000002dfb01c560cdf500000002c99f238724f8500000002c99f23a714f8500000002e5aca3881d45500000002e59f26371489500000002978e21c514b25000000027c8e1f2514b25)) else (if i < 70 then (if i < 69 then 0x00000002df9f1c528c3a5000000027c8e1c56c518500000002c99f25487148500000002d4a0a3860d45500000002e59f26385945500000002e5a5e637148c500000002c99f254871b9500000002df9f2386d4cf5 else 0x00000002dfa063877183500000002dfab23860cc7500000002d99f238715ae500000002c9a2e388d4f8500000002e59f238809b3500000002818e1c568983500000002df9f2386d4c7500000002df9f2386d4d55) else (if i < 71 then 0x00000002c9aeea4715b9500000002c99f23a81db9500000002df9f1c560ca4500000002df9f2388d62b500000002e5ac238514d5500000002d19f238715b0500000002dfa823887183500000002e5a5e6381d455 else 0x00000002c9a62387148b5000000028a8e1c560ced500000002df9f259861835000000027c8e1c56b91a500000002ac8e20760c5a500000002c9a5254715b9500000002df9f23876db5500000002c9951c56e5115)))) else (if i < 79 then (if i < 75 then (if i < 73 then 0x000000027c8e22b5145b500000002c9ae254715b95000000027d8e1c5520ab500000002f8b96c571545500000002e5a5e3877545500000002dfab23860c0d500000002df9f26c81d83500000002e59f1c56cc465 else (if i < 74 then 0x00000002dd9f254715b9500000002df9f2386d4d8500000002ac8e183514e9500000002f3ac23860d45500000002c9a2e3874db9500000002dfa4638801835000000027c8e1c568983500000002e59f2388a61c5 else 0x00000002eab26928e21c5000000027c8e1452c890500000002c99f242714f8500000002e59f26898dc5500000002d6a123871487500000002df9f23881db5500000002df9f23876983500000002e5a8238871455)) else (if i < 77 then (if i < 76 then 0x00000002e59f26c81d455000000027c951c560ced500000002e59f26486145500000002ebac23860d45500000002c99f26b951c5500000002fab7ec071583500000002dfab23881d835000000027c965c560d1c5 else 0x00000002df9f238809b5500000002f2ac23860d45500000002da9f23a715b9500000002c9aee9381d83500000002dfa45c560c2c500000002e59f24b87145500000002c9a2e387a9b9500000002e59f253715b35) else (if i < 78 then 0x00000002df9f27596583500000002daa2e388d5b9500000002818e1c560ced500000002e5b0e9771545500000002c9a8638715b9500000002eab267c95235500000002df9f25987090500000002da9f238725b95 else 0x00000002e5a5e3872545500000002c9a2e387a8f8500000002c99f238771b15000000027c8e21160ced500000002dfb0291871835000000028b8e1c51e817500000002c99f2547d5b9500000002c9a2e5f715b95))) else (if i < 83 then (if i < 81 then (if i < 80 then 0x00000002c99f254715885000000027c8e145150085000000027c9b1c55147f500000002dfa4659715b5500000002c98e1c5444f85000000027c8e1dd2c88c500000002e79f259715835000000027c991c56e4ab5 else 0x00000002c9a2e386e50a500000002dfa464c71583500000002dfa46387142b500000002f9b26bb715b9500000002df9f25960c9a5000000027c8e21451454500000002da9f254871b95000000028b8e21c6e5185) else (if i < 82 then 0x00000002dfa063880183500000002dfa4a38714be5000000027c8e1c5398c15000000027c8e18351449500000002c99f63a715b95000000027c8e9c5514b2500000002ac8e20760ce95000000027c8e1c5680be5 else 0x00000002e5a5e3851493500000002c9a4a38871b9500000002c9a2e386e502500000002e5a5e3871d455000000027c951c56e484500000002c99f2547143f500000002c9aee8b8d5b9500000002c9a62388d5b95)) else (if i < 85 then (if i < 84 then 0x000000027c7158351442500000002da9f238871485000000027c8e1c567cc1500000002e59f2386ccd4500000002c9a2e41715b9500000002e59f259715b3500000002c9a2e386e46d500000002df9f259870c45 else 0x00000002978e1c568c14500000002f1ab27760d45500000002e59f263514c7500000002dfb1aa071583500000002c9a2e3881d875000000027c8e1c56d51c5000000027c8e20760ced500000002c99f2548d5b95) else (if i < 86 then 0x00000002d7ab23860d45500000002df9f2778ae07500000002e59f1c551437500000002daa8638715b9500000002dfa82388d583500000002e59f249871455000000027c929c560ced500000002da8e1c56e5115 else 0x00000002eaa5e3871541500000002c99f254871a9500000002c99f63887148500000002c99f254761b9500000002e59f26c71414500000002c98e1c5514b45000000027c8e2003b4c45000000027c8e145240545))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then 0x00000002df9f259715b5500000002e5a5e388708c5000000027c98dc56ccb2500000002f1b7e7c9dd835000000027c8e1c54f8af500000002c99f23860d2e500000002e59f2637148c500000002dfa4642715835 else (if i < 89 then 0x00000002eab6a7c8e235500000002c9a8254715b9500000002c9ade8b715b9500000002dfb02a37158350000000238715b90c422500000002c9aedc56e511500000002e59f26381d45500000002df9f2597c5835 else 0x00000002c9a2e388d42e500000002978e1c569545500000002c9a2dc56e50b500000002c9ad27d715b9500000002dfb0291714c4500000002c9a2e387154c500000002e59f263859b3500000002e59f249795455)) else (if i < 92 then (if i < 91 then 0x000000027c8e9c56e518500000002da9f2388c1b9500000002c99f2547a9b9500000002c9a2e38889b95000000027c8e1e5514b25000000027c8e14514c1d5000000027c8e1c5690c2500000002e59f26c715b35 else 0x00000002da9f2548d5b95000000028b8e2356e518500000002c99f264871b9500000002c99f2387a4f8500000002c9a9238715ab500000002c99f25c715aa500000002eab267c8e10a500000002e5abe978e1455) else (if i < 93 then 0x000000027c8e21d60ced5000000027c925c55a945500000002dfab23881183500000002c99f2547a8f85000000027c8e1c568d7f5000000027c951c51e817500000002cba5e3887145500000002e59f2387c5b35 else 0x00000002e8a2e38715b9500000002f1ab23860c015000000028b8e1c56e482500000002df9f2597bd83500000002c9b221a60d45500000002df9f2386d46f500000002c9a2e388b5b9500000002c9aa68b8e1b95))) else (if i < 97 then (if i < 95 then 0x00000002f4aca3860d45500000002c99f23a7c5b9500000002d19f238714f7500000002c9a8238714f8500000002c9a2e386e4fc500000002c99f2546e50a500000002e5b169771545500000002dfa0642715835 else (if i < 96 then 0x00000002d19f259714be500000002da9f2388d5b95000000027c8e2165a945500000002c99f254885b9500000002c99f23a715b1500000002df9f2388d5fe5000000027c969c560ce7500000002df9f259735835 else 0x000000027c991c560ced500000002c99f2546e46d500000002df9f238714f9500000002848e1c568c14500000002d59f2388ad45500000002c99f2387a8f8500000002c99f1c5514b6500000002c9a2e54715b95)) else (if i < 99 then (if i < 98 then 0x00000002dfab23881c56500000002df9f25973983500000002c99f2386e528500000002c98e1c56e513500000002df9f27696583500000002e5a5e388d545500000002e59f2387bdb3500000002c99f23a731b95 else 0x00000002e5a5e47715455000000027c8e2075a4b25000000027c8e1c51ec0c500000002c9a2e54714f8500000002c9a5e54715b9500000002e5b7e7c99207500000002c99f2386e50a500000002da9f2388d4f85) else (if i < 100 then 0x000000027c8e1c56d5a2500000002dfa863871583500000002c9a2dc56e517500000002c99f6388d5b9500000002c99f23885db1500000002c9a2e386e46b500000002c99f1c56e441500000002e59f238735b35 else 0x00000002c9a2e386e4d5500000002f3ac23851416500000002daa8238715b95000000027c8e1c548080500000002df9f238771b5500000002c9a2e38715b95000000027c8e1e660ced500000002c99f238428f85)))) else (if i < 108 then (if i < 104 then (if i < 102 then 0x00000002dfa46388c983500000002c9a928b8e235500000002e59f238739b3500000002e5b7e7c9b1c55000000027c9660760ced500000002e59f263514d4500000002978e216514b25000000027c9b1c560d695 else (if i < 103 then 0x00000002dfa463874983500000002e5a5e387d945500000002c99f2383e06d500000002da9f2387a9b9500000002c9a2e38714f8500000002c9a4a3871584500000002c99f23a735b9500000002c99f23849cf85 else 0x00000002c98e1c56e4a7500000002da9f2387a8f8500000002daa2e54715b9500000002dfb1eac81d835000000027c8e21c6ccb2500000002c9a5e38714f8500000002c99f2387a811500000002c9aedc56e4305)) else (if i < 106 then (if i < 105 then 0x00000002c99f1c56e50d500000002e59f1c5514de500000002e5b15c551427500000002dfb01c560ca8500000002c9a2e38714fa500000002c9b0692715b95000000027c8e1c54a411500000002da9f2388d4115 else 0x00000002c9a2dc56e446500000002c9a2a54715b9500000002c99f2548b5b9500000002df9f23889183500000002e5a5e385146a500000002df9f2388ac09500000002da9f2386e50a5000000027c952356e5185) else (if i < 107 then 0x00000002c99f270715a8500000002c9a2e67715b9500000002c99f1c542cf8500000002da9f2386e46d500000002c99f2546e4fc500000002daa2e38715b9500000002dfa82388b583500000002c99f2383548a5 else 0x00000002c9aedc56e477500000002c99f273951b9500000002c9a2e53715b9500000002c9a2e388d417500000002ea9f238715b2500000002c9a2e3c715b9500000002daa2e38714f8500000002daa5e38715b95))) else (if i < 112 then (if i < 110 then (if i < 109 then 0x00000002e59f26377145500000002e5a1a3887145500000002c99f2388b4f85000000027c8e2075a945500000002dea4e38715835000000027c8e1835145b500000002c9aee8b715b9500000002c9a6238715b95 else 0x00000002c9a1e38714f8500000002dfa823871583500000002da9f1c56e50b500000002df9f25a81d83500000002c99f2383f0f8500000002c99f254715b9500000002c9aee8b714f8500000002c9a2a38714f85) else (if i < 111 then 0x00000002c99f2383549a5000000027c8e216514b2500000002df9f1c560d0f500000002c99f26d715b9500000002c99f254714f8500000002eaa823871520500000002c9a2e4f715b9500000002c9a1238714f85 else 0x000000028b951c56e5185000000027c8e1ca514b2500000002eaa2e38715ae500000002c9a2e3873db9500000002978e207514b2500000002c99f2548d474500000002e59f2388a4d5500000002f1ab2387f5835)) else (if i < 114 then (if i < 113 then 0x00000002daaee8b715b9500000002c99f254714fa500000002daa2a38715b9500000002d9b267c8e1ea500000002da9f2388b5b9500000002e5ac238514505000000027c8e1ea460f8500000002df9f27a8d5835 else 0x00000002da9f254715b95000000028b8e1c56e518500000002df9f27760c0d500000002e5a8638715b3500000002da9f2386e4fc5000000027c8e1b94610a500000002c99f238714f8500000002c98e1c51dc2e5) else (if i < 115 then 0x00000002c9a2e6c715b9500000002da9f254714f85000000028b8e1c5460f8500000002f69f250715b9500000002c99f24e714f8500000002c9a2dc56e43050000000238715450a40b500000002c9a2e547c5b95 else 0x00000002c9a2e387c5b9500000002da9f238715b9500000002c99f654715b9500000002e59f26377545500000002c99f252715b9500000002c99f2548d417500000002da9f26d715b95)))))))
def g1_l4S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l4C (i / 8)) 84 (i % 8))
def g1_l4HC (i : ℕ) : ℕ := (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x04b3e1ca0469263904525d280411e1e004054ea103fd1f6303df6f3903da9ab703d231e20342a5720328d10402f1cbe502e4ccb802a066a5029d8fc3028dab190286bcfa027851300276ea360262f5e60231597202285a8502157a9e01ce243d0150bdd7014414b000eb8998006bf7b60065511c0058f8b5000a56dc000041bf else (if i < 2 then 0x0aa7a3350a773d5d0a6419290a1cfcfc0a04dacf09d91edb09d1998509c64cd209a4f6a30964abf808bf984e08a0c82408817e61084998b5081057a507f71b8807cc3cf00783c4f00772b3ee072cb4cb06c7d25f065bddc10619915f0619783305fec5fe05d03c9305c054c705acb62a05ab18f70548edb704c664e204b3fe02 else 0x0f554ee20f1442520f0f6dd00f0d471c0ef3ae080ed23a5e0ebd597a0e881fef0e6a39f80e4993ed0e29515f0e199fd10e0d475d0d8249f60d6b9f8f0d5300720d4fe8d70d238a110ccff8660cc1931d0cc141700cb7b9280ca465d20c956ab40c4c77c80c3bd1050c184bd50c0f7d6f0be34a9c0b83315e0b56a9c90b30feb7)) else (if i < 5 then (if i < 4 then 0x152c99f314d712d314d1ad82146736491461b2c113eaccee13920ce013815d1713452abe131f53e6130dc8d212fe174412faa19f12f66d5812edd83d12d430b512c6bb1712ac27f812a73f4a12919a3912063b231202dfc911f21f2611ec537a116d2012113fa2821110b7a7106ed8991068f89910539ce40fd249570facd08d else 0x19e47a9419e25ce819d0f6a419b00911195cc86519526e02194dfcf9192e1b6b192443a71923ae9618baf0b118b8bcd41884880f183512e41810661417db0ba617cbcd5d17b0e40d17a3e9091717eba6170ec16316d9d768168b7ce2166293d71655472a1626c36c16012cea15d3470715812769156f7e631568a12a1530f712) else (if i < 6 then 0x1f3f7a621f2b3a171f2505b51f07d0271ee1baec1ecb9d0c1e3b5bf51e1667a81dc0db721da2d1531d97d7281d5afe801d3fc16f1cdbc8801ca98b8d1c4eef601c2110331c1b8ba71c0194661bfa81931b9dfa0d1b9dcbb21b1c5a091b10a0a01af774161af763fe1af023a01adef4431aaddcd21aa07d031a6ac1e51a442b5c else 0x2623c28f25b7a9fd259f28952541e44f2538f5912517300125107bef24f7b30424bd6f8124b2bae62483e474245535ba2451c932243786bc23986ace238da095238858b0234f388e2329cb4922f68e612273c0892261c8c92237457a21bb663321739ef42171713121081a2020d33c7d20cfa0711fcf83bb1fcd60481f80431b))) else (if i < 10 then (if i < 8 then 0x2e5e11c32e13fed42defb4812dc8da432d758ef52d5829a72d30f53f2d2d34f92d275f4f2ce1602c2bedcaee2be215bf2b65c0b52b4131e82b0233612a6a3ef12a44bb862a2ddb822a1dd19a29687ddb29296e9b290387a528fa72e028633803281f7a83281580da27de5ea6273b790a26fd266f26a034f926725f9b262acdf7 else (if i < 9 then 0x34621c6833da788433ad3ec2339fbf02339d8d34337f5c693343231d333f2a053323728a32fb7b6132898e6a3261b07a3259113332468aeb3240069a32101c2431eaffed31a4a68b317afedf3155c38b312ca64430e3ad1f30b9e37c30708c353047e3243035d13a2f7f607f2ef7fdd22ecf1fa62ec7ab002e7e86602e7e24dd else 0x3b52fcab3b20f46b3ad7221a3ab0bd0a3a6647993a4f17e13a165e2239fbfa7739eac16339bb9a8338bbd9da38afdc04387c1fe737fd4dd4379bdd3a3721cb73372025e837135d6036d4ec4d36ced38b368885a5364738dd35ed428635e7d15d35c5b1a435b094573565310c3558d2753548200a35410d3735248ade35028bc7)) else (if i < 12 then (if i < 11 then 0x4303f41d42f88fc942d0b05342a36082427785394227f6d841e45ebc41df322641c2e105416b6bd540e0353140db9c46404b079f3fac180b3f8c039e3f47ceb33ef64c3d3ece42913dc825243dbe61833d44f1be3d247cd53d234dd93d1b46ab3ca4fecb3c67811f3c484fad3c350c953b7276aa3b5efcc83b5e5ac93b5c1c64 else 0x4861a5224861955c483e0d1a47f6301e47ee31cb47ba0ab4474a78924736b7ac467a3635467626cd4667cc1746675d694629a6f7462475114614bd97460bf5334604740b45d2766145a274ee4599c941454abf644535a38a4496664d447657864459d64843f4e6a843836b64437fe3bc43415eba432bdff54328d6d7431d68e4) else (if i < 13 then 0x4e39f6a04de2abc54dd425e44dcd67814db42b644d8f34f04d33199d4d1e64ca4cfd51234cf1a18e4cb7c5724cb752004c4e4d3f4c3fc05c4ba8c1d04b91c23c4b8771244ae51dbb4a45dd154a3967424a23a3364a0f83974a06f26a4a030a7649f3c36e49c879c2499c7f15497285d649424bf6491475e048fd17d548a1dc94 else 0x5542679355168d5f54b4ec85545b2197544bc8f6541c8740536754a7534e188a5349da1453475c15533a9fc8532a3a565311275452f05b8b52e06a0052b0b0e4523fc088522f030751e5c64b519d2392516f2c8e51253f4050ff584c50ab2ede508db86a508c10d74fe9b8064f2e878e4f01f48a4ee1a5754ea15bc44e98f054)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x5b8958235b3fc3935b34ee9c5aca38415a9851505a91eb135a5349675a1facf25a1ac1325a0fc67459e1045f59d1aead59aea063597f1fdd5975d03e5953a78858bbe01c58b2327d58a466a0585dd98958116ce858052a6557df37a757c9d7dd577a94d1576813c857659122572d149a571e002456f7bd4756770953557db891 else (if i < 16 then 0x63c5c1816379da13631c3cfd629d06fd628045ef62675628625d6dff623e9c9861286e3d612747ca60c2bad0606b4e80605dd1f66052126360329e62602e198d5fd35dc55f9f6cc45f3ce3c65edb42ec5df3c4cf5dca411e5d9ccf955d9c4a235d6db27c5d5a46d75d1077c95c21ab365bfe26d75bc01d8e5bb06c005ba0a92c else 0x6ad1c3a06aa6920b6a8f7c596a5f57326a52df2669bbab1769a3432d699f222268b75e0168b45e6d68a28595689c77be6853824b6808a0e767f8fce767e047bb67d5e8e3679afb70677ce57b6750eb6866e891fa66cc5a8366c4231e66a15fda651cae656504737864fd1da264ca975c6494174d647e225e646c5821645954b2)) else (if i < 19 then (if i < 18 then 0x716695ef71660d5b714e8d9271116e3a70ec11c770a9d37470a3afb8706d4e75706720927051817e6f7b551f6f70ec6a6f0fb7656ee5965c6e470c396e2b25306de7ebdc6de007046ddb07436d22f0886d1a7ffd6d117af16cfe5cfb6c9cbc216c875a356bff356f6bd920726bc6dc716bbfc0586b682f286b57204f6af8f6f0 else 0x79a8cc2a78fe857578991c90787b13c1777f5abb7771b78f7745a8d3771702087707312b77046cd476ee428776da6720768e29f97663feca761bdbcb7619a57075a36095758419bf7583ec2e75483e067537eddb7355af4d733a723c7300b2fc72cd541c72ae4403728bcf03727df3fb7268b60c72133dc871d632f37197a727) else (if i < 20 then 0x80b4cd5f8081718980243886800ff6387ff36f687fece1ed7fe01c987fccbe427f2753867f1f523a7efe38b37e9d2cfe7e264b247e14871a7ddfd4877d9176e37d8118137d72c1697d1906507ba083707b4c605c7af712f47ae306aa7adf4d3a7adbf9327acf27747aaf28137a72a6c37a49ea8979f01cc579dca96d79c86026 else 0x8ce909a78baf12468b0ab6ff8af971f98ac6dd2e8abeb6fe8a54f03d89dcf6ff89dc040c89a51153899cb14f88bb98018861dbb386fa5cab86d1ea1a86b90605859cf1fd8509b3e784a34898848741378422b94c84097d2f83ce05708358b3d38355da46834314078247ee2681dc5fc18115f2318106691580e999fd80bdfd3e))) else (if i < 25 then (if i < 23 then (if i < 22 then 0x9880303397e6f58097ad62999779eab096f0efc2966ee651964c533a96276a9495d9f6fb9555f5b49522a37f950d53bd93f7e67493aa206a9316de8393069a5191875daa9136f6f291006fdf90deda0a9084df06906ae66e905e86f5904340499026b0938ffd9ca88fa9a7738f36dc918effff788efed1a48e76d0b48d94f31c else 0xa3276ccaa2fbd00ba26392bea194cf70a16b588ea0c26b00a0b01da5a08d12b8a03836b5a02edc269f9154ce9f8870f19f559aeb9f50235c9e7542459e18bac39d485b309c0340ae9bf1200c9ba2ecbf9b9b4e9b9b86f2879b64820a9b391a1a9acd04c89a873d829a661de89a63c91f99d86a4f99a268fa990f494299046bf1) else (if i < 24 then 0xae88d65cad6ae4f0ad53254aad3a0acfacf60ec6ac7f2e1dabd6f492aba252f0aaf97481aad9be41aac817bdaa0d5e75a9a5e6b1a90a85a7a8c886b9a86ead44a7bce020a799687aa747d2e7a6d998b0a66af8aea603f71fa5ab6920a59bfe7ba5851d07a57f8508a4e5cdbaa4d3fd9ba46b8f30a3c9327ba34fed1ba32ac258 else 0xb873465ab8386b31b769e61fb6de7629b66147cdb63172a0b5ec49e6b5c8a957b5b1b4ddb4f93cd4b44932ecb41159d9b3e2b081b35d8a5bb34dfdcdb2ad8dbdb2a6281cb2a12bf5b29ed6dbb250e4e1b200f7c1b1b2eb3cb0ffef17b073ab67b00af7e4b0099b9eafbc0344af3a45bbaf27a265af1775c1aefd49bdaeceb10c)) else (if i < 27 then (if i < 26 then 0xc4e6a335c4a9ef6fc4612abac458462bc42c28f1c368d174c15ecde6c10e53afc108aae4c01bb010bf8fbc91bf6746a2be54d1ffbd7d2795bd77a540bd72fbfcbd679282bcef68e7bcc7825cbc0ac540bbc7d536bb6635a6baf841a0bad7e1deba7fb9a2ba684939ba5d2f56b97c2bfcb949b745b9122932b908ef75b890a69a else 0xd74fb93ad6cc6241d56cd6dcd5658666d5585ac8d49c0785d3e74badd3b8a255d3996062d292cd18d12bec60cfdf8d72cf5a9212cea4a2e0ce50006bcdbb0c92cd3c1dddcceae453cb601481caf83b19caaa6de1ca446361c8e0777bc8b07b6cc872316fc862d59ac7d2a95dc74d11bac7455b2cc6e62708c660b47fc4f4e5e2) else (if i < 28 then 0xe9ea395ce97fb544e91d8ef8e8d37489e847ca8ae82dd7e1e7ddf7b0e6cc629de696186de5dc65b2e59da226e54b3aa0e4097d60e3ccbea4e2be65a5e27c669ce24e461de1b6c07de17bbd41dfccf59adee0b305dec6d493dd46745edc710546dbf501bddb22ea07dae63574daa2ae34d9407648d820ddc9d803cb91d7eae77c else 0xfecf390efe9cc667fdccdf7afd5e5f7dfd34ebbbfb1a31c7faddb44ef9bd3179f99bf70ef9705a4ff952e551f90cc156f68e2e4bf612b112f48bc0e8f4594e41f42db182f1581594efafc61aef3083e6ee69861dee4cf586edc62a50ed96453fecfa068decc0d627ebfc418beb360655ea9a7f7aea32fe11ea00a8d4)))))
def g1_l4H (i : ℕ) : ℕ := fld (g1_l4HC (i / 32)) 32 (i % 32)
def g1_l5C (i : ℕ) : ℕ := (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x000009f2597158351518600000b6a7c8e1c56e400600000b96988e1c560d45600000b267c8e22e60d45600000b967c8e20d5141d600000b267c8e1e151416600000b9697a563871545600000b267c715832848c6 else 0x00000b6a7c951c56e5456000009f23860d454609a600000b6a7c8e1c56e5ae600000a2e38715b951518600000b267c945c560d45600000b268b8e1c56e4a5600000b7e93a463871583600000b267c98dc560c8c6) else (if i < 3 then 0x00000b267c8e22b5141c6000009f238715452c886600000b267c8e2073549a600000b267c8e18356d45600000b26c6a81c560d45600000b267c8e14526856600000b6a7c8e1ef60d45600000b26918e183514996 else 0x00000b267d8e1cc60d45600000b267c8e21560d456000009f2387918339814600000b267c8e1fd77183600000b267c991c56e57e600000b26978e21c60c8c600000b267d8e1c5514be600000b7e7c8e1834f0996)) else (if i < 6 then (if i < 5 then 0x00000b267c951c56e4d9600000b267c8e1b960d07600000002e5a5e38715455000009f238715b360d18600000b267c8e1c56d414600000b267c81d83514a16000009f2387719f60c14600000b26a08e23560d456 else 0x00000002e59f24971545500000b267c8e183514c6600000b7e7c965c560ce6600000b267c98e0760d456000009f238715835151b600000b267c9de2b81d45600000b267c8e173514b8600000b7e7c9de0760d456) else (if i < 7 then 0x00000b267c8e20715814600000b267c8e21663d45600000b267c8e1835149d600000b6ac99f2387c5b9600000b267c8e23568d456000009f23881d8346014600000b6a7c8e207514be600000002da9f238714f85 else 0x00000b7e7c8e2077ed83600000b7ec99f20760c46600000b267c8e20760cbc600000b96978e1c551400600000b26978e1e560d45600000b7e7c8e1c560cef600000b7e7c8e21c6d5456000009f238825452ac166))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x00000b967c8e23551416600000b267c925e560d45600000a2e38715b948118600000b267c8e1c53e07a600000b267c9e583514d56000009f2637158359d45600000b967c8e1dc5e945600000b267c8e20760d466 else 0x00000b527c8e21c5148f600000b6a7c8e1cd60d45600000b267c8e1fc60d45600000b96848e1c560d45600000b267c98e166cd83600000b6a7c951c56e520600000b267c8e2076e520600000b26ac8e2077f5836) else (if i < 11 then 0x000009f238715a260d216000009f238635835141d600000b7eda9f23881d83600000b267c8e20770183600000b267c8e20060c8c600000b267c8e207514f8600000b268b951c560c87600000b26918e1c560d216 else 0x00000b7e918e1c560c86600000b267c8e18351490600000b7e7c8e1c560d3f600000a5e38715b360cab600000b2691a423871583600000b96978e1c55153a600000b7ec99f23860c9e6000009f23873583398146)) else (if i < 14 then (if i < 13 then 0x00000b267c8e1c560c7e6000000027c8e1c5514b2500000b267c8e1c92f887600000b267c951c56e416600000b267c8e1dd60d45600000b267c871835150b600000b967c8e1c56cd41600000b267c8e21c68c146 else 0x00000b267c8e1e556087600000b7e7c965c560c87600000b267c951f16e583600000b2691909c560d45600000b267c98e0760cc7600000b82c99f23881d83600000002c99f638715b9500000b267c94def60d456) else (if i < 15 then 0x00000b967c8e1c55a945600000b267c8e9c560d3e600000b7a918e1c560d45600000b267c8e1c5480fa600000b267c8e23560d36600000b267c951c56e4ab600000b267c71583514dc600000b267c9b1c56cd836 else 0x000009f23860d4546107600000b26988e1c55140c600000b267c8e18426814600000b267c98e316cd83600000b7e7c9be5971583600000b7e7c909c560d3c6000009f238715454f8b2600000b96988e1c55f9456)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x000009f23871583514e7600000b26387159e60d45600000b267c8e1b360c956000009f238715452c800600000b26928e1c56e545600000002da9f23881db9500000b96c99f2383544b600000bc6c99f27760d456 else 0x00000b267c965c56d545600000b967c8e1ef5e945600000b6a8b8e21c60d45600000b263871583514a6600000b5e7c8e20760ce6600000b7e7c965c5514c4600000b267c991c551416600000b967c8e20f60d456) else (if i < 19 then 0x00000b267c8e2076d183600000b267c8e21c64145600000b26918e20060c14600000b267c8e1e451522600000b7e7c965c560ced600000b267c8e207480f8600000b267c8e14535016600000b267c8e183428876 else 0x00000bc6c99f2387ed83600000b6a7c8e1c56e545600000002e5a5e387148c500000b267c90183514d5600000b967c8e1e45e9456000009f259715834f0ed600000b267c965f160d45600000b267c8e1b55149a6)) else (if i < 22 then (if i < 21 then 0x00000b267c8e18351492600000b267c98e0760c8c600000b267c8e1dc60c14600000b267c90183514c7600000b5a7c8e1c55e887600000b268b8e1f16e545600000b96c99f238861456000009f2388720d514536 else 0x00000b26c0a8dc560d456000009f238715835e8ed600000b267c8e1dd60cc7600000b967c8e21c51495600000b268b8e1c560c26600000b267c9de3560d45600000b26918e21c60d45600000b26ac8e1835149a6) else (if i < 23 then 0x00000b267c8e1f16cd836000009f23871583460f8600000b7e7c8e21c60d3c600000baac99f238871416000009f2387359f60c14600000b267c8e1c56d5b3600000b7e7c8e1c568cab600000b267c8e1fd735836 else 0x00000b96df9f25a71583600000b967c8e1c56cce6600000b26c0a45c5514c4600000b6a7c98dc560d45600000baac99f254715b9600000b267c951c56e4be6000009f2387398339814600000b268b8e1c56b5456))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x000009f26371583398146000009f2387018339814600000b267c7158359545600000002c99f238514b8500000002e5a5e3881d45500000b267c8e2076d414600000b96df9f2388d5836000009f238735833b4146 else 0x00000b967c8e1cd5e9456000009f23871583484e6600000b267c8e1c360d45600000b96978e1c551424600000b26ac8e20760c146000009f2547c58351518600000b267c715b948046600000b6a7c8e1c56e4076) else (if i < 27 then 0x00000b267c991c5514be600000bd27c8e22360d45600000b96df9f23881d7a6000000027c8e21c60ced500000b96c99f238875456000009f238859b360cab600000b267c8e1832408c600000b267d8e1cd60d456 else 0x000000027c8e1c52c88c500000b7e7c8e20760c1c600000b268b8e1f16e520600000b267c8e1e260d45600000b267c8e1dd60c8c600000b3e7c8e1e560d45600000b6a7c8e1c56e520600000baac99f264715456)) else (if i < 30 then (if i < 29 then 0x00000b267c8e14526866600000b267c98dc56a9456000009f23860d451201e600000b6a7c8e1c5514f8600000b267c8e18c3544b600000b268b8e1c560c87600000b267c9665871583600000b267f8e1e560d456 else 0x00000bceb08e21c60d45600000b267c8e21c514ad600000b267c8e183514ce600000b26978e1c560c266000009f24271583514e66000009f238715833b4c4600000b267c8e1452f89a600000b2691979c560d456) else (if i < 31 then 0x00000b2638715832988c600000b26978e1c56b545600000b967c8e1c56cc87600000b7ec9a4638715b5600000b269798dc551416600000b268b8e1c5514c4600000b7e918e1c54f0c4600000b26978e1ce514166 else 0x00000b967c8e1e4514bd600000b7ec99f25971583600000b267c8e22c60d45600000b267c8e1f160d53600000b268a8e21c60d45600000b26919660060d45600000b267c8e2357e945600000b96978e1c5514076))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x00000b7ec9a2e38715b9600000b967c8e21c83545600000b267c8e21c5146e600000b267c8e145334c4600000b267c9660360d45600000b26c071583514e1600000b7ece9f23881d83600000b26c5a5dc560d456 else 0x00000b267c965dc60d45600000b267c8e183514ca600000b5a7c8e1c52f487600000b268b8e1c56e431600000b7ec99f23860c9a600000b6a7c8e20060d45600000b267c8e1b9354166000009f2388c5b360cab6) else (if i < 35 then 0x00000bc67c8e1f851456600000b7e7c9660060d3c600000b268b8e1c56e53c600000b26bba2e1c60d456000009f23871583478ed600000b267c8e1fd73983600000b267c8e14541c16600000b26988e21c60d456 else 0x00000b267c8e1c960d45600000b96978e1c551520600000b267c8e9c560d45600000b267c909c52f887600000b267c8e1b960cc86000009f2388018339814600000b967c8e2145141d6000009f25471545460be6)) else (if i < 38 then (if i < 37 then 0x00000b7e7c8e1c56d541600000b6a7c8e1c5480f8600000b267c9020760d45600000b7e7c8e22d6b983600000b267d8e1c56e545600000b267c8e1c56c583600000b96df9f23887145600000b267c8e183520c86 else 0x00000b6a7c8e1c56e47a600000002c99f264715b95000009f2387cd83515186000009f2387159f60d21600000b267c8e18358545600000b267c8e21c60cf4600000b263881d83514a6600000b267c8e1dc60c5f6) else (if i < 39 then 0x00000b967c8e1ce5e945600000b96978e1c56cd83600000b96978e1c5514b2600000b967c8e1c55147c600000b967c8e1c56bd45600000b267c8e1dc6cd83600000b267c966076d545600000b267c8e0c72f89a6 else 0x00000b267c94dc56e520600000b267c8e235480176000009f23877dce51416600000b267c8e18349090600000b7ed69f23881d83600000b967c7157a514a1600000b6a7c8e2076e5456000009f238514ab2401d6))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x00000a2e38715452ac16600000b26978e1c5514c4600000b967c98dc55e945600000b26ac8e20460d45600000b26918e1e560d45600000b268b8e23560d45600000b967c99a6371545600000b267c98dc5515226 else 0x000009f238715452c8076000009f2427159f60d45600000b267c8e1e55c545600000b26bb71583514df600000b7e38715834f0e1600000b567c8e18351497600000bce7c8e21483545600000b267c8e1c53e0166) else (if i < 43 then 0x00000b267c8e19160d45600000b267c925c5514c4600000b267c8e1b55146f600000b96978e1c55148c600000b267c8e2076cc16600000b96c99f254715b9600000b267c8e1c53e0ab600000b267c8e1f160cf86 else 0x00000b267c8e1835149b600000b26848e21c60d45600000b267c8e21c69945600000b96978e21c5e945600000002dfa463881d83500000b26818e1c560d21600000b267c8e1452f891600000b267c8e183515006)) else (if i < 46 then (if i < 45 then 0x00000b96978e1c55140b600000b269aa2e38715b9600000b267c8e1f151456600000b267c98d835149e600000b267c9121c51490600000b267c8e20760d56600000b267c965ef60d456000009f2387c583515186 else 0x00000b267c951c56e412600000b7e818e1c560c86600000b267c9e61c85145600000b5ec99f23881d83600000b267d8e1c56e520600000b267c8e23560d42600000b267c8e1c56e5686000009f23871545480b26) else (if i < 47 then 0x00000b267c965e7514c4600000b967c8e1c55f945600000b267c8e183584d5600000b267c8e2007f583600000b267c9020760cc76000009f238715694f0166000000027c951c56e518500000b267c8e183514996 else 0x00000b267c8e183584c76000009f23881d83484e6600000002e59f26387145500000b267c9521c60d45600000a463871545398c4600000b96c99f26471545600000b267c94e0060d45600000b7e918e1c560d456)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x00000002df9f2388c9b5500000b7e7c8e1c5504be600000be2c9b01c560d45600000b96978e1c551428600000b26828e18351490600000bc67c8e22360d45600000b267c8e23560d35600000b2681909c560d456 else 0x00000b267c8e21d51491600000b6ec99f2388d583600000b7e7c8e1c56d4e66000009f238715b360cb2600000b267c8e1ef6cd83600000b267c98e1651416600000b6a7c8e2076e520600000b96c99f238514d46) else (if i < 51 then 0x000009f23881d835fcab600000b967c8e1c56cdb2600000b26978e23560d45600000b267c8e1e46cd836000009f25980183514e6600000b267c8e20f73945600000b967c8e21e87145600000b268b8e20760c876 else 0x00000b6a7c8e18351490600000002e5a623871545500000b267c8e9c560c8c6000009f23887183514ed600000b7e7c8e1fb60c14600000a5e38715452ac16600000b267c8e1c5514b0600000b96978e1c5514296)) else (if i < 54 then (if i < 53 then 0x00000baac99f238714f8600000b267c8e1c53e0be600000b26b08e22987183600000b96c99f238715b3600000b267c965d760d45600000b967c8e2005e9456000009f23881d833a41c600000b267c8e23560c4d6 else 0x000009f2388717a514b2600000b267c965cd60d456000009f2385145107408600000b7ec99f26481d83600000b267c8e21760d456000009f23860d451441e600000b267c8e20754c166000009f23860ce6240146) else (if i < 55 then 0x00000b26818e21c60d45600000b267c8e17b5149a600000b327c98dc560d45600000b26c5a5e0760d45600000b967c98dc55151e600000b7ec99f25981d83600000b5a7c98dc560d45600000b267c9b1c5514166 else 0x00000b267c8e18351493600000b967c98dc5514bd600000b267c8e18358d45600000b267c8e2357f945600000b267c951f1514be600000b267c8e183515066000009f2387318351518600000bc6ac8e1f860d456))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x00000b267c8e21c6e541600000b967c98dc55e88c600000b26547158351511600000b96df9f23879545600000b267c8ea0760d456000009f238715452c87a600000b967c8e2166cd83600000b967c8e216514b26 else 0x00000b269791dc560d45600000b267c8e183514fd600000002dfa063871583500000b267c98e1c51490600000bd6df9f25971583600000b7e7c8e22b81df8600000b2694951c560d45600000b7e7c8e1c560c866) else (if i < 59 then 0x00000b967c8e21c5140c600000b267c8e19160c8c600000b267c909c560d45600000b7e7c8e1c56d487600000b267c8e19860d45600000b267c8e1dc60cf8600000b267c7158351510600000b267c8e1cd6cd836 else 0x00000b267c8e1c5514f9600000b26b8951c560d45600000b267c8e18351494600000b26918e1c560d69600000b267c8e1e560d316000009f23877183515186000009f23860d451881a600000b267c8d583514476)) else (if i < 62 then (if i < 61 then 0x00000b967c98dc551436600000b96c9a5e6371545600000b267c8e214514d5600000b267c991c56e545600000b267c8e23560d51600000b267c8e22987016600000b967c98e075e945600000b267c8e1ee60d456 else 0x000009f23863d451441d600000b268c8e21c60d45600000b7ea08e1c56e5836000009f238715b54f0ed600000b967c8e2316cd83600000b267c8e1e52f887600000b7e7c8e1c56d4ed600000b267c8e20760d6d6) else (if i < 63 then 0x00000b96c99f23851507600000b267c8e1c56e412600000b267c8e1535149a600000b96c99f2386e4d5600000b26848e1e560d45600000b267c8e1b95149a6000009f238715a260ce6600000b267c8e20060c146 else 0x00000b267c965ce60d45600000b767c951c560d45600000b267c8e21c60d456000009f2387157a5151d600000002c99f2547c5b95000009f238715a360ced600000b267c8e18351473600000b267c8e183515056)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x00000b267c951c56e4f8600000b267c8e18358485600000b7e918e20760d45600000b967c8e2075f945600000b267c8e1cd60d53600000b267c951e560d45600000beee5a5e3871545600000b26ac8e207514566 else 0x00000b967c8e17a514906000009f23860d451a41d600000b6a8b8e1c560c87600000b267c8e21760c8c600000b268b8e1c560d4b600000bc6df9f2387e183600000b267c98d835149a600000b267c98d83514d46) else (if i < 67 then 0x000009f254715b951518600000b26387158351478600000b967c8e1dd5e945600000b7ec99f26c71583600000b267c8e19d5146d600000b267c909db60d45600000002e59f23883d45500000002e59f279871455 else 0x00000b96c99f238714f8600000b267c8e23560c136000009f2387918351518600000b267c715b360ca1600000b267c8e1ce6cd83600000b267c8e1ce514b2600000b268b8e1c55f5456000009f2387bd83515186)) else (if i < 70 then (if i < 69 then 0x00000a2e3871583514f0600000b267c8e1b94809a600000b6a7c8e1f16e583600000b267c8e1b93549a600000b267c98dc5514b2600000b267c8e18f514d5600000b267c965c56e520600000b6a7c8e1c56e4166 else 0x00000b267c98e0760c146000009f238729452ac16600000b7e7c8e2357e183600000b267c8e18351498600000b96c99f23881db3600000b7e7c8e1c56b9836000009f238715a260c87600000b6a7c8e1c56e4ab6) else (if i < 71 then 0x00000b267c8e18327414600000bce7c8e20d51490600000b268b8e21c6e583600000b26978e21c6cd836000000027c8e1c5460f8500000b967c8e1e578145600000b267c8e21c5144e600000b267c8e1c53e0126 else 0x00000b267c8e1cf6e5206000009f238715a267d83600000b267c9b9c560d38600000b6a7c8e1c960d45600000b267c8e20760d21600000b26387158351511600000b6a7c8e9c560d45600000b26918e1c5514c46))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x00000b26918e1e760d45600000bba7c8e1ec60d45600000baa7c8e1c56b920600000b26978e1f660d45600000b267c8e183485016000009f23a71583398146000009f23860d565141c600000002e5b7e7c8e2355 else 0x00000b267c9660060d45600000b267c8e1e75c545600000b967c98dc5514dd600000b7e7c8e20760c86600000b26918e2006d545600000b7e7c8e1c54f0c4600000b26918e1c560ced600000b46918e1c560d456) else (if i < 75 then 0x00000b96978e1c5514e8600000b267c8e1fc60c14600000b267c9e61c51490600000b96c99f26385945600000b267c8e1dc6d545600000b267c8e18357c90600000b267c925c568d456000009f254715b9481186 else 0x000009f23881d45488ab600000b267c90a0760d45600000b96978e1c551416600000b267c8e21c51496600000b26a68e1cd60d45600000b967c8e1e55140c600000b7e7c8e2006d53c6000009f23873583515186)) else (if i < 78 then (if i < 77 then 0x00000b7e7c965c560c1f600000b267c9dd835141c6000009f238715833b014600000b268b97dc560d45600000b96978e1c5514ab600000b7ec99f23881c566000009f2387e1835145b600000b7e7c8e20760d186 else 0x00000b263871583514a9600000baada9f238715b9600000b6a7c8e1c56e4be600000a5e3871583514f0600000b267c8e1dd60c14600000b267c8e21c60c8c6000009f238714ab21c0c600000b267c951f560d456) else (if i < 79 then 0x00000b267c8e229859836000009f2388ae07514e6600000b267c8e1fb60c1c600000b7e7c8e1c569183600000b267c8e1f960d45600000b96c99f23881d53600000b7e7c8e1c56e541600000b267c8e2006cd836 else 0x00000b7e7c8e23560d3c600000b26988e1c560c87600000b267c8e1f16e4fc600000b267c8e2076e412600000b967c8e1dd5e88c6000009f26471583514ab600000a4638715452ac16600000b7e7c8e207619836)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x000009f23860d451601c600000b26918e1c56e145600000b26918e23260d45600000b267c8e1e560d456000009f2387158339c14600000b26bba2dc560c87600000b7ec99f238871a3600000b96df9f2388704b6 else 0x00000b268a8e1c5514c46000009f26c715835147a6000009f238514901441d600000b267c965c56d414600000b268b8e1c56e42e600000b6a7c9521c60d45600000b267c8e1c56e4f8600000a2e3887183515186) else (if i < 83 then 0x00000be6c9aedc560d45600000002c99f238715b1500000b267c8e1b948107600000b26aea5e3860d45600000b267c71583374346000009f238715453a0b2600000b96df9f238870e8600000b7e7c8e23260d3c6 else 0x00000b96978e1c5514be600000b26918e21c60c146000009f238715b360cab6000009f238715452c8ab600000b267c8e1e451416600000b267c8e1a751490600000b267d8e1c56e4166000009f238715452c8166)) else (if i < 86 then (if i < 85 then 0x00000b26c57158351427600000b267c8e20754c9a600000b267c8e1c56c53e600000b96c5a5dc55e945600000b267c8e183589456000009f238715833b4c2600000b267c8e183514cc600000baae5a5e38715456 else 0x00000b96c99f2388a61c600000b967c925c5514be600000bc67c8e1f860ce9600000002e5a5e38715b3500000b7e7c8e183514cf600000b967c8e1e4514e6600000b267c8e9c561145600000b7ec9a6238715b96) else (if i < 87 then 0x00000b267c8e21668d45600000b7e7c8e20761183600000b7ec9a463880183600000b267c98e076cd83600000b26918e21c5142a600000b267c8e1c568983600000b26918e1c560d4d600000b7e7c8e1832681c6 else 0x00000b7ec99f238771836000009f238715221e814600000b26818e1c560d696000009f23885d8339814600000b7e7c8e2076b983600000b967c8e1c95e945600000b267d8e9c560d45600000b26918e1d260d456))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x00000b26978e1835146a600000b263881d8351511600000b967c8e21651416600000b267c8e22b514c7600000b267c9658351490600000b267c8e1dc2f807600000b7e7c8e20760c97600000b267c8e21c60d246 else 0x00000b267c8e21c5cd45600000b267c951f16e520600000b7e7c8e2074f0c4600000b26c8ac21c60d456000009f238715b948118600000b96978e1c551414600000b267c8e18351471600000bcec9ac23860d456) else (if i < 91 then 0x00000b267c8e1b360c90600000b268b8e1c56e579600000b7e918e1c56d583600000b267c8e2325146e600000b267c8e0be26814600000b26848e1c5514c4600000b267c951c560c87600000b7ec99f23881db56 else 0x00000b96978e1c551402600000b267c8e1dd6cd83600000a5e6371583514ab600000b7e918e1c560cab600000b7ec9ab23881d83600000baa7c8e1c5514b2600000b267c8e23589d836000009f238715452f8b26)) else (if i < 94 then (if i < 93 then 0x00000b267c8e1e560c8c600000b967c98dc551541600000b267c951c5514c4600000b96da9f238715b9600000b267c8e23560cf4600000b5a7c8e1c56e416600000b7e7c965c560c3d6000000027c8e1c56ccb25 else 0x00000b268b8e18351502600000b26938e1c560d3b600000b267c8e1b94d490600000b267c8e22c60c146000009f23881d835581c600000b26828e21c60d45600000b967c8e2185f945600000b267c8e1fa60d456) else (if i < 95 then 0x00000b267c951c56e53c600000b267c9d1f160d45600000b267c8e200514566000009f2388018351518600000b267c8f9e560d45600000b5e7c8e20760c1c600000b267c8718351446600000b26928e21c60d456 else 0x000009f238715453b4c4600000b267c9ea1c60d45600000b2638715b360ca6600000b267c8e2325c945600000b268b8e21c51416600000b26919661c60d45600000b26c071583514a8600000b6a7c8e1c56e4126))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x00000b267c8e1e53e0876000009f23871520460f8600000b267c8ddc560d45600000b267c98d8351495600000b7e7c965c560cac600000b263881d83514e1600000b6a7c8e21c60d456000009f238715452c8146 else 0x00000b967c8e2076b945600000002e59f238859b3500000b267c8e18358414600000b267c8e19960d45600000b267c9b1c56e520600000b267c8e2076e4f8600000002dfa4659715835000009f23887183398146) else (if i < 99 then 0x00000b269ca5e3871583600000b267c8e22b51409600000b7e918e1c560cbe600000002c99f238770f85000009f23881d452c816600000b26818e1c5514c4600000b267c8e21160c876000009f23860d45150516 else 0x00000b267c98dc551416600000b267c8e22460d45600000b267c8e1cd62d456000009f254715452ac166000009f23881db360cab6000009f23881d452c8ab600000b46818e1c560d45600000b267c9523560d456)) else (if i < 102 then (if i < 101 then 0x00000b967c98dc5514e6600000b267c8e1c5504c1600000b967c8e17a51493600000b267c8e22b81d45600000b267c8e1be51467600000b267c8e14536090600000b267c8e183514fb600000b267c98dc56d5456 else 0x00000b267c8e1db60d69600000b6a387158351511600000b267c8e0d521c6d600000b26978e21c514166000009f23881d833b4e6600000b6a7c8e1f1514be600000b967c991c560d456000009f238715475147a6) else (if i < 103 then 0x000009f23881db948118600000b26a08e22d60d45600000b267c8e1f16e520600000b967c98dc5514346000009f23883d452ac166000009f2387ade560d456000009f238715b95f8ab600000bb67c8e1e060d456 else 0x00000b267c98dc560c35600000b267c9520760c87600000b967c8e1c56cd836000009f2388719f60c14600000b967c8e1c5514b2600000b26c0a4dc560d45600000a0638715452ac16600000b267c94e1c60d456))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x00000b267c8e1c56c520600000b26b6a11c560d45600000b267c8e1c5514c4600000b267c8e1c56e411600000b267c8e14533cc4600000b267c8e2356e5416000009f238715ae5147f600000b96c99f238791456 else 0x00000b267c8e22b81cc76000009f238715452c812600000b7e7c8e20760c1e6000009f26c71583514ab600000b26c5a5dc56cd836000009f25987183514e6600000b267c71583514da6000009f23860d45460906) else (if i < 107 then 0x00000b267c8e22551416600000b267c8e145354c4600000b967c8e1453540e600000b267c965cd60c14600000b267c8e2006d545600000b267c8e1c560ced600000b967c98dc551487600000b267d8e1c56e4126 else 0x000009f238715b3514b2600000002da9f2387c5b95000009f23860d452ac956000009f238735c060ce6600000b26ac8e20060d45600000b267d8e21c60d456000009f238801834f0ed600000b967c8e21c5e9456)) else (if i < 110 then (if i < 109 then 0x00000b267c8e20760d696000009f238715a060d45600000b6a7c8e1e560d45600000b267c8ea0760c14600000b267c8e20760d526000009f23871583398c3600000a823871583514e6600000b96978e1c56e5456 else 0x00000002c9a2e38871b95000009f2387958339814600000b267c8e22e51416600000b26868e21c60d45600000b267c8e1f1480f8600000b6a7c8e1c56e4f8600000b96df9f2388d607600000b267c98df460d456) else (if i < 111 then 0x00000b267c969c560d45600000b267c98ddc60d45600000b267c909c560c14600000b268b8e21660d45600000b967c8e1c56cc7c600000b267c98dc523016600000b267c8e1cc6e520600000b267c8e1b92f89a6 else 0x000009f238715452ac16600000bce7c8e22983583600000b967c991c55f945600000b26b08e18351490600000b267c8e23560d45600000b969798dc560d45600000b96dfa463871583600000b967c98dc56cd7a6)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x00000b967c8e2166cd45600000b267c8e183514d0600000b267c8e23260d45600000baa7c9b1c560d45600000b267c8e1db514c4600000b267c991c55140c6000009f23882a0751416600000b267c8e1c53e0116 else 0x00000b267c8e2354806d600000b7e7c8e22387183600000b26bb71583515116000009f238514d52ac16600000b267c98e0751416600000b267c8e1dc6e520600000b26a78e1dc60d45600000b267c8e19c514d56) else (if i < 115 then 0x00000b267c8e1dc514f8600000b267c8e1c530487600000b267c8e21c83d45600000b267c8e9c56e583600000b267c8e1c54f0f86000008e1c560d450c422600000b267c8e21c60d5f600000b268b8e20760c236 else 0x00000b967c8e1c52c88c600000b7e818e1c560cab6000009f238715b9514b2600000b26b7a2dc560d45600000b96df9f238871b9600000b268b8e1c56e51e600000b967c8e1c55fd45600000b267c951c56e5396)) else (if i < 118 then (if i < 117 then 0x00000b7e7c9de077e183600000b267c8e1b960d61600000b26978e21c51402600000b96c9a2e3887145600000baa7c8e1c55e9416000009f23871548514b2600000b7e7c965c560d76600000b96d49f238871456 else 0x00000b26b49f5c560d456000009f2387157d39807600000b7e7c8e20760c09600000b267c8e1cd60ce9600000b267c8e1c53108c600000b268b8e1c56e5ab600000b268b8e1e5514be600000b96978e1c5514a56) else (if i < 119 then 0x00000b267c8e1c55f53e600000b267c8e23560cd56000009f23873983514b2600000b26978e21660d45600000b263881d8351457600000b96978e1c5514e2600000b268b715835150b600000b6ac99f238871b96 else 0x00000b427c8e20060d456000009f26371583514b2600000b967c8e2316cd45600000b267c8e1452e09a600000b6a7c951c560c87600000b268b8e2356e583600000a2e387158346087600000b7ec99f238801836))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x00000b267c98de460d45600000b267c8e1ea2f887600000b267c8e183575456000009f238715a32f4146000009f2388720d63d45600000b26918e1c660d45600000b268b919c560d45600000b267c9261660d456 else 0x000009f23860d545140d600000b267c951c55f545600000b267c8e207498c7600000b267c8e1834849a600000b267c8e145360c4600000b967c8e207514b2600000b267c8e1b551490600000b267c8e19360d456) else (if i < 123 then 0x00000b267c8e1ef6e5206000009f2387156851416600000b527c8e1835148f600000b26bca45c560d45600000b267c8e1dc5f487600000b7e7c96656715836000009f2387ed83514e6600000b7e7c8e20760d7f6 else 0x00000b7e7c8e1c56d583600000b267c8e1b360c93600000b967c8e1e55e945600000b267c8e23560c0e600000b267c8e20760ced600000b267c8e1e551522600000b267c8e183514cb600000b267c8e183260146)) else (if i < 126 then (if i < 125 then 0x00000b967c98e1660d45600000b267c951c56e433600000b267c8e23560c8c6000009f23a7158351518600000b267c8e0d52404b600000b26918e1c531014600000b96c9a5e3887145600000b267c9521c6e5836 else 0x00000b26918e183514cd600000b267c8e1b924414600000b7e8b8e1c560d3c600000b967c8e22387145600000b267c951c56e43e600000b2691921c560d456000009f238714ab23016600000b26a4a2e38715b96) else (if i < 127 then 0x00000b267c9921c60d45600000b26918e21c6d545600000b26918e21c51416600000b26b08e1835141d600000b2697919c560d45600000b7ec99f26381d83600000b96848e1c5514be6000009f23871547514ab6 else 0x00000b7e7c8e21c6d53c600000b967c9b1c560d45600000b7e7c8e21c4f016600000b7e7c8e1c56d4ac600000b267c8e20731cc4600000b267c8e22960cd5600000b267c8e21c4d49a600000b26c498dc560d456))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x00000b264f7158351511600000b267c8e2076ed83600000b267c8e19b60d45600000002df9f25971583500000b96b08e21c83545600000b267c8e1cd6e520600000b267c95250715b9600000b268b8e21c6e5456 else 0x00000b26a9a2e3860d45600000b26928e1c560c87600000b029171583514e6600000b267c8e21c6cd83600000b26a08e1c560d45600000b269196dc560d45600000b26978e21660c8c600000b267c8e1c5611416) else (if i < 131 then 0x00000b967c98dc5514a06000009f23860c5807014600000b7ec99f23877583600000b7e7c965c560c00600000b267c8e20960d45600000b26b08e18351450600000b267c8e1c53e00c600000b267c8e21c631356 else 0x00000b6a7c8e1c560c87600000b96c99f2637148c600000b26b28e21c60d45600000b267c8e21c51504600000b6a7c8e1f16e520600000b967c8e1c56b814600000b7e978e1c560d3c6000009f25487183515186)) else (if i < 134 then (if i < 133 then 0x00000b967c8e22987183600000b7e7c8e18326897600000b267c8e183514d6600000b267c8e1a3514d5600000b267c96a0260d45600000b967c8e1e5514bd600000b267c8e18357145600000b268b8e1f160c876 else 0x00000b6a7c8e1c56e411600000b7e7c8e1c560ce7600000b267c8e14526855600000b26c571583514a56000009f23881cc72ac16600000b2691965c5514c4600000b268b8e21c6e520600000b267c8e207670c76) else (if i < 135 then 0x00000b267c999c55dd456000009f2387157a5a945600000b7ec99f259715b5600000b26c5a5dc551416600000b967c8e14535416600000b96c99f23885545600000b267c715835150f600000b6a7c8e1c5514c46 else 0x000009f27781d83514e6600000b6a7c8e1c56e53c600000b267c92d83514d5600000b96a2a5e3871545600000b267c8e1ea60d45600000b46c99f238714f8600000b96c99f26381d45600000b268b8e183514fc6))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x00000b267c8e22b81dfd600000b267c8e9f160d45600000b267c8e1c56c416600000b269798e1c60d45600000b7ec9a463887183600000b2693a2e3881d83600000b267c8e1c96d5456000009f23887122398146 else 0x00000b2692969c560d45600000b267c8e1835146e600000002e59f26471545500000b267c8e21c514096000009f26371583514f26000009f2387147a05814600000b7e7c8e2076d583600000b267c8e20160c146) else (if i < 139 then 0x00000b267c8e19b60c8c600000b268b8e1c52f887600000b267c8e1cd6d4146000009f23881dfb60ce6600000b267c8d583514466000009f23881d835500d600000b7e7c8e20760cab600000b967c8e21c515376 else 0x00000b267c8e1fb60d45600000b267c8e2256e545600000b267c9ea3560d45600000b267c8e21c48c6d600000b269771583514aa600000b267c8e1dc60d56600000b267c8e22981d836000009f24271583515186)) else (if i < 142 then (if i < 141 then 0x00000b267c8e1fa60c14600000002e59f238715b3500000b267c8e2355ccc76000009f2388d58339814600000b267c8e2355ccd5600000b6a7c8e23560d45600000b265971583514e1600000b6a7c969c560d456 else 0x00000b267c8e183514d7600000b267c94dc5514c4600000b267c8fdcd60d45600000b267c9518351502600000b267c98e0060d45600000b268b951c560d45600000b26918e21660d45600000b96978e1c55153c6) else (if i < 143 then 0x00000b267c9dd83514c7600000b267c8e9c5514be600000b26a08e20760d45600000b267c8e18356545600000b8a7c965c560d456000009f238715b946012600000b267c8e1b551499600000b7ec99f2382f89a6 else 0x000009f2388718351518600000b267c8e1c56c4be600000b267c8e2354d416600000bd67c981c560d45600000b267c965c5514c0600000b267c9521c51416600000b267c8e9cc60d45600000b967c8e1c56cc006)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x000009f2387156a514bd600000b267c9118351490600000b267c8e1454946d600000bc6c99f2387f583600000b267c8e2006e5206000009f25971545398c4600000b7e7c965c560d45600000b967c8e1c56cdae6 else 0x00000b269171583514db600000b26387158351513600000b7e918e1c560d44600000b6a7c8e20760c87600000b267d8e1c5514c4600000be6c9a2e38715b9600000b467c8e1c561145600000b26978e1c52f8876) else (if i < 147 then 0x00000b267c8e1bf60d45600000b2697951c560d45600000b267c8e1cd62c14600000b267c8e1835150a600000b7e7c8e1c5514b26000009f26371583514ab600000b267c8e21c6e57e600000b96c9a4638871456 else 0x00000b268a8e21660d45600000b267c8e1c56d521600000a5e3887183514ab600000b267c8e18351503600000b7e7c8e20760c146000009f2387cd45488ab600000b7ec99f23860d61600000b267c8e2357f5836)) else (if i < 150 then (if i < 149 then 0x000009f23871548480ab600000bce7c8e183514546000008e1c560d4546111600000b267c8e21c5bd45600000b967c8e21683545600000b7e7c965c560d20600000b26b08e21c60d45600000b267c8e1ea3e0876 else 0x00000b967c969c55e945600000b267c8e21c5148a600000b267c8e23551522600000b267c9b21c60d45600000b268b8e1835146b600000002c99f23a715b95000009f23881d8348518600000b7e7c8e1c56d4866) else (if i < 151 then 0x00000b267c9e61c60c4d600000b267c8e1e360d456000009f638715452ac16600000b96df9f238859456000009f2387a1cd60d45600000b267c909c56d545600000b267c8e20860d45600000b967c8e2355141d6 else 0x00000b267c8e2147c545600000b267c8e183428d5600000b267c9160760d45600000002df9f26c71583500000b268b7158351517600000b7ec99f23860c9b600000b267c8e1c560c8b600000a5e387157a514b26))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x00000002c9a2e388d5b9500000b267c99a54715b9600000b267c98ddd60d45600000b267c8e1833504c6000000027c8e1ce514b2500000b267c98d8351490600000b267c965c560d69600000b267c8e1d960d456 else 0x00000002e59f23881db3500000b96c9b169771545600000b567c8e1f860d45600000b267c8e183514c9600000b268b8e1c560d45600000b7e918e1c560d3c600000b268b8e1c56e4176000000027c98dc5514b25) else (if i < 155 then 0x00000b267c8e1835146d600000b267c8e21160c4d6000009f238715452ac7f600000b268b9520760d45600000b7e7c9b1c56b983600000b267c9de0760d45600000b267c8e2006d414600000b267c8e183515026 else 0x00000b267c8e21c51416600000b527c8e21c83545600000b267c8e1f16e412600000b268b8e183514d5600000b267c8e1b948090600000b268b8e1c56e4e6600000b267c8e2162f887600000b967c8e21c514176)) else (if i < 158 then (if i < 157 then 0x00000b7e7c8e23588d836000009f238715b9460f8600000002918e1c560ced5000009f238871834f0ed600000b26848e21660d45600000b96978e2165e945600000b268b8e183514c7600000b267c8e21c6d5456 else 0x00000b267c951c55143c600000002e59f26385945500000b267c9521660d45600000b267c8e1c56c412600000b96df9f2388d5b9600000b267c951c56e50b600000002c99f254871b9500000b7e7c9660760d456) else (if i < 159 then 0x00000b6ac99f2388d5b9600000b967c98dc551404600000b66c99f238715b9600000b7e7c8e20060ccd600000b2696a2e3871545600000b6a7c8e1c55f545600000b267c8e9cd60d45600000b267c8e23560c146 else 0x00000b26978e183514d56000009f238715452c80c600000b7ec99f24271583600000b268b8e1c56e487600000b267c8e23260c14600000b267c991c560c87600000b967c8e1c56cc07600000b26978e1c560d456))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x00000b267c951c56e51e600000b967c8e21c63545600000b26978e183514c7600000b26c0a460760d45600000b96df9f23880983600000b967c8e1c56cd20600000b267c8e18332061600000b7e8a8e1c560d3c6 else 0x00000b267c8e1c56e51a600000b96c99f25487145600000b967c8e216514186000009f238715835f8ed600000b5e7c8e20760c0d600000b26387c58351511600000b7e988e1c560d3c600000b267c8e1cc6e4126) else (if i < 163 then 0x000009f25471583514b7600000a463871583514e6600000b267c951e5514be600000b7ec99f264715b9600000b26bb7158351430600000b96c99f2388d535600000b267c8e21c51509600000b267c8e1453109a6 else 0x00000b66c99f238714f8600000b267c8e2356e50a600000b267c9c5cd60d45600000b267c8e1c56ccc4600000b267c952356e583600000b2693a463881d83600000b967c8e21c67d45600000b267c8e1cd60d326)) else (if i < 166 then (if i < 165 then 0x000000027c8e1c568983500000b96df9f23881d7e600000b96c99f23885d45600000002e59f2388a61c500000b967c8e1c56cc8c600000b267c8e1c56e5b1600000b267c8e21c23016600000b267c8e21c514536 else 0x00000b267c8e1c54a4f8600000b467c8e20760c14600000b6a8b951c560d45600000b267c8e21c51d45600000b268b8e20760d45600000002dfa463880183500000b967c8e21c6cd7a600000b96dfa4a38715836) else (if i < 167 then 0x000009f238514ab26816600000b26918e2326d545600000b967c8e1c56cc7a600000b267c9663560d45600000b267c8e2014f8be600000b26388718351432600000b267c8e19d514be600000b263871583514a76 else 0x00000b26c1a49c560d45600000b7e7c8e2326d53c600000b267c8e1f16e4f8600000b967c8e1e5514e6600000b967c8e2076cd45600000b267c9663260d45600000002f3ac23860d455000009f2387158347ced6))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x00000b267c925c560c8c600000b267c8e2356cd83600000b267c8e9c56e520600000002df9f23881db5500000b7e7c951c560d3c600000b267c8e1bb60c9a600000b267c8e21660d45600000b267d8e1c55f5456 else 0x00000b7ec9a4638714c46000009f238715a160c07600000002dfab23881d835000009f2388716751416600000b267c8e18341c876000009f238715b32ac16600000b267c951d660d45600000a46387159f60d456) else (if i < 171 then 0x00000b26b28e23560d45600000b268b8e20760cc7600000b267c9521c6e5456000009f23881cab05814600000b267c8e1ce60d32600000a463871583514ed600000b267c715835150d600000b267c8d9c560d456 else 0x00000b267c9260760d45600000b26a08e1c560c14600000b268b8e2356e520600000b267c8e1c56c087600000b268b8e1c56e511600000b967c8e1c55147f6000009f23887183514b2600000b267c715835150c6)) else (if i < 174 then (if i < 173 then 0x00000b267c951c56e474600000b267c96607514c4600000b267c8e20960c14600000b7e818e1c560d3c6000009f2387156b514b2600000b96c99f23887145600000b267c71583514db6000009f23860d505140e6 else 0x00000b267c8e1cd6e412600000b2638715452a02a600000b26bba4dc560d45600000b268a951c560d45600000b7e7c8e1f860cc76000009f2387c5b948118600000b7e7c8e1c56d407600000b267c715835150b6) else (if i < 175 then 0x00000b267c8e09a154146000009f238715833b486600000b967c98e0760d45600000b267c9521c6e5206000009f238715ae60d69600000b7e7c965c56d583600000b268d98dc560d45600000b7e7c965c560c166 else 0x00000b6a8b8e1c560d45600000b267c8e21451408600000b7e7c8e1832ac9a600000b267c81d8351447600000b267c8e1de60d45600000b7e7c8e1831601c600000b26978e20760cc76000009f23871545460c46)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x00000b267c8e23160cc7600000b267c8e1c5478f8600000b267c8e21c5149a600000b267c8e21660c8c600000b267c95183514fc600000b6a7c8e18351502600000b267c9121c60d45600000b96df9f238715ae6 else 0x00000b727c965c560d45600000b26918e183514cf600000b267c8e1c53e0bd600000b6a7c8e21c51416600000b26a38e1c55e145600000b267c98d8351493600000b267c8e1c56d569600000b267c8e20760d516) else (if i < 179 then 0x00000b267c8e21060d45600000b7e7c8e1834f0cf600000b7e918e20060d456000009f238715a260d45600000b7e7c8e1f860c0d6000009f2387156a514e6600000b967c8e22987145600000b26848e1c52f8876 else 0x000009f23860d451501d600000b26918e183514d5600000b267c8e1b960d5d600000b267c8e21c63145600000b267c8e23560cf8600000b267c8e22b77145600000b26978e20760c8c600000b7e7c8e1c560d3c6)) else (if i < 182 then (if i < 181 then 0x00000b267c8e19660c8c600000b267c8e23160c8c600000baadf9f259715836000009f2388d58351518600000b7e7c8e1834f0d5600000b267c8e1fb60c14600000b26918e183514c7600000b267c951c52f8876 else 0x00000b267c8e21c8504d600000b267c8e1fd60c1c600000b26a08e1c56cd836000009f2387e183514e9600000b7e7c8e2076d545600000b6a978e1c560d45600000a063871583514e6600000b96c99f2388708c6) else (if i < 183 then 0x000009f2497158339814600000b267c87183514a1600000b7eac8e20760d45600000b267c8fdcd60c14600000b7e7c8e23560c17600000b268b8e1d060d45600000b268b8f1c560d45600000b267c8e1452e0556 else 0x00000b267c8e22760d45600000b267c8e23560cea600000b267c8e17d5149a600000b267c98e1c60d45600000b267c8e22d60d45600000b268b94dc560d45600000b267c8e20060d21600000b267c8e1dc514676))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x00000b267c9ce5460d45600000b267c8e20760c156000009f23871583488ed600000b7ec99f2387e983600000b7e7c965c560c14600000b7e7c8e20060c86600000b7e7c8e20760c5a600000b26918e1db60d456 else 0x00000b26988e1c560d45600000b267c8e15e514c4600000b26b08e23560d45600000b967c8e1c56cc16600000b268a8e1c560d45600000b268b8e1c561145600000b267c8e21c51491600000b267c8e183514f46) else (if i < 187 then 0x00000b267c8e1dc60d696000009f2387153c3b4c4600000b267c8e1f1514c4600000b267c8e21c514f8600000b267c9b23560d45600000b267c8e21c52120600000b267c8e1ed60d45600000b26bba2dc560d456 else 0x00000b267d8e21c51416600000b267c8e183514fc600000b267c8e1c55152d600000b26aa8e1f160d45600000b967c8e20d514d5600000b267c8e1c56d4ed600000b467c8e1c56d545600000b267c8e207659836)) else (if i < 190 then (if i < 189 then 0x000009f238715452b017600000b26918e183514d8600000b269794dc560d45600000b96df9f238514d5600000b267c8e1e755d45600000b267c8e1e55149a600000b267c8e1c160d45600000a06387159f60d456 else 0x000009f238735833b4e6600000b267c969c56d545600000b267c8e1c52f887600000b267c8e1b9674d5600000b62c99f2388d583600000b7e7c8e1834f0d8600000b26918e20760d45600000b267c8e1c460d456) else (if i < 191 then 0x00000b96c5a5dc560d45600000bae7c8e1f860d45600000b96df9f25971583600000baae59f238715b3600000b267c8e17d51491600000b26848e1c560d456000009f2388598339814600000b2638715b9481116 else 0x00000b267c8e0c72f887600000b267c8e2326d545600000b267c8e23251416600000b967c8e235514e66000009f2387c5452ac16600000b267c8e0d52f887600000b267c925c551522600000b56c99f238871456)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x00000b267c9de0760c14600000b96c9a4a3887145600000b267c8e9c56e416600000b267c951c560d45600000b267c951c56e417600000b267c9865471545600000002c99f2548d5b9500000b267c8e1cc514c46 else 0x000009f2387157e514af600000b267c8e1cd51467600000bce7c8e20d60d456000000027c8e20760ced500000b26838e1835149a6000009f238514c82ac16600000b6ac9a2e38715b96000009f238715482ac126) else (if i < 195 then 0x000009f23871583514ed6000009f2387153c2b00c600000b26918e20760cc7600000b967c8e1c56cc14600000b267c95183514c7600000b267c95183514d5600000b46c99f238770be600000b6a7c8e1c56e51e6 else 0x00000b267c8e23535416600000b7e7c8e2004f0c4600000b967c8e21c39814600000b267c8e21451490600000b267c871835144f600000b267c8e1c260d45600000b267c8e1582f887600000b6a7c8e1e5514be6)) else (if i < 198 then (if i < 197 then 0x000009f23881df860ce9600000b267c8e21c5c145600000b6a7c8e2356e5836000009f2387157a514b2600000b267c8e1453606e600000b267c8e1db2f887600000b7ec99f238801b5600000b6a7c715835150b6 else 0x00000b268b951c56e583600000b96df9f2387147a6000009f238731452ac16600000b267c98dc5514c0600000b267c965c860d45600000b967c8e1c5520be600000b268b93dc560d456000009f263715b360cab6) else (if i < 199 then 0x00000b267c8e19560d45600000b269998dc560d45600000b7e7c8e1c56e407600000b7e7c8e20760cba600000b96978e1c55151e600000b267c8e22781d83600000b267c8e1c56e541600000b267c8e1ea60cf86 else 0x00000b8e918e1c560d45600000b7e7c965c56e583600000b7e7c715834f046600000b26a09b1c560d45600000b7ec99f2388d5836000009f2388718351454600000b5a7c925c560d45600000b26808e1cd60d456))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x00000b267c8e1ce51467600000b7ec99f2388c983600000b267c8e21c57945600000b268b965c560d45600000b7e91965c560d3c600000b967c925c5514bd600000b967c8e2165e945600000b263880183514e16 else 0x00000baac99f2388d520600000b26388d58351432600000b267c8e1e4514c4600000002e59f2637148c500000b267c8e1c56e52b600000b267c8e1ef514c4600000b267c8e1fa6e545600000b267c8e21c2404d6) else (if i < 203 then 0x00000b6a7c8e21c6e545600000b267c8e183514cf600000b267c8e1835145b600000b268b8e1c56cd83600000b26818e1db60d45600000b96978e2075e945600000b267c8e1b960d0a600000b967c98dc5514a16 else 0x00000002e59f26381d45500000a2e547158351518600000b267c965c560d4f6000009f2387158351480600000b26387158359945600000002df9f259715b5500000b267c951c56e420600000b267c8e1c560d456)) else (if i < 206 then (if i < 205 then 0x00000b267c951c560d4e600000b268b8e1c56e423600000b268b8e20c60d45600000b2697965c560d45600000b267c8e1cd514c4600000b5a7c8e1e551416600000b267c8e1834d49a600000b267c8e183514d56 else 0x00000b268b8e1c56e583600000b26978e1c56cd83600000a4a3871583514e6600000b267c8e18356145600000b6abba2dc560d45600000b6a988e1c560d45600000b6a8a8e1c560d45600000b96db9f238871456) else (if i < 207 then 0x00000b26978edc560d45600000b267c8e1db60d45600000b267c8e18351504600000b96c99f2388c945600000b267c8e1c53e017600000b267c8e1835149f600000b268b8e21c60c87600000b7e7c94dc560d3c6 else 0x00000b5e7c8e1f860d45600000b967c8e1c56e5b3600000b267c952356e520600000b7e7c8e21860d3c600000b6a7c8e183514fc600000b267c9520760cc7600000bc67c9ddf860d45600000b967c98dc5514076)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x00000b967c98dc56cd83600000b6a7c8e1c52f887600000b96c99f2388d4d5600000b267c8e9c56e412600000b267c8e1b55146e600000b267c8e15a2f887600000b267c8e1be60d45600000b267c8e183514ff6 else 0x00000b268a94dc560d45600000b267c8e183514d8600000b267c8e18331c8c600000b267c98dc5514c4600000b268b8e1c560cf8600000b267c8f60760d45600000b267c8e1ce514c4600000b7ec9a8238715836) else (if i < 211 then 0x00000b267c8e21c26814600000b967c98e1c5e945600000b268b951f160d45600000b6a7c951c560d45600000a2e387158351518600000b96978e1c5514a6600000b967c98dc55148c600000b267c8e2026e5416 else 0x00000b267c8e2353549a600000b26918e1c560c14600000b267c8e1c567cf8600000b26988e21860d45600000b96df9f238715b5600000b267c969c56e545600000b267c8e21360d45600000b26938e1c560d446)) else (if i < 214 then (if i < 213 then 0x00000b7e7c965c560c0f600000b7e918e21c60d45600000b967c8e21c5f945600000b267c951c56a945600000b7e7c8e1dc60c14600000b268b7158351430600000b267c8e216514b26000009f238715a260c146 else 0x00000b7e7c9b1c56e583600000b26918e20660d45600000b267c8e20260d45600000b267c8e1c56e5b2600000b263871583514e0600000b267c98dc56d9836000009f263715452ac16600000b26928e1c56e5416) else (if i < 215 then 0x00000bdedf9f259715836000009f2387c9452ac16600000002e5b169771545500000b6a7c8e1c56e541600000bda7c941c560d45600000a5e387158351518600000b267c8e20760cc7600000b7e7c8e21c4f0906 else 0x00000b267c8e23160cd4600000b267c8e17d26814600000b267c8e22d60c14600000b7e7c965c560d43600000b7ec99f2387ed836000009f2388458339814600000b267c8e20760cb1600000b267c8e2356e5206))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x00000b267c8e18356945600000b267c8e20760c0d600000b267c7158351446600000b267c8e1c560d40600000b7e7c8e21c60c86600000b267c951c561145600000b267c8e20760c8c600000a8238715835147a6 else 0x00000002da9f2388d5b9500000b267e8e21c60d45600000b7e918e1c56d53c600000b2691965c560d456000009f238715833b4ab600000b96978e1c551541600000b26387158351512600000b267d951c560d456) else (if i < 219 then 0x00000b7e7c8e1834f09a600000b267c8e21160c4b600000b96978e1c551421600000b268b8e1f160d45600000bcec99f2388a583600000b267c8e21c85145600000b6a7c8e1c560d45600000b6a7c8e1c56e4176 else 0x00000b96df9f23881cab6000009f23860ce631c14600000b26918e1c56cd83600000b6a7c8e183514d5600000002c99f2387a8f8500000002c9a2e54715b9500000b26ac9de0760d45600000b267c8e235480f86)) else (if i < 222 then (if i < 221 then 0x00000b6a8b8e1c56e5836000009f238715833b4be600000ab23881d8351458600000b267c7158351475600000b267c8e23505814600000b267c8e18551490600000b267c8e21c52012600000b267c9520760cd96 else 0x00000b6ac99f254715b9600000b268b8e1c56e518600000b268a965c560d45600000b268b8e1cc60d45600000002c99f2386e50a500000b26978e1f160d45600000b267c8e2326d414600000b2a918e1c560d456) else (if i < 223 then 0x00000a5e3885983514ab600000b267c8e1c53dc876000009f2387159f60c14600000b267c8e1e53e0be600000b267c94dc560d45600000b267c8e22d6cd83600000b26387158351515600000b967c925c5514e66 else 0x00000b268b8e1dc60d45600000b26a08e1c56e520600000b267c8e183581456000009f1c560d454610b600000b268a8e1c56cd83600000b7e7c8e20060cab600000b96df9f23881cbe600000b26b08e21c514026))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x00000b967c8e1c56cd3c600000b26818e1c560c14600000b267c8e1c53a0ac600000b7e7c8e21c4f0c4600000b267d8e1c560d45600000b26988e1c56cd83600000b268b8e1c56e477600000b7ec99f27781d836 else 0x000009f23881d8339814600000b267c9c254715b9600000b26808e1cd60c14600000002c9a2e38715b9500000b267c9c9e560d45600000b967c8e17a514c7600000b267c965c52f887600000b267c9023560d456) else (if i < 227 then 0x00000b267c8e21c6e507600000b7e7c8e1dc60c19600000b268b8e1ef60d45600000b268b8e1c56e5ae600000b7e7c909c560d45600000b267c8e1ea6e520600000b268b8e1c56e400600000b26c571583514216 else 0x00000b967c8e21c51522600000b267c8e23560d56600000b267c8e183528d5600000b267c8e21c6e523600000b6a7c8e20760c07600000b26848e1c56cd83600000b267c8e1bd60d45600000b26bba2dc56e5836)) else (if i < 230 then (if i < 229 then 0x00000b267c951c56cd83600000b6a7c8e20260d45600000b6a7c8e1c56e5b2600000b267c8e18351508600000b264771583514a6600000b267c8e1454949a600000b267c7158359145600000b96df9f238715b96 else 0x00000b2681965c560d45600000b267c8e19460d45600000b6a7c8e2356e520600000b6ac99f238715b9600000002c9a2e38714f85000009f238871b360cab600000b6a7c8e20760cc76000009f238871452c8166) else (if i < 231 then 0x000009f25981d83514e6600000b26978e1ef60d45600000b267c7c5835150b600000b268b8e1cd60d45600000b7e7c8e2077e056600000b267c8e1ea480f8600000b268b951c56e5206000009f238715201e8176 else 0x00000b26978e1c560c88600000b268ba2238715b9600000b96c99f2388d414600000b7e91a3e3871583600000b26a2a5e3881d83600000b267c8e21c514ae6000009f238625835141c600000a2a3871583515186))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x00000b267c8e21623016600000b6a8b8e1f160d45600000b267c9de0060d45600000baaa08e1c560d45600000b267c9521c60c87600000b96c9a5e3871545600000b267c951c56e583600000aee8b71583515186 else 0x00000b267c965c560d45600000b267c9b22d60d45600000b267c8e1b94810a600000b7e918e1c5514c4600000b267c8e1c56e48b6000009f23860d45460fc600000b267c8e14531099600000b6ac99f238714f86) else (if i < 235 then 0x00000b267c8e20760d5f600000a12387158351518600000b967c8e1c52f48c6000009f238715182f887600000b5a7c8e1c55f945600000b7e7c8e1f160d3c600000b7e7c8e1c56d53c600000b26978e1cd60d456 else 0x00000b267c98e1c514166000009f23885983514b2600000b26c0a460060d45600000b267c8e1c53e0f66000009f2547158351518600000b267c951c560cf8600000b267c8e1cf60d45600000b267c8e1c56cd836)) else (if i < 238 then (if i < 237 then 0x00000b7ec99f2388709a600000b268a8e1f160d45600000b6a7c8e1c561145600000b267c8e1b94806d600000b267c8e18351472600000b268b8e1c56e520600000b267c8e1833549a600000b6a7c94dc560d456 else 0x00000b267c8e20260c14600000b26bb7158351422600000b267c8e21f87145600000b26bba2df160d45600000b6a7d8e1c560d45600000b26978e1ce60d45600000b267c9760760d45600000b26988e1c5514166) else (if i < 239 then 0x00000b26978e1c56e520600000b267c8e183520d5600000002daa2e38715b9500000ac23887183514ab600000baac9a4a3871583600000b967c8e21c514b2600000b267c8e18351491600000b96a08e1c560d456 else 0x00000b26978e1c5514bf600000b268b8e1c56e47a6000009f2387156721c0c600000b267c8e1c52c88c600000b267c9920760d45600000be2e5a5e3871545600000b268b8e1c5480f8600000b267c8e21c60ced6)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x00000b26828e21c514906000009f2387158351518600000b267c8e1835146f600000b267c8e19a60d45600000b267c8e2356e412600000b7ec99f2388b583600000b267c8e21c51499600000b267c8e1c560cf86 else 0x00000b26918e1e7514c4600000b263871583515166000009f238715b567d45600000b267c8e1c56c007600000b96c99f2388588c600000bce7c8e20d51416600000b267c951f160d45600000b267c8e1ff60c146) else (if i < 243 then 0x00000002c9a6238715b9500000b267c8e1c54f8be600000b7e7c8e2356b983600000b267c999c560545600000b267c85983514a1600000b267c8e14531c56600000b267c96600514c4600000b267d8e1c5611456 else 0x00000b268a8e1ef60d45600000b267c951c56e518600000b267c8e1e5514c4600000b267c951cc60d45600000b267c9b1c560d456000009f23860d451701b6000000027c8e1835145b500000002c9aee8b715b95)) else (if i < 246 then (if i < 245 then 0x00000b967c8e21c84945600000b267c715b94810b600000b7e7c965c560d7a600000b96c9a623871545600000b267c901835146d600000b7ec99f2388c9b5600000b267c8e1f360d45600000b267c951c56e5a86 else 0x00000b267c8e1b5514d5600000b267c8e20751456600000b267c8e14535416600000b267c8e18327814600000b267c8e2356e4f86000009f238795452ac16600000b267c8e1f160d45600000b6a7c8e1c56cd836) else (if i < 247 then 0x00000b267c951c56e5ae600000b267c951c56e440600000b26928e1c56e583600000b267c951c56e400600000b7e7c98dc560d3c600000b6a8b8e1c56e520600000b7ec9a063871583600000002c99f254715b95 else 0x00000a5e3881d83514ab600000b268b8e1c56e416600000b26978e1c56cc16600000002dfa823871583500000b267c71583514a4600000b267c8e2358ad45600000b267c951ef60d45600000b267c9a263715836))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x00000b268b8e9c560d45600000b7ea08e1c56b983600000b267c94dc56cd83600000002c99f254714f8500000b267c8e1cc60d45600000b26adab23881d836000009f23881d83460c7600000b7e7c96657715836 else 0x00000b267c951cd60d456000000027c8e216514b2500000b267c8e2186cd83600000b26977158351427600000b267c8e197514be600000bdac99f254715b9600000b7e7c8e1c56c9836000009f2388d5b9481186) else (if i < 251 then 0x00000a2e387c58351518600000b268a8e1c56e520600000b267b8e1c560d45600000baac9a2e38715b9600000b267c8e1b5514d8600000b267c8e22d6e520600000002c99f2383549a500000b7e7c8e23560c1e6 else 0x00000b267c8e1b9480fc6000009f1c560d4510020600000b928b8e1c560d45600000b96dfb267c8e235600000b26bba2dc56e5206000009f238715833b47b600000b6a7c951f160d45600000b267c8e1c5460f86)) else (if i < 254 then (if i < 253 then 0x00000b267c951c56e5206000009f2537158351518600000b26ac8e20760cc7600000002c99f238714f8500000b967c8e1c56cd1e600000b267c8e2076d4c7600000b267c9e26360d45600000b267c8e1ef60d456 else 0x00000b267c965835149a6000009f6387158351518600000b2691965c56d545600000b267c8e1c56b8f8600000b267c8e1ea6e4f8600000b26baa29c560d45600000b267c8e1cd60d45600000b267c8e1c53e0006) else (if i < 255 then 0x00000b267c951c56e47a600000b267c951c5480f8600000002da9f254715b95000009f23881d692ac166000000028b8e1c56e518500000b268b8e1c56e412600000b26898e1c560d45600000b6a7c8e1f160d456 else (if i < 256 then 0x00000b268b8e1c56e422600000b267d8e1f160d45600000b267c8e1c56e520600000b267c94df160d45600000b6a7c8e1c56e518600000b6a7c8e1cc60d45600000b267c8e1c568d69600000b267c9520760d396 else 0x00000b268b8e1c56e4f8600000b267c8e1c5480f8600000002c9a2e387c5b9500000002da9f238715b95)))))))))
def g1_l5S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l5C (i / 8)) 84 (i % 8))
def g1_l5HC (i : ℕ) : ℕ := (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x027ad4ff0273fdd0026dfd3002667497025007fc023bd1cc022cbb73021a12c002158a0e01b182f701a21a71018bb89f015e5214014ce27b0142835f0131fa5d011b37030107eb8201044e0c00ef9a4400d1af2100b324c000a1e40400a12f86008a59e80082d8120082ace60062ff0e003469d90020165d001dd44100123397 else 0x051faa95051361090508254004cade5e04982867048990e90481602a043d90d904370cdb0435855b042d8ce7041817fa0413477d03f215e203edfd5303df6f3903da9ab703d3115d03a750d00364258e035f494e035e6c7503550055034c6961034ad8d40349337202e4ccb802de171802da8e9702d5299f02c5677d02ac5489) else (if i < 3 then 0x07408507072b1e62071d13d206d7e1f106ccc63206bfaf7d06b7f09d069e645d068db527068b8276067be60c066ab968065f3bdc0643b16106421236063eed440636dfe4060b3d9f0602fb8405d1833905b95e5605b7791c059d4aad059b3a4305903bdf058df666058bdc5d058856750555e38f054910bf052c76e005270966 else 0x099f1ac1099f0da709871af8098633e6098056000936f87a092faae809264c8208b061df08a6d56008a1d818089ba98e08889a66087e8d8508752c7d086d970f086b9d86086925a4085d05cd084ee01708489d01081369a2081057a5080ab75b07faf82607f71b8807c9182c07c0012407a1b66a078d0fa7077da2aa07596213)) else (if i < 6 then (if i < 5 then 0x0b74a1670b5eaf290b56a9c90b5652550b3c7afa0b3256080b2be1740b2537500b1571dc0b14951b0b0112330af4384a0aebb70e0adff37a0ac997c60ac15ef70aa7a5b60aa427e70a486ef40a4398a70a16ed800a0e94050a06d2920a03ef5009f7126109f1a87d09ef167609dd2d2e09d6ae5909d1998509a82bcc09a16033 else 0x0ddaa9450dcda7370dc2c41e0dc1cc230db07e2e0da8d9670d9d3d620d9714740d7f9ea40d419f340d25f7350d0ca87b0d05d2c40cfb62e60cd56c630ca6dfde0c8b3ea20c8af81d0c862ddd0c5cf31a0c5c0ff50c4b41920c3dded20c06e1590bd652590bd6029f0bbc460d0bb7f32f0ba7b3650b9121d00b8e63f90b85fb22) else (if i < 7 then 0x1068f899104da03c102d63e9102213a91013937b100fec0a0ffaf1420ff74f9c0fefaad50fe48f5d0fdd8a940fd249570fca51e80fa150320f9cfb730f7eced80f6ce2270f50da480f354b2c0f0f5f9a0ef10bb90eb2ed1c0e926c3f0e712c7d0e54f2e10e4640920e446c4d0e29515f0e199fd10e0f61b00e06fcdb0de2ca9b else 0x131b8c9813059dc712fc9e2e12da626a12d2288d12ce295212c6dd7612b932c912b575b812ab13e9128f7c0b127d3368126b3996122af8bd122ac0b111b3841711afb8a811a4747411776d6011700f6a1160cd1b11206e2710f546a810f4a25f10e10e2310c6795010aad90110a157f6109cb80510858a5c107b0dad106a553e))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x146053e41442f78e14302ebd1427de5a141ada1d1412ff371410364513fec0b613d0b58013b641b513b17d1d13a797a513a6febd13a5b8e313a39da4138eb39013895d2c138819fa1386c50313840fef13832f61137fd879137109ba136e25c2136ade231361bf101345d4ec133c40401337e396132fdca7132bd888131d6305 else 0x16c3253e16bbd4c816b8644616a52bf016a398b7169474bc16938242168599af166bbb2c1662afc316557e35164d794315e3ff8915dd1a5c15dc78cf15d9be1b15d8275615d3470715ce5a0f15b848af15a1e3bd159737c715786bc015478d8a153f1bdf153d9a0f151d94fe14f71f2114d2406214bcce7814b1f172149cda40) else (if i < 11 then 0x18de5bc718dd89e318c77eda18be12f118baf0b118862ff4187cbae31863c04d184e11f71834c631182b6ca21818928618176d1418095b571804ae7817e326c017cb819917c83b8217c7646617afc8181797d93a178cad5f1782b80717462217173f2bfd173ef832172370ab170d433d170c127e16f3c81316f11bec16db2dfb else 0x1a865b301a85ad611a6ac1e51a6aa0a71a5495521a502cc51a480c751a4806551a4621ff1a45b1bf1a24ba561a1b7ab81a020c7119ec38b519e25ce819a23458199ddb071987c7b71983cc7819753a77196e827b195ab184195702c11955465e193f45fc193dae06193b5c3b1932a9cd19243f0f19146e2619010e3318f66542)) else (if i < 14 then (if i < 13 then 0x1cbd98101ca98b8d1ca20bce1c9432141c597eb61c532b721c4a06a71c4213f51c30bf581c17e2651c07c7881bed1e761be016561bd787b01bbbcdf31bba5d751bb504661b9386061b8f206c1b74fe931b54cb631b34a7d71b2fc45b1b12f1f91b10a0a01b0f2b371afef8161ad365a61acd79701ac3fea81a963fef1a9622c7 else 0x1f15046a1f0282491ead65b61ea6a3a01ea048421e9803fc1e9052681e8ab45e1e8521821e5efd071e5cccd31e52361e1e3f774b1e3a70e01de97ece1de8e0901dd061c11dc9c8731db7d8ac1db266a71d9b67c41d99e2d31d7230da1d50bece1d369f211d2efa5a1d2ec5731d2bf42e1cf1230b1ce17d011cd5fcd91ccf3d90) else (if i < 15 then 0x21e378c721c1c45b2191cfba217ae14e215ecc972153e0fa2125562f2109da7920d303ad20bfef0820bf1a122050f5402045a97d2040a278203e3c86201d85a3200691291fe03ac71fcd60481fcafd0a1fc714861fc40ea81fbd53cc1fb0bf021faa88a31f954dbc1f80cecd1f80251e1f6501d61f327c721f2c1e041f1eec76 else 0x24c8a17824b6e0ed24ae18cd24aa3c792483e47424427ad72408cee42403f2a423ecf7d723e1532d23d4b00e23ba63ed23abbd8f239acb97239a66f723714c2e236410b1234c6c3a233e4a40231a25a422f8f39422e510c122d386aa22b88f4422b4e2f222b493c922968b2322952fc42290df6d22759a7b225843c42215ab4d)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x278f7c4a277bd8632763e51427451838271c5ea8270f2d1a2702728d26cb920126a445a5269785f12695d4a0265fa18c2654ad6f26339e19262acdf72623c28f261f3c98261e22562618040a260d44d526074c742607026625fde89125bb11f22591072325811241257cd96e257a84d8257849692538d45324d1aa9a24cd9d9f else 0x2a29c2eb2a01d55e29ff357929f2cd9229e3fa5829c446f329c2a86b29b2e24929b17a4a2982e943297b9647296eb66d29687ddb294c0f0729478c172923fbfa28e812f128bfe94528b0e3c5287b44a42860c747285ddf33285c3bcb28547f59284f077628370db02832f7a1281da23027c6e29927bdcb9c27b97c162795f2f8) else (if i < 19 then 0x2bf7f2f02bf3ed2b2bddf9442bb673662baf894c2ba137592b9e11512b944c412b89f6812b86e8e72b83fdb42b7e020a2b712cc82b6108432b56d2e12b4087be2b3e634d2b3ae6372b247ec02ae5921b2ab5f8ee2a9afaac2a9005522a809d262a7f944f2a7b5e8c2a73dd5a2a708c5c2a5d76372a55cf292a2e88c22a2ddb82 else 0x2f63ca022f5e48a62f3248ff2f1626462f07b1b12ee03e9a2ec715892ec285552eaa8dbb2ea0c9862e9baae72df17df22dbbe50d2dbb8b0d2db4b0262d92207d2d89ad992d8670022d7ecb3b2d6306eb2d25a3cd2d1ff5de2d17caf12cf354df2ccd9eea2cc869b32cb393cc2ca4f73b2c9c85a52c49eba72c0d4b772c04f4ae)) else (if i < 22 then (if i < 21 then 0x31c6d18731c1cc3531bc060331aed475316867f7315623473109843130f0481430efe01930e3ad1f30ce3cef30c50afd30ae11fc309c45513095327e3077206830472c043045f495303d0174302b93193001c66a2ffd1a552fd47f492fd17d962fcc98232fc6b2e72f8f08052f7c4c792f7affc42f772cbb2f6c40df2f655a52 else 0x33cf24d933cab53733c223fe33c108303392b24c3354721a333639a433302067332a7323331b16683313f0ff3308e740330589b732f8b3ee32f5032a32e7633f32bef4ae32bc9f86328f5f0332898e6a32820b8f325375333246f92032439c6d322785a9321ec950321c3c7f3211813b320a44ef31f7983831f0863931ce764e) else (if i < 23 then 0x3756f4db3746781c3744a59e373dd6853703ea8536e0c51e36df0ae536d9205736cfe01436c68e4a3698130f3696fe1f3679340b36528d5a363a35bd3622407c3600a66a35e20f4a35cfcdc535a05dad3583ffe4352aa2d8352005dc35067fb834ff4a2d34f91a0c34a76785349974ae347c22e43453b974343cabf43428265b else 0x3a09358b39ea4b8a39e85a5939e3b63e39d60079398ee3543974873d3973ccdb3966287e395b0a08394dde143908e71b38fe5dda38d96e5538d80d7838b891ab38b031a738a6fea13883db1c38808b913878a204385073db384ce33c37fab16037ee298a37ea665737dfa41e37df4d2b37d50a9437bda5a3379e0fde379bdd3a))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x3d4f5da83d1fb09c3d1f0dc83cf3d75e3cf0d91c3ce3a78e3cc7dfd63ca873743c7457a23c6bd8e43c6822673c67811f3c251b2d3bfa24f93bd8dd463b6a5c2a3b654b833b52fcab3b25d1203b1ac44d3b137fdb3b0952623ad7221a3ad3b9393acd3e7d3ac6a8b13aa937af3a5bda233a55161b3a54cdeb3a40927b3a3cf1a8 else 0x41891dc2416f08d64146d3d5413b27a04139a247411dfbdd410e58394108c67740b8d2fd407775ee402587703fa4742d3f992cb13f8d8ca33f8084ee3f7a24213f5f9f503f56c0a13f2c12eb3ee9ffee3ed6c56f3e763a163e6b0c6c3e585daf3e3a6ae43e1185bd3e0922a03dff167d3df655793d7e19fd3d6b3a1d3d682693) else (if i < 27 then 0x445dc5f74459d6484443cbff443290334407dcf243b423b443b0e33b43a2370343a1900a4390acb44379d87c434db5d6432632e943003f4d42fc3fb842e75e1442e38df042ce21f742cd904f42c24c9842c224b742a0d05842769e264246a6b24241d7f5422524ab42231c44421bd76e41ece78341e85b7041e0b7df41b1c22a else 0x47374f84471f00e0470eac084704548d46ebeb9a46cf737046c8a45746c8325d46bf98044649de0946430775460af3b945f23af545c13ab945bf749645bae7a945a274ee45a1ece545830a414577c6534568303d4566f8f74539dd81452a08fb451fee624511b91a450ec62744e8ef3944cc0bbe44bf4a0a447fe909446c5676)) else (if i < 30 then (if i < 29 then 0x49ab7f5849851935497ea54649799e404977927349772a54496f817549320bcf492969dc49235f1e490e038748f5cfbe48ec497148ebeaa748e402ae48cfbdf148c9024b48c6d96948b5e95248a4dff4488430c1488303284852cfba483125854814e5684814594947ff420047f43d414797a04b47876d2d4769c504475e803b else 0x4bf58f4f4be1c2404be1baf84bcf16614bccaf6b4bb969144ba112ac4b842afa4b713cb74b6ec2334b2a0cc14b1ef32e4b1a35454b10669e4b04a0644aeb53d54ab66d174aaec6714aa3ef124a97ecbd4a94f9554a8f8d504a8d0c684a85c8414a76ee4d4a6784be4a62fb854a1f5aac4a07158f4a00a56949fdc44749f5616b) else (if i < 31 then 0x4f084d0a4eb9c61c4e706aaf4e6d5a1f4e3512664e2827ff4e114f6a4dff32074dfab42f4dcc4c9a4da8869b4d9a5c404d75027a4d0cd0954cdcd11d4cd1bb574cca14604cb71dee4c7e79724c7dbd5b4c780a524c6e75604c63f2804c5e53c04c59e2234c5111944c4fa5b44c32e0c54c2ac7c04c2432514c198daa4c14c12d else 0x525ecb53524d1a6a52460268523ce5b7523c66d05232d3fc522510cb51f95e03517713165176b2f0515dea055159f9c1512d8d1f50faf1bd50da66af50d4b5b250c6b71250a62d35509d87f2509972a050167aba4fc4a1e14fa92c954fa8d4214f98e1b14f6ae1824f5dc8ab4f4bb70d4f4a253f4f36cfac4f335a214f3041a8))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x56102791560a94ec5603341055f7533455b8011e55b465cd55b18767558628f7556f62075550858655388299552d6dbb55240e6654ef5bc654c6bcb254b65ec154af7ed3548826c1545f27f45452da7f53de360053cfcebe5390d03f53829ee553708366536a8c3a534a4dcc53475c15533af53b52c36e6f5291efec52645dab else 0x5953a92b593c1a5259223dc558f5296c58e84d4c58de414858cd8af458b9670958b75e3358b6d59d583e71e5583d6e38582fadc657dd633657c517a957b595f257ae511c578dde90578bc7ce5777092b57509a105703e6cb57009fc456dcdfa156d9d45556d66ef756bc830256b2b964566c6585564f7c4d564f1dbf56429a38) else (if i < 35 then 0x5c3b1e145c2fed3c5c281e575c178c1e5bfa57cc5bfa26a15bfa16a55bdaa2625bbc2add5b8e6dd25b3585725b26ea5f5b15e0455b142da25ae2e3995ad649665aca10e25ab77ba35a91eb135a4dbbda5a48b30e5a3ee4e45a3d20235a33ad145a2d326a59ed3e9959dcd9ab59db7a1a59d4ab0159b45a5259992802597f94bf else 0x5fc9a11d5fc5b1ee5fb64b225f8ff3a35f8f1e2a5f8aabda5f872bbf5f53c4225f4c54535f3912335f1309195f11fd105f064e4a5efcdb7d5edb08765e8c12d75e8ae5145e7dc9ee5e738f3c5e64dd085dfee42a5de231645d92dd455d84209e5d7e9ec35d6db27c5d22f0aa5d118c065cc14fd05c7e65485c70ff545c5211b2)) else (if i < 38 then (if i < 37 then 0x6427270063e7fb5d63c36bf66378c20b637100cc635824806338afec631a07876315c9ff62f630d962a2fb2b62617e25624fd0746228c9b06217596a61a74438617008f361646539614712f36144faaa6129272b611e13506107a18460a26d476095e73b6095e5c660718e0060702628603809496015d3cf600944d25fd53a1c else 0x66e60a8f66e454be66a59e2166a15fda667d6677667527f6665f1c85665bf1f3665bf0cc665625b6663d5a6b6606efe56605f2dc65f7ee3065d6915965d134b965b3b63a659fb09b6597c720655921146544f2f8651cae6564ff82a864e9932064e3eef264e1e6d564dfcf4364de0dce64b6bd8364a586eb64874ef864393f50) else (if i < 39 then 0x69ce240069bb5d36699e6309699339fa6975c8e069721ded696bdb88696604ef6960941c695c4e6a6930e92c6917047d6908e77a68b1f62268aa204c68a8552e68a285956886c86b686799c06826ad216825a98a6825717e681ef1a06808a0e767e047bb67dd7a5667b33bc96783894c6750eb68673ca3c1673c1fcb66f66a49 else 0x6ea7396f6e70e2af6e55e6416e33f2c16d832f636d46a82c6d42188d6d39a8ff6d2926a26ccbc6e66cb94b136cb63c2a6c94fad56c8d0fc26c8b25986c6fd8fd6c0df7b56bbfc0586bbf9f1a6bbab38e6bb565406b67a4606b57204f6b3e17eb6b04ac366af007996ad1c3a06a719d3d6a3288566a13116469f4dad469e6eceb))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x71fbf3e071f34b3c71da1e7871c7ddf6716e1475713c43de71209fa370cbac4e7083d5ab704f461f7041b7c9702bfbf37021d4076fffa5556ff36da86ff1b2606fefb20a6fd4060d6fd0be936fbebe906f908fb96f8156cf6f76463c6f38502f6f2bd5b56f223d136f08da496ef248046ee5abd36ecbdd526ec81ba76eb9bb39 else 0x75f9a76075aff48675918f25758764e875646e527550468275483e06751ea9e17505e5a074c7dc2374a91366743cf01c742f49ca742d0fda741cbc4d73fa238d73d79e0c73a9979d7374ab12736b8a2e735a7ca37355af4d7346f8b573435730733a723c731151077304cd2a7300b2fc72a1784a726b36dd72400111723bba45) else (if i < 43 then 0x79644a1779622363793e7291793455db78e41c8978bbb6fe786088987856a126784106dd783ef4167819090c77f0100077ca85537793ac5d7785b1c7775ef7587749ae78774716627745a8d376e7e24a76e3733e76dc113676cd4a9d76b6b48676a1540f7690ad4c767ad93b7663feca7652335376044f3d760317407600a0fb else 0x7db823387db123377d7ca69c7d708f097d6b2c757d6364527d52f38b7d3ea4947d0fb5317cfc650a7ce86a9b7cb54b257c9461377c59518c7c412fc17c4088a17c3c4a087c2c504d7bffbc677bfe64ab7bb1f6867b410fc07b0391c27afcc3eb7ae7431b7aa8f3df7aa7fbc97a6cb42e7a27f8ad7a177e3379e042ee79d16f8d)) else (if i < 46 then (if i < 45 then 0x813560de811b2386811546b5810c0a6c80f4356880e4cef880e059298095ab79809451fc805f76b88017980a7ffc5af97fe52d4a7fcdcfd67fc29bb97fb6026f7f8fdb9f7f775e557f7501a67f609dae7f4aff8f7f2689c97f23ef677ef793fd7eb464437eb1f6a87e7abc767e74f4517e6e126a7e3acedc7e18e0317dc74499 else 0x84fba63384ed273084c92c3084bf9e2c84b70cff84805734847eb8f4845b2c088455176a8430a23d8407919083f77c9f83d13e8583b6746b83af87dd83a1d754839c986083972fa88382f7b28355dbb08325e78782cc22ad829688cf82895b448241e4798241c9e1823105ab820773ea82033be981bf0b77817cc46081431933) else (if i < 47 then 0x88d42ee788b18a908876c1478856b5ff883f03c48839136b8829ab3f881a20aa8805a6dd87e6a0b487e02c20879f29ff8796f3e1877ac36e874e29c587174be986fe67d486f9f38a86c521c58666df088641dcd1863c73ed860230b185f1a5e285dfe29985dd5d6f85c6fa7a85917d8f858d3235858050b7852a488c8522171d else 0x8d55c2a38d38161e8d1f4d338cf704098cf45f608cf421c98cdb52848cc7c70d8ca1a8128c8e4b3f8c89e2d48c575c128c50a06b8c4d3e278c28b7ac8c0ef1718bfce9318bf86c228b8691598b4517d58b3e40728aea99878ae2662f8aa3c1978aa0ec7a8a028124899456a9898f3626895fed118948f022892846fc88fdf736)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x908ecd66906a8c61903d1e9f90364bff9034e302902db0579017f4079017a99d9003e6588feb56618fc6dda28fb3889c8fa986358f47e55b8f109f208f01c7898ef70a148e9b974f8e778a658e76d0b48e7664de8e6ebb8a8e62e4928e5cca8b8e35e3858e21f7118e15daf18dda54eb8dd39d018da126fe8d94f31c8d7a1946 else 0x94d9ca3894cee5d394bfa02494893e479482b7c99462b61593e9a35793b11cd4938b7b9d937e4ae293792609936a85cc9349cdd59345bf75931a3ce792f0971a92a7d265929b1de3928e4c86924f9f0791f6f93991f296bd91d1e5fd91cd8b62919ff4f291703a8c9144064991401605910a773e90fb156090bcff18908f3d99) else (if i < 51 then 0x990f494298fdb9b498d2ecaf98b90b3c98b16a31988030339875c263981dcd1197eefae097e7985097df1f7b97ca6b3c976959cd97629a4e97271f26971ed88c9698b5f0966ae2a7964dabf2964c533a95bc6e6695b558df95a919c5959cc99c959a705495960e2f9582fda09576ae0c957676009502a6d294f7357694ef8c87 else 0x9f594d2c9ef53c3a9ef31df29e9cdcf69e44043e9df39f779dcf8c2a9daedc3a9d94064c9d9251189d68f9eb9d68a7669d59bdf49d3c13c69d15d6139cf059239ceb4a8b9cde6ab19cc9f8f89caf2fbf9ca9c5979c90e1829bd4567f9bc2bfaa9b69c4279b49533d9b230daf9a8aad819a7e131f9a5684059996b782998b5d81)) else (if i < 54 then (if i < 53 then 0xa53b65dca5318079a51458a8a5059951a471b270a46e0069a41076caa40d26a6a3fea9d9a3b3bc62a39f4140a36cce99a34131daa33611bea30e3bf7a2c70a68a29c8a7ba272bb1fa25edb6ca234a1a3a22df358a1a89effa17cec24a175022fa1585934a1190b07a0d827999ff3b4d49ff04fc19fd72b919fd382169fca5195 else 0xaa70f276aa4d1993aa3afa62aa22e553a9d1ea43a99e9ce0a9491449a9369618a91eca30a8df561ea8c886b9a8acb695a86665a9a855314fa837179da831560ea828e998a80f46dba7ca9a92a7b47ca2a7aadb2ea799ce05a748d4e3a724b5c5a7022f44a6d8520ca6d5fd76a6717bc6a656b947a5a1aea3a59aa764a580485c) else (if i < 55 then 0xb04c48ffb0129ec7af5254c8af1dd72faf1775c1aeceb10caecc7449ae793ee5ae644195ae2c6554adf153c7ade2b966add4c003adb9466aadb046bfada98ed5ad6ae4f0ad5e6f2ead5e459cacfe9798acf9b688acf4bce1acef65d8ace05fd2ac6e6749ac6a4e61ac47c1bcac415a93ac410ab9abf11f4eabc47d3bab5b5538 else 0xb640351eb628e07eb619bedeb6184c3bb5e69e83b57da235b57694e1b52055c2b5186a69b516d73cb4aadbe4b48d79bdb4787abbb45bceb1b457e6bdb43a8f6db4178ff3b3ebf334b392e153b37ca68cb34dfdcdb2f6b8dbb2bc0381b2a45e2bb27dc439b224026ab1d0a2b9b1a6403db18fe430b12c16a8b0f39f07b0d14383))) else (if i < 60 then (if i < 58 then (if i < 57 then 0xbcde3960bcadb991bc949ccfbc851febbbf7972cbbf1ffd9bbeb778bbbdceceabbd78cb6bbc6d8bcbbb7e625bb79b0d2bb598d4cbb32f7cabaf83ad8bae294b1b9784096b975fc9fb9350a37b9122932b8f6380bb8e11c91b8d795dbb8b6e069b80d0662b778c329b735a6cab72b4663b723d7f8b6a32986b6916cc9b648c251 else 0xc21eb424c1e9b05fc1d93e63c1cd71e9c1bcf00fc19b1b07c188fea6c15d6521c14557b5c0cbe59ac0b9d3c7c080a065c078179ec075a097c02cdbe2bf6ad577bf45da48bef8e3c0bec90fc6be5b0819be54d1ffbe4c51babdc9914bbd8093cbbd7f169dbd5d1440bd46f650bd2949bdbd1080ccbcfd5d11bce96796bce746b7) else (if i < 59 then 0xc9dfa95fc9b5870bc98d06a0c94141fac8f5dd3bc7e29eb9c7df1868c7c28ec3c7888a0bc768c677c762d9f6c6a219a9c67b9906c652bb55c5ce7f97c5949fdac56ed193c5621546c4ac28a3c44d5583c40d84eac3cd12e0c3a78386c39db0e6c394ff84c3753314c34cb4bec3099de4c2ca8174c2a30e65c29ff5ecc232d439 else 0xd05035c2d04d8a1cd03811fbd0273a46d01b9a73cfe18f58cfb2fcd5cf908b04cf84537dced2fea5cea4a2e0ce80c633ce5006c8cdc9edfecd73d768cd627b0dcd4e87f5cd29e7fbccda0039ccd45bc5ccb651a6cc9378dfcc41582ecc1e7307cc1188a5cbfeecadcbc71122cbab3e9acb81dd1dca705408ca6f39c6ca0af469)) else (if i < 62 then (if i < 61 then 0xd9d4196cd9a09e95d9819ba7d93151edd8c8d558d833ad48d820ddc9d803cb91d7eae77cd79d572ad72bfdb7d65273a4d585a0b0d54d7da4d543b27bd53aa25bd484e37dd474f3abd45fc29fd3e6f25dd3de59b7d3979598d39764c7d38486a2d35bd2b4d3395561d2f2987fd2cb2e82d2af71b1d24dd92ed2308d9cd22616df else 0xe267f353e20b55bee1fe75e4e1b6c07de1a2ca9de19861e8e16c9186e12f4367e12e5c33e1002b54e0ede6f0e0ace639e0a730d8e002cdb6df8ba1f5dec6d493dec4319fdeb31f73deab68b4dea511ccdea29dcdde95cee7dddadceddd550871dd486528dd476e69dc905692dc67cd3adb2b88ebdacee24ddab2d1bad9f022e1) else (if i < 63 then 0xeafc350eea85f6fdea3474bee9ec1d2fe961f667e94ce812e929de75e926bf88e8fe41b6e88c874fe7fe5f16e7fbd2c8e7ab8f3de701b77de696186de666dbbae6354bc6e5dc65b2e5c9c040e5c94813e4cd058fe4c46c77e4a08777e4521e68e4380b31e41e481de41d3c6de4097d60e374ca13e36fd4f6e3529fede317e931 else (if i < 64 then 0xfd581b32fce0e7d4fa68778ffa358a97f9769069f90743c1f7127727f6b8767ef602357df567a836f4594e41f43970d0f42db182f3e92fa1f3887a48f36d569bf33d67aff23f6048f2376bb6f0b47d26f09eff7ff09e4b0bf078c3ecf033072cf024ff69ef94030bee5195c4ee4cf586edd2b399ed6febbbecdf4eeaebb009ac else 0xffdc5bbdffab205cfecf390efe9cc667)))))))
def g1_l5H (i : ℕ) : ℕ := fld (g1_l5HC (i / 32)) 32 (i % 32)
def g1_l6C (i : ℕ) : ℕ := (if i < 77 then (if i < 38 then (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x002c99f238871b9514907002c99f238715833e0be7002e5b267c8e1c56cd837002e5b267c8e1c5514b2700000b267c98dc560c8c6002c99f2387153e2f8167002c99f23873583514077002df9f23871583398ab7 else 0x002c99f23873583515207002c99f238715452b00c7002c9a5e3881d835e9457002c99f254941c560d457002c99f26371583514a170027c8e21c83583514517002c99f238795835145e7002c99f23881ddc60d457) else (if i < 3 then 0x002c99f23881d834f0c77002d1b267c8e1c560d457002c99f238801454f0c47002dfb267c8e20760cc77002dfb267c8e20760d207002c99f23873583514c770027c8e1c560d45460be7002e5b267c8e20760c147 else 0x00000b267c98e0760d456002e5b267c8e21c5e9457002e5b267c8e21c5141d7002c99f23887145240517002c99f2388c5835e9457002f1b267c8e23560d45700000002e5a5e3871545500000b267c8e1c56d4146)) else (if i < 6 then (if i < 5 then 0x002c99f23871583514ee7002df9f238715832ac877002da9f2387c583515207002e5b267c8e1c55147a70027c8e1c560d45488ab70027c8e1c56b983514ab7002c99f23887183515427002c99f23881d83050127 else 0x002c99f23873583514657002c99f238871835146d7002c99f238715b951407700000b267c8e2076e5206002c99f23881d83514ba70027c8e1c560d45460147002c99f2387c5835144b7002c99f23887183515357) else (if i < 7 then 0x002dfb267c71583514467000009f23873583398146002c99f23881d83268147002f3b267c8e183514d57002c99f238859835151e7002c99f238715b5514167002dbb267c8e21c60d457002c9a2e3887183515207 else (if i < 8 then 0x002c99f23881db960cbe7002c99f259715b960d457002c99f238715452ac167002c99f2387c583514167002dfb267c8e20760c0d7002c99f23887214835457002c99f238795832f8877002c99f2388714548c907 else 0x002c99f2387c583514ab7002c99f2386e5835149a7002c99f238871835144d7002c99f2387157e5140c7002c99f23885983514bd700000b267c8e183514906002c99f238715b9515207002c99f238715b5514ab7)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x002da9f238715835153c7002c99f23860d45320167002c99f23871583520127002dfb6a7c8e1c560d457000000027c8e1c5514b25002c99f238715b960c12700000b267c8e1dd60d456002c9a4659715835153c7 else 0x002c99f238715b96cd837002e5b7e7c8e1c560d417002c99f23860d45240007002c9a4638715835e94570027c8e1c560d3c398147002c99f2388d61c60c147002df9f23871583398147002c99f23860d54514c77) else (if i < 12 then 0x002c99f23881d83514e97002d6b267c8e21c60d457002da9f23871545480be7002df9f238715835e93c7002c99f23881d835140c7002ea9f238715ae60d457002c99f26371583515207002c99f23873db960d457 else (if i < 13 then 0x002c99f23887183514ac70027c8e1c560d675140c7002c99f23881dcd60d457002c99f23881d8352545700000b6a7c8e1c56e545600000b267c965c56d5456002c99f23881db960c14700000b263871583514a66 else 0x002e59f23871583515187002c99f23873183514167002c99f23871545480f8700000b26918e21c60d456002c99f238715b5514be7002c99f238715452f8167002c99f2387157d51487700000b267c8e1dc60c146))) else (if i < 16 then (if i < 15 then 0x002c99f263715835148c7002df9f2387158321c14700000b7e7c8e21c60d3c6002c99f23887183545457002c99f23873583515307002c99f23885983514937002c99f2387c583514be7002c99f23880183514067 else 0x002dfb267c8e1c56d5837002c9a463871583514df7002df9f238715834f0c47002dfb267c8e1c560ce870027c8e1c560d45460127002c99f263871835e9457002c9a463871583514c47002c9a5e3871583514a67) else (if i < 17 then 0x002c99f23860d4531c557000009f23871583484e66002c99f23880183515207002c99f23877183514167002c99f23887183515337002c99f253715835153c7002c99f238739be60d457002c99f23871567514c47 else (if i < 18 then 0x00000b267c8e1dd60c8c6002c9a4638715835151e700000b6a7c8e1c56e5206002c99f23877183514ab7002c99f238715b5514147002e5b7e7c8e1c560ce67002c99f23880183514c77002c9a2a38715835e9457 else 0x002c99f238871835f9457002df9f238715834f11e700000b267c8e1452f89a60027c965c560d454f0e6700000b268b8e1c560c876002dfb267c8e21860d45700000b7e7c8e20760c1c6002f9b268b8e1c560d457))))) else (if i < 28 then (if i < 23 then (if i < 21 then (if i < 20 then 0x002c99f23881db9515207002c99f23881d452ac167002c99f23887183514137002d5b267c8e1835149a7002c99f23881d8355145700000b267c8e21c514ad6002c99f238715b94807a7002e5b7e7c8e1c55e9457 else 0x002c99f238715b960cf8700000b7ec99f23860c9a6002c99f23871568514be700000b967c8e21c8354560027c8e1cd60d4539814700000b26c5a5dc560d45600000b7ec99f259715836002c99f2388721660d457) else (if i < 22 then 0x0027c8e1c56e58351518700000b96df9f23887145600000b267c8e1c960d456002e5b7e7c8e1c560c87700000b267c8e9c560d456002da9f238715835140c7002e59f23871583515227002e59f238715ae60d457 else 0x00000b267c8e183585456002c9a1238715835e94570027c8e1c560d452c8ab7002c99f23877183514be7002c99f23877183514667002d6b267c8e1e560d457002c99f2387157a2f88770027c8e1c560d452c8167)) else (if i < 25 then (if i < 24 then 0x002e5b267c8e1f160d457002cdb267c8e21c60d457002c99f266951c560d457002c9a2a38715835151e7002c99f23881d83550c77002e5b267c8e1c56d5457002df9f238715b960c177002dab267c8e1c560c877 else 0x002c99f238715834f0147002dfb5a7c8e1c560d4570027c8e21c60d7a514ab70027c8e21c60d452ac1d7002c99f23881d452f8167002e5b267c8e1c5514ab700000b967c98dc55e9456002c99f254715835e9457) else (if i < 26 then 0x002c99f2388720d514907002c99f2387c583514127002c99f23860d45480907002c9a2e3871583514e67002c99f23877183514147002c99f23860d45354907002c99f23871583484867002c9a5e3871583514217 else (if i < 27 then 0x00000b267c8e18351499600000b5ec99f23881d836002c99f238735835141670027c8e1c56e5834811870027c8e1c559d452f816700000b267c8e20760d566000009f2387c583515186002c99f23881d83514557 else 0x002c99f23873583514ab7002c99f23887145398167002dfb267c8e21c514907002df9f238871835153c7002dfb267c8e20760c167002dfb267c8e2077f5837002c99f2387e1835149a7002c99f238715b3514167)))) else (if i < 33 then (if i < 30 then (if i < 29 then 0x002c99f254715835150b7002c99f2427158351486700000b267c9521c60d456002c99f238871454f0907002c99f26c715b960d45700000b7e918e1c560d45600000b967c8e1c55f9456002c99f238871835148f7 else 0x002c99f23873583180147002e5b267c8e1c5514be7002c99f25971583515437002c99f23879183514be7002c99f23885983601457002c99f2387719260d457002dfb267c8e20760cab700000b267c8e23560d356) else (if i < 31 then 0x00000b267c8e1c53e0be600000b96c99f238715b36002df9f23881d835141c7002c99f238775835148c7002d7b267c8e183514c77002c99f23881df860c147002da9f238715b9515207002c99f238714be2f4877 else (if i < 32 then 0x002e5b267c8e1c55a14570027c8e1c560d7f514ab7002c99f23881d8331c55700000b267c8e21760d456002c9a5e3871583514e67002d19f2387158321c147002c9a123871583514bd7002c9a2e3871583514877 else 0x00000b267c8e183514936002c99f2388714521c167002c99f238715b9514167002c99f24971583514e67002c99f23887183514867002c99f23873183514127002c99f254715835151e7002c99f238715452f8127))) else (if i < 35 then (if i < 34 then 0x00000b7e7c8e1c560c866002e59f238715b9514e67002c99f23887183515187002c9a4638715b55153c7002e5b267c8e1dc60d457002c99f2387c5b960d457002c99f23873583514be7002dfb267c991c560d457 else 0x002c99f23860d454f09a7002c99f23873983514167002dfb267c8e1835149a7002c99f259715835153c7002eab7ec99f23881d837002c99f238871834d44b7002dfb267c8e20760cbe7002dfb267c965c560d457) else (if i < 36 then 0x002c99f23860d4531c587002c99f26371583514ab7002c9a2e3871583480877002c99f2388ae0760d457002c99f238715835e9457002c99f23873983514ab7002c99f2637158351416700000b267c909c560d456 else (if i < 37 then 0x002c99f23860d7a514c77002dfb267c8e20760c14700000b267c8e1e52f8876002c99f23860d453541d7002c99f238875cd60d457002e5b267c8e207514ab7002c99f238715b360d3c7002c9a5e3871583514877 else 0x00000b267c8e1c56e4126002c99f238771835149a7002c99f23860d4524085700000b267c8e1b95149a6002c99f2387c983514ab7002c99f23881d834f014700000b267c8e20060c146002c99f238715b9480167)))))) else (if i < 57 then (if i < 47 then (if i < 42 then (if i < 40 then (if i < 39 then 0x00000b267c8e21c60d456002c99f238859835144c7002d69f238715835140c7002c99f23872583514077002e5b267c8e21c515417002c99f238715b9480ab7002c99f23881d83514ae7002c99f2387c5b960d207 else 0x002c99f23871583514c47002d6b267c8e1c560c877002c99f238871835153e7002c99f23881d83559457002c99f259715835143a7002c99f23a71583515207002e59f23871583514b27002c99f238871452f8877) else (if i < 41 then 0x002c99f238801b560d457002c99f23880183514167002c99f2388718460d457002c99f23887183514007002c99f23885983514e67002c99f23873983514be7002d7b267c8e20760d457002c99f2388d5835141c7 else 0x002dfb267c8e1c560d487002e59f238871835e9457002dfb267c8e21c60c877002c99f2388d583515357002dfb267c8e1c56e5837002c99f23887183515227002c99f238871ae60d457002c99f26371583514be7)) else (if i < 44 then (if i < 43 then 0x0027c8e1c56d5454f0e67002c99f238715835151e7002c99f2388d61c51416700000b7e7c8e1c56b9836002c99f2388d5835146d7002c9a2e3871583515117002dfb26918e1c560d3c7002c99f238771b960d457 else 0x002c99f238715835e88c700000b263871583515116002e5b267c8e1cd60d45700000b26918e1c5514c46002c99f238871454f0c47002eab267c8e1c56e5207002c99f238715b9480be7002c99f23871583514bd7) else (if i < 45 then 0x002c99f26371583514147002dfb267c8e1c56e4ac7002c99f238701835141470027c8e1f160d45481187002e5b7ec99f23881d837002c99f23881db9514167002c99f238715453e0be700000b267c8e20760d216 else (if i < 46 then 0x002c99f2387358351412700000b267c9660060d456002c99f23885983514877002c99f238715b9050077002d7b267c8e20760cc770027c8e1c560d452ac167002f39f2388720d60d45700000b7e7c8e1c54f0c46 else 0x002c99f23881d835e9457002df9f23871583514867002c99f23887145240087002c99f23881d452f89a7002c99f238795835141a7002c99f25487183515207002c99f23881d83514587002c99f23871583515217)))) else (if i < 52 then (if i < 49 then (if i < 48 then 0x002dfb267c8e20760c9a70027c8e1c560d7a59d457002c99f238715b360c0c70027c8e1c560d454f118700000b267c8e21c60c8c6002c99f238715835f8877002c99f2388720f60d457002f3b267c8e21c514907 else 0x002c99f2388721160d457002dfb267c8e1c56e57e700000b267c8e1c56e4f86000009f23860d451601c6002c99f238795452f88770027c8e1c551520460be700000b267c8e1e560d456002c99f238859b360d7a7) else (if i < 50 then 0x000009f238715452c8166002dfb267c8e235871837002c99f23860d452ac907002e5b267c8e1ce60d457002c99f23881d83585457002c99f23880183514147002c99f23860d45240167002c9a463871583514e67 else (if i < 51 then 0x002c99f238715832f48c7000009f238715452c8ab60027c8e21c60d451441d7002c99f23879583514007002c99f23881d83514c47002c99f23881dcd60c147002df9f238715834f0e67002c99f238715834788c7 else 0x002c99f238715835a48670027c8e1c560d45504e67002c99f2388c5b360d7a7002c99f238871a760d457002c99f23881df8514567002dfb267c8e2076e5837002c99f238735b960d457000009f238715b360cab6))) else (if i < 54 then (if i < 53 then 0x002c9a463871583514877002df9f2387158460d457002c99f263715b360d457002c99f238715a160d457002c99f238715835200c700000b7ec99f238771836002c99f23881d835151e7002e5b267c8e1c56e5207 else 0x002c99f23887183515207002c99f23887183514d57002c99f238715834847a7002c99f238805835153e7002df9f238715834f0877002c99f23873583514917000009f238715b9481186002c99f238715b9480127) else (if i < 55 then 0x002c99f23860d50514d57002c99f238871450740870027c8e1c560d67514bd7002c99f2388a61c835837002c99f238871835141e70027c8e20760d452ac16700000b267c951c560c876002c99f23860d452f8907 else (if i < 56 then 0x002df9f238715834f0ed700000b267c8e1fa60d456002c99f238715b55153c70027c8e1c560d453981770027c8e1c560d7a398147002df9f238715454f0c47002e5b267c8e20060d457002c99f2388821c60d457 else 0x002c99f25971583514a37002c99f23860d45240147002c99f238715a360d4570027c8e1c560d21398ab7002c99f238871835140e7002e5b267c8e235871457002f3b267c8e183514517002c99f2387c5835153c7))))) else (if i < 67 then (if i < 62 then (if i < 59 then (if i < 58 then 0x002e5b267c8e2076e5457002c99f2387c545480be700000b6a7c8e21c60d456002c9a5e3871583609457002f8b26978e1c560d457002c99f238871b960d357002c99f23888e0760d457002c99f23873983521457 else 0x002c99f23860d45268557002c98e1c560d45481117000009f23887183398146002c99f238715835f5457002c99f26e98dc560d457002c99f23867583514c77002e59f23871583514167002c99f23867583514d57) else (if i < 60 then 0x00000b267c98dc5514166002c99f23a71583514167002c99f2388d61c5149a7002c9a123871583514e67002d19f23871583514867002c99f238871835147a7002c99f238714e62f8877002c9a5e387157a514167 else (if i < 61 then 0x0027c8e1c56cd83514ab7002c99f23881d83154147002c99f25471583514e67002c9a8e918e1c560d457002da9f238715835151e700000b267c8e22b81d456002dab268b8e1c560d457002c9ab23881df860d457 else 0x002c99f2387157a515227002c99f2387c5835145c7002c99f25971583514037002c99f238801b960d4570027c8e1c560ce62f41470027c8e21c60d45398ab7002c99f23887183514d87002c99f23881db95149a7))) else (if i < 64 then (if i < 63 then 0x002c99f238715b92f8167002c99f23879583515207002c99f238771835153c7002dfb267c8e1dc60d457002e5b267c8e183514907002dfb267c8e1c560d3c700000b267c8e1f16e5206002c9a4638801835153c7 else 0x002c99f2387158351541700000b267c8e1c5514c46002c9a4638715835142d7002c99f238715482f8167002c99f2388718351485700000b967c8e1c56cd83600000b967c8e1c5514b26002c99f238715b9480f87) else (if i < 65 then 0x002c99f23881db55153c700000b267c8e2006d545600000b267c8e1c560ced6002c99f25471583514877002df9f23871583514077002c99f23860d7a5149e7002c99f2387159f2f8877002edb267c8e1e560d457 else (if i < 66 then 0x002c99f23881da360d457002c99f238715b9058147002e59f2387158351d4570027c8e1c560d48514ab7002c99f23881d9d60d457002c99f2387154531000700000b967c8e21c5e9456002c99f238715835f48c7 else 0x002c99f2387bd835153c7002e59f23881d83514167002c99f259715834f014700000b267c8e20760d696002c99f253715835151e7002dfb267c8e2077e1837002c99f23860d61514be7002c99f2388597a514167)))) else (if i < 72 then (if i < 69 then (if i < 68 then 0x002c99f25471583514207000009f238715452ac166002c99f23871583514177002d69f238715835e9457002c9a06387158351487700000b267c8e23560d45600000b267c969c560d456002c99f23872583514147 else 0x002c99f2386e583514907002c99f23871583514e670027c8e1c55153e2ac167002e59f2387157a514bd700000b267c8e23260d456002c99f2388721260d457002c99f25471583480877002c99f23879d454f0c47) else (if i < 70 then 0x002df9f238715832ac867002c99f2388d5ae60d4570027c8e20060d454f0e670027c8e1c5514ab05800700000b267c8e21c83d456002c99f23881d9d60cc77002c99f238871452401d7002c99f2388d583514007 else (if i < 71 then 0x00000b7ec99f23880183600000b267c8e23560cd5600000b26978e21660d456002c99f238735835153c7002c99f238735835b9457002c9a2e3871583514237002c99f238871454d4167002c99f23860d45398d57 else 0x002c99f238871b560d457002c99f23887183514167002e5b267c8e1c960d457002c99f23887183514e87002c99f23871583514877002c99f238715b905812700000b267c8e183575456002da9f23887183515207))) else (if i < 74 then (if i < 73 then 0x002c99f23860d45354877002e59f23887183514e67002c99f23887183514ab7002f3b267c8e20d60d457002c99f23860d4548c907002c99f23860d45268587002e59f238715b360d457002c99f23881d8354c557 else 0x0027c8e1c568d83398147002c99f23860d7a5149a700000b7e7c8e1c56d5836002c99f23a71583514127002c99f23860d7a514d47002c99f23865d83514877002c99f2387159f60d457002c99f259715835e9457) else (if i < 75 then 0x002c99f238715835a47a7002c99f2387157a514b27002c99f23881d83160147002c99f238715833988c7002c99f238871833544b7002c9a2e38715835153b7002c99f23885d83514147002c99f23871583514ed7 else (if i < 76 then 0x002c99f23881d835e8147002c99f238739835153c7002c99f23881d835a5457002c99f23871583480877002c99f23880983515417002c99f238801f860d457002c99f238871835144a7002e5b267c8e1c56e4be7 else 0x002c99f23881d83484ab7002eab267c8e21c60d457002c99f23887183514be7002c99f23871545480c4700000002df9f259715835002c99f254715835dd457002dfb267c98dc560d457002c99f23881d83514177))))))) else (if i < 115 then (if i < 96 then (if i < 86 then (if i < 81 then (if i < 79 then (if i < 78 then 0x002c99f23860d451441d7002e5b267c8e2165e9457002e5b267c8e1c56e4147002c99f23887183529457002f4b267c8e20760d45700000b267c8e21c6cd8360027c8e1c560d69398ab700000b26a08e1c560d456 else 0x00000b6a7c8e1c560c876002f1b267c8e183514c77002c99f259715835151e7002c99f238715832308770027c8e1c560d67514e67002c99f25471583514a0700000b267c8e20960d456002c99f238715b94f1207) else (if i < 80 then 0x002da9f2387158351541700000b267c8e145268556002c99f238735b960c147002dfb267c8e20760c0c7002c99f23887183514147002c99f2388761c60d457002c9a8238715ae60d457002c9a4a3871583515417 else 0x0027c8e1c5515202ac167002c99f2388d583514c77002c99f2388d5835141e7002c99f238801835153c7002c99f2388d583515207002dfb267c8e20060d457002c99f2388d583514d57002c99f238715b360d1e7)) else (if i < 83 then (if i < 82 then 0x002c99f23877183514687002c99f23871583515197002c99f23881d9f60d457002c99f2388d5b9514877002c99f23879583514ab7002c99f238715b360cbd7002c99f23873983514647002c99f23881d83398c77 else 0x00000b267c8e1fb60d456002c9a4e8b8e1c560d457002c99f23887183514487002c99f23881d835d5457002f39f238871835141d700000b7e7c8e20760cab60027c8e1c5514b22ac167002e5b267c8e21c515357) else (if i < 84 then 0x002c99f238715b54f014700000002e59f238715b35002c99f23881d8331c877002c99f23881d83480877002c99f2387c583514907002c99f263981c560d457002df9f23871583514ab7002c99f23881db360d7a7 else (if i < 85 then 0x0027c8e1c5514ab1e8167002c99f23879583514be7002c99f2388d5835147a7002da9f23871583514e67002e5b267c8e21c60d457002c99f23881d4515416700000b268b951c560d456002c99f23887183514d17 else 0x002c99f23883583514907002c99f23881d8351405700000b7e7c965c560d456000009f23887183515186002c99f23887183514127002c99f263859835e9457002f1b267c8e20760d457002c99f238715a360c147)))) else (if i < 91 then (if i < 88 then (if i < 87 then 0x002c99f2388d60760d457002dfb267c8e183514907002e59f2387157a515417002c99f238871b360d457002c99f2387e983514167002978e1c560d7a514ab7002d1b267c8e1c56e5457002c99f238715b960d217 else 0x00000b7e7c8e20760c1460027c8e1c560ce621c147002dab267c951c560d457002c9a2e3871583515187002da9f23871583514877002c99f238871835149a7000009f26371583514ab6002c99f23880183514187) else (if i < 89 then 0x002c99f259715b55153c7002c99f2388718c60d45700000b26b08e21c60d4560027c8e1c560d45460bd7002f3b267c8e1ce60d457002eab267c8e1c560d4170027c8e1c560d45479187002c99f23860d7a514957 else (if i < 90 then 0x002df9f238715832ac7a7002c99f2388d60760cc77002c99f2387157d514077002c99f238871835214570027c8e1c560d45485187002dfb267c8e20760c557002c99f238739452ac167002c99f238871b960d457 else 0x002c99f2387157d51520700000b268b8e1c560d45600000b7e918e1c560d3c6002c99f23871583504147002df9f238715834f0ac7002c99f2388c61660d457002e59f2387157a514e67002c99f238735bc60d457))) else (if i < 93 then (if i < 92 then 0x002df9f238715b96b983700000b267c8e21c514166002c9a46387158351401700000b267c8e1835146d6002c99f238715833a087700000b267c9de0760d45600000b267c8e1835150260027c8e1c560d452ac0c7 else 0x002c9a463871583514a87002c99f23871545310167002c99f238871454f8167002c99f23887183515077002c99f238835835141d7002c9a5e958e1c560d457002c9a2e387158351400700000b267c8e21c6d5456) else (if i < 94 then 0x002e59f2387157a514877002c99f25c965c560d457002e5b7e7c8e1c560d457002c99f23887145058007002c99f23887183515237002c99f238739452f8167002c99f23871584514877002c99f238715b5514c47 else (if i < 95 then 0x002c99f2387c5835151e7002e5b267c8e207514557002ebb267c8e20060d457002dfb267c965c560d3c7002dab267c8e1c560d45700000b26978e1c560d456002d19f23871583514ab700000b267c8e23560c146 else 0x002c99f238715832f8877002c9a2e5471583515207002e5b7e7c8e1c5514ac7002c9a5e3871583514007002c99f2387157a230167002c99f23881d835a4ab7002c99f238715452f4167002c99f2388d5835144b7))))) else (if i < 105 then (if i < 100 then (if i < 98 then (if i < 97 then 0x002df9f23881d83514147002c99f23881d8359d457002c99f23887145398907002e5a5e38715835e94570027c8e21c60d454f0e67002c99f2388d583514167002c99f238715b960d7d7002c99f238771835e9457 else 0x0027c8e21c60d45481187002c9a5e38715835153a7002c99f2388c9b560d457002d6b267c8e1c52f8877002c9a2e888e1c560d457002c99f2388d583514ab7002c99f238735834f014700000a463871583514e66) else (if i < 99 then 0x002c99f23871545310147002c99f23860d4524008700000b268b8e20760d456002c99f2388d6075cd457002c9a4e918e1c560d457002c99f2388720f514167002c99f23864983514877002c99f23881d7a514167 else 0x002c99f2388d583514be7002d8b267c8e21c60d457002c99f238791835e9457002c99f238715833b4147002d19f238715835141470027c8e1c560d7a514b27002c99f23887145240877002c99f2387159f60c147)) else (if i < 102 then (if i < 101 then 0x002c99f23885983514007002e5b7e7c8e20760d457002c99f238715b960d417002c99f23873d83514177002c99f23887183514957002c99f23860d453989a700000b267c8e21660d456002eab267c8e23560d457 else 0x002c9a463871583514867002c9a5e3871583514247002c99f23881d83398147002c99f23860d4531c1c7002c99f238715835148e7002dfb267c8e20760c587002e59f238859835e9457002dab267c8e20760d457) else (if i < 103 then 0x002c99f238871f160d457002dfb267c8e20760d7a700000b96c99f238871456002c99f23860d45481027002c99f23860d454d4d5700000b267c71583514db6002c9a2e38715835152070027c8e1c5514ab058147 else (if i < 104 then 0x002c99f238715b960d697002e5b267c8e1c5514c47002c99f242715835153c7002c99f23887145480167002c99f23860d45268877002c99f23860d4531c6d700000b267c715835150b6002c99f23860d453546d7 else 0x00000b6a8b8e1c560d456002c99f2388720d60d457002c99f23879183514bd7002c99f2388d583514487002c99f23871545310127002e5b7ec99f238715b97002c99f2387bd835151e7002e5b267c8e21c514007)))) else (if i < 110 then (if i < 107 then (if i < 106 then 0x002c99f238715a3514ab7002e5b267c8e1c5514bd7002c9a5e3871583515207002f3b267c8e21c514ad700000b267c8e21c5149a600000b267c8e21660c8c6002c99f23882583514167002c99f23881d8321c147 else 0x002c99f238715af60d457002e5b267c8e23560d457002c99f238795835c1457002eeb267c8e1f160d457002c99f2387157d514167002e5b267c8e1c55e88c7002c99f23871583514ac7002dfb267c8e21c60d457) else (if i < 108 then 0x002c99f23881d835141c70027c8e1c5514ab058127002e5b267c8e2075e945700000b267c8e1fb60c14600000b267c8e21c631456002c99f1c560d7a514a17002c99f238739835141d700000b7e7c8e1c560d3c6 else (if i < 109 then 0x00000b267c8e22d60d456002c9a4638715454f0c47002c99f238715a3514be7002c99f238715b9514c470027c8e1c560d45460e67002c9a5e38871835e9457002df9f238715834f00070027c8e1c560d45398867 else 0x00000b26988e1c560d456002dfb267c8e1c568d83700000b268a8e1c560d456002c99f23887a1c60d457002c99f23880183514587002dfb267c8e1c56d53c7002f1b267c8e20760c14700000b267c98e1c60d456))) else (if i < 112 then (if i < 111 then 0x002c99f2547158351518700000b267c8e183514fc6002c99f2388d5b960d457002c99f238871b960cbe7002c99f238715b5515417002c99f238801835e9457002c99f2388b5ae60d45700000b26bba2dc560d456 else 0x002c99f2388d583514517002c99f263715835e88c7002c98e1c560d454f0e17002c99f26371583514bd7002c99f23881d8331c6d70027c8e1c5521452ac167002d6b267c8e20760d4570027c8e1c56e5452ac167) else (if i < 113 then 0x00000b267c8e1c52f8876002c99f2387c5835141b70027c8e1c560d7a514ab7002c99f238859835148c7002c99f238871835140c700000b26918e20760d456002c99f238715b94811e7002c99f23881d8331cbb7 else (if i < 114 then 0x00000b267c8e2326d5456002c99f2387c983515217002c99f2388d5b960d207002c99f2388d5b960cd57002c99f26381d835e9457002c99f1c560d454810b700000b26848e1c560d456002c99f23879545480be7 else 0x002c99f238871835153d7002c99f2387ed8351414700000bce7c8e20d60d45600000b267c951c560d456002c99f238715b5514e67002c99f238714be21c0070027c8e1c55153c398c47002df9f238715835153c7)))))) else (if i < 134 then (if i < 124 then (if i < 119 then (if i < 117 then (if i < 116 then 0x002c99f25471583514407000009f23871583514ed6002c99f23881d835f9457002dfb267c8e1c560d417002c99f25471583514007002c99f23880183514997002c99f23860d73514c77002daa2e3871583515207 else 0x002c99f2387157d514127002c99f2388721460d457000009f2387157a514b26002c9a2e3871583514167002c99f23887183514087002c99f238775835e9457002c99f23860d7a514907002e5b267c8e1c55f5457) else (if i < 118 then 0x002c99f238735835f5457002c99f238795b960cbe700000b267c8e1c56e5416002c99f23871583515187002c99f238715b5514877002df9f238715834f1207002f5b267c965c560d457002df9f23881df860d457 else 0x002c9a8238715b960d45700000b967c8e2165e9456002c99f2388c60760d457002c99f238715835a53c700000b7ec99f2388d5836002f6b267c951c560d457002c99f238871b9515207002c99f238795e060d457)) else (if i < 121 then (if i < 120 then 0x002c9aee8b71583515207002e59f238715b951416700000b267c8e1c560d45600000b267c8e183514cf6002c9a2a3871583515207002c99f23882583521457002c9a5e3871583514167002c99f238795835140c7 else 0x002c99f2388d5f860d457002c99f238715ae60d457002c99f23871583230867002c99f23860d45480fc7002c99f2387158460d457002c99f23871583514007002e59f2387398351416700000b267c8e183514d56) else (if i < 122 then 0x00000b267c8e183561456002c99f23879183514e67002dfb267c8e1c567d837002dfb267c8e1c5514c47002c9b1697715835e9457002c99f23887145058147002c99f23860d45354007002c99f238714be21c077 else (if i < 123 then 0x002c99f23881d835ccc77002c99f25471583514397002c99f24971583514be7002c99f23881d83514867002c99f2387719f60d45700000b268b8e1c56e5836002c99f238715202f887700000b26978e1c56cd836 else 0x00000b267c8e1be60d456002c99f23885983514ab7002c9a5e3871583514147002c99f25471583515207002c99f259715835141f70027c8e1c560d451e8177002c99f2387c5ec60d45700000b267c8e1db60d456)))) else (if i < 129 then (if i < 126 then (if i < 125 then 0x002dab267c8e1c56e5837002df9f238715452ac167002c99f2388d5835153c7002e5b268b8e1c560d457002dfb267c8e20760ce67002c99f23881d83558587002e5b7e7c8e1c56e5837002c99f238715b9515417 else 0x002c99f23887183514907002c99f238795452f8167002c99f23881d452f887700000b6a7c951c560d45600000a2e3871583515186002c9a2e3871583514127002e5b267c8e21c514e8700000b267c8e183514d86) else (if i < 127 then 0x002c99f2387158321c0c7002e5b26978e1c560d457002dfb267c8e20760c877002c99f23881d8351522700000b26918e1c560c146002c99f23885983514be7002c99f2388d5dc60d457002c99f23881d835153e7 else (if i < 128 then 0x002da9f23871583515187002c99f23872983514be7002c99f23860d7a51493700000b267c8e20760cc76002c99f23881d83070147002c99f23881d454f0c47002c99f2387158351407700000b267c8e20260d456 else 0x002c9a2e38715b960d457002df9f238715b560d3c7002df9f238715834f0167002c99f23871583515207002c99f238715b948017700000b267c8e2356e5206002c9a4638715b560d457002c99f26371583514e67))) else (if i < 131 then (if i < 130 then 0x002c99f2388714851416700000b267c8e20760c8c6002c99f23881d835d1457002c99f238715b9514877002c99f23860d45480d57002c99f2386e5835146d7002c99f23881d8331c007002c99f259715835143d7 else 0x00000b6a7c8e1c560d456002c99f238871834d4877002c99f2637158351487700000b2691965c560d456002f1b7ec99f23881d837002c9a2e387158351422700000b267c8e20760c0d600000b267c71583514466) else (if i < 132 then 0x002c99f23879583514907002c9a2e38715b960d207002c99f2388d5b960c147002c99f238871835e945700000b268b8e1f160d456002c99f23860d453540e700000b267c8e21c8514560027c8e1c5514ab0580c7 else (if i < 133 then 0x0027c8e1c560d45398ab7002c99f264715835f94570027c8e1c560d22398147002c9a2e3871583514a57002da9f23871583514007002eab7e7c8e1c560d3c7002c99f238715835147a7002c9a5e38715b960d457 else 0x0028b8e1c560d45481187002c99f238714be21c16700000b267c94dc560d456002e5b267c8e1e5514be7002c99f238715835fd457002dab267c8e1f160d457002df9f238715834f0147002c99f23887183514c47))))) else (if i < 144 then (if i < 139 then (if i < 136 then (if i < 135 then 0x00000b267d8e1c560d456002c99f25471583514167002ea9f23871583514177002c99f238871452408f7002c99f23885983515347002c99f23881d9760d457002da9f25471583515207000009f2387159f60c146 else 0x002c99f2388d6075149a7002df9f259715835153c7002c99f23881d83480c77000009f23881d8339814600000002c9a2e38715b95002e5b26918e1c560d4570027c8e21c60d452ac167002c99f23860d45398907) else (if i < 137 then 0x002da9f2387158351520700000b6ac99f238715b96002c99f2387c583515357002c99f23881d8960d45700000b96df9f238715b96002c99f27781df860d457002c99f23860d45240877002c99f259715835d9457 else (if i < 138 then 0x0027c8e1c567d83514147002c99f238715b560d457002c99f23871583514167002e59f23871583514177002c99f23879583514bd7002c99f238715ae60c147002c99f26371583514a07002c9a2e387c583515207 else 0x002c99f238715452b0167002e59f238715452f80c7002c9a2e38715835153c700000b96c9a5e3871545600000b267c951c56e5836002c9a2e3871583514317002c99f23860d45354167002df9f238715b960d3c7))) else (if i < 141 then (if i < 140 then 0x002e59f2387157a514077002c99f2388b5b960d457002c99f2537158351520700000b7e7c8e1c56d53c600000b267c965c560d456002c99f238715af514167002c99f23873583514697002e5b267c8e1c52f8877 else 0x002c99f63871583515207002e59f2387159f60d45700000b267c8e1cf60d45600000b267c8e1c56cd836002c99f23871584515207002c99f25971583514007002e5b267c951c560d457002eab267c8e1c560d457) else (if i < 142 then 0x00000b268b8e1c56e5206002c99f238715832ac8c7002eab267c8e1c5514ac7002c99f238715b36b9837002c99f238715b360c007002c99f23860d45268977000009f25471583515186002c99f25471583514127 else (if i < 143 then 0x002c99f23871583484e6700000b267c8e183514916002e59f23881d83514e67002c99f238715b92f8877002c99f23881d83514ab7002c99f23860d45354147002c99f2387157a514c47002e59f238715b360d7a7 else 0x002e5b267c8e1c560d457002c99f23881d8331c167002c99f23887145354907002c99f238871450580c7002dab267c8e1c56e5207002c99f2387157e514be7002c99f238715832f88c7002c99f254715b960d457)))) else (if i < 149 then (if i < 146 then (if i < 145 then 0x002c99f2387158348487700000b267c951f160d456002c99f23887183514527000009f23871583515186002c99f23871583514127002c99f238714f82f8877002c99f23881d83514be700000b267c8e1c560cf86 else 0x00000b267c8e1c54f8be6002da9f23871583514167002dfb267c8e2356e58370027c8e1c560d45460007002c99f238715831e8147002df9f2387158321c867002c99f23860d4531cc57002c99f254715b960d207) else (if i < 147 then 0x002c99f23881d8331c1470027c951c560d45481187002c9a4638715835153c7002c99f238715b960d457002c99f238715b360d20700000b267c9b1c560d456002c99f2387c5835151870027c8e1c560ce62ac147 else (if i < 148 then 0x00000b267c8e1f160d456002c99f2388d62360d4570027c8e1c560ce62f8147002c99f238715b9514ac7002df9f23871583515417002eab267c71583514467002c99f26c715ae60d45700000b267c8e1f360d456 else 0x002c99f238715b360c7a7002c99f23871583514f8700000002c99f254715b9500000b267c8e20751456600000b267c8e145354166002c99f23887183480877002c99f2387c583514fc7002c99f238715b96bd457))) else (if i < 151 then (if i < 150 then 0x0027c8e1c560d4548118700000b267c8e1cc60d456002c99f238715835f4877002c99f238795835152f7002dfb26988e1c560d457002c99f63871583514167002c99f2387c583514007002c99f23871584514167 else 0x002da9f238715b960d45700000002c99f238714f85002c99f1c56e58351446700000b267c8e1ef60d456002da9f23871583514127002dfb267c8e1c56b98370027c8e21c83583514ab7002c99f2547c583515207) else (if i < 152 then 0x00000b6a7c8e1f160d456002c99f238735835140070027c8e1c56b9835147a7002c99f63871583514127002c99f238715452c8ab700000b267c8e1cd60d45600000b267c951c56e5206002c99f2387c583515207 else (if i < 153 then 0x002c99f238715b948000700000b267c8e1c56e5206002c9a2e38715835151e7002f4b267c8e23560d457002c99f2388d583514177002c99f238715b9481187002c99f23873183515207002dfb267c8e183514d57 else 0x00000b267c8e1c5480f8600000002da9f238715b95002c99f2387bd83515207002c99f238715b96b9207))))))))
def g1_l6S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l6C (i / 8)) 84 (i % 8))
def g1_l6HC (i : ℕ) : ℕ := (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x0364258e036078b50351a39e0328985d0318e75202e757aa02e4ccb802da8e9702d66b8802af18d3029201e4028fcc8e02479734021f2421021b5a350219145101d6eec701cc2cea01b7769a01a570440173b4d801677a5c0150938b01445aa90141016901081bb30105158700f7e3f900a12f86009683bb004d2a02000e053b else 0x06fa45ff06f65b5606f5913606d4097e06c3035206c1c8f906be321a06a3ff2106a076ad069e645d067c5294067208e306681862064fcdc006179bf60614201c05e9c53605c80ebe05a09b8c059d4aad0591fb4f057f2b8605502e8f051a55df04f9f29304cfda0f04cb817604c29366049c4130047ecbf103dec77403ad9401) else (if i < 3 then 0x0a33b1b80a2686d80a17551009dea5fb09cc675609b0bc9a098d7d4b0966a22b094a18860948ce800911300808f68d9808e2c16808d7539f089c226e08551f4e084f9aaa084e65a8083c74a90808fbb007f71b8807ba748607a1b66a079deb83079295df0773ecf007535380073b33d9072b2360072b1e62072a6051070e5a21 else 0x0ec68ebc0e7965330e741c050e59c30e0e105bd50e0898ae0d8c03a20d8aee0a0d6318430d5df7420d25f7350d14f55d0ce223300cd17d7f0cbce1c10ca6883f0c7bdc250c6df6a40c6d091e0c3dded20c38a6030c1fdd180c1c5fa30bbc460d0bbbd2d30bb152870b84c5f00b7c9ca40b5eaf290aa7a5b60a5e17500a4398a7)) else (if i < 6 then (if i < 5 then 0x125f336a122a644f11ffee5311df32cb11bac11d11a4747411a3d87e116aa038112ad9c210faac9b10f546a810afd88710858a5c107db37f104da03c103193a81013937b101294380ffaf1420ff011970f9c77540f98d30d0f93befb0f8ad7530f6584550f50da480f4b89a10f3185360f20fe160f17cea60f0480e10efb1c40 else 0x171d63b116f69dae16f0faae16a6ddf3169f3890169927f3168aa9bf15ce694315a1e3bd159638a91587f5ce151a5d79150624f414f4ba8414cf8bdb14c9696d14c0df2414b1f172146053e4145aa7e114302ebd142a0deb14270f02140999c313ada0a213832f611373668f1361bf1013604d1a131d630513059dc7126a91e2) else (if i < 7 then 0x1a307cde1a2e18bb1a122c9719e7dff219e298ea19d9710819d8d0db19a482b819a2345819753a771971f07d195d213d19399b6219146e2618f6654218cb262418c1fa3518b1e3611889493818859e45187e2eca186fddb818698eae1846301318410e5f1830ae5b17f08a8a17e1b5731754b031173eeb69172370ab17234f6d else (if i < 8 then 0x1dd3e87f1dbdd4fc1daf9d971d9b67c41d999dba1d968e131d754a471d4773191d2efa5a1d2bf42e1d0f88f91cd57c381cd181651cc2fb3b1cbcd9ff1cae9d791ca3dad41c69374b1c4a5ad61b2a61931b2822621ab06a421aa1254b1a963fef1a7b24b81a7981811a6aa0a71a58cb911a505f1b1a4806551a45b1bf1a321e05 else 0x220ec47521e70b6221e3b53221d837d62166c793212f55e321287f0120bf1a12208bb7182070c9822045181e200e257e1fd315f41fcdbebf1fcb712d1fc786841fb0bf021fb06f431f87e2cf1f85bb1f1f7adf691f6266b01f5ac8c01f3f7c4b1f15046a1eefed8f1ec562071e8f6bb91e68803c1e4bd0871e3f560d1dfdb6fb)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x25fc3d9d25f61bee25e6a82d25d656e3258f4d33258e59932512c3a024d8c5d224ae18cd249efcbb2451c0962434b9f524276e61242030812418c3c223fea8c923e1532d23de1dac23cc35a3239acb97237d8c9d2375e17823714c2e2361a4202335f8dd232f427e22e510c122c582ec229312432273be822261e2ae225b728e else 0x29d8a4a429c446f329bb4ab029b2e2492952bbe62952212a294a7c632945d9312897a8232882ce332873716f285ddf332805e18b27f79ce127e3b33027bfe26827be2326277b585c2766ae8b275828ac273c2303273315ac2715a06d2711574426ff544226e68b57269e048926942a7326630bfb2659a1c526372334260e612a) else (if i < 12 then 0x2e8f31602e8085dd2e3c55ef2dd8a94c2d1ff5de2cfa6ed82ce724e02ca023082c9b9aac2c72a7bf2c18cf152c0148a72bf174122bc8cb7d2b7466442b710ffc2b4fca602b3e634d2b24e0cf2b2488ef2b1b9aa72b1070dd2adf05072a9afaac2a7528952a70bbb02a6676462a5490182a2bf31d29fa352029f0e31729e3fa58 else (if i < 13 then 0x33a582b832cf704832bda90432b23f0b329f8d213270f61c32004daf31bc060331b7b64231aed47531991d3831625e1f313110b63108b35330f5a03430f4ab4430f0481430ea326b30e2d74f30ba23b530ade5bc303334eb30244aee300d87d12fe077162fdfc29f2fd47f492fcc98232fa6f97e2fa063b22f7c4c792ef0d374 else 0x383a067237fab16037f5f51a37cc4888378c67ff375ce369372fe58a36f09cbf36911953366e7449365f977b365e11d236507e70364543f6363a35bd360d2331360c43a335f2d82335ea882935e84f1135b7750835a5fd2e3583ffe4353f7e0334cf5ca534a82c0c3495fce433f2dac033df356133cf24d933b7a14c33aafe53))) else (if i < 16 then (if i < 15 then 0x3d4f5da83d295b493d2009e53cad32e23cab3e903be979b73be686143ba2aeb43b64e9273b2271c93ad3b9393ad3b76d3acceccb3aba39073a9b3eaf3a58982d3a438f533a41eb3e3a40927b3a3e761c3a366ba439dff6e03992d649398126d7397a52e63970f482391e4a4d3908933538f1700f38bccba2389c6a3f387a30d8 else 0x422dbd3f42231c4441d1a21f41677e3c414f300e4146d3d54139a2474132aa1f40e57e1940da774f40d7ac9040910d96406da5214053ed2b40258770401c78b64012a3193ff877f13fbd49143f74e8893f6b799d3f0784c33eda35c13ea6cd963e7deec03e4f13873e3a49a63e369c473e1547e13dff167d3d7664ea3d598bff) else (if i < 17 then 0x478942bb47374f84472a957f4720f3ec47169f5546ebeb9a46bf980446a62a04464f5d9745d011c8459212e1451fee6244dd7bdd44d5da074483e88c446c1cf544531d6644494f6a4438a4dd4420ce32441fdad644092dea43a237034345947e432ac833432632e943003f4d42fc1e7a428ca661426a1eeb424df47b42497547 else (if i < 18 then 0x4dc00e444da745594da2daa34d5342964d3f96a04cda7fb94c4fa5b44b9ebd514b842afa4b6ec2334b1ef32e4b1817d74a8ebc384a5cd3954a3a611249eb523c496877ef4953733a492e65ba491d612a490e03874904524948f39d1148d1fd4048b2a820487dc1cc486fdee44839f76747ff4200479d41744798609347947163 else 0x521f880f5216f0dc51e1d71f51dbd8b951da8ac051d9cc745187a552512ed84c51267c3350fe57b750f853a750ef9edd50a64103508076e04fe13de44fc2280a4f43eab94f355daf4f084d0a4f07352c4ef287104ee5eba84ee530334eb7cc154ead27104e9252954e65d1ba4e35cc174e15a5d84e0e29474e08bc924dcaab9c))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then 0x57c036ed578bc7ce57843b125763338556f3eeed56c8671f5645bda05638361d5610279155e86a6b55d3d2b555b173b155978016556f40c955240e665507cb7a54efe44854b577285492a99d547940d8546e9cef5452da7f5444873f53de3600539bb3455397c26353901d9c5381471a53475c1552f83a9652880761525f6898 else 0x5d79e27d5d6db27c5d58e12c5d10abd25cbf5d245ca1db365c6ff93d5c405c5e5c3b1e145b416ff65b2e2fad5b2d68675b10a7e35ae2e3995aa801015a83bb455a5a1dcb5a2b8e315a1a034c59bc1d8e5934056658ea9ae3589ebe3a58970c5858957a5a58924bca588e513d588cb2b1584a1670584613b75830aaf058278fe5) else (if i < 22 then 0x637100cc6365370c632b104b62ff738c62d2104e6253ddcf6228c9b0620fe26561f7ed996183d34e6121db756114c33c60f3ddec607c1abc605d81386036b0fd6033a0ec603296f8600944d25fc9a11d5f851f3c5f5d97215f4e0c3a5ea237b05e72b06e5e5e51485e274c845e103b7a5df09f8c5deb31575de231645dde3745 else (if i < 23 then 0x69e568f169ce2400696a9d9d6960941c6922d7ac68b1f62268a8552e68910b786858c0ea6825a98a6825717e67b1aaa267a3657f678c65e56771e002670ecce466e9716a66dc650c66cefc2566b7a2ae668c984c6661f253664f61166635a28b6546f99c64e52bc564874ef864616181645e485364557e18639e568363934f41 else 0x6f5fb2b26f405c3a6f2f5fbc6f1fbaa56ef8afd76ed7a74f6e65e4646e613d376e3fde0f6e348b8a6e06dfe36da4f1ad6d6e88716d39a8ff6ca8900e6c6fd8fd6c33b4d66c000a576bfac70f6bb435a66b98a0436b79acf86b5661036b3511bb6b1fe4e26b1c48d06b06b3606aeb0d0e6a8946206a72b0886a0bbb3069e6eceb))) else (if i < 26 then (if i < 25 then 0x75cdf06975c25662759157417546156d7536ad417519375e74db413574691d967468f264738a75cc735a7ca3734a7b3672c959827207301371e0795271bba5df7127cbf371148bc47111377770feff6470fd30b770a3a487709c053a704f461f7032e989702aa02670196c617006e88e6fef1fbc6fe518266f99586e6f815327 else 0x7b72a5077b65a3037b5e6df87b2c4ed67b0e2cbc7b06f44c7afcc3eb7aa553727a42578f7a3266db7a177e337a06800479f79a9379e042ee7983d460797d25a47967fa8579643be179368248790f73eb790ce283790b327378d056cf78a35b8a77e928e6772f9a2876f35e4076ebe0d676b1cf61764c57e87603174075d59530) else (if i < 27 then 0x827515ba820e55f38205001281bf0b77810c0a6c80e9510380b1c25c8095ab798038dbd0802e725980178f9180079e747ff3c2a07f420a0a7f2b87177f06cdb97efce1e17eaf3e977e97d3d57e8b1fd17e7abc767e74f4517e1d3af27df8571c7db823387db69b577d7068df7d6c027a7cfa22b37ca588697c150ace7bfd8fd9 else (if i < 28 then 0x8a5b0c4c89ea2a0389bf4eb889575e9089510d8e8940d96588cb0e3588bed94288b41eed88b18a90887375588855be9d8766915d87365948871e949f87174be986fe67d486b5167c8641dcd18610aa3a860f24e0858cc14984d1f99d84bf9e2c84b70cff8452362f84272dc383aaa60283994a1c8312ef38827bbd1f8279e789 else 0x9013abac9003e6588fcf611f8fc4896e8fc066918f48f4f38f18ad518f164e0e8ee5ae888e80f4348e778a658dda54eb8db695ea8d6ca2ff8d6423338d5794368d38161e8d1916968d0fb7718cf64bf18cad200b8c5aeec18c4d3e278be35ac58b8691598b6892bd8b603ece8b36dd0e8b27dff48ae2662f8acd78b18aa501ee)))) else (if i < 34 then (if i < 31 then (if i < 30 then 0x987576bf9849a714981dcd1197e7985097a007a7972d98479632d58b95f613a09565bfbe94f7357694dbeecf948a6f2f9482b7c993d7eccf93baac0893a0eb4e932eae489323f249931a3ce792f7971392786abe91f3d64f91ee8a0491d9811291d19c83919267c391401605911ed616910d703790eab0e7907418df903d1cd3 else 0x9fd382169fbad02d9f7f7f1f9f387fc19ef514689ea7b4b79da11d799d9251189d62c6939d16bdea9d117bcd9d0d07999cffbbc79ceb4a8b9ce4bc2f9cde6ab19caf2fbf9ca8517a9c7bfc629c7bd1309c665d829c13fa209b716f279b5af76a9ad859439a8554b19a4a11919a0fb5669a0db8cd9a03deb799f50e8f998b5d81) else (if i < 32 then 0xa88a10c1a8886ba1a85dfee7a837179da7f9031da7f74343a7f23322a7ca9a92a6f7750aa67c2fbea60b35e8a5d79d09a5318079a4e51c0fa4dda614a48b2f8aa39298ffa37e5c7ba37d4d2fa36cce99a34131daa2fcaff9a2bca7fca272bb1fa2342972a1900470a18b3f80a1683049a1496114a136343ba0c068109fdc25a4 else (if i < 33 then 0xae60ccabae497561adf762bbadf7134aade2b966adceb4c3adb9466aadb116abadb046bfad7a36acad511bffacfe9798ace4d869ac6b9b8aac6a4e61ac47c1bcabd7ade1abc47d3bab423349aaedff05aae98857aae81ddaaa1d2943a9c5855ca9ad3348a9a7a0f0a98ed805a97bf7e7a9753ffda9369618a8bf888da88f472b else 0xbbc49142baa898b8b9954273b9784096b9122932b8f019d5b7a0bc94b78b1318b723d7f8b6d38177b655fd63b53d7cdeb508f02eb4d02418b4caf96fb4aadbe4b49f5cb0b47fbde5b4787abbb3c7b6aeb3c45dbcb32b984db2db8199b28c8954b2773907b163884fb0c86a5cafc6a513af965865af7f550faf592dfbaec132bd))) else (if i < 36 then (if i < 35 then 0xc6e65158c63e96bdc5d6a591c5ce7f97c56ed193c558e703c4d4645ec4c91818c44b924ac324bcc0c2c4fd70c2a30e65c29ff5ecc2979042c2848a0dc21d3537c16cc4a1c12fc288c116f99dc0aeda8cc0a45894c0094214bfc43e4ebf40e43cbf0e7195be5b0819be4719ffbd30ccc7bce746b7bc9e63cbbc4ce7ecbc2539c5 else 0xd16053d0d1304429d0fe36fcd047eb27cfb932efcfa3717ccf71aef1cf61dea9cf0f1bf5cd73d768cd36d9f2cd0e1b17cd0a5917cbd133a1cb6c16c1ca8fce52ca705408ca47630fca3c0f54ca2a1663c9a8a069c8fde475c8f5dd3bc8b15b5ac88202cec8697540c7df1868c7c28ec3c792c24ac754e339c71cdbaac70776a7) else (if i < 37 then 0xdddadceddd2c21b4dd25724cdcd9ef7cdcc83079db316b52db305cf8dab2d1bada7cedbdda540811da4ce6fcd9a556cfd920b999d8c8d558d8b4a6efd7fb266ad79d572ad6a9734bd60a4187d51f6707d4dd1b5ed4d2888cd4929586d3fe20c2d3d0f0c9d39764c7d33957f1d3395561d2f4d380d250c3e4d234a4f9d22616df else (if i < 38 then 0xf36d569bf25ed592f20273e9f1fade67f16d1622f078c3ecf024ff69ef3907c3ef37d07dee4cf586edcf4b7aebb009ace8874d2ee81c20e0e7b01292e4f58f9de4978037e374ca13e333983ae24b60dce1571cc0e01d0484dfc0ee93df2dc400defdefaddee7ff9cdec6d493deb31f73deab68b4de6c2470de45c952dde74435 else 0xffab205cfe9cc667fd0e3482fccfff2ffc4e8935fa68778ff88aaaa7f807e85af5f8b403f5424191f4d2f4e9f3e4126d))))))
def g1_l6H (i : ℕ) : ℕ := fld (g1_l6HC (i / 32)) 32 (i % 32)
def g1_l7C (i : ℕ) : ℕ := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0xb7ec99f23871583515208b96c99f23871583514148b267c8e1c56e583514ab8b267c8e1c560d48514168002d1b267c8e1c560d457b267c8e1c56e583514168baae5b267c8e1c560d458b96c99f23871583514be8 else 0xb267c8e1c56e583514be800000b267c8e183514906002c99f238715b9515207002c99f238715452ac167b267c8e1c560d45050128002c99f23887183515357b267c8e1c560d454f1208b267c8e1c567d83514878) else (if i < 3 then 0xb267c8e1c56d5835153c8b267c8e1c560d454f0168002c99f23881d83514557002c99f238715834f0147002e5b267c8e1c5514ab7b96c99f238715b960d458002c99f238715452f8167baac99f238715b960d458 else (if i < 4 then 0x002c99f238715835e9457b7ec99f23871583514be8002c99f23873983514167002c99f259715835153c7002c99f238715b9514167b267c8e1c560d454f0ab8002e5b267c8e1c5514be7b7ec99f23871583514ab8 else 0xb267c8e1c560d450580c8002dfb267c8e1c56e5837002c99f23887183514007002c99f23871583514c47b267c8e1c560d454f0148b7ec99f23871583514148b267c8e1c560d7a514008b267c8e1c560d454f0be8))) else (if i < 8 then (if i < 6 then 0xb96c99f238715835153c8b96dfb267c8e1c560d458002c99f23881d83514587002c99f238715835152170027c8e1c560d452ac167002c99f238715835e88c7002c99f23871583514bd7002c99f238715835151e7 else (if i < 7 then 0x002c99f238715b55153c7b267c8e1c560d7a5148c8002c99f23887183515207002c99f23887183514d57b267c8e1c56e5835153c800000b267c8e1e560d456b267c8e1c560d452f80c8002c99f23881d835e9457 else 0x00000b267c8e23560d456002c99f2387158351541700000b267c8e1c5514c46002dfb267c8e1c560d3c7002c99f238715835f5457002e59f23871583514167b267c8e1c560d454811e8002c99f238715a360d457)) else (if i < 9 then 0xb7ec99f238715835153c8b267c8e1c560d7a514ab8b267c8e1c560d45488e68b267c8e1c560d45398008002c99f23871583514e67000009f238715452ac166002c99f23871583514177b267c8e1c560d4521c868 else (if i < 10 then 0x002c99f23887183514be7002c99f23871583480877b267c8e1c560d7a514be8b267c8e1c560d4521c008002c99f2387159f60d457002c99f23887183514ab7002c99f23887183514167002c99f23871583514877 else 0xb267c8e1c560d45480878002c99f23879583514be7002e5b267c8e21c60d457002df9f23871583514ab7b267c8e1c560d45480e68b7ec99f238715835140c8002c99f238801835153c7002c99f23887183514147)))) else (if i < 16 then (if i < 13 then (if i < 12 then 0xb267c8e1c560d7d514148002e5b7e7c8e1c560d45700000b267c8e21c51416600000b268b8e1c560d456002c99f238871b960d457002c99f2388d60760d457b267c8e1c560d453987a8002f1b267c8e20760d457 else 0xb267c8e1c560d4521c16800000b267c8e21660d456b267c8e1c560d45398ab8b267c8e1c560d45398168b267c8e1c560d69514ab8002c99f238715832f8877002dab267c8e1c560d45700000b26978e1c560d456) else (if i < 14 then 0x002c99f2388720d60d457b267c8e1c560d452f8878b267c8e1c560d7a5153c8b96c99f23871583515418b267c8e1c560d4539814800000b96c99f238871456002c9a2e3871583515207b267c8e1c560d452ac878 else (if i < 15 then 0x002c99f2388d5b960d457b267c8e1c560d454f11e8002c99f23881d835141c700000b7e7c8e1c560d3c6b267c8e1c560d4521c148002c99f23871583514ac7002dfb267c8e21c60d457b6ac99f23871583515208 else 0x002c99f2387158351400700000b267c8e183514d56002c99f2387158351518700000b267c951c560d456002df9f238715835153c700000b267c8e1c52f88760027c8e1c560d7a514ab7b267c8e1c56e583514178))) else (if i < 19 then (if i < 17 then 0x00000b267c8e20760cc76002c99f23871583514077b267c8e1c560d45481188002c99f23887183514907b7ec99f23871583514e68002c99f25471583515207002c99f238715ae60d457002c99f2387158460d457 else (if i < 18 then 0x0027c8e1c560d45398ab7002c99f238715835147a7002c99f238871835e945700000b6a7c8e1c560d456b5ac99f23871583514be8b267c8e1c560d45480008002c99f238715b9514877002c99f23871583515207 else 0x002eab267c8e1c560d45700000b267c965c560d456b267c8e1c560d45058008002c99f238715b560d457002c99f23871583514167002da9f23871583515207b267c8e1c560d452ac868b267c8e1c560d7a514bd8)) else (if i < 20 then 0xb96c99f23871583514008000009f23871583515186002c99f23871583514127b267c8e1c560d45480168002c99f23881d83514be7002e5b267c8e1c560d457002c99f23881d83514ab700000b267c8e1c56cd836 else (if i < 21 then 0x0027c8e1c560d45481187b267c8e1c560d4548012800000b267c8e1f160d456b267c8e1c56e5ae60d458b267c8e1c56e583514008002c9a4638715835153c7002c99f238715b960d457b7ec99f23871583514ac8 else 0x00000b267c8e1c56e5206b267c8e1c560d45058148b267c8e1c56e5835147a8b267c8e1c560d452f8ab800000b267c8e1cd60d456002c99f2387c583515207b267c8e1c56e583515208)))))
def g1_l7S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l7C (i / 8)) 84 (i % 8))
def g1_l7HC (i : ℕ) : ℕ := (if i < 3 then (if i < 1 then 0x2166c793215886d12070c982200e257e1ec562071c74d9e91c69374b1c2e3aef1bcf16731bb64d8818cb262418410e5f173eeb6912e7dd930c1fdd18088f006a08875ba3072b1e62072a605106f59136053aa9a5051a55df041b4bd20406f9c203d4acd803a629f5035d0fc10320838302af18d3029e83600049fd6b004258a4 else (if i < 2 then 0x46ebeb9a422dbd3f42231c444053ed2b3ad3b76d3a9b3eaf39e0f909391e4a4d37f5f51a369a8d61360c43a335f2d8233444aaba2f7c4c792d79990c2c9b9aac2bffa7bb2bb908c12b7466442b710ffc2b1070dd29d8a4a42945d9312882ce332790c0c9273c230326942a7325fc3d9d2502f71c24bc5822234cd939219f25cb else 0x6d198d8d6bfac70f69ce24006825a98a6635a28b61f7ed995fb922b65f4e0c3a5e9dc1765e5e51485df09f8c5c6ff93d59dbeca258f04929588cb2b156f3eeed53901d9c51dbd8b95048cc624f25a8464ee530334e65d1ba4da745594d3f96a04d15d5e84b1e80804b02beab4a63d372487dc1cc47374f84472a957f46f9fe0f)) else (if i < 4 then 0x9a03deb7998b5d8192f797138dda54eb8d5794368b8691598b603ece88b21f3d8873755883222219827515ba8095ab797f856cc07f2b87177f06cdb97eccb3477db69b577c219b6f7c061b797b7043fe7ac397ec7a177e337983d46076f74f8d7638c32c7603174072357ab97176ee587064bcf36f5fb2b26d6e88716d39a8ff else (if i < 5 then 0xd3466576d3395561d2f4d380d2752473d234a4f9d16053d0cd0a5917c7c28ec3c70776a7c56ed193c2fd0b43c12fc288c116f99dbf0e7195bb8fed6db28ed3aeb2773907af592dfbadf7134aadb046bfac783febab62098daaedff05a97bf7e7a837179da7f23322a455c1e9a39298ffa2d676b89f387fc19a8554b19a0db8cd else 0xfa68778ff35ccfbdf0e0b7b9f0b78acdf078c3ecef3907c3eb0381a5e4978037e452fe56dddadceddc0cde6fdb8b6875da4ce6fcd9a556cfd9843c03)))
def g1_l7H (i : ℕ) : ℕ := fld (g1_l7HC (i / 32)) 32 (i % 32)
def g1_l8C (_ : ℕ) : ℕ := 0x002c99f238715b960d457002e5b267c8e1c560d457002c99f23871583514167002c99f23871583515207002c99f23871583514877002c99f23871583514e6700000b267c8e21c60d456002c99f238715835e9457
def g1_l8S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l8C (i / 8)) 84 (i % 8))
def g1_l8HC (_ : ℕ) : ℕ := 0xd9a556cfd16053d0c116f99da97bf7e74d3f96a0487dc1cc24ae18cd2166c793
def g1_l8H (i : ℕ) : ℕ := fld (g1_l8HC (i / 32)) 32 (i % 32)
def g1_l9C (_ : ℕ) : ℕ := 0x00000b267c8e1c560d456
def g1_l9S (i : ℕ) : List ℕ := g1_decSt (fld (g1_l9C (i / 8)) 84 (i % 8))
def g1_l9HC (_ : ℕ) : ℕ := 0x981dcd11
def g1_l9H (i : ℕ) : ℕ := fld (g1_l9HC (i / 32)) 32 (i % 32)
def g1_N : ℕ → ℕ
  | 2 => 4
  | 3 => 53
  | 4 => 927
  | 5 => 2052
  | 6 => 1228
  | 7 => 175
  | 8 => 8
  | 9 => 1
  | _ => 0
def g1_S : ℕ → ℕ → List ℕ
  | 2, i => g1_l2S i
  | 3, i => g1_l3S i
  | 4, i => g1_l4S i
  | 5, i => g1_l5S i
  | 6, i => g1_l6S i
  | 7, i => g1_l7S i
  | 8, i => g1_l8S i
  | 9, i => g1_l9S i
  | _, _ => []
def g1_idx : ℕ → List ℕ → ℕ
  | 2, zs => bsrF g1_l2H (hk zs) 12 0 4
  | 3, zs => bsrF g1_l3H (hk zs) 12 0 53
  | 4, zs => bsrF g1_l4H (hk zs) 12 0 927
  | 5, zs => bsrF g1_l5H (hk zs) 12 0 2052
  | 6, zs => bsrF g1_l6H (hk zs) 12 0 1228
  | 7, zs => bsrF g1_l7H (hk zs) 12 0 175
  | 8, zs => bsrF g1_l8H (hk zs) 12 0 8
  | _, _ => 0
def g1_bar : ℕ → ℕ → Bool := bar (w64v 2).toNat (w64v 3).toNat (w64v 4).toNat g1_dt0 g1_dt1 g1_dt2 g1_dt3 g1_dt4 g1_dt5 g1_S g1_N g1_idx (ori swap01Nat)
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s2_0 : span (g1_bar 2) 4 0 = true := by decide +kernel
theorem g1_l2_all : span (g1_bar 2) 4 0 = true := g1_s2_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s3_0 : span (g1_bar 3) 53 0 = true := by decide +kernel
theorem g1_l3_all : span (g1_bar 3) 53 0 = true := g1_s3_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_0 : span (g1_bar 4) 65 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_1 : span (g1_bar 4) 65 65 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_2 : span (g1_bar 4) 65 130 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_3 : span (g1_bar 4) 65 195 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_4 : span (g1_bar 4) 65 260 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_5 : span (g1_bar 4) 65 325 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_6 : span (g1_bar 4) 65 390 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_7 : span (g1_bar 4) 65 455 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_8 : span (g1_bar 4) 65 520 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_9 : span (g1_bar 4) 65 585 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_10 : span (g1_bar 4) 65 650 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_11 : span (g1_bar 4) 65 715 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_12 : span (g1_bar 4) 65 780 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_13 : span (g1_bar 4) 65 845 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s4_14 : span (g1_bar 4) 17 910 = true := by decide +kernel
theorem g1_l4_all : span (g1_bar 4) 927 0 = true := (@span_join (g1_bar 4) 455 0 472 (@span_join (g1_bar 4) 195 0 260 (@span_join (g1_bar 4) 65 0 130 g1_s4_0 (@span_join (g1_bar 4) 65 65 65 g1_s4_1 g1_s4_2)) (@span_join (g1_bar 4) 130 195 130 (@span_join (g1_bar 4) 65 195 65 g1_s4_3 g1_s4_4) (@span_join (g1_bar 4) 65 325 65 g1_s4_5 g1_s4_6))) (@span_join (g1_bar 4) 260 455 212 (@span_join (g1_bar 4) 130 455 130 (@span_join (g1_bar 4) 65 455 65 g1_s4_7 g1_s4_8) (@span_join (g1_bar 4) 65 585 65 g1_s4_9 g1_s4_10)) (@span_join (g1_bar 4) 130 715 82 (@span_join (g1_bar 4) 65 715 65 g1_s4_11 g1_s4_12) (@span_join (g1_bar 4) 65 845 17 g1_s4_13 g1_s4_14))))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_0 : span (g1_bar 5) 65 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_1 : span (g1_bar 5) 65 65 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_2 : span (g1_bar 5) 65 130 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_3 : span (g1_bar 5) 65 195 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_4 : span (g1_bar 5) 65 260 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_5 : span (g1_bar 5) 65 325 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_6 : span (g1_bar 5) 65 390 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_7 : span (g1_bar 5) 65 455 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_8 : span (g1_bar 5) 65 520 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_9 : span (g1_bar 5) 65 585 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_10 : span (g1_bar 5) 65 650 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_11 : span (g1_bar 5) 65 715 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_12 : span (g1_bar 5) 65 780 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_13 : span (g1_bar 5) 65 845 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_14 : span (g1_bar 5) 65 910 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_15 : span (g1_bar 5) 65 975 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_16 : span (g1_bar 5) 65 1040 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_17 : span (g1_bar 5) 65 1105 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_18 : span (g1_bar 5) 65 1170 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_19 : span (g1_bar 5) 65 1235 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_20 : span (g1_bar 5) 65 1300 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_21 : span (g1_bar 5) 65 1365 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_22 : span (g1_bar 5) 65 1430 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_23 : span (g1_bar 5) 65 1495 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_24 : span (g1_bar 5) 65 1560 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_25 : span (g1_bar 5) 65 1625 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_26 : span (g1_bar 5) 65 1690 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_27 : span (g1_bar 5) 65 1755 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_28 : span (g1_bar 5) 65 1820 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_29 : span (g1_bar 5) 65 1885 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_30 : span (g1_bar 5) 65 1950 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s5_31 : span (g1_bar 5) 37 2015 = true := by decide +kernel
theorem g1_l5_all : span (g1_bar 5) 2052 0 = true := (@span_join (g1_bar 5) 1040 0 1012 (@span_join (g1_bar 5) 520 0 520 (@span_join (g1_bar 5) 260 0 260 (@span_join (g1_bar 5) 130 0 130 (@span_join (g1_bar 5) 65 0 65 g1_s5_0 g1_s5_1) (@span_join (g1_bar 5) 65 130 65 g1_s5_2 g1_s5_3)) (@span_join (g1_bar 5) 130 260 130 (@span_join (g1_bar 5) 65 260 65 g1_s5_4 g1_s5_5) (@span_join (g1_bar 5) 65 390 65 g1_s5_6 g1_s5_7))) (@span_join (g1_bar 5) 260 520 260 (@span_join (g1_bar 5) 130 520 130 (@span_join (g1_bar 5) 65 520 65 g1_s5_8 g1_s5_9) (@span_join (g1_bar 5) 65 650 65 g1_s5_10 g1_s5_11)) (@span_join (g1_bar 5) 130 780 130 (@span_join (g1_bar 5) 65 780 65 g1_s5_12 g1_s5_13) (@span_join (g1_bar 5) 65 910 65 g1_s5_14 g1_s5_15)))) (@span_join (g1_bar 5) 520 1040 492 (@span_join (g1_bar 5) 260 1040 260 (@span_join (g1_bar 5) 130 1040 130 (@span_join (g1_bar 5) 65 1040 65 g1_s5_16 g1_s5_17) (@span_join (g1_bar 5) 65 1170 65 g1_s5_18 g1_s5_19)) (@span_join (g1_bar 5) 130 1300 130 (@span_join (g1_bar 5) 65 1300 65 g1_s5_20 g1_s5_21) (@span_join (g1_bar 5) 65 1430 65 g1_s5_22 g1_s5_23))) (@span_join (g1_bar 5) 260 1560 232 (@span_join (g1_bar 5) 130 1560 130 (@span_join (g1_bar 5) 65 1560 65 g1_s5_24 g1_s5_25) (@span_join (g1_bar 5) 65 1690 65 g1_s5_26 g1_s5_27)) (@span_join (g1_bar 5) 130 1820 102 (@span_join (g1_bar 5) 65 1820 65 g1_s5_28 g1_s5_29) (@span_join (g1_bar 5) 65 1950 37 g1_s5_30 g1_s5_31)))))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_0 : span (g1_bar 6) 45 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_1 : span (g1_bar 6) 45 45 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_2 : span (g1_bar 6) 45 90 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_3 : span (g1_bar 6) 45 135 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_4 : span (g1_bar 6) 45 180 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_5 : span (g1_bar 6) 45 225 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_6 : span (g1_bar 6) 45 270 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_7 : span (g1_bar 6) 45 315 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_8 : span (g1_bar 6) 45 360 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_9 : span (g1_bar 6) 45 405 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_10 : span (g1_bar 6) 45 450 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_11 : span (g1_bar 6) 45 495 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_12 : span (g1_bar 6) 45 540 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_13 : span (g1_bar 6) 45 585 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_14 : span (g1_bar 6) 45 630 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_15 : span (g1_bar 6) 45 675 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_16 : span (g1_bar 6) 45 720 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_17 : span (g1_bar 6) 45 765 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_18 : span (g1_bar 6) 45 810 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_19 : span (g1_bar 6) 45 855 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_20 : span (g1_bar 6) 45 900 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_21 : span (g1_bar 6) 45 945 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_22 : span (g1_bar 6) 45 990 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_23 : span (g1_bar 6) 45 1035 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_24 : span (g1_bar 6) 45 1080 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_25 : span (g1_bar 6) 45 1125 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_26 : span (g1_bar 6) 45 1170 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s6_27 : span (g1_bar 6) 13 1215 = true := by decide +kernel
theorem g1_l6_all : span (g1_bar 6) 1228 0 = true := (@span_join (g1_bar 6) 630 0 598 (@span_join (g1_bar 6) 315 0 315 (@span_join (g1_bar 6) 135 0 180 (@span_join (g1_bar 6) 45 0 90 g1_s6_0 (@span_join (g1_bar 6) 45 45 45 g1_s6_1 g1_s6_2)) (@span_join (g1_bar 6) 90 135 90 (@span_join (g1_bar 6) 45 135 45 g1_s6_3 g1_s6_4) (@span_join (g1_bar 6) 45 225 45 g1_s6_5 g1_s6_6))) (@span_join (g1_bar 6) 135 315 180 (@span_join (g1_bar 6) 45 315 90 g1_s6_7 (@span_join (g1_bar 6) 45 360 45 g1_s6_8 g1_s6_9)) (@span_join (g1_bar 6) 90 450 90 (@span_join (g1_bar 6) 45 450 45 g1_s6_10 g1_s6_11) (@span_join (g1_bar 6) 45 540 45 g1_s6_12 g1_s6_13)))) (@span_join (g1_bar 6) 315 630 283 (@span_join (g1_bar 6) 135 630 180 (@span_join (g1_bar 6) 45 630 90 g1_s6_14 (@span_join (g1_bar 6) 45 675 45 g1_s6_15 g1_s6_16)) (@span_join (g1_bar 6) 90 765 90 (@span_join (g1_bar 6) 45 765 45 g1_s6_17 g1_s6_18) (@span_join (g1_bar 6) 45 855 45 g1_s6_19 g1_s6_20))) (@span_join (g1_bar 6) 135 945 148 (@span_join (g1_bar 6) 45 945 90 g1_s6_21 (@span_join (g1_bar 6) 45 990 45 g1_s6_22 g1_s6_23)) (@span_join (g1_bar 6) 90 1080 58 (@span_join (g1_bar 6) 45 1080 45 g1_s6_24 g1_s6_25) (@span_join (g1_bar 6) 45 1170 13 g1_s6_26 g1_s6_27)))))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s7_0 : span (g1_bar 7) 40 0 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s7_1 : span (g1_bar 7) 40 40 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s7_2 : span (g1_bar 7) 40 80 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s7_3 : span (g1_bar 7) 40 120 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s7_4 : span (g1_bar 7) 15 160 = true := by decide +kernel
theorem g1_l7_all : span (g1_bar 7) 175 0 = true := (@span_join (g1_bar 7) 80 0 95 (@span_join (g1_bar 7) 40 0 40 g1_s7_0 g1_s7_1) (@span_join (g1_bar 7) 40 80 55 g1_s7_2 (@span_join (g1_bar 7) 40 120 15 g1_s7_3 g1_s7_4)))
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s8_0 : span (g1_bar 8) 8 0 = true := by decide +kernel
theorem g1_l8_all : span (g1_bar 8) 8 0 = true := g1_s8_0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem g1_s9_0 : span (g1_bar 9) 1 0 = true := by decide +kernel
theorem g1_l9_all : span (g1_bar 9) 1 0 = true := g1_s9_0
theorem g1_chk : ∀ s ≤ 9, ∀ i < g1_N s, g1_bar s i = true := by
  intro s hs i hi
  match s with
  | 0 => simp [g1_N] at hi
  | 1 => simp [g1_N] at hi
  | 2 => exact span_ok g1_l2_all i (Nat.zero_le i) hi
  | 3 => exact span_ok g1_l3_all i (Nat.zero_le i) hi
  | 4 => exact span_ok g1_l4_all i (Nat.zero_le i) hi
  | 5 => exact span_ok g1_l5_all i (Nat.zero_le i) hi
  | 6 => exact span_ok g1_l6_all i (Nat.zero_le i) hi
  | 7 => exact span_ok g1_l7_all i (Nat.zero_le i) hi
  | 8 => exact span_ok g1_l8_all i (Nat.zero_le i) hi
  | 9 => exact span_ok g1_l9_all i (Nat.zero_le i) hi
  | _ + 10 => omega
theorem g1_root : g1_S 9 0 = w64_vars.map BitVec.toNat := by decide +kernel
theorem g1_prop : w64_vars.sublists.all (fun ws => (ws.length == 6) || !(cover6 g1_dt0 g1_dt1 g1_dt2 g1_dt3 g1_dt4 g1_dt5 (ws.map BitVec.toNat))) = true := by decide +kernel
theorem g1_no9_64 (t : W64) (ht : t = g1_tt64 ∨ t = ~~~g1_tt64)
    (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  apply bar_refute64 (c0 := w64v 2) (c1 := w64v 3) (c2 := w64v 4) (tgt := g1_tt64)
    (d0 := g1_dt0) (d1 := g1_dt1) (d2 := g1_dt2) (d3 := g1_dt3) (d4 := g1_dt4) (d5 := g1_dt5)
    (swMap := swap01Map) (swNat := swap01Nat) (S := g1_S) (N := g1_N) (idx := g1_idx)
    rfl rfl rfl rfl rfl rfl
    swap01_inv swap01_nat (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    g1_root (by decide) g1_prop g1_chk
    (fun t' ht' => enforce_drop6 2 g1_tt64 (by decide +kernel) (no7_of_k4p64 ⟨1, by decide⟩ ⟨9, by decide⟩ (w64v 3) k4m_0145 (dropVar6 2) (restrict6 2 g1_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨1, by decide⟩ ⟨9, by decide⟩ (dropVar6 2) (w64v 3) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0145) (dropVar6 2) k4_16_vars (by decide +kernel))) ht')
    (fun t' ht' => enforce_drop6 3 g1_tt64 (by decide +kernel) (no7_of_k4p64 ⟨16, by decide⟩ ⟨20, by decide⟩ (w64v 2) k4m_0145 (dropVar6 3) (restrict6 3 g1_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨20, by decide⟩ (dropVar6 3) (w64v 2) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0145) (dropVar6 3) k4_16_vars (by decide +kernel))) ht')
    (fun t' ht' => enforce_drop6 4 g1_tt64 (by decide +kernel) (no7_of_k4p64 ⟨32, by decide⟩ ⟨36, by decide⟩ (w64v 2) k4m_0135 (dropVar6 4) (restrict6 4 g1_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨32, by decide⟩ ⟨36, by decide⟩ (dropVar6 4) (w64v 2) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0135) (dropVar6 4) k4_16_vars (by decide +kernel))) ht')
    t ht hb

end G1Bar

section G4G5

def g4_tt64 : W64 := 0xfffffffefffeeca0#64
def g5_tt64 : W64 := 0xfffffffefefaeca0#64
def sep4A : Array ℕ := #[0, 0, 0, 0, 4, 6, 6, 4, 16, 4, 4, 16, 4, 12, 12, 4, 4, 16, 16, 4, 4, 32, 32, 4, 8, 9, 9, 8, 0, 0, 0, 0, 8, 12, 12, 8, 16, 8, 8, 16, 8, 16, 16, 8, 8, 32, 32, 8, 16, 1, 1, 16, 1, 3, 3, 1, 0, 0, 0, 0, 1, 9, 9, 1, 1, 16, 16, 1, 1, 32, 32, 1, 2, 3, 3, 2, 16, 2, 2, 16, 2, 6, 6, 2, 0, 0, 0, 0, 2, 16, 16, 2, 2, 32, 32, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 8, 8, 1, 0, 0, 0, 0, 1, 32, 32, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 8, 8, 1, 1, 16, 16, 1, 0, 0, 0, 0]
def sep4B : Array ℕ := #[0, 0, 0, 0, 5, 7, 7, 5, 17, 5, 5, 17, 5, 13, 13, 5, 5, 17, 17, 5, 5, 33, 33, 5, 10, 11, 11, 10, 0, 0, 0, 0, 10, 14, 14, 10, 18, 10, 10, 18, 10, 18, 18, 10, 10, 34, 34, 10, 20, 5, 5, 20, 5, 7, 7, 5, 0, 0, 0, 0, 5, 13, 13, 5, 5, 20, 20, 5, 5, 36, 36, 5, 10, 11, 11, 10, 24, 10, 10, 24, 10, 14, 14, 10, 0, 0, 0, 0, 10, 24, 24, 10, 10, 40, 40, 10, 18, 17, 17, 18, 17, 18, 18, 17, 17, 20, 20, 17, 17, 24, 24, 17, 0, 0, 0, 0, 17, 48, 48, 17, 34, 33, 33, 34, 33, 34, 34, 33, 33, 36, 36, 33, 33, 40, 40, 33, 33, 48, 48, 33, 0, 0, 0, 0]
def sep5A : Array ℕ := #[0, 0, 0, 0, 4, 6, 6, 4, 16, 4, 4, 16, 4, 12, 12, 4, 4, 16, 16, 4, 4, 32, 32, 4, 8, 9, 9, 8, 0, 0, 0, 0, 8, 12, 12, 8, 32, 8, 8, 32, 8, 24, 24, 8, 8, 32, 32, 8, 16, 1, 1, 16, 1, 3, 3, 1, 0, 0, 0, 0, 1, 9, 9, 1, 1, 16, 16, 1, 1, 32, 32, 1, 2, 3, 3, 2, 32, 2, 2, 32, 2, 6, 6, 2, 0, 0, 0, 0, 2, 18, 18, 2, 2, 32, 32, 2, 4, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4, 1, 1, 9, 9, 1, 0, 0, 0, 0, 1, 32, 32, 1, 4, 32, 4, 32, 8, 32, 8, 32, 1, 32, 1, 32, 2, 32, 2, 32, 1, 32, 1, 32, 0, 0, 0, 0]
def sep5B : Array ℕ := #[0, 0, 0, 0, 5, 7, 7, 5, 17, 5, 5, 17, 5, 13, 13, 5, 5, 17, 17, 5, 5, 33, 33, 5, 10, 11, 11, 10, 0, 0, 0, 0, 10, 14, 14, 10, 34, 10, 10, 34, 10, 26, 26, 10, 10, 34, 34, 10, 20, 5, 5, 20, 5, 7, 7, 5, 0, 0, 0, 0, 5, 13, 13, 5, 5, 20, 20, 5, 5, 36, 36, 5, 10, 11, 11, 10, 40, 10, 10, 40, 10, 14, 14, 10, 0, 0, 0, 0, 10, 26, 26, 10, 10, 40, 40, 10, 20, 17, 17, 20, 17, 19, 19, 17, 17, 20, 20, 17, 17, 25, 25, 17, 0, 0, 0, 0, 17, 48, 48, 17, 5, 33, 5, 33, 10, 34, 10, 34, 5, 36, 5, 36, 10, 40, 10, 40, 17, 48, 17, 48, 0, 0, 0, 0]

def checkSep64 (tgt : W64) (pick : Fin 6 → Fin 6 → Fin 6) (sA sB : Array ℕ) : Bool :=
  (List.finRange 6).all fun i =>
    (List.finRange 6).all fun j =>
      if i == j then true else
        (List.finRange 4).all fun op =>
          let p := pick i j
          let a := sA[24 * i.val + 4 * j.val + op.val]! % 64
          let b := sB[24 * i.val + 4 * j.val + op.val]! % 64
          let z := (ops (w64v i) (w64v j)).getD op.val 0
          (tgt[a]! != tgt[b]!) &&
          (z[a]! == z[b]!) &&
          (List.finRange 6).all fun q =>
            (q == p) || ((w64v q)[a]! == (w64v q)[b]!)

theorem no9_forced64 (tgt : W64) (pick : Fin 6 → Fin 6 → Fin 6) (sA sB : Array ℕ)
    (hpick : ∀ i j, i ≠ j → pick i j = i ∨ pick i j = j)
    (hnt : ∀ i : Fin 6, w64v i ≠ tgt ∧ w64v i ≠ ~~~tgt)
    (hsep : checkSep64 tgt pick sA sB = true)
    (hdrop : ∀ i j, i ≠ j →
      (restrict6 (pick i j) tgt ≠ 0 ∧ restrict6 (pick i j) tgt ≠ ~~~0) ∧
      ∀ t5, (t5 = restrict6 (pick i j) tgt ∨ t5 = ~~~restrict6 (pick i j) tgt) →
        build basicOps t5 7 (dropVar6 (pick i j)).toFinset → False)
    (t : W64) (ht : t = tgt ∨ t = ~~~tgt)
    (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 8) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := w64_cover mt
    rcases ht with rfl | rfl
    · exact (hnt i).1 hi
    · exact (hnt i).2 hi
  · obtain ⟨i, rfl⟩ := w64_cover (hs ha)
    obtain ⟨j, rfl⟩ := w64_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg w64v e)
    have hsub : rest ⊆ w64_vars.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    obtain ⟨op, hop⟩ := index_of_op _ _ _ hz
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hsep i (List.mem_finRange i)) j (List.mem_finRange j)
    have hne : (i == j) = false := beq_false_of_ne hij
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h1
    have h2 := List.all_eq_true.mp h1 op (List.mem_finRange op)
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h2
    obtain ⟨⟨hdt, hzeq⟩, hallq⟩ := h2
    rw [hop] at hzeq
    let p := pick i j
    let aa : Fin 64 := ⟨sA[24 * i.val + 4 * j.val + op.val]! % 64, Nat.mod_lt _ (by decide)⟩
    let bb : Fin 64 := ⟨sB[24 * i.val + 4 * j.val + op.val]! % 64, Nat.mod_lt _ (by decide)⟩
    have hdt' : bitDiff aa bb tgt := by
      unfold bitDiff
      simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hdt
    have hzeq' : z[aa.val] = z[bb.val] := by
      simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hzeq
    have hd : bitDiff aa bb t := by
      rcases ht with rfl | rfl
      · exact hdt'
      · exact bitDiff_not hdt'
    have hkeep : w64v p ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff aa bb) hd (ops_bitDiff aa bb) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hdw hzeq').elim
      · obtain ⟨q, rfl⟩ := w64_cover (hsub hw)
        have hq := List.all_eq_true.mp hallq q (List.mem_finRange q)
        simp only [Bool.or_eq_true, beq_iff_eq] at hq
        rcases hq with hqp | hqeq
        · exact (show q = p from hqp) ▸ hw
        · have hqeq' : (w64v q)[aa.val] = (w64v q)[bb.val] := by
            simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hqeq
          exact (hdw hqeq').elim
    let f := restrict6 p
    have hm := ops_map_of (selectRows_land (fixBit6 p)) (selectRows_lor (fixBit6 p)) (selectRows_neg (fixBit6 p))
    have hfp0 : f (w64v p) = 0 := restrict6_self p
    have hhold : ∀ w ∈ w64_vars, holds (dropVar6 p).toFinset (f w) := by
      have hall : ∀ d' : Fin 6, w64_vars.all (fun w => restrict6 d' w == 0 || restrict6 d' w == ~~~0 || (dropVar6 d').any (fun u => restrict6 d' w == u)) = true := by
        decide +kernel
      exact map_holds_list (restrict6 p) w64_vars (dropVar6 p) (hall p)
    have hft : f t = f tgt ∨ f t = ~~~f tgt := by
      rcases ht with rfl | rfl
      · exact .inl rfl
      · exact .inr (selectRows_neg (fixBit6 p) tgt)
    obtain ⟨hnc, hbot⟩ := hdrop i j hij
    have hng : f t ≠ 0 ∧ f t ≠ ~~~0 := by
      rcases hft with h' | h' <;> rw [h']
      · exact hnc
      · exact not_const_of_neg hnc
    have hfz : holds (dropVar6 p).toFinset (f z) := by
      have hi_m : w64v i ∈ w64_vars := by fin_cases i <;> decide
      have hj_m : w64v j ∈ w64_vars := by fin_cases j <;> decide
      have hc : (f (w64v i) = 0 ∨ f (w64v i) = ~~~0) ∨ (f (w64v j) = 0 ∨ f (w64v j) = ~~~0) := by
        rcases hpick i j hij with hp | hp
        · exact .inl (.inl (hp ▸ hfp0))
        · exact .inr (.inl (hp ▸ hfp0))
      exact mem_ops_const (hhold _ hi_m) (hhold _ hj_m) hc (hm _ _ _ hz)
    obtain ⟨_, hsb⟩ := live_transport_save_const hm tail (Finset.mem_insert_of_mem hkeep) (.inl hfp0) hng (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact hfz
      · exact hhold w (List.mem_toFinset.mp (hsub hr)))
    obtain ⟨t5, ht5, hb5⟩ := unwrap_sb hng.1 hng.2 hsb
    have ht5' : t5 = f tgt ∨ t5 = ~~~f tgt := by
      rcases hft with h' | h' <;> rcases ht5 with rfl | rfl <;> rw [h']
      · exact .inl rfl
      · exact .inr rfl
      · exact .inr rfl
      · exact .inl BitVec.not_not
    exact hbot t5 ht5' hb5

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sep4_ok : checkSep64 g4_tt64 (fun i _ => i) sep4A sep4B = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sep5_ok : checkSep64 g5_tt64 (fun i j => if i.val == 5 then j else i) sep5A sep5B = true := by decide +kernel

theorem g4_no9_64 (t : W64) (ht : t = g4_tt64 ∨ t = ~~~g4_tt64)
    (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  apply no9_forced64 g4_tt64 (fun i _ => i) sep4A sep4B (fun _ _ _ => .inl rfl) (by decide) sep4_ok ?_ t ht hb
  intro i _ _
  fin_cases i
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨16, by decide⟩ ⟨20, by decide⟩ (w64v 2) k4m_1345 (dropVar6 0) (restrict6 0 g4_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨20, by decide⟩ (dropVar6 0) (w64v 2) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_1345) (dropVar6 0) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨16, by decide⟩ ⟨24, by decide⟩ (w64v 3) k4m_0245 (dropVar6 1) (restrict6 1 g4_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨24, by decide⟩ (dropVar6 1) (w64v 3) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 1) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨16, by decide⟩ ⟨17, by decide⟩ (w64v 0) k4m_1345 (dropVar6 2) (restrict6 2 g4_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨17, by decide⟩ (dropVar6 2) (w64v 0) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_1345) (dropVar6 2) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨16, by decide⟩ ⟨18, by decide⟩ (w64v 1) k4m_0245 (dropVar6 3) (restrict6 3 g4_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨16, by decide⟩ ⟨18, by decide⟩ (dropVar6 3) (w64v 1) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 3) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_bow64 bowm_02135 (dropVar6 4) (restrict6 4 g4_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_02135) (dropVar6 4) bow_32_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_bow64 bowm_02134 (dropVar6 5) (restrict6 5 g4_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_02134) (dropVar6 5) bow_32_vars (by decide +kernel))⟩

theorem g5_no9_64 (t : W64) (ht : t = g5_tt64 ∨ t = ~~~g5_tt64)
    (hb : build basicOps t 9 w64_vars.toFinset) : False := by
  apply no9_forced64 g5_tt64 (fun i j => if i.val == 5 then j else i) sep5A sep5B
    (fun i j _ => by by_cases h : i.val = 5 <;> simp [h]) (by decide) sep5_ok ?_ t ht hb
  intro i j hij
  have hp5 : (if i.val == 5 then j else i).val ≠ 5 := by
    by_cases hi : i.val = 5
    · simp [hi]; intro hj; exact hij (Fin.ext (hi.trans hj.symm))
    · simp [hi]
  generalize hp : (if i.val == 5 then j else i) = p at hp5 ⊢
  fin_cases p
  · exact ⟨by decide +kernel, no7_of_bow64 bowm_13245 (dropVar6 0) (restrict6 0 g5_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_13245) (dropVar6 0) bow_32_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨32, by decide⟩ ⟨40, by decide⟩ (w64v 3) k4m_0245 (dropVar6 1) (restrict6 1 g5_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨32, by decide⟩ ⟨40, by decide⟩ (dropVar6 1) (w64v 3) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 1) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_bow64 bowm_04135 (dropVar6 2) (restrict6 2 g5_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_04135) (dropVar6 2) bow_32_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_k4p64 ⟨32, by decide⟩ ⟨34, by decide⟩ (w64v 1) k4m_0245 (dropVar6 3) (restrict6 3 g5_tt64) (by unfold bitDiff; decide +kernel) (sep_of_all ⟨32, by decide⟩ ⟨34, by decide⟩ (dropVar6 3) (w64v 1) (by decide +kernel)) (by decide +kernel) (by decide +kernel) (map_holds_list (selectRows k4m_0245) (dropVar6 3) k4_16_vars (by decide +kernel))⟩
  · exact ⟨by decide +kernel, no7_of_bow64 bowm_02135 (dropVar6 4) (restrict6 4 g5_tt64) (by decide +kernel) (map_holds_list (selectRows bowm_02135) (dropVar6 4) bow_32_vars (by decide +kernel))⟩
  · exact (hp5 rfl).elim

end G4G5


section Lower10564

def edges10564 : List ℕ := [0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]
def edgeValue (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edges10564.length / 2,
    (List.ofFn x).getD (edges10564.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges10564.getD (2 * i + 1) 0) false = true)
def v0 : W128 := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#128
def v1 : W128 := 0xcccccccccccccccccccccccccccccccc#128
def v2 : W128 := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#128
def v3 : W128 := 0xff00ff00ff00ff00ff00ff00ff00ff00#128
def v4 : W128 := 0xffff0000ffff0000ffff0000ffff0000#128
def v5 : W128 := 0xffffffff00000000ffffffff00000000#128
def v6 : W128 := 0xffffffffffffffff0000000000000000#128
def rows7 : List W128 := [v0, v1, v2, v3, v4, v5, v6]
def r7v (i : Fin 7) : W128 := rows7.getD i.val 0
def target7 : W128 := 0xfffffffffffffffefffefffefefaeca0#128
theorem t7_nc : target7 ≠ 0 ∧ target7 ≠ ~~~0 := by decide
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sample7 : ∀ k : Fin 128, edgeValue (fun i => (rows7.getD i.val 0)[k.val]) = target7[k.val] := by decide +kernel
def m7_0Arr : Array ℕ := #[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126]
def m7_1Arr : Array ℕ := #[0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 96, 97, 100, 101, 104, 105, 108, 109, 112, 113, 116, 117, 120, 121, 124, 125]
def m7_2Arr : Array ℕ := #[0, 2, 1, 3, 8, 10, 9, 11, 16, 18, 17, 19, 24, 26, 25, 27, 32, 34, 33, 35, 40, 42, 41, 43, 48, 50, 49, 51, 56, 58, 57, 59, 64, 66, 65, 67, 72, 74, 73, 75, 80, 82, 81, 83, 88, 90, 89, 91, 96, 98, 97, 99, 104, 106, 105, 107, 112, 114, 113, 115, 120, 122, 121, 123]
def m7_3Arr : Array ℕ := #[0, 1, 4, 5, 2, 3, 6, 7, 16, 17, 20, 21, 18, 19, 22, 23, 32, 33, 36, 37, 34, 35, 38, 39, 48, 49, 52, 53, 50, 51, 54, 55, 64, 65, 68, 69, 66, 67, 70, 71, 80, 81, 84, 85, 82, 83, 86, 87, 96, 97, 100, 101, 98, 99, 102, 103, 112, 113, 116, 117, 114, 115, 118, 119]
def m7_4Arr : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
def m7_5Arr : Array ℕ := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
def m7_0 (k : Fin 64) : Fin 128 := ⟨m7_0Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def m7_1 (k : Fin 64) : Fin 128 := ⟨m7_1Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def m7_2 (k : Fin 64) : Fin 128 := ⟨m7_2Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def m7_3 (k : Fin 64) : Fin 128 := ⟨m7_3Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def m7_4 (k : Fin 64) : Fin 128 := ⟨m7_4Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def m7_5 (k : Fin 64) : Fin 128 := ⟨m7_5Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def sep7A : Array ℕ := #[0, 0, 0, 0, 4, 6, 6, 4, 16, 4, 4, 16, 4, 12, 12, 4, 4, 16, 16, 4, 4, 32, 32, 4, 4, 64, 64, 4, 8, 9, 9, 8, 0, 0, 0, 0, 8, 12, 12, 8, 32, 8, 8, 32, 8, 24, 24, 8, 8, 32, 32, 8, 8, 64, 64, 8, 16, 1, 1, 16, 1, 3, 3, 1, 0, 0, 0, 0, 1, 9, 9, 1, 1, 16, 16, 1, 1, 32, 32, 1, 1, 64, 64, 1, 2, 3, 3, 2, 32, 2, 2, 32, 2, 6, 6, 2, 0, 0, 0, 0, 2, 18, 18, 2, 2, 32, 32, 2, 2, 64, 64, 2, 4, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4, 1, 1, 9, 9, 1, 0, 0, 0, 0, 1, 18, 1, 1, 1, 64, 64, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 8, 8, 1, 1, 18, 18, 1, 0, 0, 0, 0, 1, 64, 64, 1, 4, 64, 4, 64, 8, 64, 8, 64, 1, 64, 1, 64, 2, 64, 2, 64, 1, 64, 1, 64, 1, 64, 1, 64, 0, 0, 0, 0]
def sep7B : Array ℕ := #[0, 0, 0, 0, 5, 7, 7, 5, 17, 5, 5, 17, 5, 13, 13, 5, 5, 17, 17, 5, 5, 33, 33, 5, 5, 65, 65, 5, 10, 11, 11, 10, 0, 0, 0, 0, 10, 14, 14, 10, 34, 10, 10, 34, 10, 26, 26, 10, 10, 34, 34, 10, 10, 66, 66, 10, 20, 5, 5, 20, 5, 7, 7, 5, 0, 0, 0, 0, 5, 13, 13, 5, 5, 20, 20, 5, 5, 36, 36, 5, 5, 68, 68, 5, 10, 11, 11, 10, 40, 10, 10, 40, 10, 14, 14, 10, 0, 0, 0, 0, 10, 26, 26, 10, 10, 40, 40, 10, 10, 72, 72, 10, 20, 17, 17, 20, 17, 19, 19, 17, 17, 20, 20, 17, 17, 25, 25, 17, 0, 0, 0, 0, 17, 50, 33, 17, 17, 80, 80, 17, 34, 33, 33, 34, 33, 34, 34, 33, 33, 36, 36, 33, 33, 40, 40, 33, 33, 50, 50, 33, 0, 0, 0, 0, 33, 96, 96, 33, 5, 65, 5, 65, 10, 66, 10, 66, 5, 68, 5, 68, 10, 72, 10, 72, 17, 80, 17, 80, 33, 96, 33, 96, 0, 0, 0, 0]

def pickP7 (i j : Fin 7) (op : Fin 4) : Fin 7 :=
  if i.val == 6 || (i.val == 4 && j.val == 5 && (op.val == 1 || op.val == 2)) then j else i

def checkSep7 : Bool :=
  (List.finRange 7).all fun i =>
    (List.finRange 7).all fun j =>
      if i == j then true else
        (List.finRange 4).all fun op =>
          let p := pickP7 i j op
          let a := sep7A[28 * i.val + 4 * j.val + op.val]! % 128
          let b := sep7B[28 * i.val + 4 * j.val + op.val]! % 128
          let z := (ops (r7v i) (r7v j)).getD op.val 0
          (target7[a]! != target7[b]!) &&
          (z[a]! == z[b]!) &&
          (List.finRange 7).all fun q =>
            (q == p) || ((r7v q)[a]! == (r7v q)[b]!)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem sep7_ok : checkSep7 = true := by decide +kernel

theorem rows7_cover {w : W128} (hw : w ∈ rows7.toFinset) : ∃ i : Fin 7, r7v i = w := by
  rw [List.mem_toFinset] at hw
  simp only [rows7, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩

theorem rows7_not_t7 : ∀ i : Fin 7, r7v i ≠ target7 ∧ r7v i ≠ ~~~target7 := by decide

theorem step7_drop (p : Fin 7) (hp6 : p.val ≠ 6) {t z : W128}
    (ht : t = target7 ∨ t = ~~~target7)
    (i j : Fin 7) (hptouch : p = i ∨ p = j) (hz : z ∈ basicOps (r7v i) (r7v j))
    (rest : Finset W128) (hsub : rest ⊆ rows7.toFinset)
    (hkeep : r7v p ∈ rest) (tail : live basicOps t 10 (insert z rest)) : False := by
  have go (mp : Fin 64 → Fin 128) (tgt6 : W64)
      (hft0 : selectRows mp target7 = tgt6)
      (hfp0 : selectRows mp (r7v p) = 0)
      (hnc : tgt6 ≠ 0 ∧ tgt6 ≠ ~~~0)
      (hhold : ∀ w ∈ rows7, holds w64_vars.toFinset (selectRows mp w))
      (hbot : ∀ t6, (t6 = tgt6 ∨ t6 = ~~~tgt6) → build basicOps t6 9 w64_vars.toFinset → False) : False := by
    let f := selectRows mp
    have hm := ops_map_of (selectRows_land mp) (selectRows_lor mp) (selectRows_neg mp)
    have hft : f t = tgt6 ∨ f t = ~~~tgt6 := by
      rcases ht with rfl | rfl
      · exact .inl hft0
      · exact .inr ((selectRows_neg mp target7).trans (congrArg (fun u : W64 => ~~~u) hft0))
    have hng : f t ≠ 0 ∧ f t ≠ ~~~0 := by
      rcases hft with h | h <;> rw [h]
      · exact hnc
      · exact not_const_of_neg hnc
    have hfz : holds w64_vars.toFinset (f z) := by
      have hi : r7v i ∈ rows7 := by fin_cases i <;> decide
      have hj : r7v j ∈ rows7 := by fin_cases j <;> decide
      have hc : (f (r7v i) = 0 ∨ f (r7v i) = ~~~0) ∨ (f (r7v j) = 0 ∨ f (r7v j) = ~~~0) := by
        rcases hptouch with rfl | rfl
        · exact .inl (.inl hfp0)
        · exact .inr (.inl hfp0)
      exact mem_ops_const (hhold _ hi) (hhold _ hj) hc (hm _ _ _ hz)
    obtain ⟨_, hsb⟩ := live_transport_save_const hm tail (Finset.mem_insert_of_mem hkeep) (.inl hfp0) hng (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact hfz
      · exact hhold w (List.mem_toFinset.mp (hsub hr)))
    obtain ⟨t6, ht6, hb6⟩ := unwrap_sb hng.1 hng.2 hsb
    have ht6' : t6 = tgt6 ∨ t6 = ~~~tgt6 := by
      rcases hft with h | h <;> rcases ht6 with rfl | rfl <;> rw [h]
      · exact .inl rfl
      · exact .inr rfl
      · exact .inr rfl
      · exact .inl BitVec.not_not
    exact hbot t6 ht6' hb6
  fin_cases p
  · exact go m7_0 g0_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_0) rows7 w64_vars (by decide +kernel)) g0_no9_64
  · exact go m7_1 g1_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_1) rows7 w64_vars (by decide +kernel)) g1_no9_64
  · exact go m7_2 g0_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_2) rows7 w64_vars (by decide +kernel)) g0_no9_64
  · exact go m7_3 g1_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_3) rows7 w64_vars (by decide +kernel)) g1_no9_64
  · exact go m7_4 g4_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_4) rows7 w64_vars (by decide +kernel)) g4_no9_64
  · exact go m7_5 g5_tt64 (by decide +kernel) (by decide +kernel) (by decide) (map_holds_list (selectRows m7_5) rows7 w64_vars (by decide +kernel)) g5_no9_64
  · exact (hp6 rfl).elim

theorem no_eleven_binary (t : W128) (ht : t = target7 ∨ t = ~~~target7)
    (hb : build basicOps t 11 rows7.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 10) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := rows7_cover mt
    rcases ht with rfl | rfl
    · exact (rows7_not_t7 i).1 hi
    · exact (rows7_not_t7 i).2 hi
  · obtain ⟨i, rfl⟩ := rows7_cover (hs ha)
    obtain ⟨j, rfl⟩ := rows7_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg r7v e)
    have hsub : rest ⊆ rows7.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    obtain ⟨op, hop⟩ := index_of_op _ _ _ hz
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp sep7_ok i (List.mem_finRange i)) j (List.mem_finRange j)
    have hne : (i == j) = false := beq_false_of_ne hij
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h1
    have h2 := List.all_eq_true.mp h1 op (List.mem_finRange op)
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h2
    obtain ⟨⟨hdt, hzeq⟩, hallq⟩ := h2
    rw [hop] at hzeq
    let p := pickP7 i j op
    let aa : Fin 128 := ⟨sep7A[28 * i.val + 4 * j.val + op.val]! % 128, Nat.mod_lt _ (by decide)⟩
    let bb : Fin 128 := ⟨sep7B[28 * i.val + 4 * j.val + op.val]! % 128, Nat.mod_lt _ (by decide)⟩
    have hdt' : bitDiff aa bb target7 := by
      unfold bitDiff
      simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hdt
    have hzeq' : z[aa.val] = z[bb.val] := by
      simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hzeq
    have hd : bitDiff aa bb t := by
      rcases ht with rfl | rfl
      · exact hdt'
      · exact bitDiff_not hdt'
    have hkeep : r7v p ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff aa bb) hd (ops_bitDiff aa bb) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hdw hzeq').elim
      · obtain ⟨q, rfl⟩ := rows7_cover (hsub hw)
        have hq := List.all_eq_true.mp hallq q (List.mem_finRange q)
        simp only [Bool.or_eq_true, beq_iff_eq] at hq
        rcases hq with hqp | hqeq
        · exact (show q = p from hqp) ▸ hw
        · have hqeq' : (r7v q)[aa.val] = (r7v q)[bb.val] := by
            simpa [aa, bb, getElem!_pos, aa.isLt, bb.isLt] using hqeq
          exact (hdw hqeq').elim
    have hp6 : p.val ≠ 6 := by
      dsimp only [p, pickP7]
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
        rcases hc with hi6 | ⟨⟨_, hj5⟩, _⟩
        · intro hj6; exact hij (Fin.ext (hi6.trans hj6.symm))
        · omega
      · rename_i hc
        intro hi6
        apply hc
        simp [hi6]
    have hptouch : p = i ∨ p = j := by
      dsimp only [p, pickP7]
      split
      · exact .inr rfl
      · exact .inl rfl
    exact step7_drop p hp6 ht i j hptouch hz rest hsub hkeep tail

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeValue x) :
    11 < binaryCost gs := by
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
  obtain ⟨t, ht, run⟩ := compile target7 t7_nc.1 t7_nc.2 gs o hg rows7 rows7.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rows7.toFinset) :
      build basicOps t b rows7.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_eleven_binary t ht (lift low run)

def witnessGates : List Gate :=
  [⟨.or, [0, 2]⟩,
   ⟨.or, [1, 3]⟩,
   ⟨.or, [7, 8]⟩,
   ⟨.or, [5, 6]⟩,
   ⟨.and, [9, 10]⟩,
   ⟨.or, [4, 5]⟩,
   ⟨.or, [7, 6]⟩,
   ⟨.and, [12, 13]⟩,
   ⟨.and, [0, 2]⟩,
   ⟨.and, [1, 3]⟩,
   ⟨.or, [11, 14]⟩,
   ⟨.or, [15, 16]⟩,
   ⟨.or, [17, 18]⟩]

theorem witness_basis : ∀ g ∈ witnessGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witnessGates, 19⟩ (List.ofFn x) = edgeValue x := by
  decide +kernel

end Lower10564


end PEqualNP.Outside.L_meta_10564

theorem PEqualNP.Outside.L_meta_10564 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hasNot
    have hlt : PEqualNP.Outside.L_meta_10564.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_10564.isBinary)).mpr
        ⟨g, hmem, by simp [PEqualNP.Outside.L_meta_10564.isBinary, hop]⟩
    have hbd := PEqualNP.Outside.L_meta_10564.cost_bound gates o legal computes
    have hlen : PEqualNP.Outside.L_meta_10564.witnessGates.length = 13 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10564.witnessGates, 19,
      PEqualNP.Outside.L_meta_10564.witness_basis, by omega,
      PEqualNP.Outside.L_meta_10564.witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hcap⟩ := legal g hg
    refine ⟨?_, hcap⟩
    rcases hop with h | h | h
    · exact .inl h
    · exact .inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
