import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10754

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

section Lower10754

def edges10754 : List ℕ := [0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6]

def edgeValue (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edges10754.length / 2,
    (List.ofFn x).getD (edges10754.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges10754.getD (2 * i + 1) 0) false = true)

def v0 : W128 := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#128
def v1 : W128 := 0xcccccccccccccccccccccccccccccccc#128
def v2 : W128 := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#128
def v3 : W128 := 0xff00ff00ff00ff00ff00ff00ff00ff00#128
def v4 : W128 := 0xffff0000ffff0000ffff0000ffff0000#128
def v5 : W128 := 0xffffffff00000000ffffffff00000000#128
def v6 : W128 := 0xffffffffffffffff0000000000000000#128

def rows7 : List W128 := [v0, v1, v2, v3, v4, v5, v6]
def rows6 : List W128 := [v0, v1, v3, v4, v5, v6]
def r6v (i : Fin 6) : W128 := rows6.getD i.val 0

def rows5_0 : List W128 := [v1, v3, v4, v5, v6]
def rows5_1 : List W128 := [v0, v3, v4, v5, v6]
def rows5_3 : List W128 := [v0, v1, v4, v5, v6]
def rows5_4 : List W128 := [v0, v1, v3, v5, v6]
def rows5_5 : List W128 := [v0, v1, v3, v4, v6]
def rows4 : List W128 := [v0, v3, v5, v6]

def target7 : W128 := 0xfffffffffffffffefffefffaeeccaa00#128
def target6 : W128 := 0xffffffffffffffeeffeeffaaeeccaa00#128
def t5_0 : W128 := 0xffffffffffffffccffccff00cccc0000#128
def t5_1 : W128 := 0xffffffffffffffaaffaaffaaaa00aa00#128
def t5_3 : W128 := 0xffffffffffffeeeeeeeeaaaacccc0000#128
def t5_4 : W128 := 0xffffffffffeeffeeffaaffaaaa00aa00#128
def t5_5 : W128 := 0xffffffeeffffffeeeeccaa00eeccaa00#128
def target4 : W128 := 0xffffffffffaaffaaffaaffaaaa00aa00#128

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sample7 : ∀ k : Fin 128,
    edgeValue (fun i => (rows7.getD i.val 0)[k.val]) = target7[k.val] := by
  decide +kernel

def fixBit (i : Fin 7) (val : Bool) (k : Fin 128) : Fin 128 :=
  let bit := 1 <<< i.val
  let m := if val then k.val ||| bit else k.val &&& (127 - bit)
  ⟨m % 128, Nat.mod_lt _ (by decide)⟩

def restrict (i : Fin 7) (val : Bool) : W128 → W128 := selectRows (fixBit i val)

def f0 : W128 → W128 := restrict 0 false
def f1 : W128 → W128 := restrict 1 false
def f2 : W128 → W128 := restrict 2 false
def f3 : W128 → W128 := restrict 3 false
def f4 : W128 → W128 := restrict 4 false
def f5 : W128 → W128 := restrict 5 false

theorem t7_nc : target7 ≠ 0 ∧ target7 ≠ ~~~0 := by decide
theorem t6_nc : target6 ≠ 0 ∧ target6 ≠ ~~~0 := by decide
theorem t50_nc : t5_0 ≠ 0 ∧ t5_0 ≠ ~~~0 := by decide
theorem t51_nc : t5_1 ≠ 0 ∧ t5_1 ≠ ~~~0 := by decide
theorem t53_nc : t5_3 ≠ 0 ∧ t5_3 ≠ ~~~0 := by decide
theorem t54_nc : t5_4 ≠ 0 ∧ t5_4 ≠ ~~~0 := by decide
theorem t55_nc : t5_5 ≠ 0 ∧ t5_5 ≠ ~~~0 := by decide
theorem t4_nc : target4 ≠ 0 ∧ target4 ≠ ~~~0 := by decide

theorem f2_t7 : f2 target7 = target6 := by decide +kernel
theorem f0_t6 : f0 target6 = t5_0 := by decide +kernel
theorem f1_t6 : f1 target6 = t5_1 := by decide +kernel
theorem f3_t6 : f3 target6 = t5_3 := by decide +kernel
theorem f4_t6 : f4 target6 = t5_4 := by decide +kernel
theorem f5_t6 : f5 target6 = t5_5 := by decide +kernel
theorem f4_t51 : f4 t5_1 = target4 := by decide +kernel
theorem f1_t54 : f1 t5_4 = target4 := by decide +kernel

theorem f2_v2 : f2 v2 = 0 := by decide +kernel
theorem f0_v0 : f0 v0 = 0 := by decide +kernel
theorem f1_v1 : f1 v1 = 0 := by decide +kernel
theorem f3_v3 : f3 v3 = 0 := by decide +kernel
theorem f4_v4 : f4 v4 = 0 := by decide +kernel
theorem f5_v5 : f5 v5 = 0 := by decide +kernel

theorem sep7 : bitDiff ⟨32, by decide⟩ ⟨36, by decide⟩ target7 ∧
    ∀ w ∈ rows7, bitDiff ⟨32, by decide⟩ ⟨36, by decide⟩ w → w = v2 :=
  ⟨by unfold bitDiff; decide +kernel,
   sep_of_all ⟨32, by decide⟩ ⟨36, by decide⟩ rows7 v2 (by decide +kernel)⟩

theorem sep51 : bitDiff ⟨64, by decide⟩ ⟨80, by decide⟩ t5_1 ∧
    ∀ w ∈ rows5_1, bitDiff ⟨64, by decide⟩ ⟨80, by decide⟩ w → w = v4 :=
  ⟨by unfold bitDiff; decide +kernel,
   sep_of_all ⟨64, by decide⟩ ⟨80, by decide⟩ rows5_1 v4 (by decide +kernel)⟩

theorem sep54 : bitDiff ⟨64, by decide⟩ ⟨66, by decide⟩ t5_4 ∧
    ∀ w ∈ rows5_4, bitDiff ⟨64, by decide⟩ ⟨66, by decide⟩ w → w = v1 :=
  ⟨by unfold bitDiff; decide +kernel,
   sep_of_all ⟨64, by decide⟩ ⟨66, by decide⟩ rows5_4 v1 (by decide +kernel)⟩

theorem hold_rows6 : ∀ w ∈ rows7, holds rows6.toFinset (f2 w) :=
  map_holds_list f2 rows7 rows6 (by decide +kernel)
theorem hold_rows5_0 : ∀ w ∈ rows6, holds rows5_0.toFinset (f0 w) :=
  map_holds_list f0 rows6 rows5_0 (by decide +kernel)
theorem hold_rows5_1 : ∀ w ∈ rows6, holds rows5_1.toFinset (f1 w) :=
  map_holds_list f1 rows6 rows5_1 (by decide +kernel)
theorem hold_rows5_3 : ∀ w ∈ rows6, holds rows5_3.toFinset (f3 w) :=
  map_holds_list f3 rows6 rows5_3 (by decide +kernel)
theorem hold_rows5_4 : ∀ w ∈ rows6, holds rows5_4.toFinset (f4 w) :=
  map_holds_list f4 rows6 rows5_4 (by decide +kernel)
theorem hold_rows5_5 : ∀ w ∈ rows6, holds rows5_5.toFinset (f5 w) :=
  map_holds_list f5 rows6 rows5_5 (by decide +kernel)
theorem hold_rows4_1 : ∀ w ∈ rows5_1, holds rows4.toFinset (f4 w) :=
  map_holds_list f4 rows5_1 rows4 (by decide +kernel)
theorem hold_rows4_4 : ∀ w ∈ rows5_4, holds rows4.toFinset (f1 w) :=
  map_holds_list f1 rows5_4 rows4 (by decide +kernel)

def k4Map128Arr : Array ℕ := #[0, 1, 8, 9, 32, 33, 40, 41, 64, 65, 72, 73, 96, 97, 104, 105]
def k4Map128 (k : Fin 16) : Fin 128 := ⟨k4Map128Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def projK4_16 : W128 → BitVec 16 := selectRows k4Map128

def bowMap0Arr : Array ℕ :=
  #[0, 8, 32, 40, 2, 10, 34, 42, 16, 24, 48, 56, 18, 26, 50, 58,
    64, 72, 96, 104, 66, 74, 98, 106, 80, 88, 112, 120, 82, 90, 114, 122]
def bowMap3Arr : Array ℕ :=
  #[0, 1, 32, 33, 2, 3, 34, 35, 16, 17, 48, 49, 18, 19, 50, 51,
    64, 65, 96, 97, 66, 67, 98, 99, 80, 81, 112, 113, 82, 83, 114, 115]
def bowMap5Arr : Array ℕ :=
  #[0, 1, 8, 9, 2, 3, 10, 11, 16, 17, 24, 25, 18, 19, 26, 27,
    64, 65, 72, 73, 66, 67, 74, 75, 80, 81, 88, 89, 82, 83, 90, 91]

def bowMap0 (k : Fin 32) : Fin 128 := ⟨bowMap0Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def bowMap3 (k : Fin 32) : Fin 128 := ⟨bowMap3Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩
def bowMap5 (k : Fin 32) : Fin 128 := ⟨bowMap5Arr[k.val]! % 128, Nat.mod_lt _ (by decide)⟩

def projBow0 : W128 → BitVec 32 := selectRows bowMap0
def projBow3 : W128 → BitVec 32 := selectRows bowMap3
def projBow5 : W128 → BitVec 32 := selectRows bowMap5

theorem proj_k4_t : projK4_16 target4 = k4_tt16 := by decide +kernel
theorem proj_bow0_t : projBow0 t5_0 = bow_tt32 := by decide +kernel
theorem proj_bow3_t : projBow3 t5_3 = bow_tt32 := by decide +kernel
theorem proj_bow5_t : projBow5 t5_5 = bow_tt32 := by decide +kernel

theorem hold_k4_16 : ∀ w ∈ rows4, holds k4_16_vars.toFinset (projK4_16 w) :=
  map_holds_list projK4_16 rows4 k4_16_vars (by decide +kernel)
theorem hold_bow0 : ∀ w ∈ rows5_0, holds bow_32_vars.toFinset (projBow0 w) :=
  map_holds_list projBow0 rows5_0 bow_32_vars (by decide +kernel)
theorem hold_bow3 : ∀ w ∈ rows5_3, holds bow_32_vars.toFinset (projBow3 w) :=
  map_holds_list projBow3 rows5_3 bow_32_vars (by decide +kernel)
theorem hold_bow5 : ∀ w ∈ rows5_5, holds bow_32_vars.toFinset (projBow5 w) :=
  map_holds_list projBow5 rows5_5 bow_32_vars (by decide +kernel)

theorem k4_128_false (t : W128) (ht : t = target4 ∨ t = ~~~target4)
    (hb : build basicOps t 6 rows4.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hm := ops_map_of (selectRows_land k4Map128) (selectRows_lor k4Map128) (selectRows_neg k4Map128)
  have hsb := live_transport hm hl (fun w hw => hold_k4_16 w (List.mem_toFinset.mp (hs hw)))
  have hft : projK4_16 t = k4_tt16 ∨ projK4_16 t = ~~~k4_tt16 := by
    rcases ht with rfl | rfl
    · exact .inl proj_k4_t
    · exact .inr ((selectRows_neg k4Map128 target4).trans (congrArg (fun u : BitVec 16 => ~~~u) proj_k4_t))
  have hnc : k4_tt16 ≠ 0 ∧ k4_tt16 ≠ ~~~0 := by decide
  have hng : projK4_16 t ≠ 0 ∧ projK4_16 t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact hnc
    · exact not_const_of_neg hnc
  obtain ⟨t16, ht16, hb16⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht16' : t16 = k4_tt16 ∨ t16 = ~~~k4_tt16 := by
    rcases hft with h | h <;> rcases ht16 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact k4_no6_16 t16 ht16' hb16

theorem bow_128_false (mp : Fin 32 → Fin 128) (rs : List W128) (tgt : W128)
    (hproj : selectRows mp tgt = bow_tt32)
    (hhold : ∀ w ∈ rs, holds bow_32_vars.toFinset (selectRows mp w))
    (t : W128) (ht : t = tgt ∨ t = ~~~tgt)
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

theorem k4p1_false (t : W128) (ht : t = t5_1 ∨ t = ~~~t5_1)
    (hb : build basicOps t 7 rows5_1.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff ⟨64, by decide⟩ ⟨80, by decide⟩ t := by
    rcases ht with rfl | rfl
    · exact sep51.1
    · exact bitDiff_not sep51.1
  have hp : v4 ∈ s := live_has_unique_sep hs hl ⟨64, by decide⟩ ⟨80, by decide⟩ hd sep51.2
  have hm := ops_map_of (selectRows_land (fixBit 4 false)) (selectRows_lor (fixBit 4 false)) (selectRows_neg (fixBit 4 false))
  have hft : f4 t = target4 ∨ f4 t = ~~~target4 := by
    rcases ht with rfl | rfl
    · exact .inl f4_t51
    · exact .inr ((selectRows_neg (fixBit 4 false) t5_1).trans (congrArg (fun u : W128 => ~~~u) f4_t51))
  have hng : f4 t ≠ 0 ∧ f4 t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact t4_nc
    · exact not_const_of_neg t4_nc
  obtain ⟨_, hsb⟩ := live_transport_save_const hm hl hp (.inl f4_v4) hng
    (fun w hw => hold_rows4_1 w (List.mem_toFinset.mp (hs hw)))
  obtain ⟨t4, ht4, hb4⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht4' : t4 = target4 ∨ t4 = ~~~target4 := by
    rcases hft with h | h <;> rcases ht4 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact k4_128_false t4 ht4' hb4

theorem k4p4_false (t : W128) (ht : t = t5_4 ∨ t = ~~~t5_4)
    (hb : build basicOps t 7 rows5_4.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  have hd : bitDiff ⟨64, by decide⟩ ⟨66, by decide⟩ t := by
    rcases ht with rfl | rfl
    · exact sep54.1
    · exact bitDiff_not sep54.1
  have hp : v1 ∈ s := live_has_unique_sep hs hl ⟨64, by decide⟩ ⟨66, by decide⟩ hd sep54.2
  have hm := ops_map_of (selectRows_land (fixBit 1 false)) (selectRows_lor (fixBit 1 false)) (selectRows_neg (fixBit 1 false))
  have hft : f1 t = target4 ∨ f1 t = ~~~target4 := by
    rcases ht with rfl | rfl
    · exact .inl f1_t54
    · exact .inr ((selectRows_neg (fixBit 1 false) t5_4).trans (congrArg (fun u : W128 => ~~~u) f1_t54))
  have hng : f1 t ≠ 0 ∧ f1 t ≠ ~~~0 := by
    rcases hft with h | h <;> rw [h]
    · exact t4_nc
    · exact not_const_of_neg t4_nc
  obtain ⟨_, hsb⟩ := live_transport_save_const hm hl hp (.inl f1_v1) hng
    (fun w hw => hold_rows4_4 w (List.mem_toFinset.mp (hs hw)))
  obtain ⟨t4, ht4, hb4⟩ := unwrap_sb hng.1 hng.2 hsb
  have ht4' : t4 = target4 ∨ t4 = ~~~target4 := by
    rcases hft with h | h <;> rcases ht4 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact k4_128_false t4 ht4' hb4

def sep6A : Array ℕ :=
  #[0, 0, 0, 0, 8, 10, 10, 8, 32, 8, 8, 32, 8, 24, 24, 8, 8, 32, 32, 8, 8, 64, 64, 8,
    16, 17, 17, 16, 0, 0, 0, 0, 16, 24, 24, 16, 64, 16, 16, 64, 16, 48, 48, 16, 16, 64, 64, 16,
    32, 1, 1, 32, 1, 3, 3, 1, 0, 0, 0, 0, 1, 17, 17, 1, 1, 32, 32, 1, 1, 64, 64, 1,
    2, 3, 3, 2, 64, 2, 2, 64, 2, 10, 10, 2, 0, 0, 0, 0, 2, 34, 34, 2, 2, 64, 64, 2,
    8, 1, 1, 8, 1, 3, 3, 1, 1, 8, 8, 1, 1, 17, 17, 1, 0, 0, 0, 0, 1, 64, 64, 1,
    8, 64, 8, 64, 16, 64, 16, 64, 1, 64, 1, 64, 2, 64, 2, 64, 1, 64, 1, 64, 0, 0, 0, 0]

def sep6B : Array ℕ :=
  #[0, 0, 0, 0, 9, 11, 11, 9, 33, 9, 9, 33, 9, 25, 25, 9, 9, 33, 33, 9, 9, 65, 65, 9,
    18, 19, 19, 18, 0, 0, 0, 0, 18, 26, 26, 18, 66, 18, 18, 66, 18, 50, 50, 18, 18, 66, 66, 18,
    40, 9, 9, 40, 9, 11, 11, 9, 0, 0, 0, 0, 9, 25, 25, 9, 9, 40, 40, 9, 9, 72, 72, 9,
    18, 19, 19, 18, 80, 18, 18, 80, 18, 26, 26, 18, 0, 0, 0, 0, 18, 50, 50, 18, 18, 80, 80, 18,
    40, 33, 33, 40, 33, 35, 35, 33, 33, 40, 40, 33, 33, 49, 49, 33, 0, 0, 0, 0, 33, 96, 96, 33,
    9, 65, 9, 65, 18, 66, 18, 66, 9, 72, 9, 72, 18, 80, 18, 80, 33, 96, 33, 96, 0, 0, 0, 0]

def sep6IdxA (i j : Fin 6) (op : Fin 4) : Fin 128 :=
  ⟨sep6A[24 * i.val + 4 * j.val + op.val]! % 128, Nat.mod_lt _ (by decide)⟩

def sep6IdxB (i j : Fin 6) (op : Fin 4) : Fin 128 :=
  ⟨sep6B[24 * i.val + 4 * j.val + op.val]! % 128, Nat.mod_lt _ (by decide)⟩

def pickP (i j : Fin 6) : Fin 6 := if i.val == 5 then j else i

def checkSep6 : Bool :=
  (List.finRange 6).all fun i =>
    (List.finRange 6).all fun j =>
      if i == j then true else
        (List.finRange 4).all fun op =>
          let p := pickP i j
          let a := sep6IdxA i j op
          let b := sep6IdxB i j op
          let z := (ops (r6v i) (r6v j)).getD op.val 0
          (target6[a.val] != target6[b.val]) &&
          (z[a.val] == z[b.val]) &&
          (List.finRange 6).all fun q =>
            (q == p) || ((r6v q)[a.val] == (r6v q)[b.val])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sep6_ok : checkSep6 = true := by decide +kernel

theorem rows6_cover {w : W128} (hw : w ∈ rows6.toFinset) : ∃ i : Fin 6, r6v i = w := by
  rw [List.mem_toFinset] at hw
  simp only [rows6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩

theorem rows6_not_t6 : ∀ i : Fin 6, r6v i ≠ target6 ∧ r6v i ≠ ~~~target6 := by decide

theorem raw_present6 {t : W128} (ht : t = target6 ∨ t = ~~~target6)
    (i j : Fin 6) (hij : i ≠ j) {z : W128} (hz : z ∈ basicOps (r6v i) (r6v j))
    (rest : Finset W128) (hsub : rest ⊆ rows6.toFinset)
    (tail : live basicOps t 8 (insert z rest)) : r6v (pickP i j) ∈ rest := by
  obtain ⟨op, hop⟩ := index_of_op _ _ _ hz
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp sep6_ok i (List.mem_finRange i)) j (List.mem_finRange j)
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h1
  have h2 := List.all_eq_true.mp h1 op (List.mem_finRange op)
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h2
  obtain ⟨⟨hdt, hzeq⟩, hallq⟩ := h2
  rw [hop] at hzeq
  let a := sep6IdxA i j op
  let b := sep6IdxB i j op
  have hd : bitDiff a b t := by
    rcases ht with rfl | rfl
    · exact hdt
    · exact bitDiff_not hdt
  obtain ⟨w, hw, hdw⟩ := live_separates (bitDiff a b) hd (ops_bitDiff a b) tail
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact (hdw hzeq).elim
  · obtain ⟨q, rfl⟩ := rows6_cover (hsub hw)
    have hq := List.all_eq_true.mp hallq q (List.mem_finRange q)
    simp only [Bool.or_eq_true, beq_iff_eq] at hq
    rcases hq with hqp | hqeq
    · exact hqp ▸ hw
    · exact (hdw hqeq).elim

theorem step_drop_p (p : Fin 6) (hp5 : p.val ≠ 5) {t z : W128}
    (ht : t = target6 ∨ t = ~~~target6)
    (i j : Fin 6) (hptouch : p = i ∨ p = j) (hz : z ∈ basicOps (r6v i) (r6v j))
    (rest : Finset W128) (hsub : rest ⊆ rows6.toFinset)
    (hkeep : r6v p ∈ rest) (tail : live basicOps t 8 (insert z rest)) : False := by
  have go (bit : Fin 7) (rs : List W128) (tgt : W128)
      (hft0 : restrict bit false target6 = tgt)
      (hfp0 : restrict bit false (r6v p) = 0)
      (hnc : tgt ≠ 0 ∧ tgt ≠ ~~~0)
      (hhold : ∀ w ∈ rows6, holds rs.toFinset (restrict bit false w))
      (hbot : ∀ t5, (t5 = tgt ∨ t5 = ~~~tgt) → build basicOps t5 7 rs.toFinset → False) : False := by
    let f := restrict bit false
    have hm := ops_map_of (selectRows_land (fixBit bit false)) (selectRows_lor (fixBit bit false)) (selectRows_neg (fixBit bit false))
    have hft : f t = tgt ∨ f t = ~~~tgt := by
      rcases ht with rfl | rfl
      · exact .inl hft0
      · exact .inr ((selectRows_neg (fixBit bit false) target6).trans (congrArg (fun u : W128 => ~~~u) hft0))
    have hng : f t ≠ 0 ∧ f t ≠ ~~~0 := by
      rcases hft with h | h <;> rw [h]
      · exact hnc
      · exact not_const_of_neg hnc
    have hfz : holds rs.toFinset (f z) := by
      have hi : holds rs.toFinset (f (r6v i)) := hhold _ (List.mem_toFinset.mp (by
        have : r6v i ∈ rows6 := by fin_cases i <;> decide
        exact List.mem_toFinset.mpr this))
      have hj : holds rs.toFinset (f (r6v j)) := hhold _ (List.mem_toFinset.mp (by
        have : r6v j ∈ rows6 := by fin_cases j <;> decide
        exact List.mem_toFinset.mpr this))
      have hc : (f (r6v i) = 0 ∨ f (r6v i) = ~~~0) ∨ (f (r6v j) = 0 ∨ f (r6v j) = ~~~0) := by
        rcases hptouch with rfl | rfl
        · exact .inl (.inl hfp0)
        · exact .inr (.inl hfp0)
      exact mem_ops_const hi hj hc (hm _ _ _ hz)
    obtain ⟨_, hsb⟩ := live_transport_save_const hm tail (Finset.mem_insert_of_mem hkeep) (.inl hfp0) hng (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hr
      · exact hfz
      · exact hhold w (List.mem_toFinset.mp (hsub hr)))
    obtain ⟨t5, ht5, hb5⟩ := unwrap_sb hng.1 hng.2 hsb
    have ht5' : t5 = tgt ∨ t5 = ~~~tgt := by
      rcases hft with h | h <;> rcases ht5 with rfl | rfl <;> rw [h]
      · exact .inl rfl
      · exact .inr rfl
      · exact .inr rfl
      · exact .inl BitVec.not_not
    exact hbot t5 ht5' hb5
  fin_cases p
  · exact go 0 rows5_0 t5_0 f0_t6 f0_v0 t50_nc hold_rows5_0 (bow_128_false bowMap0 rows5_0 t5_0 proj_bow0_t hold_bow0)
  · exact go 1 rows5_1 t5_1 f1_t6 f1_v1 t51_nc hold_rows5_1 k4p1_false
  · exact go 3 rows5_3 t5_3 f3_t6 f3_v3 t53_nc hold_rows5_3 (bow_128_false bowMap3 rows5_3 t5_3 proj_bow3_t hold_bow3)
  · exact go 4 rows5_4 t5_4 f4_t6 f4_v4 t54_nc hold_rows5_4 k4p4_false
  · exact go 5 rows5_5 t5_5 f5_t6 f5_v5 t55_nc hold_rows5_5 (bow_128_false bowMap5 rows5_5 t5_5 proj_bow5_t hold_bow5)
  · exact (hp5 rfl).elim

theorem no_nine_t6 (t : W128) (ht : t = target6 ∨ t = ~~~target6)
    (hb : build basicOps t 9 rows6.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress hb
  rcases first_live (k := 8) hl with done | ⟨a, ha, b, hb', hab, z, hz, _, rest, he, tail⟩
  · have mt := hs (show t ∈ s by simp [done])
    obtain ⟨i, hi⟩ := rows6_cover mt
    rcases ht with rfl | rfl
    · exact (rows6_not_t6 i).1 hi
    · exact (rows6_not_t6 i).2 hi
  · obtain ⟨i, rfl⟩ := rows6_cover (hs ha)
    obtain ⟨j, rfl⟩ := rows6_cover (hs hb')
    have hij : i ≠ j := fun e => hab (congrArg r6v e)
    have hsub : rest ⊆ rows6.toFinset := fun u hu =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have hkeep := raw_present6 ht i j hij hz rest hsub tail
    have hp5 : (pickP i j).val ≠ 5 := by
      unfold pickP
      by_cases hi5 : i.val = 5
      · simp [hi5]
        intro hj5
        exact hij (Fin.ext (hi5.trans hj5.symm))
      · simp [hi5]
    have hptouch : pickP i j = i ∨ pickP i j = j := by
      unfold pickP
      by_cases hi5 : i.val = 5 <;> simp [hi5]
    exact step_drop_p (pickP i j) hp5 ht i j hptouch hz rest hsub hkeep tail

theorem no_ten_binary (t : W128) (ht : t = target7 ∨ t = ~~~target7)
    (hb : build basicOps t 10 rows7.toFinset) : False := by
  obtain ⟨s7, hs7, hl7⟩ := compress hb
  have hd7 : bitDiff ⟨32, by decide⟩ ⟨36, by decide⟩ t := by
    rcases ht with rfl | rfl
    · exact sep7.1
    · exact bitDiff_not sep7.1
  have hp2 : v2 ∈ s7 :=
    live_has_unique_sep hs7 hl7 ⟨32, by decide⟩ ⟨36, by decide⟩ hd7 sep7.2
  have hm2 := ops_map_of (selectRows_land (fixBit 2 false)) (selectRows_lor (fixBit 2 false)) (selectRows_neg (fixBit 2 false))
  have hft6 : f2 t = target6 ∨ f2 t = ~~~target6 := by
    rcases ht with rfl | rfl
    · exact .inl f2_t7
    · exact .inr ((selectRows_neg (fixBit 2 false) target7).trans (congrArg (fun u : W128 => ~~~u) f2_t7))
  have hng6 : f2 t ≠ 0 ∧ f2 t ≠ ~~~0 := by
    rcases hft6 with h | h <;> rw [h]
    · exact t6_nc
    · exact not_const_of_neg t6_nc
  obtain ⟨_, hsb6⟩ := live_transport_save_const hm2 hl7 hp2 (.inl f2_v2) hng6
    (fun w hw => hold_rows6 w (List.mem_toFinset.mp (hs7 hw)))
  obtain ⟨t6, ht6, hb6⟩ := unwrap_sb hng6.1 hng6.2 hsb6
  have ht6' : t6 = target6 ∨ t6 = ~~~target6 := by
    rcases hft6 with h | h <;> rcases ht6 with rfl | rfl <;> rw [h]
    · exact .inl rfl
    · exact .inr rfl
    · exact .inr rfl
    · exact .inl BitVec.not_not
  exact no_nine_t6 t6 ht6' hb6

theorem cost_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = edgeValue x) :
    10 < binaryCost gs := by
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
  exact no_ten_binary t ht (lift low run)

def witnessGates : List Gate :=
  [⟨.or, [0, 3]⟩,
   ⟨.and, [0, 3]⟩,
   ⟨.or, [7, 2]⟩,
   ⟨.and, [9, 5]⟩,
   ⟨.or, [9, 5]⟩,
   ⟨.or, [1, 4]⟩,
   ⟨.and, [1, 4]⟩,
   ⟨.or, [11, 12]⟩,
   ⟨.and, [14, 6]⟩,
   ⟨.or, [8, 10]⟩,
   ⟨.or, [13, 15]⟩,
   ⟨.or, [16, 17]⟩]

theorem witness_basis : ∀ g ∈ witnessGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witnessGates, 18⟩ (List.ofFn x) = edgeValue x := by
  decide +kernel

end Lower10754

end PEqualNP.Outside.L_meta_10754

theorem PEqualNP.Outside.L_meta_10754 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hasNot
    have hlt : PEqualNP.Outside.L_meta_10754.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_10754.isBinary)).mpr
        ⟨g, hmem, by simp [PEqualNP.Outside.L_meta_10754.isBinary, hop]⟩
    have hbd := PEqualNP.Outside.L_meta_10754.cost_bound gates o legal computes
    have hlen : PEqualNP.Outside.L_meta_10754.witnessGates.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10754.witnessGates, 18,
      PEqualNP.Outside.L_meta_10754.witness_basis, by omega,
      PEqualNP.Outside.L_meta_10754.witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hcap⟩ := legal g hg
    refine ⟨?_, hcap⟩
    rcases hop with h | h | h
    · exact .inl h
    · exact .inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
