import PEqualNP.Defs

-- Signed live-wire search with two 1-variable deletions (8v -> 7v -> 6v) + normalized 6v cofactor-replay DAG (adapted from L_meta_9136.lean & L_meta_11076.lean, Apache-2.0):
-- 6v DAG (83 states at k=8) lifts via two 1-var deletions to k=10 on 8 inputs, matching a 12-gate Monotone2 witness.

namespace PEqualNP.Outside.L_meta_15014_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {k₁ k₂ : ℕ} {av : Finset α}
    (hle : k₁ ≤ k₂) (h : build ops goal k₁ av) : build ops goal k₂ av := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_av {ops : α → α → Finset α} {goal : α} {k : ℕ} {av₁ av₂ : Finset α}
    (hsub : av₁ ⊆ av₂) (h : build ops goal k av₁) : build ops goal k av₂ := by
  induction k generalizing av₁ av₂ with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
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
          by_contra hn; apply sub; intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := fun u hu =>
          (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hu).2)).resolve_left (Finset.mem_erase.mp hu).1
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

theorem live_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {ops1 : α → α → Finset α} {ops2 : β → β → Finset β}
    {g1 : α} {g2 : β} (f : α → β)
    (hinj : Function.Injective f) (hgoal : f g1 = g2)
    (hops : ∀ a b z, z ∈ ops1 a b → f z ∈ ops2 (f a) (f b))
    {k : ℕ} {s : Finset α} (h : live ops1 g1 k s) :
    live ops2 g2 k (s.image f) := by
  induction k generalizing s with
  | zero => change s = {g1} at h; subst h; simp [live, hgoal]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun he => hab (hinj he), f z, hops a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        exact hout (hinj he ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

def ops (n : ℕ) (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (n : ℕ) (a b : BitVec n) : Finset (BitVec n) :=
  ((ops n a b).filter (fun z => z != 0 && z != BitVec.allOnes n)).toFinset
def nrm (n : ℕ) (u : BitVec n) : BitVec n := if u.getLsbD 0 then ~~~u else u

theorem ops_swap (n : ℕ) (a b : BitVec n) : basicOps n a b = basicOps n b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem ops_diff_ij {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (a b z : BitVec n)
    (hz : z ∈ basicOps n a b) (hd : z.getLsbD i ≠ z.getLsbD j) :
    a.getLsbD i ≠ a.getLsbD j ∨ b.getLsbD i ≠ b.getLsbD j := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz.1 with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      decide_eq_true hi, decide_eq_true hj, Bool.true_and, ha, hb]

def dif (n : ℕ) (w : BitVec n) (d : ℕ) : BitVec n := (w ^^^ (w >>> d)) &&& (BitVec.allOnes n >>> d)
def unionDif (n : ℕ) (ws : List (BitVec n)) (d : ℕ) : BitVec n := ws.foldr (fun w s => dif n w d ||| s) 0
def cover (n : ℕ) (jumps : List ℕ) (t : BitVec n) (ws : List (BitVec n)) : Bool :=
  jumps.all fun d => (dif n t d &&& unionDif n ws d) == dif n t d

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (_hi : i < n) :
    (dif n w d).getLsbD i = true ↔ i + d < n ∧ w.getLsbD i ≠ w.getLsbD (i + d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (n : ℕ) (ws : List (BitVec n)) (d i : ℕ) :
    (unionDif n ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif n w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif n w d ||| unionDif n ws d).getLsbD i = true ↔ _
    simp [ih]

theorem live_cover {n k : ℕ} {jumps : List ℕ} {goal : BitVec n} {ws : List (BitVec n)}
    (h : live (basicOps n) goal k ws.toFinset) : cover n jumps goal ws = true := by
  apply List.all_eq_true.mpr; intro d _
  apply beq_iff_eq.mpr; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif n goal d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    obtain ⟨w, hw, hdw⟩ := live_separates (fun u : BitVec n => u.getLsbD i ≠ u.getLsbD (i + d))
      hne (ops_diff_ij i (i + d) hi hj) h
    rw [(bit_union n ws d i).mpr ⟨w, List.mem_toFinset.mp hw, (bit_dif hi).mpr ⟨hj, hdw⟩⟩]; rfl

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
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
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

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {α : Type} [DecidableEq α] {xs ys : List α} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def actN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p2 :: ps, n => Nat.bit (Nat.beq (Nat.mod (Nat.div n p2) 2) 1) (actN ps n)

def actB (n : ℕ) (ps : List ℕ) (x : BitVec n) : BitVec n := BitVec.ofNat n (actN ps x.toNat)

theorem mod_div_two_pow_eq_testBit (n p : ℕ) :
    Nat.beq (Nat.mod (Nat.div n (2 ^ p)) 2) 1 = n.testBit p := by
  change Nat.beq (n / 2 ^ p % 2) 1 = n.testBit p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : n / 2 ^ p % 2 with
  | zero => rfl
  | succ k =>
    have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : k = 0 := by omega
    subst hk; rfl

theorem actN_testBit : ∀ (pi ps : List ℕ) (n k : ℕ),
    ps = pi.map (fun p => 2 ^ p) →
    (actN ps n).testBit k = (pi[k]?.map n.testBit).getD false
  | [], _, _, _, rfl => by simp [actN]
  | p :: pi, _, n, 0, rfl => by simp [actN, mod_div_two_pow_eq_testBit]
  | p :: pi, _, n, k + 1, rfl => by
    simp [actN, Nat.testBit_bit_succ, actN_testBit pi (pi.map (fun q => 2 ^ q)) n k rfl]

theorem actB_getLsbD (n : ℕ) (pi : List ℕ) (x : BitVec n) (k : ℕ) (hk : k < n) :
    (actB n (pi.map (fun p => 2 ^ p)) x).getLsbD k = (pi[k]?.map x.getLsbD).getD false := by
  unfold actB
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, actN_testBit pi _ x.toNat k rfl]
  cases pi[k]? <;> rfl

def symValid (n gsize : ℕ) (G_idx G_pow : Array (List ℕ)) (G_inv : Array ℕ) (goal : BitVec n) (g : ℕ) : Bool :=
  let pi := G_idx[g]?.getD []
  let inv := G_idx[G_inv[g]?.getD 0]?.getD []
  let ps := G_pow[g]?.getD []
  Nat.blt (G_inv[g]?.getD 0) gsize &&
  Nat.beq (G_inv[G_inv[g]?.getD 0]?.getD 0) g &&
  Nat.beq pi.length n &&
  Nat.beq inv.length n &&
  (ps == pi.map (fun p => 2 ^ p)) &&
  (actB n ps goal == goal) &&
  (List.range n).all (fun k => match pi[k]? with
    | some p => Nat.blt p n && (inv[p]? == some k)
    | none => false)

theorem actB_spec {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) :
    G_inv[g]?.getD 0 < gsize ∧
    G_inv[G_inv[g]?.getD 0]?.getD 0 = g ∧
    G_pow[g]?.getD [] = (G_idx[g]?.getD []).map (fun p => 2 ^ p) ∧
    actB n (G_pow[g]?.getD []) goal = goal ∧
    (∀ k < n, ∃ p < n, (G_idx[g]?.getD [])[k]? = some p ∧ (G_idx[G_inv[g]?.getD 0]?.getD [])[p]? = some k) := by
  have hv := List.all_eq_true.mp hvalid g (List.mem_range.mpr hg)
  unfold symValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at hv
  refine ⟨hv.1.1.1.1.1.1, Nat.eq_of_beq_eq_true hv.1.1.1.1.1.2, hv.1.1.2, hv.1.2, fun k hk => ?_⟩
  have h1 := hv.2 k hk
  cases hp : (G_idx[g]?.getD [])[k]? with
  | none => simp [hp] at h1
  | some p =>
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
    exact ⟨p, h1.1, rfl, h1.2⟩

theorem actB_inv_left {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (x : BitVec n) :
    actB n (G_pow[G_inv[g]?.getD 0]?.getD []) (actB n (G_pow[g]?.getD []) x) = x := by
  obtain ⟨hinv_lt, hinv2, hpow, _, _⟩ := actB_spec hv g hg
  obtain ⟨_, _, hpow', _, hpi'⟩ := actB_spec hv (G_inv[g]?.getD 0) hinv_lt
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow', actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, hpk⟩ := hpi' k hk
  rw [hinv2] at hpk
  rw [hkp]; simp only [Option.map_some, Option.getD_some]
  rw [hpow, actB_getLsbD n _ _ p hp, hpk]; simp

theorem actB_inj {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : Function.Injective (actB n (G_pow[g]?.getD [])) :=
  Function.LeftInverse.injective (actB_inv_left hv g hg)

theorem actB_and {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a &&& b) = actB n (G_pow[g]?.getD []) a &&& actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_and]

theorem actB_or {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a ||| b) = actB n (G_pow[g]?.getD []) a ||| actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_or]

theorem actB_not {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a : BitVec n) :
    actB n (G_pow[g]?.getD []) (~~~a) = ~~~actB n (G_pow[g]?.getD []) a := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  simp [hkp, hk, hp]

theorem actB_zero {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) 0 = 0 := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp]

theorem actB_allOnes {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) (BitVec.allOnes n) = BitVec.allOnes n := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  rw [hkp]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_allOnes, hk, hp, decide_true]

theorem actB_ops {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b z : BitVec n) (hz : z ∈ basicOps n a b) :
    actB n (G_pow[g]?.getD []) z ∈ basicOps n (actB n (G_pow[g]?.getD []) a) (actB n (G_pow[g]?.getD []) b) := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun e => hz.2.1 (actB_inj hv g hg (e.trans (actB_zero hv g hg).symm)),
               fun e => hz.2.2 (actB_inj hv g hg (e.trans (actB_allOnes hv g hg).symm))⟩
  have hz' := hz.1
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
  rcases hz' with rfl | rfl | rfl | rfl
  · left; exact actB_and hv g hg a b
  · right; left; exact actB_or hv g hg a b
  · right; right; left; rw [actB_and hv g hg, actB_not hv g hg]
  · right; right; right; rw [actB_and hv g hg, actB_not hv g hg]

def checkChildP (n k : ℕ) (targets : List (List (BitVec n))) (nxt : List (BitVec n)) : Bool :=
  decide (nxt.length > k) || targets.any (fun t => sameSet nxt t)

def checkStepP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (k extra : ℕ)
    (targets : List (List (BitVec n))) (a b : BitVec n) (r : List (BitVec n)) : Bool :=
  (ops n a b).all fun w =>
    (w == 0 || w == BitVec.allOnes n || w == a || w == b || r.contains w) ||
    (!cover n jumps goal (w :: r) || checkChildP n k targets (w :: r)) &&
    ((extra == 0) ||
      ((!cover n jumps goal (w :: a :: r) || checkChildP n k targets (w :: a :: r)) &&
       (!cover n jumps goal (w :: b :: r) || checkChildP n k targets (w :: b :: r)))) &&
    ((extra < 2) || !cover n jumps goal (w :: a :: b :: r) || checkChildP n k targets (w :: a :: b :: r))

def checkNodeP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hs) =>
    decide ws.Nodup && !(ws.contains goal) && decide (ws.length ≤ k + 1) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepP n jumps goal k extra targets a b r)

def checkBlockP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeP n jumps goal gsize G_pow k cur prev (start + m) &&
      checkBlockP n jumps goal gsize G_pow k cur prev start m

theorem checkBlockP_at {n gsize k start m : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h : checkBlockP n jumps goal gsize G_pow k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeP n jumps goal gsize G_pow k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_P {n gsize k i : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hchk : checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hs⟩
  have hget : cur[i]? = some (ws, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeP at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps n) goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB n (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [])).1.map (actB n (G_pow[g]?.getD []))).toFinset.image
        (actB n (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB n (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec n} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps n a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps n) goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover n jumps goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepP at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes n || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildP n k targets (z :: kept) = true) : False := by
        unfold checkChildP at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with hgt | ⟨t, ht, hss⟩
        · omega
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap n a b ▸ hz)

theorem level_sound_P {n gsize k : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (hblk i hi)

theorem no_build_of_top {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows top_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) top_ws = true)
    (hdead : ¬ live (basicOps n) goal k top_ws.toFinset) :
    ¬ build (basicOps n) goal k rows.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rows.filter (· ∈ s)
  have hsubl : ws.Sublist rows := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps goal ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ rows.sublists.filter (fun zs => cover n jumps goal zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  have hs_eq : s = rows.toFinset := by rw [← heq, hmem]
  have hl_rows : live (basicOps n) goal k rows.toFinset := hs_eq ▸ hl
  have hrg_g := (actB_spec hvalid rg hrg).2.2.2.1
  have hrot := live_map (actB n (G_pow[rg]?.getD [])) (actB_inj hvalid rg hrg) hrg_g (actB_ops hvalid rg hrg) hl_rows
  have himg : rows.toFinset.image (actB n (G_pow[rg]?.getD [])) =
      (rows.map (actB n (G_pow[rg]?.getD []))).toFinset := by
    ext u; simp [List.mem_map]
  rw [himg, sameSet_sound hmatch] at hrot
  exact hdead hrot

def jumps4 : List ℕ := [1, 2, 4, 8]
def jumps5 : List ℕ := [1, 2, 4, 8, 16]
def jumps6 : List ℕ := [1, 2, 4, 8, 16, 32]
def rows4 : List (BitVec 16) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def rows5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def b4_0_goal : BitVec 16 := 0xeae8
def b4_0_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def b4_0_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
def b4_0_s1 : List ℕ := [0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
def b4_0_p1 : List ℕ := [1, 2, 16, 32, 4, 8, 64, 128, 256, 512, 4096, 8192, 1024, 2048, 16384, 32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0, b4_0_s1]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0, b4_0_p1]
def b4_0_inv : Array ℕ := Array.mk [0, 1]
theorem b4_0_G_valid : (List.range 2).all (symValid 16 2 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xfaf0],[]),
  ([0xaaaa,0xcccc,0xf3f0],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaa00,0xaaaa,0xcccc,0xf0f0],[(0,0),(1,0)]),
  ([0xaa,0xaaaa,0xcccc,0xf0f0],[]),
  ([0xaaaa,0xcccc,0xf0f0,0xffcc],[]),
  ([0xf00,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true :=
  fun i hi => checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) ((show b4_0_L2.size = 2 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 3 b4_0_L3 b4_0_L2 0 4 = true := by decide +kernel
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true :=
  fun i hi => checkBlockP_at b4_0_chk_3_0 i (Nat.zero_le _) ((show b4_0_L3.size = 4 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 2 b4_0_pow 4 b4_0_L4 b4_0_L3 0 1 = true := by decide +kernel
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 2 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true :=
  fun i hi => checkBlockP_at b4_0_chk_4_0 i (Nat.zero_le _) ((show b4_0_L4.size = 1 by rfl) ▸ hi)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 4 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L4_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xfeea
def b4_1_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def b4_1_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
def b4_1_s1 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15]
def b4_1_p1 : List ℕ := [1, 2, 4, 8, 256, 512, 1024, 2048, 16, 32, 64, 128, 4096, 8192, 16384, 32768]
def b4_1_s2 : List ℕ := [0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
def b4_1_p2 : List ℕ := [1, 2, 16, 32, 4, 8, 64, 128, 256, 512, 4096, 8192, 1024, 2048, 16384, 32768]
def b4_1_s3 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 2, 3, 6, 7, 10, 11, 14, 15]
def b4_1_p3 : List ℕ := [1, 2, 16, 32, 256, 512, 4096, 8192, 4, 8, 64, 128, 1024, 2048, 16384, 32768]
def b4_1_s4 : List ℕ := [0, 1, 8, 9, 2, 3, 10, 11, 4, 5, 12, 13, 6, 7, 14, 15]
def b4_1_p4 : List ℕ := [1, 2, 256, 512, 4, 8, 1024, 2048, 16, 32, 4096, 8192, 64, 128, 16384, 32768]
def b4_1_s5 : List ℕ := [0, 1, 8, 9, 4, 5, 12, 13, 2, 3, 10, 11, 6, 7, 14, 15]
def b4_1_p5 : List ℕ := [1, 2, 256, 512, 16, 32, 4096, 8192, 4, 8, 1024, 2048, 64, 128, 16384, 32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0, b4_1_s1, b4_1_s2, b4_1_s3, b4_1_s4, b4_1_s5]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0, b4_1_p1, b4_1_p2, b4_1_p3, b4_1_p4, b4_1_p5]
def b4_1_inv : Array ℕ := Array.mk [0, 1, 2, 4, 3, 5]
theorem b4_1_G_valid : (List.range 6).all (symValid 16 6 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xcccc,0xfafa,0xffaa],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
  ([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 1 = true := by decide +kernel
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true :=
  fun i hi => checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) ((show b4_1_L2.size = 1 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 0 2 = true := by decide +kernel
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true :=
  fun i hi => checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) ((show b4_1_L3.size = 2 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true :=
  fun i hi => checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) ((show b4_1_L4.size = 1 by rfl) ▸ hi)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 4 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L4_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xeac8
def b4_2_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def b4_2_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
def b4_2_s1 : List ℕ := [0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
def b4_2_p1 : List ℕ := [1, 4, 2, 8, 256, 1024, 512, 2048, 16, 64, 32, 128, 4096, 16384, 8192, 32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0, b4_2_s1]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0, b4_2_p1]
def b4_2_inv : Array ℕ := Array.mk [0, 1]
theorem b4_2_G_valid : (List.range 2).all (symValid 16 2 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xf0f0,0xff00],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 (Array.mk []) 0 1 = true := by decide +kernel
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 (Array.mk []) i = true :=
  fun i hi => checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) ((show b4_2_L3.size = 1 by rfl) ▸ hi)
theorem b4_2_L3_sound : ∀ i < b4_2_L3.size, ¬ live (basicOps 16) b4_2_goal 3 (b4_2_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid (fun j hj => by simp at hj) b4_2_chk_3
theorem b4_2_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_2_goal ws) = [rows4] := by decide +kernel
theorem b4_2_top_match : sameSet (rows4.map (actB 16 (b4_2_pow[0]?.getD []))) (b4_2_L3[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_2_no_build : ¬ build (basicOps 16) b4_2_goal 3 rows4.toFinset :=
  no_build_of_top b4_2_G_valid (by decide) b4_2_sublists b4_2_top_match (b4_2_L3_sound 0 (by decide))

def b4_3_goal : BitVec 16 := 0xeee8
def b4_3_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def b4_3_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]
def b4_3_s1 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15]
def b4_3_p1 : List ℕ := [1, 2, 4, 8, 256, 512, 1024, 2048, 16, 32, 64, 128, 4096, 8192, 16384, 32768]
def b4_3_s2 : List ℕ := [0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15]
def b4_3_p2 : List ℕ := [1, 4, 2, 8, 16, 64, 32, 128, 256, 1024, 512, 2048, 4096, 16384, 8192, 32768]
def b4_3_s3 : List ℕ := [0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
def b4_3_p3 : List ℕ := [1, 4, 2, 8, 256, 1024, 512, 2048, 16, 64, 32, 128, 4096, 16384, 8192, 32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0, b4_3_s1, b4_3_s2, b4_3_s3]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0, b4_3_p1, b4_3_p2, b4_3_p3]
def b4_3_inv : Array ℕ := Array.mk [0, 1, 2, 3]
theorem b4_3_G_valid : (List.range 4).all (symValid 16 4 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xfff0],[])
]
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xfff0],[]),
  ([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
  ([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_3_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
  ([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_2_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 2 b4_3_L2 (Array.mk []) 0 1 = true := by decide +kernel
theorem b4_3_chk_2 : ∀ i < b4_3_L2.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 2 b4_3_L2 (Array.mk []) i = true :=
  fun i hi => checkBlockP_at b4_3_chk_2_0 i (Nat.zero_le _) ((show b4_3_L2.size = 1 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 3 b4_3_L3 b4_3_L2 0 3 = true := by decide +kernel
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 3 b4_3_L3 b4_3_L2 i = true :=
  fun i hi => checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) ((show b4_3_L3.size = 3 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_4_0 : checkBlockP 16 jumps4 b4_3_goal 4 b4_3_pow 4 b4_3_L4 b4_3_L3 0 1 = true := by decide +kernel
theorem b4_3_chk_4 : ∀ i < b4_3_L4.size, checkNodeP 16 jumps4 b4_3_goal 4 b4_3_pow 4 b4_3_L4 b4_3_L3 i = true :=
  fun i hi => checkBlockP_at b4_3_chk_4_0 i (Nat.zero_le _) ((show b4_3_L4.size = 1 by rfl) ▸ hi)
theorem b4_3_L2_sound : ∀ i < b4_3_L2.size, ¬ live (basicOps 16) b4_3_goal 2 (b4_3_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid (fun j hj => by simp at hj) b4_3_chk_2
theorem b4_3_L3_sound : ∀ i < b4_3_L3.size, ¬ live (basicOps 16) b4_3_goal 3 (b4_3_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L2_sound b4_3_chk_3
theorem b4_3_L4_sound : ∀ i < b4_3_L4.size, ¬ live (basicOps 16) b4_3_goal 4 (b4_3_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L3_sound b4_3_chk_4
theorem b4_3_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_3_goal ws) = [rows4] := by decide +kernel
theorem b4_3_top_match : sameSet (rows4.map (actB 16 (b4_3_pow[0]?.getD []))) (b4_3_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_3_no_build : ¬ build (basicOps 16) b4_3_goal 4 rows4.toFinset :=
  no_build_of_top b4_3_G_valid (by decide) b4_3_sublists b4_3_top_match (b4_3_L4_sound 0 (by decide))

-- Generic projection + live_restrict
def projN {m : ℕ} : List ℕ → BitVec m → ℕ
  | [], _ => 0
  | idx :: idxs, w => Nat.bit (w.getLsbD idx) (projN idxs w)

theorem projN_testBit {m : ℕ} : ∀ (idxs : List ℕ) (w : BitVec m) (k : ℕ),
    (projN idxs w).testBit k = (idxs[k]?.map w.getLsbD).getD false
  | [], _, _ => by simp [projN]
  | idx :: idxs, w, 0 => by simp [projN]
  | idx :: idxs, w, k + 1 => by simp [projN, Nat.testBit_bit_succ, projN_testBit idxs w k]

def projB (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := BitVec.ofNat n (projN idxs w)
def projS (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := nrm n (projB n idxs w)

theorem projB_getLsbD (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) (k : ℕ) (hk : k < n) :
    (projB n idxs w).getLsbD k = (idxs[k]?.map w.getLsbD).getD false := by
  unfold projB; rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, projN_testBit]

theorem projB_and (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a &&& b) = projB n idxs a &&& projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_and]

theorem projB_or (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a ||| b) = projB n idxs a ||| projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_or]

theorem projB_not (n : ℕ) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m) (a : BitVec m) :
    projB n idxs (~~~a) = ~~~projB n idxs a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  have hk' : k < idxs.length := by omega
  rw [List.getElem?_eq_getElem hk']
  have hmem := hlt idxs[k] (List.getElem_mem hk')
  simp [hk, hmem]

theorem nrm_bit0 (n : ℕ) (hn : 0 < n) (u : BitVec n) : (nrm n u).getLsbD 0 = false := by
  unfold nrm
  cases h : u.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]

theorem projS_ne_allOnes (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (w : BitVec m) :
    projS n idxs w ≠ BitVec.allOnes n := by
  intro h
  have := nrm_bit0 n hn (projB n idxs w)
  change (projS n idxs w).getLsbD 0 = false at this
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hn] at this
  exact Bool.noConfusion this

theorem nrm_neg (n : ℕ) (hn : 0 < n) (u : BitVec n) : nrm n (~~~u) = nrm n u := by
  unfold nrm
  cases h : u.getLsbD 0
  · have h1 : (~~~u).getLsbD 0 = true := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_false]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · have h1 : (~~~u).getLsbD 0 = false := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true]

theorem projS_not (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (w : BitVec m) :
    projS n idxs (~~~w) = projS n idxs w := by
  unfold projS; rw [projB_not n idxs hlen hlt w, nrm_neg n hn]

theorem nrm_ops (n : ℕ) (hn : 0 < n) (x y z : BitVec n) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)
    (hz : z ∈ ops n x y ∨ z ∈ ops n (~~~x) y ∨ z ∈ ops n x (~~~y) ∨ z ∈ ops n (~~~x) (~~~y)) :
    nrm n z ∈ ops n x y := by
  have nrm_f (u : BitVec n) (hu : u.getLsbD 0 = false) : nrm n u = u := by
    unfold nrm; simp only [hu, Bool.false_eq_true, ite_false]
  have nrm_t (u : BitVec n) (hu : u.getLsbD 0 = true) : nrm n u = ~~~u := by
    unfold nrm; simp only [hu, ite_true]
  have b_eq (u v : BitVec n) (h : ∀ i < n, u.getLsbD i = v.getLsbD i) : u = v := BitVec.eq_of_getLsbD_eq h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, hx, hy, Bool.and_false])
  · right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_or, hx, hy, Bool.or_false])
  · right; right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.and_false])]
    exact BitVec.and_comm ..
  · right; right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.or_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem projS_ops (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (a b z : BitVec m) (hz : z ∈ ops m a b) :
    projS n idxs z ∈ ops n (projS n idxs a) (projS n idxs b) := by
  have hrest : projB n idxs z ∈ ops n (projB n idxs a) (projB n idxs b) := by
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · left; exact projB_and n idxs a b
    · right; left; exact projB_or n idxs a b
    · right; right; left; rw [projB_and, projB_not n idxs hlen hlt]
    · right; right; right; rw [projB_and, projB_not n idxs hlen hlt]
  apply nrm_ops n hn (projS n idxs a) (projS n idxs b) (projB n idxs z) (nrm_bit0 n hn _) (nrm_bit0 n hn _)
  unfold projS nrm
  cases ha : (projB n idxs a).getLsbD 0 <;> cases hb : (projB n idxs b).getLsbD 0 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · exact Or.inl hrest
  · exact Or.inr (Or.inr (Or.inl hrest))
  · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inr hrest))

theorem ops_zero_left (n : ℕ) (y : BitVec n) : ∀ w ∈ ops n 0 y, w = 0 ∨ w = y := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]

theorem ops_zero_right (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x 0, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.and_zero
  · right; exact BitVec.or_zero
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]
  · left; exact BitVec.zero_and

theorem ops_self (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x x, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · right; exact BitVec.and_self
  · right; exact BitVec.or_self
  · left; exact BitVec.and_not_self x
  · left; exact BitVec.and_not_self x

def zCount {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : ℕ :=
  (s.filter (fun w => f w = 0)).card
def nonZeroImg {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : Finset (BitVec n) :=
  (s.image f).erase 0

set_option maxRecDepth 100000 in
theorem live_restrict {m n : ℕ} (hn : 0 < n) (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) {opsM : BitVec m → BitVec m → Finset (BitVec m)}
    (hopsM : ∀ a b z, z ∈ opsM a b → z ∈ ops m a b)
    {g : BitVec m} {goalN : BitVec n} (hg : projS n idxs g = goalN) (hgnz : goalN ≠ 0)
    {k : ℕ} {s : Finset (BitVec m)} (h : live opsM g k s) :
    build (basicOps n) goalN (k - zCount (projS n idxs) s) (nonZeroImg (projS n idxs) s) := by
  let f : BitVec m → BitVec n := projS n idxs
  change build (basicOps n) goalN (k - zCount f s) (nonZeroImg f s)
  induction k generalizing s with
  | zero =>
    change s = {g} at h; subst h
    have hzc : zCount f {g} = 0 := by
      unfold zCount; rw [Finset.filter_singleton, if_neg (by change projS n idxs g ≠ 0; rw [hg]; exact hgnz)]; rfl
    rw [hzc]; change goalN ∈ nonZeroImg f {g}
    exact Finset.mem_erase.mpr ⟨hgnz, Finset.mem_image.mpr ⟨g, Finset.mem_singleton_self g, hg⟩⟩
  | succ k ih =>
    have hsc := live_card h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs_eq, tail⟩
    · exact build_mono_k (by omega) (ih skip)
    · have htail := ih tail
      have hz_ops : f z ∈ ops n (f a) (f b) := projS_ops n hn idxs hlen hlt a b z (hopsM a b z hz)
      have hsub_rest : nonZeroImg f rest ⊆ nonZeroImg f s := by
        intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu ⊢
        obtain ⟨hne, v, hv, rfl⟩ := hu; exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
      have hcard_rest : zCount f rest ≤ zCount f (insert z rest) := by
        unfold zCount; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert z rest))
      by_cases hza : f a = 0
      · have hzb_or := ops_zero_left n (f b) (f z) (hza ▸ hz_ops)
        have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
          obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
          · rcases hzb_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, b, hb, h1.symm⟩
          · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
        have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
          by_cases hzb : f b = 0
          · have hzz : f z = 0 := by rcases hzb_or with h0 | h1; exact h0; exact h1.trans hzb
            have hz_nr : z ∉ rest := fun hm => hout (by rw [hs_eq]; simp [hm])
            have h1 : zCount f (insert z rest) = zCount f rest + 1 := by
              unfold zCount; rw [Finset.filter_insert, if_pos hzz, Finset.card_insert_of_notMem (by simp [hz_nr])]
            have h2 : zCount f s ≤ zCount f rest + 2 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_pos hza]
              have hc1 := Finset.card_insert_le a (insert b (rest.filter (fun w => f w = 0)))
              have hc2 := Finset.card_insert_le b (rest.filter (fun w => f w = 0))
              omega
            omega
          · have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_pos hza]
              exact Finset.card_insert_le a (rest.filter (fun w => f w = 0))
            omega
        exact build_mono_k (by omega) (build_mono_av hsub htail)
      · by_cases hzb : f b = 0
        · have hza_or := ops_zero_right n (f a) (f z) (hzb ▸ hz_ops)
          have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
            intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
            obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
            · rcases hza_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
            · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
          have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
            have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_neg hza]
              exact Finset.card_insert_le b (rest.filter (fun w => f w = 0))
            omega
          exact build_mono_k (by omega) (build_mono_av hsub htail)
        · have hzc_eq : zCount f s = zCount f rest := by
            unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_neg hza]
          have hzc_le : zCount f s ≤ k := by
            have hsubf : insert a (insert b (s.filter (fun w => f w = 0))) ⊆ s := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact ha
              · rcases Finset.mem_insert.mp hu with rfl | hu
                · exact hb
                · exact (Finset.mem_filter.mp hu).1
            have han : a ∉ insert b (s.filter (fun w => f w = 0)) := by
              simp only [Finset.mem_insert, Finset.mem_filter, not_or]; exact ⟨hab, fun h => hza h.2⟩
            have hbn : b ∉ s.filter (fun w => f w = 0) := by
              simp only [Finset.mem_filter]; exact fun h => hzb h.2
            have hle := Finset.card_le_card hsubf
            rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hle
            unfold zCount; omega
          by_cases hzz : f z = 0
          · have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
              obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
              · exact (hne hzz).elim
              · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
            exact build_mono_k (by omega) (build_mono_av hsub htail)
          · by_cases heqab : f a = f b
            · have hsame := ops_self n (f a) (f z) (heqab ▸ hz_ops)
              have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
                intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
                obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                · rcases hsame with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
                · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
              exact build_mono_k (by omega) (build_mono_av hsub htail)
            · have hstep : build (basicOps n) goalN ((k - zCount f (insert z rest)) + 1) (nonZeroImg f s) := by
                refine Or.inr ⟨f a, ?_, f b, ?_, heqab, f z, ?_, ?_⟩
                · exact Finset.mem_erase.mpr ⟨hza, Finset.mem_image_of_mem f ha⟩
                · exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_image_of_mem f hb⟩
                · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
                  exact ⟨hz_ops, hzz, projS_ne_allOnes n hn idxs z⟩
                · apply build_mono_av _ htail
                  intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu
                  obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hsub_rest (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f hv⟩))
              exact build_mono_k (by omega) hstep

-- Generic 1-variable deletion lemma
theorem no_build_of_proj {m n k : ℕ} (hn : 0 < n) (rowsM : List (BitVec m)) (rowsN : List (BitVec n))
    (goalM : BitVec m) (goalN : BitVec n) (idxs : List ℕ) (u p0 p1 : ℕ)
    (hp0 : p0 < m) (hp1 : p1 < m) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m)
    (hgnz : goalN ≠ 0) (hpg : projS n idxs goalM = goalN)
    (hxu : projS n idxs (rowsM.getD u 0) = 0)
    (hsub : rowsM.all (fun w => projS n idxs w == 0 || rowsN.contains (projS n idxs w)) = true)
    (hess : rowsM.all (fun w => w == rowsM.getD u 0 || w.getLsbD p0 == w.getLsbD p1) = true)
    (hdiff : goalM.getLsbD p0 ≠ goalM.getLsbD p1)
    (hbase : ¬ build (basicOps n) goalN k rowsN.toFinset) :
    ¬ build (basicOps m) goalM (k + 1) rowsM.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  obtain ⟨w, hw, hdw⟩ := live_separates (fun v : BitVec m => v.getLsbD p0 ≠ v.getLsbD p1)
    hdiff (ops_diff_ij p0 p1 hp0 hp1) hl
  have hw_eq : w = rowsM.getD u 0 := by
    have h1 := List.all_eq_true.mp hess w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hmem_z : rowsM.getD u 0 ∈ s.filter (fun v => projS n idxs v = 0) :=
    Finset.mem_filter.mpr ⟨hw_eq ▸ hw, hxu⟩
  have hzc_pos : 1 ≤ zCount (projS n idxs) s := Finset.one_le_card.mpr ⟨_, hmem_z⟩
  have hopsM : ∀ a b z : BitVec m, z ∈ basicOps m a b → z ∈ ops m a b := fun a b z hz =>
    (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
  have hbN := live_restrict hn idxs hlen hlt hopsM hpg hgnz hl
  have hsubN : nonZeroImg (projS n idxs) s ⊆ rowsN.toFinset := by
    intro v hv
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hv
    obtain ⟨hne, y, hy, rfl⟩ := hv
    have h1 := List.all_eq_true.mp hsub y (List.mem_toFinset.mp (hs hy))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact hbase (build_mono_k (by omega) (build_mono_av hsubN hbN))

theorem projB_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projB n idxs (0 : BitVec m) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk]; cases idxs[k]? <;> simp

theorem projB_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projB n idxs (w &&& mask) = projB n idxs w := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases h : idxs[k]? with
  | none => rfl
  | some idx =>
    have hmem : idx ∈ idxs := List.mem_of_getElem? h
    simp [BitVec.getLsbD_and, hm idx hmem]

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by unfold nrm; simp
theorem projS_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projS n idxs (0 : BitVec m) = 0 := by
  unfold projS; rw [projB_zero, nrm_zero]
theorem projS_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projS n idxs (w &&& mask) = projS n idxs w := by
  unfold projS; rw [projB_mask n idxs mask hm w]

-- 5-variable normalized cofactor-replay pruning
def nrmM32 (m : BitVec 32) (b0 : ℕ) (u : BitVec 32) : BitVec 32 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM32 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 32) :
    projS 16 idxs (nrmM32 m b0 u) = projS 16 idxs u := by
  unfold nrmM32
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

abbrev W5Node := List (BitVec 32) × List (BitVec 32 × BitVec 32 × BitVec 32) × List ℕ × List (ℕ × ℕ)

def checkReplay32 (m : BitVec 32) (b0 : ℕ) (bank : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → Bool
  | [], targets => targets.all (fun t => nrmM32 m b0 t == 0 || bank.contains (nrmM32 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 32 a b).contains v &&
    checkReplay32 m b0 (v :: bank) rest targets

theorem checkReplay32_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 32 × BitVec 32 × BitVec 32)) (targets : List (BitVec 32)) :
    ∀ (bank : List (BitVec 32)) (k : ℕ),
      checkReplay32 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 32 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay32, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM32 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM32 m b0 t, hmem, projS_nrmM32 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay32, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed32 (stock needed : List (BitVec 32)) (u : BitVec 32) : List (BitVec 32) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded32 (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM32 m b0 w
    let needed' := if needed.contains pw then addNeed32 stock (addNeed32 stock needed (nrmM32 m b0 a)) (nrmM32 m b0 b) else needed
    buildNeeded32 m b0 stock rest needed'

def buildSteps32 (m : BitVec 32) (b0 : ℕ) (needed : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32 × BitVec 32 × BitVec 32)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM32 m b0 w
    let pa := nrmM32 m b0 a
    let pb := nrmM32 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 32 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps32 m b0 needed rest (pw :: bank)
    else
      buildSteps32 m b0 needed rest bank

def checkCofClose32 (L fuel : ℕ) (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM32 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem L then
    let start := nxt.foldl (fun acc u => addNeed32 stock acc (nrmM32 m b0 u)) []
    if Nat.blt (start.length + rem) L then
      let needed := buildNeeded32 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) L then
        let steps := buildSteps32 m b0 needed hist stock
        Nat.blt (steps.length + rem) L && checkReplay32 m b0 stock steps nxt
      else false
    else false
  else false


theorem checkCofClose32_sound_aux (goal5 : BitVec 32) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 32)) (g : BitVec 16) (L : ℕ) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal5 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (L - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32))
    (hnd : nxt.Nodup) (hchk : checkCofClose32 L fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose32 at hchk; dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops32 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM32 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM32 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]; apply Finset.card_le_card; intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM32 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay32_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu; have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1; exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW5 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  decide (nxt.length > k) ||
  targets.any (fun t => sameSet nxt t) ||
  cfs.any (fun c => checkCofClose32 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt)

def checkStepW5 (goal5 : BitVec 32) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (a b : BitVec 32) (r : List (BitVec 32)) : Bool :=
  (ops 32 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 32 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 32 jumps5 goal5 (w :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 32 jumps5 goal5 (w :: a :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 32 jumps5 goal5 (w :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 32 jumps5 goal5 (w :: a :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (goal5 : BitVec 32) (ncf gsize : ℕ) (G_pow : Array (List ℕ))
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal5) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 goal5 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW5 (goal5 : BitVec 32) (ncf gsize : ℕ) (G_pow : Array (List ℕ))
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW5_at {goal5 : BitVec 32} {ncf gsize k start m : ℕ} {G_pow : Array (List ℕ)}
    {cfLBs : Array ℕ} {cfMasks : Array (BitVec 32)} {cfB0s : Array ℕ} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (h : checkBlockW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W5 {goal5 : BitVec 32} {ncf gsize k i : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cfLBs : Array ℕ} {cfMasks : Array (BitVec 32)} {cfB0s : Array ℕ} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node} (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 32 gsize G_idx G_pow G_inv goal5) = true)
    (hcf : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk; rw [hget] at hchk ⊢; dsimp only at hchk ⊢; simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 32) goal5 (k - 1) t.toFinset := by
    intro t ht; obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht; obtain ⟨hg, hc⟩ := hhs (g, c) hmem; intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1; have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 32 (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt) hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 32 (G_pow[g]?.getD []))).toFinset.image
        (actB 32 (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]; constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 32 (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg; exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · exact hng (List.mem_toFinset.mp (done.symm ▸ Finset.mem_singleton_self _))
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 32} (hpair : (a, b, r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps 32 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr; exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 32) goal5 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail; rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 32 jumps5 goal5 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair; unfold checkStepW5 at hstep; dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 32 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw; simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq; simp only [List.length_cons] at plen
      have close (hc : checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc; simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨t, ht, hss⟩) | ⟨c, hcm, hcc⟩
        · omega
        · rw [sameSet_sound hss] at htail; exact htargets t ht htail
        · exact hcf c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcc htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept; have h1 := hw.1.1; rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1; exact close h1
      · have h1 := hw.1.2; have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1; rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2; exact close h2
      · have h1 := hw.1.2; have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2; rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2; exact close h2
      · have h1 := hw.2; have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1; rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1; exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 32 a b ▸ hz)

theorem level_sound_W5 {goal5 : BitVec 32} {ncf gsize k : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cfLBs : Array ℕ} {cfMasks : Array (BitVec 32)} {cfB0s : Array ℕ} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node} (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 32 gsize G_idx G_pow G_inv goal5) = true)
    (hcf : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 goal5 ncf gsize G_pow cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hvalid hcf hprev (hblk i hi)


namespace pg5_0_ns
def goal5 : BitVec 32 := 0xfeeafcc8
def g5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def g5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def g5_s1 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25, 26, 27, 20, 21, 22, 23, 28, 29, 30, 31]
def g5_p1 : List ℕ := [1, 2, 4, 8, 256, 512, 1024, 2048, 16, 32, 64, 128, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 16777216, 33554432, 67108864, 134217728, 1048576, 2097152, 4194304, 8388608, 268435456, 536870912, 1073741824, 2147483648]
def g5_idx : Array (List ℕ) := Array.mk [g5_s0, g5_s1]
def g5_pow : Array (List ℕ) := Array.mk [g5_p0, g5_p1]
def g5_inv : Array ℕ := Array.mk [0, 1]
theorem g5_G_valid : (List.range 2).all (symValid 32 2 g5_idx g5_pow g5_inv goal5) = true := by decide +kernel
def cfMask0 : BitVec 32 := 0xffff
def cfStock0 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def cfIdx0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15]
def cfMask1 : BitVec 32 := 0xffff0000
def cfStock1 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def cfIdx1 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def cfMask2 : BitVec 32 := 0xf0f0f0f
def cfStock2 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def cfIdx2 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27]
def cfMask3 : BitVec 32 := 0xff00ff
def cfStock3 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def cfIdx3 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]
def cfLBs : Array ℕ := Array.mk [5, 5, 4, 4]
def cfMasks : Array (BitVec 32) := Array.mk [cfMask0, cfMask1, cfMask2, cfMask3]
def cfB0s : Array ℕ := Array.mk [0, 16, 0, 0]
def cfStocks : Array (List (BitVec 32)) := Array.mk [cfStock0, cfStock1, cfStock2, cfStock3]
theorem cf_specs :
  (cfIdx0.length = 16 ∧ (∀ idx ∈ cfIdx0, idx < 32) ∧ (∀ idx ∈ cfIdx0, cfMask0.getLsbD idx = true) ∧ projS 16 cfIdx0 goal5 = b4_0_goal ∧ cfStock0.all (fun w => rows4.contains (projS 16 cfIdx0 w)) = true) ∧
  (cfIdx1.length = 16 ∧ (∀ idx ∈ cfIdx1, idx < 32) ∧ (∀ idx ∈ cfIdx1, cfMask1.getLsbD idx = true) ∧ projS 16 cfIdx1 goal5 = b4_1_goal ∧ cfStock1.all (fun w => rows4.contains (projS 16 cfIdx1 w)) = true) ∧
  (cfIdx2.length = 16 ∧ (∀ idx ∈ cfIdx2, idx < 32) ∧ (∀ idx ∈ cfIdx2, cfMask2.getLsbD idx = true) ∧ projS 16 cfIdx2 goal5 = b4_2_goal ∧ cfStock2.all (fun w => rows4.contains (projS 16 cfIdx2 w)) = true) ∧
  (cfIdx3.length = 16 ∧ (∀ idx ∈ cfIdx3, idx < 32) ∧ (∀ idx ∈ cfIdx3, cfMask3.getLsbD idx = true) ∧ projS 16 cfIdx3 goal5 = b4_2_goal ∧ cfStock3.all (fun w => rows4.contains (projS 16 cfIdx3 w)) = true) := by decide +kernel
theorem cf_sound (c fuel : ℕ) (hc : c < 4) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup)
    (hchk : checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  obtain ⟨h0, h1, h2, h3⟩ := cf_specs
  match c with
  | 0 => exact checkCofClose32_sound_aux goal5 cfIdx0 h0.1 h0.2.1 cfMask0 h0.2.2.1 0 cfStock0 b4_0_goal 5 (by decide) h0.2.2.2.1 h0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux goal5 cfIdx1 h1.1 h1.2.1 cfMask1 h1.2.2.1 16 cfStock1 b4_1_goal 5 (by decide) h1.2.2.2.1 h1.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux goal5 cfIdx2 h2.1 h2.2.1 cfMask2 h2.2.2.1 0 cfStock2 b4_2_goal 4 (by decide) h2.2.2.2.1 h2.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux goal5 cfIdx3 h3.1 h3.2.1 cfMask3 h3.2.2.1 0 cfStock3 b4_2_goal 4 (by decide) h3.2.2.2.1 h3.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | c + 4 => omega
def g5_L4 : Array W5Node := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff88ff88,0xffff0000],[(0x88888888,0xaaaaaaaa,0xcccccccc),(0xff88ff88,0x88888888,0xff00ff00)],[0],[]),
  ([0x22222222,0x44444444,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0x22222222,0xaaaaaaaa,0xcccccccc),(0x44444444,0xaaaaaaaa,0xcccccccc)],[],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff0aff0a,0xffff0000],[(0xa0a0a0a,0xaaaaaaaa,0xf0f0f0f0),(0xff0aff0a,0xa0a0a0a,0xff00ff00)],[0],[]),
  ([0xfc00fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[(0xfcfcfcfc,0xcccccccc,0xf0f0f0f0),(0xfc00fc,0xfcfcfcfc,0xff00ff00)],[],[])
]
def g5_L5 : Array W5Node := Array.mk [
  ([0x88888888,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0x88888888,0xaaaaaaaa,0xcccccccc)],[0, 1, 2, 3],[(0,0),(1,0)]),
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0xeeeeeeee,0xaaaaaaaa,0xcccccccc)],[0, 1],[]),
  ([0x22222222,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0x22222222,0xaaaaaaaa,0xcccccccc)],[0, 1],[(0,1)]),
  ([0x44444444,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0x44444444,0xaaaaaaaa,0xcccccccc)],[0, 1],[(0,1)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000],[(0xfafafafa,0xaaaaaaaa,0xf0f0f0f0)],[0, 1, 2],[]),
  ([0xaa00aa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0xaa00aa,0xaaaaaaaa,0xff00ff00)],[0, 2, 3],[(1,2)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000],[(0xfcfcfcfc,0xcccccccc,0xf0f0f0f0)],[3],[(0,3)]),
  ([0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0xcc00cc,0xcccccccc,0xff00ff00)],[0, 1, 3],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000],[(0xfff0fff0,0xf0f0f0f0,0xff00ff00)],[2],[])
]
def g5_L6 : Array W5Node := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[],[0, 1, 2, 3],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5),(1,6),(1,7)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_4_0 : checkBlockW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 4 g5_L4 (Array.mk []) 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_4 : ∀ i < g5_L4.size, checkNodeW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 4 g5_L4 (Array.mk []) i = true :=
  fun i hi => checkBlockW5_at g5_chk_4_0 i (Nat.zero_le _) ((show g5_L4.size = 4 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_5_0 : checkBlockW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 5 g5_L5 g5_L4 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_5 : ∀ i < g5_L5.size, checkNodeW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 5 g5_L5 g5_L4 i = true :=
  fun i hi => checkBlockW5_at g5_chk_5_0 i (Nat.zero_le _) ((show g5_L5.size = 9 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_6_0 : checkBlockW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 6 g5_L6 g5_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_6 : ∀ i < g5_L6.size, checkNodeW5 goal5 4 2 g5_pow cfLBs cfMasks cfB0s cfStocks 6 g5_L6 g5_L5 i = true :=
  fun i hi => checkBlockW5_at g5_chk_6_0 i (Nat.zero_le _) ((show g5_L6.size = 1 by rfl) ▸ hi)
theorem g5_L4_sound : ∀ i < g5_L4.size, ¬ live (basicOps 32) goal5 4 (g5_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound (fun j hj => by simp at hj) g5_chk_4
theorem g5_L5_sound : ∀ i < g5_L5.size, ¬ live (basicOps 32) goal5 5 (g5_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound g5_L4_sound g5_chk_5
theorem g5_L6_sound : ∀ i < g5_L6.size, ¬ live (basicOps 32) goal5 6 (g5_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound g5_L5_sound g5_chk_6
theorem g5_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 goal5 ws) = [rows5] := by decide +kernel
theorem g5_top_match : sameSet (rows5.map (actB 32 (g5_pow[0]?.getD []))) (g5_L6[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem no_build : ¬ build (basicOps 32) goal5 6 rows5.toFinset :=
  no_build_of_top g5_G_valid (by decide) g5_sublists g5_top_match (g5_L6_sound 0 (by decide))
end pg5_0_ns
def pg5_0_goal : BitVec 32 := pg5_0_ns.goal5
theorem pg5_0_no_build : ¬ build (basicOps 32) pg5_0_goal 6 rows5.toFinset := pg5_0_ns.no_build
namespace pg5_1_ns
def goal5 : BitVec 32 := 0xfeeafce8
def g5_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def g5_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648]
def g5_s1 : List ℕ := [0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15, 16, 17, 20, 21, 18, 19, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31]
def g5_p1 : List ℕ := [1, 2, 16, 32, 4, 8, 64, 128, 256, 512, 4096, 8192, 1024, 2048, 16384, 32768, 65536, 131072, 1048576, 2097152, 262144, 524288, 4194304, 8388608, 16777216, 33554432, 268435456, 536870912, 67108864, 134217728, 1073741824, 2147483648]
def g5_idx : Array (List ℕ) := Array.mk [g5_s0, g5_s1]
def g5_pow : Array (List ℕ) := Array.mk [g5_p0, g5_p1]
def g5_inv : Array ℕ := Array.mk [0, 1]
theorem g5_G_valid : (List.range 2).all (symValid 32 2 g5_idx g5_pow g5_inv goal5) = true := by decide +kernel
def cfMask0 : BitVec 32 := 0xff00ff
def cfStock0 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def cfIdx0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23]
def cfMask1 : BitVec 32 := 0xffff
def cfStock1 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def cfIdx1 : List ℕ := [0, 2, 4, 6, 1, 3, 5, 7, 8, 10, 12, 14, 9, 11, 13, 15]
def cfMask2 : BitVec 32 := 0xffff0000
def cfStock2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def cfIdx2 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def cfMask3 : BitVec 32 := 0x33333333
def cfStock3 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def cfIdx3 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29]
def cfMask4 : BitVec 32 := 0xf0f0f0f
def cfStock4 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def cfIdx4 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27]
def cfLBs : Array ℕ := Array.mk [5, 5, 5, 4, 4]
def cfMasks : Array (BitVec 32) := Array.mk [cfMask0, cfMask1, cfMask2, cfMask3, cfMask4]
def cfB0s : Array ℕ := Array.mk [0, 0, 16, 0, 0]
def cfStocks : Array (List (BitVec 32)) := Array.mk [cfStock0, cfStock1, cfStock2, cfStock3, cfStock4]
theorem cf_specs :
  (cfIdx0.length = 16 ∧ (∀ idx ∈ cfIdx0, idx < 32) ∧ (∀ idx ∈ cfIdx0, cfMask0.getLsbD idx = true) ∧ projS 16 cfIdx0 goal5 = b4_0_goal ∧ cfStock0.all (fun w => rows4.contains (projS 16 cfIdx0 w)) = true) ∧
  (cfIdx1.length = 16 ∧ (∀ idx ∈ cfIdx1, idx < 32) ∧ (∀ idx ∈ cfIdx1, cfMask1.getLsbD idx = true) ∧ projS 16 cfIdx1 goal5 = b4_3_goal ∧ cfStock1.all (fun w => rows4.contains (projS 16 cfIdx1 w)) = true) ∧
  (cfIdx2.length = 16 ∧ (∀ idx ∈ cfIdx2, idx < 32) ∧ (∀ idx ∈ cfIdx2, cfMask2.getLsbD idx = true) ∧ projS 16 cfIdx2 goal5 = b4_1_goal ∧ cfStock2.all (fun w => rows4.contains (projS 16 cfIdx2 w)) = true) ∧
  (cfIdx3.length = 16 ∧ (∀ idx ∈ cfIdx3, idx < 32) ∧ (∀ idx ∈ cfIdx3, cfMask3.getLsbD idx = true) ∧ projS 16 cfIdx3 goal5 = b4_2_goal ∧ cfStock3.all (fun w => rows4.contains (projS 16 cfIdx3 w)) = true) ∧
  (cfIdx4.length = 16 ∧ (∀ idx ∈ cfIdx4, idx < 32) ∧ (∀ idx ∈ cfIdx4, cfMask4.getLsbD idx = true) ∧ projS 16 cfIdx4 goal5 = b4_2_goal ∧ cfStock4.all (fun w => rows4.contains (projS 16 cfIdx4 w)) = true) := by decide +kernel
theorem cf_sound (c fuel : ℕ) (hc : c < 5) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup)
    (hchk : checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := cf_specs
  match c with
  | 0 => exact checkCofClose32_sound_aux goal5 cfIdx0 h0.1 h0.2.1 cfMask0 h0.2.2.1 0 cfStock0 b4_0_goal 5 (by decide) h0.2.2.2.1 h0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux goal5 cfIdx1 h1.1 h1.2.1 cfMask1 h1.2.2.1 0 cfStock1 b4_3_goal 5 (by decide) h1.2.2.2.1 h1.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux goal5 cfIdx2 h2.1 h2.2.1 cfMask2 h2.2.2.1 16 cfStock2 b4_1_goal 5 (by decide) h2.2.2.2.1 h2.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux goal5 cfIdx3 h3.1 h3.2.1 cfMask3 h3.2.2.1 0 cfStock3 b4_2_goal 4 (by decide) h3.2.2.2.1 h3.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux goal5 cfIdx4 h4.1 h4.2.1 cfMask4 h4.2.2.1 0 cfStock4 b4_2_goal 4 (by decide) h4.2.2.2.1 h4.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | c + 5 => omega
def g5_L4 : Array W5Node := Array.mk [
  ([0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xffaaffaa,0xffff0000],[(0xeeeeeeee,0xaaaaaaaa,0xcccccccc),(0xffaaffaa,0xaaaaaaaa,0xff00ff00)],[1, 2],[]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff0aff0a,0xffff0000],[(0xa0a0a0a,0xaaaaaaaa,0xf0f0f0f0),(0xff0aff0a,0xa0a0a0a,0xff00ff00)],[],[]),
  ([0xa0a0a0a,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffff0000],[(0xa0a0a0a,0xaaaaaaaa,0xf0f0f0f0),(0xffaaffaa,0xaaaaaaaa,0xff00ff00)],[1],[]),
  ([0xfc00fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffff0000],[(0xfcfcfcfc,0xcccccccc,0xf0f0f0f0),(0xfc00fc,0xfcfcfcfc,0xff00ff00)],[],[])
]
def g5_L5 : Array W5Node := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0xeeeeeeee,0xaaaaaaaa,0xcccccccc)],[1, 2],[(0,0)]),
  ([0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[(0xa0a0a0a,0xaaaaaaaa,0xf0f0f0f0)],[0, 1, 2, 4],[(0,1),(0,2)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffff0000],[(0xffaaffaa,0xaaaaaaaa,0xff00ff00)],[0, 1, 2],[(0,0),(0,2),(1,0),(1,2)]),
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000],[(0xfcfcfcfc,0xcccccccc,0xf0f0f0f0)],[0, 1, 2, 3],[(0,3)])
]
def g5_L6 : Array W5Node := Array.mk [
  ([0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000],[],[0, 1, 2, 3, 4],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_4_0 : checkBlockW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 4 g5_L4 (Array.mk []) 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_4 : ∀ i < g5_L4.size, checkNodeW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 4 g5_L4 (Array.mk []) i = true :=
  fun i hi => checkBlockW5_at g5_chk_4_0 i (Nat.zero_le _) ((show g5_L4.size = 4 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_5_0 : checkBlockW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 5 g5_L5 g5_L4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_5 : ∀ i < g5_L5.size, checkNodeW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 5 g5_L5 g5_L4 i = true :=
  fun i hi => checkBlockW5_at g5_chk_5_0 i (Nat.zero_le _) ((show g5_L5.size = 4 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g5_chk_6_0 : checkBlockW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 6 g5_L6 g5_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g5_chk_6 : ∀ i < g5_L6.size, checkNodeW5 goal5 5 2 g5_pow cfLBs cfMasks cfB0s cfStocks 6 g5_L6 g5_L5 i = true :=
  fun i hi => checkBlockW5_at g5_chk_6_0 i (Nat.zero_le _) ((show g5_L6.size = 1 by rfl) ▸ hi)
theorem g5_L4_sound : ∀ i < g5_L4.size, ¬ live (basicOps 32) goal5 4 (g5_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound (fun j hj => by simp at hj) g5_chk_4
theorem g5_L5_sound : ∀ i < g5_L5.size, ¬ live (basicOps 32) goal5 5 (g5_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound g5_L4_sound g5_chk_5
theorem g5_L6_sound : ∀ i < g5_L6.size, ¬ live (basicOps 32) goal5 6 (g5_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) g5_G_valid cf_sound g5_L5_sound g5_chk_6
theorem g5_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 goal5 ws) = [rows5] := by decide +kernel
theorem g5_top_match : sameSet (rows5.map (actB 32 (g5_pow[0]?.getD []))) (g5_L6[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem no_build : ¬ build (basicOps 32) goal5 6 rows5.toFinset :=
  no_build_of_top g5_G_valid (by decide) g5_sublists g5_top_match (g5_L6_sound 0 (by decide))
end pg5_1_ns
def pg5_1_goal : BitVec 32 := pg5_1_ns.goal5
theorem pg5_1_no_build : ¬ build (basicOps 32) pg5_1_goal 6 rows5.toFinset := pg5_1_ns.no_build
def pg5_2_goal : BitVec 32 := 0xfeeefac8
def pg5_2_idxs4 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 8, 9, 10, 11, 24, 25, 26, 27]
theorem pg5_2_no_build : ¬ build (basicOps 32) pg5_2_goal 5 rows5.toFinset :=
  no_build_of_proj (by decide) rows5 rows4 pg5_2_goal b4_0_goal pg5_2_idxs4 2 2 6
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    b4_0_no_build
def pg5_3_goal : BitVec 32 := 0xeeeaeee8
def pg5_3_idxs4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
theorem pg5_3_no_build : ¬ build (basicOps 32) pg5_3_goal 5 rows5.toFinset :=
  no_build_of_proj (by decide) rows5 rows4 pg5_3_goal b4_3_goal pg5_3_idxs4 4 1 17
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    b4_3_no_build
def pg5_4_goal : BitVec 32 := 0xfffefeee
def pg5_4_idxs4 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]
theorem pg5_4_no_build : ¬ build (basicOps 32) pg5_4_goal 5 rows5.toFinset :=
  no_build_of_proj (by decide) rows5 rows4 pg5_4_goal b4_1_goal pg5_4_idxs4 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    b4_1_no_build
def pg5_5_goal : BitVec 32 := 0xeeeaeee0
def pg5_5_idxs4 : List ℕ := [0, 1, 8, 9, 2, 3, 10, 11, 16, 17, 24, 25, 18, 19, 26, 27]
theorem pg5_5_no_build : ¬ build (basicOps 32) pg5_5_goal 4 rows5.toFinset :=
  no_build_of_proj (by decide) rows5 rows4 pg5_5_goal b4_2_goal pg5_5_idxs4 2 1 5
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    b4_2_no_build
def pg5_6_goal : BitVec 32 := 0xeeeaece0
def pg5_6_idxs4 : List ℕ := [0, 1, 4, 5, 2, 3, 6, 7, 16, 17, 20, 21, 18, 19, 22, 23]
theorem pg5_6_no_build : ¬ build (basicOps 32) pg5_6_goal 4 rows5.toFinset :=
  no_build_of_proj (by decide) rows5 rows4 pg5_6_goal b4_2_goal pg5_6_idxs4 3 2 10
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    b4_2_no_build

-- 6-variable normalized cofactor-replay pruning
def nrmM64 (m : BitVec 64) (b0 : ℕ) (u : BitVec 64) : BitVec 64 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM64 (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 32 idxs (nrmM64 m b0 u) = projS 32 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]; exact projS_mask 32 idxs m hm u
  · simp only [ite_true]; rw [projS_mask 32 idxs m hm (~~~u), projS_not 32 (by decide) idxs hlen hlt u]

abbrev W6Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay64 (m : BitVec 64) (b0 : ℕ) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => nrmM64 m b0 t == 0 || bank.contains (nrmM64 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay64 m b0 (v :: bank) rest targets

theorem checkReplay64_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb; intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne; rw [← projS_nrmM64 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 32 (f a) (f b) := projS_ops 32 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 32 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 32 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 32 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 32 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed64 (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded64 (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM64 m b0 w
    let needed' := if needed.contains pw then addNeed64 stock (addNeed64 stock needed (nrmM64 m b0 a)) (nrmM64 m b0 b) else needed
    buildNeeded64 m b0 stock rest needed'

def buildSteps64 (m : BitVec 64) (b0 : ℕ) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM64 m b0 w
    let pa := nrmM64 m b0 a
    let pb := nrmM64 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps64 m b0 needed rest (pw :: bank)
    else
      buildSteps64 m b0 needed rest bank

def checkCofClose64 (L fuel : ℕ) (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM64 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem L then
    let start := nxt.foldl (fun acc u => addNeed64 stock acc (nrmM64 m b0 u)) []
    if Nat.blt (start.length + rem) L then
      let needed := buildNeeded64 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) L then
        let steps := buildSteps64 m b0 needed hist stock
        Nat.blt (steps.length + rem) L && checkReplay64 m b0 stock steps nxt
      else false
    else false
  else false

def goal6 : BitVec 64 := 0xfffefffefefaee00
def rows6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def g6_s0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def g6_p0 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648, 4294967296, 8589934592, 17179869184, 34359738368, 68719476736, 137438953472, 274877906944, 549755813888, 1099511627776, 2199023255552, 4398046511104, 8796093022208, 17592186044416, 35184372088832, 70368744177664, 140737488355328, 281474976710656, 562949953421312, 1125899906842624, 2251799813685248, 4503599627370496, 9007199254740992, 18014398509481984, 36028797018963968, 72057594037927936, 144115188075855872, 288230376151711744, 576460752303423488, 1152921504606846976, 2305843009213693952, 4611686018427387904, 9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0]
def g6_inv : Array ℕ := Array.mk [0]
theorem g6_G_valid : (List.range 1).all (symValid 64 1 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel
def cf6Mask0 : BitVec 64 := 0x5555555555555555
def cf6Stock0 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def cf6Idx0 : List ℕ := [0, 4, 32, 36, 2, 6, 34, 38, 8, 12, 40, 44, 10, 14, 42, 46, 16, 20, 48, 52, 18, 22, 50, 54, 24, 28, 56, 60, 26, 30, 58, 62]
def cf6Mask1 : BitVec 64 := 0x0f0f0f0f0f0f0f0f
def cf6Stock1 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def cf6Idx1 : List ℕ := [0, 1, 8, 9, 32, 33, 40, 41, 2, 3, 10, 11, 34, 35, 42, 43, 16, 17, 24, 25, 48, 49, 56, 57, 18, 19, 26, 27, 50, 51, 58, 59]
def cf6Mask2 : BitVec 64 := 0x3333333333333333
def cf6Stock2 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def cf6Idx2 : List ℕ := [0, 1, 32, 33, 4, 5, 36, 37, 16, 17, 48, 49, 20, 21, 52, 53, 8, 9, 40, 41, 12, 13, 44, 45, 24, 25, 56, 57, 28, 29, 60, 61]
def cf6Mask3 : BitVec 64 := 0x0000ffff0000ffff
def cf6Stock3 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def cf6Idx3 : List ℕ := [0, 32, 8, 40, 1, 33, 9, 41, 2, 34, 10, 42, 3, 35, 11, 43, 4, 36, 12, 44, 5, 37, 13, 45, 6, 38, 14, 46, 7, 39, 15, 47]
def cf6Mask4 : BitVec 64 := 0xffff0000ffff0000
def cf6Stock4 : List (BitVec 64) := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]
def cf6Idx4 : List ℕ := [16, 17, 20, 21, 18, 19, 22, 23, 24, 25, 28, 29, 26, 27, 30, 31, 48, 49, 52, 53, 50, 51, 54, 55, 56, 57, 60, 61, 58, 59, 62, 63]
def cf6Mask5 : BitVec 64 := 0x00ff00ff00ff00ff
def cf6Stock5 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def cf6Idx5 : List ℕ := [0, 32, 16, 48, 1, 33, 17, 49, 4, 36, 20, 52, 5, 37, 21, 53, 2, 34, 18, 50, 3, 35, 19, 51, 6, 38, 22, 54, 7, 39, 23, 55]
def cf6Mask6 : BitVec 64 := 0x00000000ffffffff
def cf6Stock6 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def cf6Idx6 : List ℕ := [0, 8, 16, 24, 1, 9, 17, 25, 4, 12, 20, 28, 5, 13, 21, 29, 2, 10, 18, 26, 3, 11, 19, 27, 6, 14, 22, 30, 7, 15, 23, 31]
def cf6LBs : Array ℕ := Array.mk [7, 7, 6, 6, 6, 5, 5]
def cf6Masks : Array (BitVec 64) := Array.mk [cf6Mask0, cf6Mask1, cf6Mask2, cf6Mask3, cf6Mask4, cf6Mask5, cf6Mask6]
def cf6B0s : Array ℕ := Array.mk [0, 0, 0, 0, 16, 0, 0]
def cf6Stocks : Array (List (BitVec 64)) := Array.mk [cf6Stock0, cf6Stock1, cf6Stock2, cf6Stock3, cf6Stock4, cf6Stock5, cf6Stock6]

theorem cf6_specs :
    (cf6Idx0.length = 32 ∧ (∀ idx ∈ cf6Idx0, idx < 64) ∧ (∀ idx ∈ cf6Idx0, cf6Mask0.getLsbD idx = true) ∧ projS 32 cf6Idx0 goal6 = pg5_0_goal ∧ cf6Stock0.all (fun w => rows5.contains (projS 32 cf6Idx0 w)) = true) ∧
    (cf6Idx1.length = 32 ∧ (∀ idx ∈ cf6Idx1, idx < 64) ∧ (∀ idx ∈ cf6Idx1, cf6Mask1.getLsbD idx = true) ∧ projS 32 cf6Idx1 goal6 = pg5_1_goal ∧ cf6Stock1.all (fun w => rows5.contains (projS 32 cf6Idx1 w)) = true) ∧
    (cf6Idx2.length = 32 ∧ (∀ idx ∈ cf6Idx2, idx < 64) ∧ (∀ idx ∈ cf6Idx2, cf6Mask2.getLsbD idx = true) ∧ projS 32 cf6Idx2 goal6 = pg5_2_goal ∧ cf6Stock2.all (fun w => rows5.contains (projS 32 cf6Idx2 w)) = true) ∧
    (cf6Idx3.length = 32 ∧ (∀ idx ∈ cf6Idx3, idx < 64) ∧ (∀ idx ∈ cf6Idx3, cf6Mask3.getLsbD idx = true) ∧ projS 32 cf6Idx3 goal6 = pg5_3_goal ∧ cf6Stock3.all (fun w => rows5.contains (projS 32 cf6Idx3 w)) = true) ∧
    (cf6Idx4.length = 32 ∧ (∀ idx ∈ cf6Idx4, idx < 64) ∧ (∀ idx ∈ cf6Idx4, cf6Mask4.getLsbD idx = true) ∧ projS 32 cf6Idx4 goal6 = pg5_4_goal ∧ cf6Stock4.all (fun w => rows5.contains (projS 32 cf6Idx4 w)) = true) ∧
    (cf6Idx5.length = 32 ∧ (∀ idx ∈ cf6Idx5, idx < 64) ∧ (∀ idx ∈ cf6Idx5, cf6Mask5.getLsbD idx = true) ∧ projS 32 cf6Idx5 goal6 = pg5_5_goal ∧ cf6Stock5.all (fun w => rows5.contains (projS 32 cf6Idx5 w)) = true) ∧
    (cf6Idx6.length = 32 ∧ (∀ idx ∈ cf6Idx6, idx < 64) ∧ (∀ idx ∈ cf6Idx6, cf6Mask6.getLsbD idx = true) ∧ projS 32 cf6Idx6 goal6 = pg5_6_goal ∧ cf6Stock6.all (fun w => rows5.contains (projS 32 cf6Idx6 w)) = true) := by
  decide +kernel

theorem checkCofClose64_sound_aux (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 32) (L : ℕ) (hgnz : g ≠ 0)
    (hg : projS 32 idxs goal6 = g)
    (hstock : stock.all (fun w => rows5.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g (L - 1) rows5.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 L fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk; dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]; apply Finset.card_le_card; intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows5.toFinset := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu; have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1; exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

theorem checkCofClose64_sound (c fuel : ℕ) (hc : c < 7)
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup)
    (hchk : checkCofClose64 (cf6LBs[c]?.getD 0) fuel (cf6Masks[c]?.getD 0) (cf6B0s[c]?.getD 0) (cf6Stocks[c]?.getD []) hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := cf6_specs
  match c with
  | 0 => exact checkCofClose64_sound_aux cf6Idx0 h0.1 h0.2.1 cf6Mask0 h0.2.2.1 0 cf6Stock0 pg5_0_goal 7 (by decide) h0.2.2.2.1 h0.2.2.2.2 pg5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_sound_aux cf6Idx1 h1.1 h1.2.1 cf6Mask1 h1.2.2.1 0 cf6Stock1 pg5_1_goal 7 (by decide) h1.2.2.2.1 h1.2.2.2.2 pg5_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux cf6Idx2 h2.1 h2.2.1 cf6Mask2 h2.2.2.1 0 cf6Stock2 pg5_2_goal 6 (by decide) h2.2.2.2.1 h2.2.2.2.2 pg5_2_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux cf6Idx3 h3.1 h3.2.1 cf6Mask3 h3.2.2.1 0 cf6Stock3 pg5_3_goal 6 (by decide) h3.2.2.2.1 h3.2.2.2.2 pg5_3_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_sound_aux cf6Idx4 h4.1 h4.2.1 cf6Mask4 h4.2.2.1 16 cf6Stock4 pg5_4_goal 6 (by decide) h4.2.2.2.1 h4.2.2.2.2 pg5_4_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_sound_aux cf6Idx5 h5.1 h5.2.1 cf6Mask5 h5.2.2.1 0 cf6Stock5 pg5_5_goal 5 (by decide) h5.2.2.2.1 h5.2.2.2.2 pg5_5_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose64_sound_aux cf6Idx6 h6.1 h6.2.1 cf6Mask6 h6.2.2.1 0 cf6Stock6 pg5_6_goal 5 (by decide) h6.2.2.2.1 h6.2.2.2.2 pg5_6_no_build fuel hist nxt hnd hchk
  | c + 7 => omega

def checkChildW6 (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  targets.any (fun t => sameSet nxt t) ||
  cfs.any (fun c => checkCofClose64 (cf6LBs[c]?.getD 0) (k - 1) (cf6Masks[c]?.getD 0) (cf6B0s[c]?.getD 0) (cf6Stocks[c]?.getD []) hist nxt)

def checkStepW6 (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 goal6 (w :: r) || checkChildW6 k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 goal6 (w :: a :: r) || checkChildW6 k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 goal6 (w :: b :: r) || checkChildW6 k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 goal6 (w :: a :: b :: r) || checkChildW6 k cfs targets h' (w :: a :: b :: r))

def checkNodeW6 (k : ℕ) (cur prev : Array W6Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal6) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c 7) &&
    hs.all (fun p => Nat.blt p.1 1 && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW6 k extra cfs targets hist a b r)

def checkBlockW6 (k : ℕ) (cur prev : Array W6Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW6 k cur prev (start + m) && checkBlockW6 k cur prev start m

theorem checkBlockW6_at {k start m : ℕ} {cur prev : Array W6Node}
    (h : checkBlockW6 k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW6 k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW6, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W6 {k i : ℕ} {cur prev : Array W6Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW6 k cur prev i = true) :
    ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW6 at hchk; rw [hget] at hchk ⊢; dsimp only at hchk ⊢; simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) goal6 (k - 1) t.toFinset := by
    intro t ht; obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht; obtain ⟨hg, hc⟩ := hhs (g, c) hmem; intro hlive
    have hinv_lt := (actB_spec g6_G_valid g hg).1; have hinv_g := (actB_spec g6_G_valid (g6_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD [])) (actB_inj g6_G_valid _ hinv_lt) hinv_g (actB_ops g6_G_valid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[g]?.getD []))).toFinset.image
        (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]; constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left g6_G_valid g hg v]
      · intro hu; exact ⟨actB 64 (g6_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left g6_G_valid g hg u⟩
    rw [hset] at himg; exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · exact hng (List.mem_toFinset.mp (done.symm ▸ Finset.mem_singleton_self _))
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 64} (hpair : (a, b, r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps 64 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr; exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 64) goal6 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail; rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 goal6 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair; unfold checkStepW6 at hstep; dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 64 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw; simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq; simp only [List.length_cons] at plen
      have close (hc : checkChildW6 k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW6 at hc; simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨t, ht, hss⟩) | ⟨c, hcm, hcc⟩
        · omega
        · rw [sameSet_sound hss] at htail; exact htargets t ht htail
        · exact checkCofClose64_sound c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcc htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept; have h1 := hw.1.1; rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1; exact close h1
      · have h1 := hw.1.2; have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1; rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2; exact close h2
      · have h1 := hw.1.2; have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2; rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2; exact close h2
      · have h1 := hw.2; have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1; rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1; exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 64 a b ▸ hz)

theorem level_sound_W6 {k : ℕ} {cur prev : Array W6Node}
    (hk : 0 < k)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW6 k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W6 hk hi hprev (hblk i hi)

def g6_L3 : Array W6Node := Array.mk [
  ([0xffeeffeeeeeeeeee,0xfffafffafafafafa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffeeffeeeeeeeeee,0xcccccccccccccccc,0xffaaffaaaaaaaaaa),(0xfffafffafafafafa,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[]),
  ([0xf0f0f0f0f0f0f0f0,0xffeeffeeeeaaeeaa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00),(0xffeeffeeeeaaeeaa,0xcccccccccc00cc00,0xffaaffaaaaaaaaaa)],[],[]),
  ([0xff00ffff00ff00,0xeeeeeeeeeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00),(0xeeeeeeeeeeaaeeaa,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00)],[],[]),
  ([0xff00ffff00ff00,0xaaeeaaeeeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00),(0xcc00cccc00cc00,0xff00ffff00ff00,0xcccccccccccccccc),(0xaaeeaaeeeeaaeeaa,0xcc00cccc00cc00,0xaaaaaaaaaaaaaaaa)],[],[])
]
def g6_L4 : Array W6Node := Array.mk [
  ([0xff00ff00ff00ff00,0xffeeffeeeeeeeeee,0xfffafffafafafafa,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffeeffeeeeeeeeee,0xcccccccccccccccc,0xffaaffaaaaaaaaaa),(0xfffafffafafafafa,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa)],[],[(0,0)]),
  ([0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa,0xffeeffeeeeeeeeee,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffeeffeeeeeeeeee,0xcccccccccccccccc,0xffaaffaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[(0,0)]),
  ([0x44004444444444,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0x44004444444444,0xcccccccccccccccc,0xffaaffaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[]),
  ([0xcccccccccccccccc,0xffaaffaaaaaaaaaa,0xfffafffafafafafa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xfffafffafafafafa,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[(0,0)]),
  ([0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00)],[],[(0,1)]),
  ([0x3333333333003300,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffcccc00cc00,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccc00cc00,0xffccffcccccccccc,0xffffffffff00ff00)],[],[(0,1)]),
  ([0x33003333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x33003333003300,0xffccffcccccccccc,0xffffffffff00ff00)],[],[]),
  ([0xeeeeeeeeeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00),(0xeeeeeeeeeeaaeeaa,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00)],[],[(0,1),(0,2)]),
  ([0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00)],[],[(0,2)]),
  ([0xff00ffff00ff00,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00)],[],[]),
  ([0xcc00cccc00cc00,0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00),(0xcc00cccc00cc00,0xff00ffff00ff00,0xcccccccccccccccc)],[],[(0,3)]),
  ([0x33003333003300,0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00),(0x33003333003300,0xff00ffff00ff00,0xcccccccccccccccc)],[],[])
]
def g6_L5 : Array W6Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffffcccccccc,0xffffffffff00ff00],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2, 5],[]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffffccffcc,0xffccffccffccffcc,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffffccffcc)],[],[]),
  ([0xffccffcc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffffffff0000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffccffcc,0xffccffccffccffcc,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff33003300],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffff33003300,0x3300330033003300,0xffffffff00000000),(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000)],[],[]),
  ([0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff33ff33ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000),(0xff33ff33ff00ff00,0x3333333300000000,0xff00ff00ff00ff00)],[],[]),
  ([0x3300330033003300,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffff00ff00],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[]),
  ([0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xffeeffeeeeeeeeee,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffeeffeeeeeeeeee,0xcccccccccccccccc,0xffaaffaaaaaaaaaa)],[],[(0,0),(0,1)]),
  ([0x44004444444444,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0x44004444444444,0xcccccccccccccccc,0xffaaffaaaaaaaaaa)],[],[(0,2)]),
  ([0xcccccccccccccccc,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xfffafffafafafafa,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xfffafffafafafafa,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa)],[],[(0,0),(0,3)]),
  ([0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[1],[(0,1),(0,2),(0,3),(0,4),(0,5)]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0],[(0,6),(0,7)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00)],[],[(0,4),(0,6),(0,8),(0,9)]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00)],[],[(0,5),(0,7),(0,10)]),
  ([0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00)],[0],[(0,11),(0,12)]),
  ([0xff00ffff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ffff00ff00,0xff00ff0000000000,0xffffffffff00ff00)],[],[(0,7),(0,9),(0,10)]),
  ([0xeeeeeeeeeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00),(0xeeeeeeeeeeaaeeaa,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00)],[],[(0,8)]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[]),
  ([0xffff0000,0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[],[])
]
def g6_L6 : Array W6Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[5, 6],[(0,0)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2, 6],[(0,0)]),
  ([0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffccffcc],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffffccffcc,0xffccffccffccffcc,0xffffffff00000000)],[],[(0,1)]),
  ([0xffccffcc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffccffcc,0xffccffccffccffcc,0xffffffff00000000)],[],[(0,2)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffffffff00000000,0xffffffffffff0000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 6],[(0,2)]),
  ([0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffff33003300],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffff33003300,0x3300330033003300,0xffffffff00000000)],[],[(0,1),(0,3)]),
  ([0x3300330033003300,0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000)],[],[(0,1),(0,3),(0,4),(0,5)]),
  ([0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2, 5],[(0,5)]),
  ([0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[]),
  ([0xffff0000,0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc,0xffffffffff00ff00],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2, 5],[(0,0)]),
  ([0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff00ff00000000,0xff00ff00ff00ff00,0xffffffff00000000)],[2],[]),
  ([0xff00ff00cc00cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xff00ff00cc00cc,0xff00ff00ff00ff00,0xffffffffcccccccc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffcccccccc,0xffffffffffff0000],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[]),
  ([0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff33ff33ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000),(0xff33ff33ff00ff00,0x3333333300000000,0xff00ff00ff00ff00)],[],[(0,1),(0,4)]),
  ([0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffffff00ff00],[(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[2, 5],[(0,5)]),
  ([0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffaaffaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xff00ff0000000000)],[1, 5, 6],[(0,6),(0,7),(0,8),(0,9)]),
  ([0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000)],[0, 5, 6],[(0,10)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffcccccccccc,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffccffcccccccccc,0xcccccccccccccccc,0xff00ff0000000000)],[],[(0,11)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xfff0fff0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xfff0fff0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000)],[0, 5, 6],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xffff0000ffff0000,0xffffffffff00ff00],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 5],[(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xcccccccccc00cc00,0xcccccccccccccccc,0xffffffffff00ff00)],[],[(0,1),(0,12),(0,16)]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00)],[0],[(0,17),(0,18)]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00)],[],[]),
  ([0x3333333333003300,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0x3333333333003300,0xcccccccccccccccc,0xffffffffff00ff00)],[2],[(0,13)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffff00ff00,0xffffffffffff0000],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 6],[(0,17)]),
  ([0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffff00ff00],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[2, 6],[(0,18)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccccccccffccffcc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xccccccccffccffcc,0xff00ff00,0xcccccccccccccccc)],[],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffff00ff00,0xff00ff00,0xffffffff00000000)],[2, 5],[(0,1)]),
  ([0xff00ff00,0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xff00ff00000000,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 5, 6],[(0,14)]),
  ([0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[6],[]),
  ([0xff00ff00,0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000),(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[6],[]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xccffccffcccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff00000000,0xff00ff00ff00ff00,0xffffffff00000000),(0xccffccffcccccccc,0xff00ff00000000,0xcccccccccccccccc)],[],[])
]
def g6_L7 : Array W6Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000],[(0xffccffccffccffcc,0xcccccccccccccccc,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4, 5, 6],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]),
  ([0x3300330033003300,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0x3300330033003300,0xcccccccccccccccc,0xff00ff00ff00ff00)],[0, 1, 2, 3, 4, 5, 6],[(0,7),(0,8),(0,9),(0,10),(0,11)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc],[(0xffffffffcccccccc,0xcccccccccccccccc,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,0),(0,3),(0,12),(0,13),(0,14),(0,15),(0,16)]),
  ([0x3333333300000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0x3333333300000000,0xcccccccccccccccc,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,8),(0,17),(0,18)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff0000000000,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,19),(0,20),(0,21),(0,22),(0,23)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00],[(0xffffffffff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,1),(0,3),(0,9),(0,12),(0,18),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29)]),
  ([0xff00ff00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff00,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,2),(0,30),(0,31),(0,32),(0,33),(0,34)]),
  ([0xff00ff00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0xff00ff00000000,0xff00ff00ff00ff00,0xffffffff00000000)],[0, 1, 2, 3, 4, 5, 6],[(0,13),(0,31),(0,32),(0,35)]),
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000,0xffffffffffff0000],[(0xffffffffffff0000,0xffff0000ffff0000,0xffffffff00000000)],[0, 1, 2, 3, 4, 6],[(0,5),(0,10),(0,15),(0,28),(0,33)]),
  ([0xffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000],[(0xffff0000,0xffff0000ffff0000,0xffffffff00000000)],[0, 1, 2, 3, 4, 6],[(0,6),(0,11),(0,16),(0,29),(0,34)])
]
def g6_L8 : Array W6Node := Array.mk [
  ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[],[0, 1, 2, 3, 4],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_3_0 : checkBlockW6 3 g6_L3 (Array.mk []) 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_3 : ∀ i < g6_L3.size, checkNodeW6 3 g6_L3 (Array.mk []) i = true :=
  fun i hi => checkBlockW6_at g6_chk_3_0 i (Nat.zero_le _) ((show g6_L3.size = 4 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 4 g6_L4 g6_L3 0 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 4 g6_L4 g6_L3 i = true :=
  fun i hi => checkBlockW6_at g6_chk_4_0 i (Nat.zero_le _) ((show g6_L4.size = 13 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 5 g6_L5 g6_L4 0 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 5 g6_L5 g6_L4 i = true :=
  fun i hi => checkBlockW6_at g6_chk_5_0 i (Nat.zero_le _) ((show g6_L5.size = 19 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 6 g6_L6 g6_L5 0 25 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_25 : checkBlockW6 6 g6_L6 g6_L5 25 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : i < 36 := (show g6_L6.size = 36 by rfl) ▸ hi
  by_cases h0 : i < 25
  · exact checkBlockW6_at g6_chk_6_0 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_6_25 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 7 g6_L7 g6_L6 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 7 g6_L7 g6_L6 i = true :=
  fun i hi => checkBlockW6_at g6_chk_7_0 i (Nat.zero_le _) ((show g6_L7.size = 10 by rfl) ▸ hi)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 8 g6_L8 g6_L7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 8 g6_L8 g6_L7 i = true :=
  fun i hi => checkBlockW6_at g6_chk_8_0 i (Nat.zero_le _) ((show g6_L8.size = 1 by rfl) ▸ hi)
theorem g6_L3_sound : ∀ i < g6_L3.size, ¬ live (basicOps 64) goal6 3 (g6_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) (fun j hj => by simp at hj) g6_chk_3
theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) g6_L3_sound g6_chk_4
theorem g6_L5_sound : ∀ i < g6_L5.size, ¬ live (basicOps 64) goal6 5 (g6_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) g6_L4_sound g6_chk_5
theorem g6_L6_sound : ∀ i < g6_L6.size, ¬ live (basicOps 64) goal6 6 (g6_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) g6_L5_sound g6_chk_6
theorem g6_L7_sound : ∀ i < g6_L7.size, ¬ live (basicOps 64) goal6 7 (g6_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) g6_L6_sound g6_chk_7
theorem g6_L8_sound : ∀ i < g6_L8.size, ¬ live (basicOps 64) goal6 8 (g6_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W6 (by decide) g6_L7_sound g6_chk_8

theorem g6_sublists : rows6.sublists.filter (fun ws => cover 64 jumps6 goal6 ws) = [rows6] := by decide +kernel
theorem g6_top_match : sameSet (rows6.map (actB 64 (g6_pow[0]?.getD []))) (g6_L8[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem g6_no_build : ¬ build (basicOps 64) goal6 8 rows6.toFinset :=
  no_build_of_top g6_G_valid (by decide) g6_sublists g6_top_match (g6_L8_sound 0 (by decide))

-- Two 1-variable deletions: 6v -> 7v -> 8v
def rows7 : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def goal7 : BitVec 128 := 0xfffefffefffefffefefefefafefeee00
def idxs76 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]

theorem g7_no_build : ¬ build (basicOps 128) goal7 9 rows7.toFinset :=
  no_build_of_proj (by decide) rows7 rows6 goal7 goal6 idxs76 4 1 17
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    g6_no_build

def rows8 : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def goal8 : BitVec 256 := 0xfffffffefffffffefffffefefffffefefffefffefffefffafefefefeeeee0000
def idxs87 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]

theorem g8_no_build : ¬ build (basicOps 256) goal8 10 rows8.toFinset :=
  no_build_of_proj (by decide) rows8 rows7 goal8 goal7 idxs87 3 64 72
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    g7_no_build

-- 8-variable circuit compilation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W8 := BitVec 256
abbrev basicOps8 (a b : W8) : Finset W8 := (ops 256 a b).toFinset

def holds (av : Finset W8) (z : W8) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W8} {z a : W8} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W8} {z : W8} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W8) (z : W8) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps8 a b, holds (insert w av) z

theorem reachable_not {av : Finset W8} {z : W8} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W8} {x y : W8} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W8) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W8) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W8) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W8) (hw : w ∈ basicOps8 a b) (z : W8) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps8, ops] : a &&& b ∈ basicOps8 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps8, ops] : a &&& ~~~b ∈ basicOps8 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps8, ops] : b &&& ~~~a ∈ basicOps8 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps8, ops] : a ||| b ∈ basicOps8 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W8} {x y : W8} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit8 (k : Fin 256) (z : W8) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit8 (w : List W8) (i : ℕ) (k : Fin 256) :
    (w.map (bit8 k)).getD i false = bit8 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit8]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W8) (g : Gate) : W8 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W8) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit8 k)) g = (w ++ [action w g]).map (bit8 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W8)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit8, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit8, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W8} {w : List W8} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W8) (av : Finset W8) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W8, x ||| (0 : W8) = x from fun x => BitVec.or_zero,
    show ∀ x : W8, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W8) (av : Finset W8) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit8 k))).getD out false = bit8 k goal8) :
    ∃ t, (t = goal8 ∨ t = ~~~goal8) ∧ build basicOps8 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal8 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit8, bit8] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal8 ≠ 0) zero)
    · exact False.elim ((by decide : goal8 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W8 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit8 k))).getD out false = bit8 k goal8 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W8) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
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

def F (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7)
def idxs256 : List ℕ := List.range 256

theorem sample8_ok : ∀ k : Fin 256, F (fun i => (rows8.getD i.val 0)[k.val]) = goal8[k.val] := by decide +kernel
theorem idxs256_spec : idxs256.length = 256 ∧ ∀ idx ∈ idxs256, idx < 256 := by decide +kernel
theorem projS256_goal8 : projS 256 idxs256 goal8 = goal8 := by decide +kernel
theorem projS256_rows8_sub : rows8.all (fun w => projS 256 idxs256 w == 0 || rows8.contains (projS 256 idxs256 w)) = true := by decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows8, holds rows8.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (rows8.map (bit8 k))).getD o false = bit8 k goal8 := by
    let x (i : Fin 8) : Bool := bit8 k (rows8.getD i.val 0)
    have same : List.ofFn x = rows8.map (bit8 k) := by
      apply List.ext_getElem
      · simp [rows8]
      · intro i hi hj
        have hlt : i < rows8.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows8.map (bit8 k)) = bit8 k goal8
    rw [← same, he]
    exact sample8_ok k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows8 rows8.toFinset init evaluate
  obtain ⟨s, hs, hl⟩ := compress (build_mono_k low run)
  have hpt : projS 256 idxs256 t = goal8 := by
    rcases ht with rfl | rfl
    · exact projS256_goal8
    · rw [projS_not 256 (by decide) idxs256 idxs256_spec.1 idxs256_spec.2]; exact projS256_goal8
  have hb256 := live_restrict (by decide : 0 < 256) idxs256 idxs256_spec.1 idxs256_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt (by decide : goal8 ≠ 0) hl
  have hsub256 : nonZeroImg (projS 256 idxs256) s ⊆ rows8.toFinset := by
    intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS256_rows8_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact g8_no_build (build_mono_k (Nat.sub_le _ _) (build_mono_av hsub256 hb256))

theorem bridge : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = F x := by
  decide +kernel

def wg : List Gate := [
  ⟨.or, [7, 5]⟩,
  ⟨.or, [2, 1]⟩,
  ⟨.or, [9, 0]⟩,
  ⟨.or, [3, 2]⟩,
  ⟨.or, [11, 0]⟩,
  ⟨.or, [7, 1]⟩,
  ⟨.or, [13, 0]⟩,
  ⟨.and, [12, 6]⟩,
  ⟨.and, [4, 14]⟩,
  ⟨.and, [10, 8]⟩,
  ⟨.or, [15, 16]⟩,
  ⟨.or, [18, 17]⟩
]

theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval_fast : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wg, 19⟩ (List.ofFn x) = F x := by
  decide +kernel

theorem weval (x : Fin 8 → Bool) : Circuit.eval ⟨wg, 19⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  (weval_fast x).trans (bridge x).symm

end PEqualNP.Outside.L_meta_15014_aux

open PEqualNP.Outside.L_meta_15014_aux in
theorem PEqualNP.Outside.L_meta_15014 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have hb := bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (bridge x))
    have hl : wg.length = 12 := rfl
    exact ⟨wg, 19, wfits, by omega, weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
